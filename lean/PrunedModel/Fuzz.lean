import PrunedModel.Spec

/-!
# Differential-fuzzing front end for the dangling-path-free subset

This module turns `PrunedModel` into an **oracle**: it decodes a raw fuzzer
input into a program over two maps and two zippers, runs it, and emits a trace.
`differential/src/pruned.rs` decodes the *same bytes* with the *same* rules and
emits the *same* trace format from the real crate, so a behavioural divergence
is a textual diff.  `lean/pruned_differential.py` drives the pair.

## How this differs from `PathMapModel.Fuzz`

That harness explores the whole zipper API and reproduces whatever `pathmap`
does with dangling paths, including the parts nobody wants.  Its prune flags are
therefore pinned to `false` and compared against nothing, because the flag's
effect is a function of where an internal node boundary happens to fall.

This one explores a smaller API and makes a stronger claim about it.  Three
restrictions define the subset:

1. **No `create_path`.**  Its whole purpose is a location with no value.
2. **`prune = true` everywhere.**  Removal here is inherently pruning: a chain
   that exists only to reach a value goes when the value does.  `prune_path` and
   `prune_ascend` stay in the table as *assertions* — the model says `0`, so a
   non-zero count from the crate means something in the subset leaked a dangling
   path for it to find.
3. **The write zipper is rooted at the map root.**  A write zipper rooted below
   it holds a node at its own root, which survives as a location leading nowhere
   once everything beneath is removed, and `prune_path` is documented not to rise
   above the zipper's origin.  That is outside the model by construction rather
   than by a bug.  Off-root *writing* is still covered: the root-rooted zipper
   reaches every focus with `descend_to`.

The read zipper may be rooted anywhere that exists.  Its root is decoded as a
path and then clamped to its longest existing prefix, so it is never a location
the seeding did not create — a read zipper whose root does not exist can walk
out of it (FINDINGS.md #3), which would contaminate every other comparison.

Operations that *can* still leave a dangling path in `pathmap` 0.4.0 are
specified, not skipped.  `graft` of an empty source is the clearest: the focus
loses its value and its branches, so the model removes it and the chain above
it, while the crate leaves both behind.  Producing those divergences is what
this harness is for.

## Wire format

The input is consumed one byte at a time; decoding stops, and the program ends,
as soon as the input runs out.

```
header:
  n         := u8 % 8            -- entries seeded into map0 (the write target)
  n × ( len := u8 % 6 ; len × pathbyte ; val := u8 )
  n         := u8 % 8            -- entries seeded into map1 (the read source)
  n × ( len := u8 % 6 ; len × pathbyte ; val := u8 )
  r1        := u8 % 4 ; r1 × pathbyte    -- read zipper root, clamped to its
                                         -- longest existing prefix
body:
  repeated: op := u8 % 54 ; operands per op (see `step`)
```

Every **path byte** is masked to `b % 4`, so generated tries share prefixes
heavily — that is where the interesting shapes (branch points, single-child
runs, chains that exist only to reach one value) live.

## Trace format

One line per operation:

```
<i> <name> ret=<r> W=<path> o<origin> e<0|1> v<val|-> c<count> n<valcount> f<byte> R=<...>
```

followed by a dump of both maps.  Values are decimal, paths lowercase hex, `e`
is `path_exists`, `c` is `child_count`, `n` is `val_count`.  A location with no
value renders as `-`, so a dangling path the crate left behind shows up in the
dump as an entry the model does not have.
-/

namespace PrunedModel
namespace Fuzz

open PathMapModel

/-- The value type the harness uses: `PathMap<u64>`. -/
abbrev V := UInt64
/-- The `Lattice`/`DistributiveLattice` instance `pathmap` provides for `u64`. -/
def ops : ValOps V := u64Ops

/-! ## Skip reasons

Why an operation was skipped.  Every `skip` in the trace carries one, so a
skipped op says which rule declined it.  `differential/src/pruned.rs` emits the
same tokens; the two must agree exactly or every input with a skip diverges.

Note which reasons from `PathMapModel.Fuzz` are *absent*: `skip:act` (there is
one read source here), `skip:off-root-prune` (the write zipper is always at the
map root, so the prune count is well-defined), and `skip:quarantined`
(`graft_child_maps` is not in this table at all). -/

/-- `to_next`/`to_prev_sibling_byte` at the zipper root, where the native read
zipper escapes its own root. -/
def skipAtRoot : String := "skip:at-root"
/-- A degenerate `k = 0` on `join_k_path_into` / `meet_k_path_into`. -/
def skipK0 : String := "skip:k0"
/-- The focus has nothing below it, where the op's behaviour is a function of
node materialisation rather than of trie state. -/
def skipEmptyFocus : String := "skip:empty-focus"
/-- `insert_prefix("")`, which destroys the subtrie. -/
def skipEmptyPath : String := "skip:empty-path"

/-! ## Rendering -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexByte (b : UInt8) : String :=
  let n := b.toNat
  String.ofList [hexDigit (n / 16), hexDigit (n % 16)]

def hexPath (p : Path) : String :=
  if p.isEmpty then "_" else String.join (p.map hexByte)

/-- The byte a movement operation moved to, or `-` for "did not move". -/
def showByteOpt : Option UInt8 → String
  | none => "-"
  | some b => hexByte b

def showVal : Option V → String
  | none => "-"
  | some v => toString v.toNat

def showBool (b : Bool) : String := if b then "1" else "0"

/-- One location of a dump: its path, relative to `root`, and its value. -/
def showEntry (t : PrunedMap V) (root : Path) (q : Path) : String :=
  hexPath q ++ ":" ++ showVal (t.valAt (root ++ q))

/-- All locations at and below `root`, depth-first, capped so a runaway trie
cannot make the trace unbounded.

Every entry here *should* carry a value or lead to one.  An entry rendering `-`
with nothing below it is a dangling path, which is the divergence this harness
exists to find. -/
def dumpAt (t : PrunedMap V) (root : Path) : String :=
  let qs := (t.subtrie root).paths.take 64
  String.intercalate "," (qs.map (showEntry t root))

/-! ## Decoder -/

/-- A cursor over the fuzzer's input bytes. -/
structure Dec where
  bytes : ByteArray
  pos : Nat

/-- Read one byte; `none` once the input is exhausted, which ends the program. -/
def Dec.u8 (d : Dec) : Option (UInt8 × Dec) :=
  if h : d.pos < d.bytes.size then some (d.bytes[d.pos]'h, { d with pos := d.pos + 1 })
  else none

/-- Read one byte reduced modulo `m`. -/
def Dec.mod (d : Dec) (m : Nat) : Option (Nat × Dec) :=
  d.u8.map (fun (b, d') => (if m == 0 then 0 else b.toNat % m, d'))

/-- Read one *path* byte.  Masked to a 4-letter alphabet so generated tries
share prefixes and actually branch. -/
def Dec.pathByte (d : Dec) : Option (UInt8 × Dec) :=
  d.u8.map (fun (b, d') => (UInt8.ofNat (b.toNat % 4), d'))

/-- Read `n` path bytes. -/
def Dec.pathN (d : Dec) : Nat → Option (Path × Dec)
  | 0 => some ([], d)
  | n + 1 => do
      let (b, d) ← d.pathByte
      let (rest, d) ← d.pathN n
      some (b :: rest, d)

/-- Read a length-prefixed path (`len := u8 % lim`). -/
def Dec.path (d : Dec) (lim : Nat := 6) : Option (Path × Dec) := do
  let (n, d) ← d.mod lim
  d.pathN n

/-- Read a boolean (`u8 % 2`). -/
def Dec.bool (d : Dec) : Option (Bool × Dec) :=
  d.u8.map (fun (b, d') => (b.toNat % 2 == 1, d'))

/-! ## Interpreter state -/

/-- Two maps, two zippers: `wz` writes into map0 and is rooted at its root, `rz`
reads map1.  Keeping the read source in a separate map is what lets the real
crate hold both zippers at once. -/
structure St where
  wz : PZip V
  rz : PZip V
  out : List String
  step : Nat

/-- The per-step fingerprint of one zipper. -/
def fingerprint (z : PZip V) : String :=
  hexPath z.path ++ " o" ++ hexPath z.focus ++
  " e" ++ showBool z.pathExists ++
  " v" ++ showVal z.val ++ " c" ++ toString z.childCount ++
  " n" ++ toString z.valCount ++
  -- `focus_byte` is unspecified at the root, so it is only compared below it.
  " f" ++ (if z.atRoot then "?" else showByteOpt z.focusByte)

def emit (s : St) (name : String) (ret : String) : St :=
  { s with
    out := (toString s.step ++ " " ++ name ++ " ret=" ++ ret ++
            " W=" ++ fingerprint s.wz ++ " R=" ++ fingerprint s.rz) :: s.out
    step := s.step + 1 }

/-! ## The operation table

`op % nops` selects the operation.  Ops `0`–`29` act on a target zipper chosen
by a following `u8 % 2` byte (`0` = write zipper, `1` = read zipper); ops
`30`–`53` are write-zipper operations. -/

/-- Number of distinct operations.  Must match `NOPS` in
`differential/src/pruned.rs`. -/
def nops : Nat := 54

/-- A full `k`-path iteration: `descend_first_k_path` followed by
`to_next_k_path` until it runs out (capped at 32 stops).  Returns the locations
visited.  This is the only well-defined way to use the `k`-path primitives:
`k_path_internal` carries iteration state, so calling `to_next_k_path` cold is
flagged by `pathmap`'s own debug assertions. -/
def kWalk (z : PZip V) (k : Nat) : List Path × PZip V :=
  let (ok, z1) := z.descendFirstKPath k
  if !ok then ([], z1) else go 31 z1 [z1.path]
where
  go : Nat → PZip V → List Path → List Path × PZip V
    | 0, z, acc => (acc.reverse, z)
    | n + 1, z, acc =>
        let (moved, z') := z.toNextKPath k
        if moved then go n z' (z'.path :: acc) else (acc.reverse, z')

/-- Apply `f` to the zipper selected by `t`. -/
def onTarget (s : St) (t : Nat) (f : PZip V → α × PZip V) : α × St :=
  if t == 0 then let (a, z) := f s.wz; (a, { s with wz := z })
  else let (a, z) := f s.rz; (a, { s with rz := z })

/-- Apply an observing operation to the zipper selected by `t`. -/
def onTargetObs (s : St) (t : Nat) (f : PZip V → Bool × Path × PZip V) : Bool × Path × St :=
  if t == 0 then let (a, o, z) := f s.wz; (a, o, { s with wz := z })
  else let (a, o, z) := f s.rz; (a, o, { s with rz := z })

/-- Read the zipper selected by `t`. -/
def getTarget (s : St) (t : Nat) : PZip V := if t == 0 then s.wz else s.rz

/-- Decode and run one operation.  `none` means the input ran out mid-operation,
which ends the program. -/
def step (s : St) (d : Dec) : Option (St × Dec) := do
  let (opRaw, d) ← d.u8
  let op := opRaw.toNat % nops
  match op with
  -- ## Movement and reading, on either zipper
  | 0 => do let (t, d) ← d.mod 2; let (p, d) ← d.path
            let (_, s) := onTarget s t (fun z => ((), z.descendTo p))
            some (emit s "descend_to" (hexPath p), d)
  | 1 => do let (t, d) ← d.mod 2; let (b, d) ← d.pathByte
            let (_, s) := onTarget s t (fun z => ((), z.descendToByte b))
            some (emit s "descend_to_byte" (hexByte b), d)
  | 2 => do let (t, d) ← d.mod 2; let (n, d) ← d.mod 8
            let (r, s) := onTarget s t (fun z => z.ascend n)
            some (emit s "ascend" (toString r), d)
  | 3 => do let (t, d) ← d.mod 2
            let (r, s) := onTarget s t (fun z => z.ascendByte)
            some (emit s "ascend_byte" (showBool r), d)
  | 4 => do let (t, d) ← d.mod 2
            let (_, s) := onTarget s t (fun z => ((), z.reset))
            some (emit s "reset" "-", d)
  | 5 => do let (t, d) ← d.mod 2
            let (r, s) := onTarget s t (fun z => z.descendFirstByte)
            some (emit s "descend_first_byte" (showByteOpt r), d)
  | 6 => do let (t, d) ← d.mod 2
            let (r, s) := onTarget s t (fun z => z.descendLastByte)
            some (emit s "descend_last_byte" (showByteOpt r), d)
  | 7 => do let (t, d) ← d.mod 2; let (i, d) ← d.mod 6
            let (r, s) := onTarget s t (fun z => z.descendIndexedByte i)
            some (emit s "descend_indexed_byte" (showByteOpt r), d)
  | 8 => do let (t, d) ← d.mod 2
            let (r, s) := onTarget s t (fun z => z.descendUntil)
            some (emit s "descend_until" (showBool r), d)
  | 9 => do let (t, d) ← d.mod 2
            let (r, s) := onTarget s t (fun z => z.ascendUntil)
            some (emit s "ascend_until" (toString r), d)
  | 10 => do let (t, d) ← d.mod 2
             let (r, s) := onTarget s t (fun z => z.ascendUntilBranch)
             some (emit s "ascend_until_branch" (toString r), d)
  | 11 => do let (t, d) ← d.mod 2
             -- Skipped at the zipper root: `ReadZipper::to_next_sibling_byte`
             -- escapes its own root there.
             if (getTarget s t).atRoot then some (emit s "to_next_sibling_byte" skipAtRoot, d)
             else
               let (r, s) := onTarget s t (fun z => z.toNextSiblingByte)
               some (emit s "to_next_sibling_byte" (showByteOpt r), d)
  | 12 => do let (t, d) ← d.mod 2
             if (getTarget s t).atRoot then some (emit s "to_prev_sibling_byte" skipAtRoot, d)
             else
               let (r, s) := onTarget s t (fun z => z.toPrevSiblingByte)
               some (emit s "to_prev_sibling_byte" (showByteOpt r), d)
  | 13 => do let (t, d) ← d.mod 2
             let (r, s) := onTarget s t (fun z => z.toNextStep)
             some (emit s "to_next_step" (showBool r), d)
  | 14 => do let (_t, d) ← d.mod 2
             -- `ZipperIteration` is read-only: the target byte is still
             -- consumed, but the operation always applies to the read zipper.
             let (r, z) := s.rz.toNextVal
             some (emit { s with rz := z } "to_next_val" (showBool r), d)
  | 15 => do let (_t, d) ← d.mod 2; let (k, d) ← d.mod 4
             -- `k = 0` is specified: `false`, focus untouched.  `kPathFrom`
             -- gives that with no special case, since it wants a location
             -- strictly after the focus and the only one at depth base+0 is the
             -- focus itself.
             let (r, z) := s.rz.descendFirstKPath k
             some (emit { s with rz := z } "descend_first_k_path" (showBool r), d)
  | 16 => do let (_t, d) ← d.mod 2; let (k, d) ← d.mod 4
             -- The op is the whole walk, not one step; see `kWalk`.  With
             -- `k = 0` the descent fails, so the walk is empty and the
             -- never-ending `to_next_k_path(0)` is not reached.
             let (ps, z) := kWalk s.rz k
             some (emit { s with rz := z } "k_path_walk"
               (String.intercalate "," (ps.map hexPath)), d)
  | 17 => do let (_t, d) ← d.mod 2
             let (r, z) := s.rz.descendLastPath
             some (emit { s with rz := z } "descend_last_path" (showBool r), d)
  | 18 => do let (t, d) ← d.mod 2; let (p, d) ← d.path
             let (n, s) := onTarget s t (fun z => z.moveToPath p)
             some (emit s "move_to_path" (toString n), d)
  | 19 => do let (t, d) ← d.mod 2; let (p, d) ← d.path
             let (n, s) := onTarget s t (fun z => z.descendToExisting p)
             some (emit s "descend_to_existing" (toString n), d)
  | 20 => do let (t, d) ← d.mod 2; let (p, d) ← d.path
             let (n, s) := onTarget s t (fun z => z.descendToVal p)
             some (emit s "descend_to_val" (toString n), d)
  | 21 => do let (t, d) ← d.mod 2; let (b, d) ← d.pathByte
             let (r, s) := onTarget s t (fun z => z.descendToExistingByte b)
             some (emit s "descend_to_existing_byte" (showBool r), d)
  | 22 => do let (t, d) ← d.mod 2; let (n, d) ← d.mod 8
             let (r, s) := onTarget s t (fun z => z.descendUntilMaxBytes n)
             some (emit s "descend_until_max_bytes" (showBool r), d)
  | 23 => do let (t, d) ← d.mod 2; let (p, d) ← d.path
             let (r, s) := onTarget s t (fun z => z.descendToCheck p)
             some (emit s "descend_to_check" (showBool r), d)
  | 24 => do let (t, d) ← d.mod 2; let (p, d) ← d.path
             let z := getTarget s t
             some (emit s "val_at" (showVal (z.valAt p)), d)
  | 25 => do let (t, d) ← d.mod 2
             let z := getTarget s t
             some (emit s "make_map_val_count" (toString (z.makeMap.valCount [])), d)
  | 26 => do let (t, d) ← d.mod 2
             let z := getTarget s t
             some (emit s "dump" (dumpAt z.trie z.focus), d)
  | 27 => do let (t, d) ← d.mod 2
             -- The blind-zipper addition: `descend_until` reporting the bytes
             -- it descended.  The observer's output is a blind zipper's only
             -- account of where it went, so it is compared byte for byte.
             let (r, obs, s) := onTargetObs s t (fun z => z.descendUntilObserved)
             some (emit s "descend_until_observed" (showBool r ++ ":" ++ hexPath obs), d)
  | 28 => do let (t, d) ← d.mod 2; let (p, d) ← d.path
             -- `ZipperReadOnlyValues::get_val`/`get_val_at` differ from
             -- `val`/`val_at` only in the lifetime of the reference they
             -- return, so they must give the same answer.  `agree` is `1` in
             -- the model by construction; a `0` from the crate is the point.
             let z := getTarget s t
             some (emit s "get_val_agrees"
               (showVal z.val ++ ":" ++ showVal (z.valAt p) ++ ":1"), d)
  | 29 => do -- `ZipperReadOnlyIteration::to_next_get_val` must advance exactly
             -- as `to_next_val` does and hand back the value at the new focus.
             let (moved, z) := s.rz.toNextVal
             let v := if moved then z.val else none
             some (emit { s with rz := z } "to_next_get_val"
               (showBool moved ++ ":" ++ showVal v ++ ":1"), d)
  -- ## Writing, on the write zipper
  | 30 => do let (v, d) ← d.u8
             let (old, z) := s.wz.setVal (UInt64.ofNat v.toNat)
             some (emit { s with wz := z } "set_val" (showVal old), d)
  | 31 => do let (old, z) := s.wz.removeVal
             some (emit { s with wz := z } "remove_val" (showVal old), d)
  | 32 => do -- Must be `0`: a trie built from this subset has no dangling tip.
             let (n, z) := s.wz.prunePath
             some (emit { s with wz := z } "prune_path" (toString n), d)
  | 33 => do let (n, z) := s.wz.pruneAscend
             some (emit { s with wz := z } "prune_ascend" (toString n), d)
  | 34 => do let leaky := s.wz.focusNodeIsEmpty
             let (r, z) := s.wz.removeBranches
             -- An empty node still comes back as `Some(..)` from
             -- `into_option()` for some representations, so `true` gets
             -- reported for a removal of nothing.  Compared only when there was
             -- something below.
             some (emit { s with wz := z } "remove_branches"
               (if leaky then "?" else showBool r), d)
  | 35 => do let (n, d) ← d.mod 4; let (m, d) ← d.pathN n
             let z := s.wz.removeUnmaskedBranches (ByteMask.ofList m)
             some (emit { s with wz := z } "remove_unmasked_branches"
               (hexPath (ByteMask.ofList m)), d)
  | 36 => do let z := s.wz.graft s.rz
             some (emit { s with wz := z } "graft" "-", d)
  | 37 => do let (p, d) ← d.path
             let z := s.wz.graftSrcAt s.rz p
             some (emit { s with wz := z } "graft_src_at" (hexPath p), d)
  | 38 => do let (st, z) := s.wz.joinInto ops s.rz
             some (emit { s with wz := z } "join_into" (toString st), d)
  | 39 => do let leaky := s.wz.focusNodeIsEmpty
             let (st, z) := s.wz.joinMapInto ops s.rz.makeMap
             some (emit { s with wz := z } "join_map_into"
               (if leaky then "?" else toString st), d)
  | 40 => do let (st, z) := s.wz.meetInto ops s.rz
             some (emit { s with wz := z } "meet_into" (toString st), d)
  | 41 => do let (st, z) := s.wz.subtractInto ops s.rz
             some (emit { s with wz := z } "subtract_into" (toString st), d)
  | 42 => do let leaky := s.wz.focusNodeIsEmpty
             let (st, z) := s.wz.restrict ops s.rz
             some (emit { s with wz := z } "restrict"
               (if leaky then "?" else toString st), d)
  | 43 => do -- Skipped, not merely masked, when either side has nothing below
             -- its focus: there `restricting` branches on whether an empty node
             -- happens to be materialised, and the two branches differ in
             -- *effect*, not just in the reported bool.
             if s.wz.focusNodeIsEmpty || s.rz.focusNodeIsEmpty then
               some (emit s "restricting" skipEmptyFocus, d)
             else
               let (r, z) := s.wz.restricting s.rz
               some (emit { s with wz := z } "restricting" (showBool r), d)
  | 44 => do let (k, d) ← d.mod 4
             -- `join_k_path_into(0)` should be the identity but collapses the
             -- subtrie in `pathmap` 0.4.0.
             if k == 0 then some (emit s "join_k_path_into" skipK0, d)
             else
               let (r, z) := s.wz.joinKPathInto ops k
               some (emit { s with wz := z } "join_k_path_into"
                 (if z.focusNodeIsEmpty then "?" else showBool r), d)
  | 45 => do let (p, d) ← d.path
             -- `insert_prefix("")` destroys the subtrie in `pathmap` 0.4.0.
             if p.isEmpty then some (emit s "insert_prefix" skipEmptyPath, d)
             else
               let (r, z) := s.wz.insertPrefix p
               some (emit { s with wz := z } "insert_prefix" (showBool r), d)
  | 46 => do let (n, d) ← d.mod 6
             let (r, z) := s.wz.removePrefix n
             some (emit { s with wz := z } "remove_prefix" (showBool r), d)
  | 47 => do let leaky := s.wz.focusNodeIsEmpty && s.wz.val.isNone
             let (m, z) := s.wz.takeMap
             if leaky then
               some (emit { s with wz := (z.graftMap (m.getD PrunedMap.empty)) }
                 "take_map_restore" "?", d)
             else
             match m with
             | some mm => some (emit { s with wz := z.graftMap mm } "take_map_restore" "1", d)
             | none => some (emit { s with wz := z } "take_map_restore" "0", d)
  | 48 => do let (k, d) ← d.mod 4
             -- `meet_k_path_into` is not implementable for these arguments; see
             -- `PZip.meetKPathUnspecified`, whose two disjuncts are split out
             -- here so the skip names which one fired.
             if k == 0 then some (emit s "meet_k_path_into" skipK0, d)
             else if s.wz.focusNodeIsEmpty then
               some (emit s "meet_k_path_into" skipEmptyFocus, d)
             else
               let (r, z) := s.wz.meetKPathInto ops k
               some (emit { s with wz := z } "meet_k_path_into" (showBool r), d)
  | 49 => do let (v, d) ← d.u8
             -- Writing through the reference `get_val_mut` hands back.  It must
             -- behave like `set_val` where a value exists and do nothing --
             -- crucially, *not* create the path -- where one does not.
             let (old, z) := s.wz.getValMutWrite (UInt64.ofNat v.toNat)
             some (emit { s with wz := z } "get_val_mut_write" (showVal old), d)
  | 50 => do let (v, d) ← d.u8
             let (r, z) := s.wz.getValOrSetMut (UInt64.ofNat v.toNat)
             some (emit { s with wz := z } "get_val_or_set_mut" (showVal (some r)), d)
  | 51 => do let (v, d) ← d.u8
             -- `ran` records whether the closure was invoked.  The contract says
             -- it supplies the value "if no value exists", so invoking it when a
             -- value is already present is observable to any caller whose
             -- closure has a side effect.
             let (r, ran, z) := s.wz.getValOrSetMutWith (UInt64.ofNat v.toNat)
             some (emit { s with wz := z } "get_val_or_set_mut_with"
               (showVal (some r) ++ ":" ++ showBool ran), d)
  | 52 => do let (n, d) ← d.mod 4; let (m, d) ← d.pathN n; let (ru, d) ← d.bool
             let z := s.wz.graftMaskedBranches s.rz (ByteMask.ofList m) ru
             some (emit { s with wz := z } "graft_masked_branches"
               (hexPath (ByteMask.ofList m) ++ ":" ++ showBool ru), d)
  | 53 => do let (p, d) ← d.path
             -- `meet_2` takes two sources; the second is the first moved to `p`.
             let b := { s.rz with path := s.rz.path ++ p }
             let (st, z) := s.wz.meet2 ops s.rz b
             some (emit { s with wz := z } "meet_2" (toString st), d)
  | _ => some (emit s "nop" "-", d)

/-- Run operations until the input is exhausted or `fuel` runs out. -/
def loop : Nat → St → Dec → St
  | 0, s, _ => s
  | n + 1, s, d =>
      match step s d with
      | some (s', d') => loop n s' d'
      | none => s

/-! ## Header -/

/-- Decode `n` seed entries and insert them into `t`. -/
def seed (t : PrunedMap V) (d : Dec) : Nat → Option (PrunedMap V × Dec)
  | 0 => some (t, d)
  | n + 1 => do
      let (p, d) ← d.path
      let (v, d) ← d.u8
      seed (t.setVal p (UInt64.ofNat v.toNat)).2 d n

/-- The longest prefix of `p` that exists in `t`.

The read zipper's root is clamped this way instead of being created, because
`create_path` is not in this subset.  A zipper whose root does not exist can
escape it — `to_next_sibling_byte` and `to_next_step` fall back on the parent's
child mask and walk out of the granted subtrie — and that one bug would
contaminate every other comparison. -/
def clampToExisting (t : PrunedMap V) (p : Path) : Path :=
  -- Existence is prefix-closed, so the prefixes that exist form an initial
  -- segment and the longest one is the answer.
  p.take (((List.range (p.length + 1)).filter
    (fun j => t.pathExists (p.take j))).getLast?.getD 0)

/-- Decode the header: two seeded maps and the read zipper's root.  The write
zipper is always rooted at the map root; see the module docstring. -/
def header (d : Dec) : Option (St × Dec) := do
  let (n0, d) ← d.mod 8
  let (m0, d) ← seed PrunedMap.empty d n0
  let (n1, d) ← d.mod 8
  let (m1, d) ← seed PrunedMap.empty d n1
  let (r1raw, d) ← d.path 4
  let r1 := clampToExisting m1 r1raw
  some ({ wz := { trie := m0, root := [], path := [] }
          rz := { trie := m1, root := r1, path := [] }
          out := [], step := 0 }, d)

/-! ## Entry point -/

/-- Decode and run a fuzzer input, returning the trace lines. -/
def run (bytes : ByteArray) (maxSteps : Nat := 256) : List String :=
  match header { bytes, pos := 0 } with
  | none => ["EMPTY"]
  | some (s0, d) =>
      let s := loop maxSteps s0 d
      let final :=
        ("MAP0 " ++ dumpAt s.wz.trie []) ::
        ("MAP1 " ++ dumpAt s.rz.trie []) ::
        ("ROOT0 " ++ hexPath s.wz.root) ::
        ("ROOT1 " ++ hexPath s.rz.root) :: []
      s.out.reverse ++ final

end Fuzz
end PrunedModel
