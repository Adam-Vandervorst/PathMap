import PathMapModel.Spec

/-!
# Differential-fuzzing front end

This module turns the model into an **oracle**: it decodes a raw fuzzer input
into a program over two maps and two zippers, runs it, and emits a trace.  The
Rust side (`differential/src/bin/pathmap_trace.rs`) decodes the *same bytes* with the *same*
rules and emits the *same* trace format from the real crate, so any behavioural
divergence shows up as a textual diff.

## Wire format

The input is consumed one byte at a time; decoding stops (and the program ends)
as soon as the input runs out.

```
header:
  n         := u8 % 8            -- entries seeded into map0 (the write target)
  n × ( len := u8 % 6 ; len × pathbyte ; val := u8 )
  n         := u8 % 8            -- entries seeded into map1 (the read source)
  n × ( len := u8 % 6 ; len × pathbyte ; val := u8 )
  r0        := u8 % 4 ; r0 × pathbyte    -- write zipper root
  r1        := u8 % 4 ; r1 × pathbyte    -- read  zipper root
body:
  repeated: op := u8 % 56 ; operands per op (see `Op.decode`)
```

Every **path byte** is masked to `b % 4`, so the generated tries share prefixes
heavily — that is where the interesting trie shapes (branch points, dangling
chains, single-child runs) live.

## Trace format

One line per operation:

```
<i> <name> ret=<r> W=<path> e<0|1> v<val|-> c<count> n<valcount> R=<...>
```

followed by a full dump of both maps.  Values are decimal, paths are lowercase
hex, `e` is `path_exists`, `c` is `child_count`, `n` is `val_count`.
-/

namespace PathMapModel
namespace Fuzz

/-- The value type used by the differential harness: `PathMap<u64>`. -/
abbrev V := UInt64
/-- The `Lattice`/`DistributiveLattice` instance `pathmap` provides for `u64`. -/
def ops : ValOps V := u64Ops

/-! ## Rendering -/

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def hexByte (b : UInt8) : String :=
  let n := b.toNat
  String.ofList [hexDigit (n / 16), hexDigit (n % 16)]

def hexPath (p : Path) : String :=
  if p.isEmpty then "_" else String.join (p.map hexByte)

/-- Render the `Option<u8>` the movement operations now return: the byte moved
to, or `-` for "did not move". -/
def showByteOpt : Option UInt8 → String
  | none => "-"
  | some b => hexByte b

def showVal : Option V → String
  | none => "-"
  | some v => toString v.toNat

/-- One location of a dump: its path and its value. -/
def showEntry (t : PathMap V) (root : Path) (q : Path) : String :=
  hexPath q ++ ":" ++ showVal (t.valAt (root ++ q))

/-- All locations at and below `root`, depth-first, capped so a runaway trie
cannot make the trace unbounded. -/
def dumpAt (t : PathMap V) (root : Path) : String :=
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

/-- Read one *path* byte.  Masked to a 4-letter alphabet so that generated
tries share prefixes and actually branch. -/
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

/-- Two maps, two zippers: `wz` writes into map0, `rz` reads map1.  Keeping the
read source in a *separate* map is what lets the real crate hold both zippers at
once. -/
structure St where
  wz : Zip V
  rz : Zip V
  out : List String
  step : Nat
  /-- Read source is an `ArenaCompactTree` rather than a `PathMap`.

  ACT is read-only, and more restrictively it does not implement
  `ZipperInfallibleSubtries` (and implements `ZipperSubtries` only for
  `Value = ()`), so it cannot be the *source* of a graft or an algebraic merge.
  In this mode those operations, and `make_map` on the read side, report `skip`
  on both sides of the comparison.  Everything else -- every read, movement and
  iteration operation, and the whole final trie -- is compared in full, which is
  the point: ACT is a second implementation of the same specification. -/
  act : Bool

/-- The per-step fingerprint of one zipper. -/
def fingerprint (z : Zip V) : String :=
  hexPath z.path ++ " o" ++ hexPath z.focus ++
  " e" ++ (if z.pathExists then "1" else "0") ++
  " v" ++ showVal z.val ++ " c" ++ toString z.childCount ++
  " n" ++ toString z.valCount ++
  -- `focus_byte` is unspecified at the root, so it is only compared below it.
  " f" ++ (if z.atRoot then "?" else showByteOpt z.focusByte)

def emit (s : St) (name : String) (ret : String) : St :=
  { s with
    out := (toString s.step ++ " " ++ name ++ " ret=" ++ ret ++
            " W=" ++ fingerprint s.wz ++ " R=" ++ fingerprint s.rz) :: s.out
    step := s.step + 1 }

def showBool (b : Bool) : String := if b then "1" else "0"


/-- Is the *explicit* `prune_path` / `prune_ascend` well-defined for this state?

Only for a write zipper rooted at the map root.  Pruning happens in two places:
`node_remove_*` prunes within the internal node holding the focus, and
`prune_path_internal` prunes the trie above it but stops at the zipper's origin.
With a non-empty zipper root the two disagree and the depth pruned becomes a
function of node layout rather than of the logical trie — a 40-byte dangling
chain under a zipper rooted at depth 5 prunes to the map root, a 100-byte one
stops at the zipper root.

The `prune` *flag* on the other operations is worse: it is passed straight to
`node_remove_val` / `node_remove_all_branches`, which prune within the node even
when they find nothing to remove and report `None`.  So `remove_val(true)` can
delete a dangling location while returning `None`, and whether it does depends on
where the node boundary falls.  The harness therefore always passes
`prune = false` to those operations (see `noPrune`) and gates the explicit prune
operations on this predicate. -/
def pruneable (s : St) : Bool := s.wz.root.isEmpty

/-- The `prune` flag the harness passes to operations that take one.

Always `false`: the flag's effect is a function of internal node layout rather
than of the logical trie, so there is nothing for a model to agree with.  See
`pruneable` and lean/FINDINGS.md finding 7. -/
def noPrune : Bool := false

/-! ## The operation table

`op % 47` selects the operation.  Ops `0`–`26` act on a target zipper chosen by
a following `u8 % 2` byte (`0` = write zipper, `1` = read zipper); ops `27`–`46`
are write-zipper operations. -/

/-- Number of distinct operations.  Must match `NOPS` in `differential/src/harness.rs`. -/
def nops : Nat := 56

/-- A full `k`-path iteration: `descend_first_k_path` followed by
`to_next_k_path` until it runs out (capped at 32 stops).  Returns the locations
visited.  This is the only well-defined way to use the k-path primitives. -/
def kWalk (z : Zip V) (k : Nat) : List Path × Zip V :=
  let (ok, z1) := z.descendFirstKPath k
  if !ok then ([], z1) else go 31 z1 [z1.path]
where
  go : Nat → Zip V → List Path → List Path × Zip V
    | 0, z, acc => (acc.reverse, z)
    | n + 1, z, acc =>
        let (moved, z') := z.toNextKPath k
        if moved then go n z' (z'.path :: acc) else (acc.reverse, z')

/-- Apply `f` to the zipper selected by `t`. -/
def onTarget (s : St) (t : Nat) (f : Zip V → α × Zip V) : α × St :=
  if t == 0 then let (a, z) := f s.wz; (a, { s with wz := z })
  else let (a, z) := f s.rz; (a, { s with rz := z })

/-- Apply an observing operation to the zipper selected by `t`. -/
def onTargetObs (s : St) (t : Nat) (f : Zip V → Bool × Path × Zip V) : Bool × Path × St :=
  if t == 0 then let (a, o, z) := f s.wz; (a, o, { s with wz := z })
  else let (a, o, z) := f s.rz; (a, o, { s with rz := z })

/-- Read the zipper selected by `t`. -/
def getTarget (s : St) (t : Nat) : Zip V := if t == 0 then s.wz else s.rz

/-- Decode and run one operation.  `none` means the input ran out mid-operation,
which ends the program. -/
def step (s : St) (d : Dec) : Option (St × Dec) := do
  let (opRaw, d) ← d.u8
  let op := opRaw.toNat % nops
  match op with
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
             -- escapes its own root there (see the notes in `Zip.toNextSiblingByte`).
             if (getTarget s t).atRoot then some (emit s "to_next_sibling_byte" "skip", d)
             else
               let (r, s) := onTarget s t (fun z => z.toNextSiblingByte)
               some (emit s "to_next_sibling_byte" (showByteOpt r), d)
  | 12 => do let (t, d) ← d.mod 2
             if (getTarget s t).atRoot then some (emit s "to_prev_sibling_byte" "skip", d)
             else
               let (r, s) := onTarget s t (fun z => z.toPrevSiblingByte)
               some (emit s "to_prev_sibling_byte" (showByteOpt r), d)
  | 13 => do let (t, d) ← d.mod 2
             let (r, s) := onTarget s t (fun z => z.toNextStep)
             some (emit s "to_next_step" (showBool r), d)
  | 14 => do let (_t, d) ← d.mod 2
             -- `ZipperIteration` is read-only: the target byte is still consumed,
             -- but the operation always applies to the read zipper.
             let (r, z) := s.rz.toNextVal
             some (emit { s with rz := z } "to_next_val" (showBool r), d)
  | 15 => do let (_t, d) ← d.mod 2; let (k, d) ← d.mod 4
             -- `k = 0` is degenerate: `k_path_internal` treats "already at depth
             -- base+0" as a hit and reports success without moving, then
             -- `to_next_k_path(0)` reports success forever.  Skipped.
             if k == 0 then some (emit s "descend_first_k_path" "skip", d)
             else
               let (r, z) := s.rz.descendFirstKPath k
               some (emit { s with rz := z } "descend_first_k_path" (showBool r), d)
  | 16 => do let (_t, d) ← d.mod 2; let (k, d) ← d.mod 4
             -- `to_next_k_path` is only meaningful as the continuation of a
             -- `descend_first_k_path` iteration -- `k_path_internal` carries
             -- iteration state, and calling it cold is flagged by pathmap's own
             -- debug assertions.  So the op is the whole walk, not one step.
             if k == 0 then some (emit s "k_path_walk" "skip", d)
             else
               let (ps, z) := kWalk s.rz k
               some (emit { s with rz := z } "k_path_walk"
                 (String.intercalate "," (ps.map hexPath)), d)
  | 17 => do let (_t, d) ← d.mod 2
             -- `ZipperIteration` is read-only: the target byte is still consumed,
             -- but the operation always applies to the read zipper.
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
             if s.act && t == 1 then some (emit s "make_map_val_count" "skip", d)
             else
               let z := getTarget s t
               some (emit s "make_map_val_count" (toString (z.makeMap.valCount [])), d)
  | 26 => do let (t, d) ← d.mod 2
             let z := getTarget s t
             some (emit s "dump" (dumpAt z.trie z.focus), d)
  | 27 => do let (v, d) ← d.u8
             let (old, z) := s.wz.setVal (UInt64.ofNat v.toNat)
             some (emit { s with wz := z } "set_val" (showVal old), d)
  | 28 => do let (_pr, d) ← d.bool
             let (old, z) := s.wz.removeVal noPrune
             some (emit { s with wz := z } "remove_val" (showVal old), d)
  | 29 => do let (r, z) := s.wz.createPath
             some (emit { s with wz := z } "create_path" (showBool r), d)
  | 30 => do if pruneable s then
               let (n, z) := s.wz.prunePath
               some (emit { s with wz := z } "prune_path" (toString n), d)
             else some (emit s "prune_path" "skip", d)
  | 31 => do if pruneable s then
               let (n, z) := s.wz.pruneAscend
               some (emit { s with wz := z } "prune_ascend" (toString n), d)
             else some (emit s "prune_ascend" "skip", d)
  | 32 => do let (_pr, d) ← d.bool
             let leaky := s.wz.focusNodeIsEmpty
             let (r, z) := s.wz.removeBranches noPrune
             some (emit { s with wz := z } "remove_branches"
               (if leaky then "?" else showBool r), d)
  | 33 => do let (n, d) ← d.mod 4; let (m, d) ← d.pathN n; let (_pr, d) ← d.bool
             let z := s.wz.removeUnmaskedBranches (ByteMask.ofList m) noPrune
             some (emit { s with wz := z } "remove_unmasked_branches" (hexPath (ByteMask.ofList m)), d)
  | 34 => do if s.act then some (emit s "graft" "skip", d) else
             do
               let z := s.wz.graft s.rz
               some (emit { s with wz := z } "graft" "-", d)
  | 35 => do let (p, d) ← d.path
             if s.act then some (emit s "graft_src_at" "skip", d)
             else
               let z := s.wz.graftSrcAt s.rz p
               some (emit { s with wz := z } "graft_src_at" (hexPath p), d)
  | 36 => do if s.act then some (emit s "join_into" "skip", d) else
             do
               let (st, z) := s.wz.joinInto ops s.rz
               some (emit { s with wz := z } "join_into" (toString st), d)
  | 37 => do if s.act then some (emit s "join_map_into" "skip", d) else
             do
               let leaky := s.wz.focusNodeIsEmpty
               let (st, z) := s.wz.joinMapInto ops s.rz.makeMap
               some (emit { s with wz := z } "join_map_into"
                 (if leaky then "?" else toString st), d)
  | 38 => do let (_pr, d) ← d.bool
             if s.act then some (emit s "meet_into" "skip", d)
             else
               let (st, z) := s.wz.meetInto ops s.rz noPrune
               some (emit { s with wz := z } "meet_into" (toString st), d)
  | 39 => do let (_pr, d) ← d.bool
             if s.act then some (emit s "subtract_into" "skip", d)
             else
               let (st, z) := s.wz.subtractInto ops s.rz noPrune
               some (emit { s with wz := z } "subtract_into" (toString st), d)
  | 40 => do if s.act then some (emit s "restrict" "skip", d) else
             do
               let leaky := s.wz.focusNodeIsEmpty
               let (st, z) := s.wz.restrict ops s.rz
               some (emit { s with wz := z } "restrict"
                 (if leaky then "?" else toString st), d)
  | 41 => do if s.act then some (emit s "restricting" "skip", d) else
             do
               -- Skipped, not merely masked, when either side has nothing below
               -- its focus: there `restricting` branches on whether an empty node
               -- happens to be materialised, and the two branches differ in
               -- *effect*, not just in the reported bool.  See FINDINGS.md #8.
               if s.wz.focusNodeIsEmpty || s.rz.focusNodeIsEmpty then
                 some (emit s "restricting" "skip", d)
               else
                 let (r, z) := s.wz.restricting s.rz
                 some (emit { s with wz := z } "restricting" (showBool r), d)
  | 42 => do let (k, d) ← d.mod 4; let (_pr, d) ← d.bool
             -- `join_k_path_into(0)` should be the identity but destroys the
             -- subtrie in pathmap 0.3.1; see `Zip.joinKPathInto`.
             if k == 0 then some (emit s "join_k_path_into" "skip", d)
             else
               -- The bool is another `AbstractNodeRef` leak: an empty node still
               -- comes back as `Some(...)` from `into_option()` for some
               -- representations, so `true` gets reported for a collapse that
               -- produced nothing.  Compared only when something survived.
               -- See FINDINGS.md #8.
               let (r, z) := s.wz.joinKPathInto ops k noPrune
               some (emit { s with wz := z } "join_k_path_into"
                 (if z.focusNodeIsEmpty then "?" else showBool r), d)
  | 43 => do let (p, d) ← d.path
             -- `insert_prefix("")` destroys the subtrie in pathmap 0.3.1; see
             -- `Zip.insertPrefix`.  Skipped so the known bug does not mask others.
             if p.isEmpty then
               some (emit s "insert_prefix" "skip", d)
             else
               let (r, z) := s.wz.insertPrefix p
               some (emit { s with wz := z } "insert_prefix" (showBool r), d)
  | 44 => do let (n, d) ← d.mod 6
             let (r, z) := s.wz.removePrefix n
             some (emit { s with wz := z } "remove_prefix" (showBool r), d)
  | 45 => do let (_pr, d) ← d.bool
             let leaky := s.wz.focusNodeIsEmpty && s.wz.val.isNone
             let (m, z) := s.wz.takeMap noPrune
             if leaky then
               some (emit { s with wz := (z.graftMap (m.getD PathMap.empty)) }
                 "take_map_restore" "?", d)
             else
             match m with
             | some mm => some (emit { s with wz := z.graftMap mm } "take_map_restore" "1", d)
             | none => some (emit { s with wz := z } "take_map_restore" "0", d)
  | 46 => do let (k, d) ← d.mod 4; let (_pr, d) ← d.bool
             -- `meet_k_path_into` is not implementable for these arguments; see
             -- `Zip.meetKPathUnspecified`.  The Rust side applies the same guard.
             if s.wz.meetKPathUnspecified k then
               some (emit s "meet_k_path_into" "skip", d)
             else
               let (r, z) := s.wz.meetKPathInto ops k noPrune
               some (emit { s with wz := z } "meet_k_path_into" (showBool r), d)
  | 47 => do let (t, d) ← d.mod 2
             -- The blind-zipper addition: `descend_until` reporting the bytes it
             -- descended.  The observer's output is a blind zipper's only account
             -- of where it went, so it is compared byte for byte.
             let (r, obs, s) := onTargetObs s t (fun z => z.descendUntilObserved)
             some (emit s "descend_until_observed" (showBool r ++ ":" ++ hexPath obs), d)
  | 48 => do let (v, d) ← d.u8
             -- Writing through the reference `get_val_mut` hands back.  It must
             -- behave like `set_val` where a value exists and do nothing --
             -- crucially, *not* create the path -- where one does not.
             let (old, z) := s.wz.getValMutWrite (UInt64.ofNat v.toNat)
             some (emit { s with wz := z } "get_val_mut_write" (showVal old), d)
  | 49 => do let (v, d) ← d.u8
             let (r, z) := s.wz.getValOrSetMut (UInt64.ofNat v.toNat)
             some (emit { s with wz := z } "get_val_or_set_mut" (showVal (some r)), d)
  | 50 => do let (v, d) ← d.u8
             -- `ran` records whether the closure was invoked.  The contract says
             -- it supplies the value "if no value exists", so invoking it when a
             -- value is already present is observable to any caller whose closure
             -- has a side effect.
             let (r, ran, z) := s.wz.getValOrSetMutWith (UInt64.ofNat v.toNat)
             some (emit { s with wz := z } "get_val_or_set_mut_with"
               (showVal (some r) ++ ":" ++ showBool ran), d)
  | 51 => do let (t, d) ← d.mod 2; let (p, d) ← d.path
             -- `ZipperReadOnlyValues::get_val`/`get_val_at` differ from
             -- `val`/`val_at` only in the lifetime of the reference they return,
             -- so they must give the same answer.  `agree` is `1` in the model by
             -- construction; a `0` from the crate is the whole point of the op.
             let z := getTarget s t
             some (emit s "get_val_agrees"
               (showVal z.val ++ ":" ++ showVal (z.valAt p) ++ ":1"), d)
  | 52 => do -- `ZipperReadOnlyIteration::to_next_get_val` must advance exactly as
             -- `to_next_val` does and hand back the value at the new focus.
             -- ACT does not implement the trait, so the op is unavailable there.
             if s.act then some (emit s "to_next_get_val" "skip", d) else
             do
             let (moved, z) := s.rz.toNextVal
             let v := if moved then z.val else none
             some (emit { s with rz := z } "to_next_get_val"
               (showBool moved ++ ":" ++ showVal v ++ ":1"), d)
  | 53 => do let (n, d) ← d.mod 4; let (m, d) ← d.pathN n; let (ru, d) ← d.bool
             if s.act then some (emit s "graft_masked_branches" "skip", d) else
             do
               let z := s.wz.graftMaskedBranches s.rz (ByteMask.ofList m) ru
               some (emit { s with wz := z } "graft_masked_branches"
                 (hexPath (ByteMask.ofList m) ++ ":" ++ showBool ru), d)
  | 54 => do let (n, d) ← d.mod 4; let (m, d) ← d.pathN n; let (ru, d) ← d.bool
             -- Fed the source's own child subtries, this must agree with
             -- `graft_masked_branches` on the same mask.
             -- Skipped outright, not just in ACT mode: `graft_child_maps` is
             -- broken three ways (FINDINGS.md #15) and the node representations
             -- it leaves behind degrade the `AlgebraicStatus` that *later*
             -- operations report, which would contaminate the whole run.
             if true then some (emit s "graft_child_maps" "skip", d) else
             do
               let mask := ByteMask.ofList m
               let maps := mask.map (fun b => ([b], s.rz.trie.subtrie (s.rz.focus ++ [b])))
               let z := s.wz.graftChildMaps maps ru
               some (emit { s with wz := z } "graft_child_maps"
                 (hexPath mask ++ ":" ++ showBool ru), d)
  | 55 => do let (p, d) ← d.path
             -- `meet_2` takes two sources; the second is the first moved to `p`.
             if s.act then some (emit s "meet_2" "skip", d) else
             do
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
def seed (t : PathMap V) (d : Dec) : Nat → Option (PathMap V × Dec)
  | 0 => some (t, d)
  | n + 1 => do
      let (p, d) ← d.path
      let (v, d) ← d.u8
      seed (t.setVal p (UInt64.ofNat v.toNat)).2 d n

/-- Decode the header: two seeded maps and the two zipper roots. -/
def header (d : Dec) (act : Bool) : Option (St × Dec) := do
  let (n0, d) ← d.mod 8
  let (m0, d) ← seed PathMap.empty d n0
  let (n1, d) ← d.mod 8
  let (m1, d) ← seed PathMap.empty d n1
  let (r0, d) ← d.path 4
  let (r1, d) ← d.path 4
  -- Both zipper roots are created if absent.  A zipper whose *root* does not
  -- exist can escape it — `to_next_sibling_byte` and `to_next_step` fall back on
  -- the parent's child mask and walk out of the granted subtrie (confirmed in
  -- pathmap 0.3.1, see `Zip.toNextSiblingByte`).  Making the roots exist keeps
  -- that one bug from contaminating every other comparison.
  let m0 := if r0.isEmpty then m0 else m0.addPath r0
  let m1 := if r1.isEmpty then m1 else m1.addPath r1
  some ({ wz := { trie := m0, root := r0, path := [] }
          rz := { trie := m1, root := r1, path := [] }
          out := [], step := 0, act := act }, d)

/-! ## Entry point -/

/-- Decode and run a fuzzer input, returning the trace lines. -/
def run (bytes : ByteArray) (maxSteps : Nat := 256) (act : Bool := false) : List String :=
  match header { bytes, pos := 0 } act with
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
end PathMapModel
