import PathMapModel.PathMap

/-!
# The zipper

A `pathmap` zipper is a cursor into a trie.  Three things determine everything
it can observe or do:

* the **trie** it is looking at,
* its **root** — the absolute path at which it was created (`root_prefix_path`);
  the zipper can never ascend above it, and can never see anything outside the
  subtrie hanging below it, and
* its **path** — the relative path from the root to the current **focus**
  (`path()`); `origin_path() = root ++ path`.

Read zippers and write zippers share this state; they differ only in which
operations are offered.  `Zip` therefore models both: the read API lives here,
the mutating API in `Write.lean`.  For a read zipper `trie` is a snapshot taken
when the zipper was created (`fork_read_zipper` etc.); for a write zipper it is
the live map, so mutations write back through `root ++ path`.

## The focus may not exist

`descend_to` moves the focus anywhere, including off the trie.  `path_exists`
then reports `false` while `path()` still reports the full path and `ascend`
still walks back up.  The model reflects this by keeping `path` an unconstrained
list of bytes.

## The blind-zipper contract

`ZipperMoving` no longer provides `path()`: a zipper that does not track its own
path is a *blind* zipper, and `path()` / `move_to_path()` live in the separate
`ZipperPath: ZipperMoving` trait.  The model keeps `path` as a field because it
has to represent the location somehow, but it mirrors the split in what each
operation is allowed to *observe*: `focusByte` is the only positional
information a blind zipper can read, and its value at the root is deliberately
unspecified.

The migration also changed what the movement operations report.  Instead of a
bare "did it move" flag they now return how far, or where to:

* `ascend`, `ascend_until`, `ascend_until_branch` return the **number of bytes
  ascended** (`0` meaning "was already at the root") rather than a `bool`.
* `descend_indexed_byte`, `descend_first_byte`, `descend_last_byte`,
  `to_next_sibling_byte`, `to_prev_sibling_byte` return `Option<u8>` -- the byte
  moved to -- rather than a `bool`.
* `descend_until` gains an `_observed` form that reports the bytes it descended
  to a `PathObserver`, which is how a blind zipper learns where it ended up.

## Depth-first order is lexicographic order

Every iteration primitive is specified as "the `Path.lt`-least existing location
strictly after the focus, subject to ...".  That is equivalent to the
implementation's node-by-node walk, and far easier to state and to check.
-/

namespace PathMapModel

/-- A zipper: a trie, the absolute path of the zipper's root, and the relative
path to the focus. -/
structure Zip (V : Type) where
  trie : PathMap V
  root : Path
  path : Path
deriving Repr

namespace Zip

variable {V : Type} (z : Zip V)

/-- `ZipperAbsolutePath::origin_path`: the absolute path of the focus. -/
def focus : Path := z.root ++ z.path

/-- `ZipperAbsolutePath::root_prefix_path`. -/
def rootPrefixPath : Path := z.root

/-- All locations of the zipper's subtrie, relative to its root, in depth-first
order.  This is the zipper's entire visible universe. -/
def subPaths : List Path := (z.trie.subtrie z.root).paths

/-! ## `trait Zipper` -/

/-- What the trie holds at the focus: the whole answer to `path_exists` and
`val` at once.  Definitions that must handle a location existing *without* a
value are written against this, so the `match` will not compile until they say
what happens to it. -/
def entry : PathMap.Entry V := z.trie.entryAt z.focus

/-- `Zipper::path_exists`. -/
def pathExists : Bool := z.trie.pathExists z.focus

/-- `Zipper::is_val`. -/
def isVal : Bool := (z.trie.valAt z.focus).isSome

/-- `Zipper::child_mask`.  Empty on a leaf or a non-existent path. -/
def childMask : ByteMask := z.trie.childMask z.focus

/-- `Zipper::child_count`. -/
def childCount : Nat := z.childMask.length

/-- `ZipperMoving::focus_byte`: the byte last descended to reach the focus.

**Unspecified at the root.**  A zipper that retains knowledge of the trie above
its root may return the byte leading to that root; one that does not, or one
rooted at the trie root, returns `none`.  So a `some` here does not mean the
zipper has descended, and callers needing that distinction must ask `at_root`.
The model returns the last byte of the relative path, which is `none` at the
root; the harness masks the value there rather than comparing it. -/
def focusByte : Option UInt8 := z.path.getLast?

/-! ## `trait ZipperValues` / `ZipperReadOnlyValues` -/

/-- `ZipperValues::val` (and `ZipperReadOnlyValues::get_val`, which differs only
in the lifetime of the returned reference). -/
def val : Option V := z.trie.valAt z.focus

/-- `ZipperValues::val_at`: the value at `k`, relative to the focus. -/
def valAt (k : Path) : Option V := z.trie.valAt (z.focus ++ k)

/-! ## `trait ZipperSubtries` / `ZipperInfallibleSubtries` -/

/-- `ZipperInfallibleSubtries::make_map`.  Under the default `graft_root_vals`
feature the value at the focus becomes the new map's root value. -/
def makeMap : PathMap V := z.trie.subtrie z.focus

/-- The node below the focus — what `get_focus` returns, i.e. `make_map` with the
focus value stripped.  This, not `makeMap`, is what the algebraic operations and
`graft_internal` consume. -/
def focusNode : PathMap V := (z.makeMap.removeVal []).2

/-- `get_focus().is_none()`: the focus has no descendants. -/
def focusNodeIsEmpty : Bool := z.trie.belowIsEmpty z.focus

/-! ## `trait ZipperMoving` — position -/

/-- The same zipper, its focus moved to the relative path `q`.

Lets an ancestor or descendant be *named* and then asked about, so the
specifications below can say "the deepest ancestor such that ..." instead of
walking there step by step. -/
def atPath (q : Path) : Zip V := { z with path := q }

/-- `ZipperMoving::at_root`. -/
def atRoot : Bool := z.path.isEmpty

/-- `ZipperMoving::reset`. -/
def reset : Zip V := { z with path := [] }

/-- `ZipperMoving::val_count`: values at and below the focus. -/
def valCount : Nat := z.trie.valCount z.focus

/-! ## `trait ZipperMoving` — descent -/

/-- `ZipperMoving::descend_to`.  Never fails; the focus may end up off-trie. -/
def descendTo (k : Path) : Zip V := { z with path := z.path ++ k }

/-- `ZipperMoving::descend_to_byte`. -/
def descendToByte (b : UInt8) : Zip V := z.descendTo [b]

/-- `ZipperMoving::descend_to_check`: descend, then report existence. -/
def descendToCheck (k : Path) : Bool × Zip V :=
  let z' := z.descendTo k
  (z'.pathExists, z')

/-- `ZipperMoving::descend_to_existing`: descend byte by byte, stopping where the
path stops existing.  Returns the number of bytes actually descended. -/
def descendToExisting (k : Path) : Nat × Zip V :=
  -- Existence is prefix-closed, so the prefixes of `k` that still exist form an
  -- initial segment: the answer is simply the longest prefix of `k` that exists.
  let reach := ((List.range (k.length + 1)).filter
    (fun j => (z.descendTo (k.take j)).pathExists)).getLast?.getD 0
  (reach, z.descendTo (k.take reach))

/-- `ZipperMoving::descend_to_val`: descend byte by byte, stopping at the first
value encountered *below* the starting focus, or where the path stops existing. -/
def descendToVal (k : Path) : Nat × Zip V :=
  -- As far as the path exists, but no further than the first value *strictly*
  -- below the starting focus -- so a value already at the focus does not stop it.
  let reach := ((List.range (k.length + 1)).filter
    (fun j => (z.descendTo (k.take j)).pathExists)).getLast?.getD 0
  let stop := ((List.range (reach + 1)).filter
    (fun j => 0 < j && (z.descendTo (k.take j)).isVal)).head?.getD reach
  (stop, z.descendTo (k.take stop))

/-- `ZipperMoving::descend_to_existing_byte`. -/
def descendToExistingByte (b : UInt8) : Bool × Zip V :=
  let z' := z.descendToByte b
  if z'.pathExists then (true, z') else (false, z)

/-- `ZipperMoving::descend_indexed_byte`: descend into the `idx`-th child in
ascending byte order, returning the byte moved to.  Out-of-range indices do
nothing and return `none`. -/
def descendIndexedByte (idx : Nat) : Option UInt8 × Zip V :=
  match z.childMask.indexedBit idx with
  | some b => (some b, z.descendToByte b)
  | none => (none, z)

/-- `ZipperMoving::descend_first_byte`. -/
def descendFirstByte : Option UInt8 × Zip V := z.descendIndexedByte 0

/-- `ZipperMoving::descend_last_byte`. -/
def descendLastByte : Option UInt8 × Zip V :=
  let c := z.childCount
  if c == 0 then (none, z) else z.descendIndexedByte (c - 1)

/-- `ZipperMoving::descend_until`: descend while there is exactly one child,
stopping on a value.  A no-op on a branch, a leaf, or a non-existent path. -/
def descendUntil : Bool × Zip V :=
  -- Nothing happens unless the focus has exactly one child.  When it does, the
  -- locations below it form a chain until the first one that branches, ends, or
  -- carries a value -- so the destination is simply the *nearest* descendant
  -- that is a value or is not single-childed.  `subPaths` is in depth-first
  -- order, which along a chain is order of increasing depth, so `find?` returns
  -- the nearest one.
  if z.childCount != 1 then (false, z)
  else
    match (z.subPaths.filter (fun q => z.path ≼ q && Path.lt z.path q)).find?
      (fun q => (z.atPath q).isVal || (z.atPath q).childCount != 1) with
    | some q => (true, z.atPath q)
    | none => (false, z)

/-- `ZipperMoving::descend_until_observed`: `descend_until`, reporting each byte
it descends to a `PathObserver`.

For the `Vec<u8>` observer -- the one the harness uses -- the reported sequence
is exactly the path delta, which is the only way a blind zipper can learn where
it ended up.  That equality is the property worth checking. -/
def descendUntilObserved : Bool × Path × Zip V :=
  let (moved, z2) := z.descendUntil
  (moved, z2.path.drop z.path.length, z2)

/-- `ZipperMoving::descend_until_max_bytes`: `descend_until`, then ascend back to
at most `maxBytes` below the starting depth. -/
def descendUntilMaxBytes (maxBytes : Nat) : Bool × Zip V :=
  if maxBytes == 0 then (false, z)
  else
    let target := z.path.length + maxBytes
    let (moved, z') := z.descendUntil
    if z'.path.length > target then (moved, { z' with path := z'.path.take target })
    else (moved, z')

/-! ## `trait ZipperMoving` — ascent -/

/-- `ZipperMoving::ascend`: ascend `steps` bytes, clamping at the zipper root.
Returns the **number of bytes actually ascended**, which is smaller than `steps`
when the root was closer than that. -/
def ascend (steps : Nat) : Nat × Zip V :=
  let n := min steps z.path.length
  (n, { z with path := z.path.take (z.path.length - n) })

/-- `ZipperMoving::ascend_byte`: still a `bool`, defined as `ascend(1) == 1`. -/
def ascendByte : Bool × Zip V :=
  let (n, z2) := z.ascend 1
  (n == 1, z2)

/-- `ZipperMoving::ascend_until`: ascend to the nearest strict ancestor that
carries a value or branches, or to the root.  Returns the number of bytes
ascended; `0` means the zipper was already at its root. -/
def ascendUntil : Nat × Zip V :=
  -- The destination is the deepest strict ancestor that carries a value or branches,
  -- or the root.  `properPrefixes` is shortest-first, so the last
  -- element that qualifies is the deepest one; the root always
  -- qualifies, so there is always an answer.
  if z.atRoot then (0, z)
  else
    let stops := (Path.properPrefixes z.path).filter fun a =>
      a.isEmpty || (z.atPath a).isVal || (z.atPath a).childCount > 1
    let a := (stops.getLast?).getD []
    (z.path.length - a.length, z.atPath a)

/-- `ZipperMoving::ascend_until_branch`: like `ascend_until`, but values do not
stop the ascent.  Returns the number of bytes ascended. -/
def ascendUntilBranch : Nat × Zip V :=
  -- The destination is the deepest strict ancestor that branches (values do not stop it),
  -- or the root.  `properPrefixes` is shortest-first, so the last
  -- element that qualifies is the deepest one; the root always
  -- qualifies, so there is always an answer.
  if z.atRoot then (0, z)
  else
    let stops := (Path.properPrefixes z.path).filter fun a =>
      a.isEmpty || (z.atPath a).childCount > 1
    let a := (stops.getLast?).getD []
    (z.path.length - a.length, z.atPath a)

/-! ## `trait ZipperMoving` — lateral movement -/

/-- `ZipperMoving::to_next_sibling_byte`.

At the zipper root there is no last byte, so the documented answer — and the
`ZipperMoving` default implementation's answer — is `false`.

BUG (`pathmap` 0.3.1): the native `ReadZipper` implementation instead consults
the last byte of the *absolute* origin path, so a read zipper whose root does
not exist but has a sibling **leaves its own root**.  With map `{[0,0,3] ↦ v}`
and a zipper rooted at `[0,0,1]`, `to_next_sibling_byte()` returns `true`,
`path()` still reports `[]` and `at_root()` still reports `true`, but
`origin_path()` is now `[0,0,3]` and the zipper reads `v`.  That breaks the
containment a `ZipperHead` relies on to hand out non-overlapping zippers.  The
model specifies the documented behaviour; the differential harness skips the
operation at the root so the known bug does not mask others. -/
def toNextSiblingByte : Option UInt8 × Zip V :=
  -- Now keyed on `focus_byte`, whose value at the root is unspecified, so the
  -- `at_root` guard is what keeps the zipper inside its own subtrie.
  match z.focusByte with
  | none => (none, z)
  | some cur =>
      if z.atRoot then (none, z)
      else
        let up := (z.ascendByte).2
        match up.childMask.nextBit cur with
        | some b => (some b, up.descendToByte b)
        | none => (none, z)

/-- `ZipperMoving::to_prev_sibling_byte`. -/
def toPrevSiblingByte : Option UInt8 × Zip V :=
  -- Now keyed on `focus_byte`, whose value at the root is unspecified, so the
  -- `at_root` guard is what keeps the zipper inside its own subtrie.
  match z.focusByte with
  | none => (none, z)
  | some cur =>
      if z.atRoot then (none, z)
      else
        let up := (z.ascendByte).2
        match up.childMask.prevBit cur with
        | some b => (some b, up.descendToByte b)
        | none => (none, z)

/-- `ZipperMoving::move_to_path`: jump to `p` relative to the zipper root.
Returns the number of bytes shared between the old and the new location. -/
def moveToPath (p : Path) : Nat × Zip V :=
  let overlap := ((List.range (min p.length z.path.length)).takeWhile
    (fun i => p[i]? == z.path[i]?)).length
  (overlap, { z with path := p })

/-! ## `trait ZipperMoving` — depth-first stepping -/

/-- `ZipperMoving::to_next_step`: the next existing location in depth-first
order.  On exhaustion the focus returns to the root and the result is `false`. -/
def toNextStep : Bool × Zip V :=
  match z.subPaths.find? (fun q => Path.lt z.path q) with
  | some q => (true, { z with path := q })
  | none => (false, z.reset)

/-! ## `trait ZipperIteration` -/

/-- `ZipperIteration::to_next_val`: the next existing location carrying a value,
in depth-first order.  Never reports the value at the starting focus.  On
exhaustion the focus returns to the root and the result is `false`. -/
def toNextVal : Bool × Zip V :=
  match z.subPaths.find? (fun q => Path.lt z.path q && (z.trie.valAt (z.root ++ q)).isSome) with
  | some q => (true, { z with path := q })
  | none => (false, z.reset)

/-- `ZipperReadOnlyIteration::to_next_get_val`. -/
def toNextGetVal : Option V × Zip V :=
  let (moved, z') := z.toNextVal
  (if moved then z'.val else none, z')

/-- `ZipperIteration::descend_last_path`: follow the last child to the end of the
depth-first-greatest path below the focus. -/
def descendLastPath : Bool × Zip V :=
  let cands := z.subPaths.filter (fun q => z.path ≼ q)
  match cands.getLast? with
  | some q => if q == z.path then (false, z) else (true, { z with path := q })
  | none => (false, z)

/-- The shared core of `descend_first_k_path` and `to_next_k_path`
(`k_path_internal`): the depth-first-least existing location that is exactly
`k` bytes below the common ancestor at depth `base`, and that comes strictly
after the current focus.  On failure the focus moves to that ancestor. -/
def kPathFrom (base k : Nat) : Bool × Zip V :=
  let anc := z.path.take base
  match z.subPaths.find?
    (fun q => q.length == base + k && anc ≼ q && Path.lt z.path q) with
  | some q => (true, { z with path := q })
  | none => (false, { z with path := anc })

/-- `ZipperIteration::descend_first_k_path`: descend to the depth-first-first
existing location exactly `k` bytes below the focus.  Leaves the focus untouched
and returns `false` when there is none. -/
def descendFirstKPath (k : Nat) : Bool × Zip V := z.kPathFrom z.path.length k

/-- `ZipperIteration::to_next_k_path`: the next existing location at the same
depth, under the common ancestor `k` bytes above the focus.  On exhaustion the
focus moves to that ancestor and the result is `false`.

NOTE: when the focus is shallower than `k`, the *native* `ReadZipper` falls back
to the **zipper root** as the common ancestor — so the call behaves like
`descend_first_k_path(k)` from the root and can succeed.  The `ZipperIteration`
default implementation instead returns `false` without moving.  The model
follows the native `ReadZipper`, which is what the public API reaches. -/
def toNextKPath (k : Nat) : Bool × Zip V :=
  if k ≤ z.path.length then z.kPathFrom (z.path.length - k) k else z.kPathFrom 0 k

/-! ## `trait ZipperForking` -/

/-- `ZipperForking::fork_read_zipper`: a new zipper rooted at the current focus,
over a snapshot of the same trie. -/
def forkReadZipper : Zip V := { z with root := z.focus, path := [] }

end Zip
end PathMapModel
