import PrunedModel.Map

/-!
# The zipper, over a trie with no dangling paths

Same cursor as `PathMapModel.Zip` — a trie, the absolute path the zipper was
created at, and the relative path to the focus — and the same read API.  What
changes is what the observations *mean*:

* `path_exists` is now "some value lies at or below here", because that is the
  only way to exist.
* `child_mask` is read off the keys rather than off a separate set of locations.
* `descend_until`, `ascend_until_branch`, `to_next_step` and the `k`-path
  primitives walk the prefix closure of the keys, which is the whole trie.

Everything else is a transcription of `PathMapModel.Zipper`, and deliberately so:
the point of the second model is a different *representation* of the same
contract, not a different reading of it.  Where the two models disagree, one of
them is wrong, and the fuzzer says which.

## The write zipper is rooted at the map root

`PrunedModel`'s fuzzer only ever builds a write zipper at the map root; see
`Fuzz.header`.  A write zipper rooted below it holds a node at its own root,
which survives as a dangling path once everything below it is removed, and
`prune_path` is documented not to rise above the zipper's origin.  That is a
location that exists without leading to a value, so it is outside this model by
construction rather than by a bug.  Off-root *writing* is still covered — the
root-rooted zipper reaches it with `descend_to`.
-/

namespace PrunedModel

open PathMapModel

/-- A zipper: a trie, the absolute path of the zipper's root, and the relative
path to the focus. -/
structure PZip (V : Type) where
  trie : PrunedMap V
  root : Path
  path : Path
deriving Repr

namespace PZip

variable {V : Type} (z : PZip V)

/-- `ZipperAbsolutePath::origin_path`: the absolute path of the focus. -/
def focus : Path := z.root ++ z.path

/-- `ZipperAbsolutePath::root_prefix_path`. -/
def rootPrefixPath : Path := z.root

/-- All locations of the zipper's subtrie, relative to its root, in depth-first
order.  The zipper's entire visible universe. -/
def subPaths : List Path := (z.trie.subtrie z.root).paths

/-! ## `trait Zipper` -/

/-- `Zipper::path_exists`. -/
def pathExists : Bool := z.trie.pathExists z.focus

/-- `Zipper::is_val`. -/
def isVal : Bool := (z.trie.valAt z.focus).isSome

/-- `Zipper::child_mask`. -/
def childMask : ByteMask := z.trie.childMask z.focus

/-- `Zipper::child_count`. -/
def childCount : Nat := z.childMask.length

/-- `ZipperMoving::focus_byte`: the byte last descended to reach the focus.
**Unspecified at the root**; the harness masks it there. -/
def focusByte : Option UInt8 := z.path.getLast?

/-! ## `trait ZipperValues` -/

/-- `ZipperValues::val`. -/
def val : Option V := z.trie.valAt z.focus

/-- `ZipperValues::val_at`: the value at `k`, relative to the focus. -/
def valAt (k : Path) : Option V := z.trie.valAt (z.focus ++ k)

/-! ## `trait ZipperSubtries` -/

/-- `ZipperInfallibleSubtries::make_map`.  Under the default `graft_root_vals`
feature the value at the focus becomes the new map's root value. -/
def makeMap : PrunedMap V := z.trie.subtrie z.focus

/-- The node below the focus — what `get_focus` returns.  This, not `makeMap`,
is what the algebraic operations and `graft_internal` consume. -/
def focusNode : PrunedMap V := (z.makeMap.removeVal []).2

/-- `get_focus().is_none()`: the focus has no descendants. -/
def focusNodeIsEmpty : Bool := z.trie.belowIsEmpty z.focus

/-! ## `trait ZipperMoving` — position -/

/-- The same zipper with its focus at the relative path `q`, so that an ancestor
or descendant can be named and then asked about. -/
def atPath (q : Path) : PZip V := { z with path := q }

/-- `ZipperMoving::at_root`. -/
def atRoot : Bool := z.path.isEmpty

/-- `ZipperMoving::reset`. -/
def reset : PZip V := { z with path := [] }

/-- `ZipperMoving::val_count`: values at and below the focus. -/
def valCount : Nat := z.trie.valCount z.focus

/-! ## `trait ZipperMoving` — descent -/

/-- `ZipperMoving::descend_to`.  Never fails; the focus may end up off-trie. -/
def descendTo (k : Path) : PZip V := { z with path := z.path ++ k }

/-- `ZipperMoving::descend_to_byte`. -/
def descendToByte (b : UInt8) : PZip V := z.descendTo [b]

/-- `ZipperMoving::descend_to_check`: descend, then report existence. -/
def descendToCheck (k : Path) : Bool × PZip V :=
  let z' := z.descendTo k
  (z'.pathExists, z')

/-- `ZipperMoving::descend_to_existing`: descend byte by byte, stopping where the
path stops existing.  Returns the number of bytes actually descended. -/
def descendToExisting (k : Path) : Nat × PZip V :=
  -- Existence is prefix-closed, so the prefixes of `k` that still exist form an
  -- initial segment: the answer is the longest prefix of `k` that exists.
  let reach := ((List.range (k.length + 1)).filter
    (fun j => (z.descendTo (k.take j)).pathExists)).getLast?.getD 0
  (reach, z.descendTo (k.take reach))

/-- `ZipperMoving::descend_to_val`: descend byte by byte, stopping at the first
value encountered *below* the starting focus, or where the path stops existing. -/
def descendToVal (k : Path) : Nat × PZip V :=
  let reach := ((List.range (k.length + 1)).filter
    (fun j => (z.descendTo (k.take j)).pathExists)).getLast?.getD 0
  let stop := ((List.range (reach + 1)).filter
    (fun j => 0 < j && (z.descendTo (k.take j)).isVal)).head?.getD reach
  (stop, z.descendTo (k.take stop))

/-- `ZipperMoving::descend_to_existing_byte`. -/
def descendToExistingByte (b : UInt8) : Bool × PZip V :=
  let z' := z.descendToByte b
  if z'.pathExists then (true, z') else (false, z)

/-- `ZipperMoving::descend_indexed_byte`: descend into the `idx`-th child in
ascending byte order, returning the byte moved to. -/
def descendIndexedByte (idx : Nat) : Option UInt8 × PZip V :=
  match z.childMask.indexedBit idx with
  | some b => (some b, z.descendToByte b)
  | none => (none, z)

/-- `ZipperMoving::descend_first_byte`. -/
def descendFirstByte : Option UInt8 × PZip V := z.descendIndexedByte 0

/-- `ZipperMoving::descend_last_byte`. -/
def descendLastByte : Option UInt8 × PZip V :=
  let c := z.childCount
  if c == 0 then (none, z) else z.descendIndexedByte (c - 1)

/-- `ZipperMoving::descend_until`: descend while there is exactly one child,
stopping on a value.  A no-op on a branch, a leaf, or a non-existent path.

The destination is the *nearest* descendant that carries a value or is not
single-childed; `subPaths` is in depth-first order, which along a chain is order
of increasing depth, so `find?` returns it. -/
def descendUntil : Bool × PZip V :=
  if z.childCount != 1 then (false, z)
  else
    match (z.subPaths.filter (fun q => z.path ≼ q && Path.lt z.path q)).find?
      (fun q => (z.atPath q).isVal || (z.atPath q).childCount != 1) with
    | some q => (true, z.atPath q)
    | none => (false, z)

/-- `ZipperMoving::descend_until_observed`: `descend_until`, reporting each byte
it descends.  For the `Vec<u8>` observer the reported sequence must be exactly
the path delta — the only way a blind zipper learns where it ended up. -/
def descendUntilObserved : Bool × Path × PZip V :=
  let (moved, z2) := z.descendUntil
  (moved, z2.path.drop z.path.length, z2)

/-- `ZipperMoving::descend_until_max_bytes`: `descend_until`, then ascend back to
at most `maxBytes` below the starting depth. -/
def descendUntilMaxBytes (maxBytes : Nat) : Bool × PZip V :=
  if maxBytes == 0 then (false, z)
  else
    let target := z.path.length + maxBytes
    let (moved, z') := z.descendUntil
    if z'.path.length > target then (moved, { z' with path := z'.path.take target })
    else (moved, z')

/-! ## `trait ZipperMoving` — ascent -/

/-- `ZipperMoving::ascend`: ascend `steps` bytes, clamping at the zipper root.
Returns the number of bytes actually ascended. -/
def ascend (steps : Nat) : Nat × PZip V :=
  let n := min steps z.path.length
  (n, { z with path := z.path.take (z.path.length - n) })

/-- `ZipperMoving::ascend_byte`: `ascend(1) == 1`. -/
def ascendByte : Bool × PZip V :=
  let (n, z2) := z.ascend 1
  (n == 1, z2)

/-- `ZipperMoving::ascend_until`: ascend to the nearest strict ancestor that
carries a value or branches, or to the root.  Returns the bytes ascended.

`properPrefixes` is shortest-first, so the last qualifying element is the
deepest; the root always qualifies, so there is always an answer. -/
def ascendUntil : Nat × PZip V :=
  if z.atRoot then (0, z)
  else
    let stops := (Path.properPrefixes z.path).filter fun a =>
      a.isEmpty || (z.atPath a).isVal || (z.atPath a).childCount > 1
    let a := (stops.getLast?).getD []
    (z.path.length - a.length, z.atPath a)

/-- `ZipperMoving::ascend_until_branch`: as above, but values do not stop it. -/
def ascendUntilBranch : Nat × PZip V :=
  if z.atRoot then (0, z)
  else
    let stops := (Path.properPrefixes z.path).filter fun a =>
      a.isEmpty || (z.atPath a).childCount > 1
    let a := (stops.getLast?).getD []
    (z.path.length - a.length, z.atPath a)

/-! ## `trait ZipperMoving` — lateral movement -/

/-- `ZipperMoving::to_next_sibling_byte`.

At the zipper root there is no last byte, so the documented answer — and the
`ZipperMoving` default implementation's — is "did not move".  The native
`ReadZipper` instead consults the last byte of the *absolute* origin path and
can leave its own root (FINDINGS.md #3); the fuzzer skips the operation at the
root so that known bug does not mask others. -/
def toNextSiblingByte : Option UInt8 × PZip V :=
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
def toPrevSiblingByte : Option UInt8 × PZip V :=
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
Returns the number of bytes shared with the old location. -/
def moveToPath (p : Path) : Nat × PZip V :=
  let overlap := ((List.range (min p.length z.path.length)).takeWhile
    (fun i => p[i]? == z.path[i]?)).length
  (overlap, { z with path := p })

/-! ## `trait ZipperMoving` — depth-first stepping -/

/-- `ZipperMoving::to_next_step`: the next existing location in depth-first
order.  On exhaustion the focus returns to the root and the result is `false`. -/
def toNextStep : Bool × PZip V :=
  match z.subPaths.find? (fun q => Path.lt z.path q) with
  | some q => (true, { z with path := q })
  | none => (false, z.reset)

/-! ## `trait ZipperIteration` -/

/-- `ZipperIteration::to_next_val`: the next location carrying a value, in
depth-first order.  Never reports the value at the starting focus. -/
def toNextVal : Bool × PZip V :=
  match z.subPaths.find?
    (fun q => Path.lt z.path q && (z.trie.valAt (z.root ++ q)).isSome) with
  | some q => (true, { z with path := q })
  | none => (false, z.reset)

/-- `ZipperReadOnlyIteration::to_next_get_val`. -/
def toNextGetVal : Option V × PZip V :=
  let (moved, z') := z.toNextVal
  (if moved then z'.val else none, z')

/-- `ZipperIteration::descend_last_path`: follow the last child to the end of
the depth-first-greatest path below the focus. -/
def descendLastPath : Bool × PZip V :=
  let cands := z.subPaths.filter (fun q => z.path ≼ q)
  match cands.getLast? with
  | some q => if q == z.path then (false, z) else (true, { z with path := q })
  | none => (false, z)

/-- The shared core of `descend_first_k_path` and `to_next_k_path`
(`k_path_internal`): the depth-first-least existing location exactly `k` bytes
below the common ancestor at depth `base`, strictly after the current focus.  On
failure the focus moves to that ancestor. -/
def kPathFrom (base k : Nat) : Bool × PZip V :=
  let anc := z.path.take base
  match z.subPaths.find?
    (fun q => q.length == base + k && anc ≼ q && Path.lt z.path q) with
  | some q => (true, { z with path := q })
  | none => (false, { z with path := anc })

/-- `ZipperIteration::descend_first_k_path`. -/
def descendFirstKPath (k : Nat) : Bool × PZip V := z.kPathFrom z.path.length k

/-- `ZipperIteration::to_next_k_path`: the next existing location at the same
depth, under the common ancestor `k` bytes above the focus.

When the focus is shallower than `k` the native `ReadZipper` falls back to the
**zipper root** as the common ancestor, so the call behaves like
`descend_first_k_path(k)` from the root and can succeed; the `ZipperIteration`
default returns `false` without moving.  The model follows the native one, which
is what the public API reaches. -/
def toNextKPath (k : Nat) : Bool × PZip V :=
  if k ≤ z.path.length then z.kPathFrom (z.path.length - k) k else z.kPathFrom 0 k

/-! ## `trait ZipperForking` -/

/-- `ZipperForking::fork_read_zipper`: a new zipper rooted at the current focus. -/
def forkReadZipper : PZip V := { z with root := z.focus, path := [] }

end PZip
end PrunedModel
