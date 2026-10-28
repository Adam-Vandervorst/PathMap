import PrunedModel.Zipper

/-!
# The write zipper, restricted to the dangling-path-free subset

Two invariants shape the whole API:

1. **A subtrie includes the value at its root.**  The subtrie at a zipper's
   focus therefore includes the focus value, and every operation on subtries —
   `graft`, `graft_map`, `make_map`, `take_map`, `join_into`, `join_map_into`,
   `meet_into`, `subtract_into`, `meet_2`, `restrict`, `insert_prefix`,
   `remove_prefix`, `join_k_path_into` — treats it as part of the subtrie.  This
   is `focus_value_consistency` (issue #104); the node-level primitives
   underneath still see only what lies strictly below a location.

2. **There is no prune flag.**  In `PathMapModel` every mutating operation takes
   one, because a write leaves a dangling path behind unless it is passed — and
   even then the flag's effect is a function of where the internal node boundary
   happens to fall (`PathMapModel/Fuzz.lean` therefore always passes `false` and
   compares nothing).  Here existence is derived from the keys, so removing the
   last value under a chain removes the chain, with nothing to opt into.  The
   crate is driven with `prune = true` and must agree.

## What is missing, and why

* **`create_path`** — its entire purpose is to make a location that carries no
  value.  It cannot be modelled here and is not in the fuzzer's table.
* **`remove_val(false)`** — the non-pruning removal leaves the chain behind.
  Only `remove_val(true)` is in the subset.
* **A write zipper below the map root** — see `PrunedModel/Zipper.lean`.

Everything else in `ZipperWriting` is here.  Several of those operations *can*
still leave a dangling path in `pathmap` 0.4.0 — `graft` of an empty source is
the clearest case — and the model says they must not.  Those divergences are the
output this model exists to produce, so they are specified, not skipped; see
`PrunedModel/Fuzz.lean`.
-/

namespace PrunedModel
namespace PZip

open PathMapModel

variable {V : Type} (z : PZip V)

/-- Replace the trie, keeping the cursor. -/
def withTrie (t : PrunedMap V) : PZip V := { z with trie := t }

/-! ## Values at the focus -/

/-- `ZipperWriting::get_val_mut` — the same observation as `val`, mutably.
Returns `some` exactly when `val` does; it never creates anything. -/
def getValMut : Option V := z.val

/-- `ZipperWriting::set_val`: sets the value at the focus, creating the path if
it did not exist.  Returns the replaced value. -/
def setVal (v : V) : Option V × PZip V :=
  let (old, t) := z.trie.setVal z.focus v
  (old, z.withTrie t)

/-- Writing through the reference `get_val_mut` returns.

Specified as: where there is a value, this is `set_val`; where there is not, it
is a no-op — in particular it must **not** create the path, which is what
separates it from `set_val`. -/
def getValMutWrite (v : V) : Option V × PZip V :=
  match z.val with
  | some old => (some old, (z.setVal v).2)
  | none => (none, z)

/-- `ZipperWriting::get_val_or_set_mut`: the value at the focus, inserting
`default` if there is none. -/
def getValOrSetMut (d : V) : V × PZip V :=
  match z.val with
  | some v => (v, z)
  | none => (d, (z.setVal d).2)

/-- `ZipperWriting::get_val_or_set_mut_with`: as above, but the value comes from
a closure.

The documented contract is that the closure supplies the value "if no value
exists", so it must run **exactly when the focus has no value** — running it
otherwise is observable to any caller whose closure has a side effect.  The
second component records whether it ran, and the fuzzer compares that too. -/
def getValOrSetMutWith (d : V) : V × Bool × PZip V :=
  match z.val with
  | some v => (v, false, z)
  | none => (d, true, (z.setVal d).2)

/-- `ZipperWriting::remove_val(true)`.

The chain above the removed value goes with it, because nothing in this model
can exist without leading to a value.  `pathmap`'s own `remove_val(true)` prunes
only as far as the zipper's root, which is why the fuzzer keeps the write zipper
at the map root. -/
def removeVal : Option V × PZip V :=
  match z.val with
  | none => (none, z)
  | some v => (some v, z.withTrie (z.trie.removeVal z.focus).2)

/-! ## Pruning

`prune_path` and `prune_ascend` are in the fuzzer's table but have nothing to do
here: a trie built from this subset has no dangling tip to prune (see
`Spec.no_dangling_tip`), so both are no-ops returning `0`.  A non-zero count
from the crate is therefore a *finding* — it means some operation in the subset
left a dangling path for `prune_path` to find. -/

/-- `ZipperWriting::prune_path`: `0`, and nothing removed. -/
def prunePath : Nat × PZip V := (0, z)

/-- `ZipperWriting::prune_ascend`: `prune_path` followed by ascending that far,
so also a no-op. -/
def pruneAscend : Nat × PZip V := (0, z)

/-! ## Removing subtries -/

/-- `ZipperWriting::remove_branches`: delete everything strictly below the focus.
The value at the focus survives; if there is none, the focus stops existing.
Returns whether anything was removed. -/
def removeBranches : Bool × PZip V :=
  (!z.focusNodeIsEmpty, z.withTrie (z.trie.removeBelow z.focus))

/-- `ZipperWriting::remove_unmasked_branches`: keep only the child bytes set in
`mask`; delete the rest along with their subtries. -/
def removeUnmaskedBranches (mask : ByteMask) : PZip V :=
  let doomed := z.childMask.filter (fun b => !mask.contains b)
  z.withTrie <| doomed.foldl (fun t b => t.removeAt (z.focus ++ [b])) z.trie

/-! ## Grafting -/

/-- Replace the subtrie at the focus with `m`, treating `m` as a whole map: its
root value becomes the focus value (or clears it), and its branches become the
focus's branches.  This is `ZipperWriting::graft_map`. -/
def graftMap (m : PrunedMap V) : PZip V :=
  let t := z.trie.graftBelow z.focus m
  z.withTrie <|
    match m.valAt [] with
    | some v => (t.setVal z.focus v).2
    | none => (t.removeVal z.focus).2

/-- `ZipperWriting::graft`: graft the subtrie at `src`'s focus, root value
included.

Note what this says when the source is empty: the focus loses its value and its
branches, so — having nothing left to lead to — it stops existing, along with
any ancestor chain that existed only for it.  `pathmap` 0.4.0 leaves that chain
behind as a dangling path.  The model specifies the removal. -/
def graft (src : PZip V) : PZip V := z.graftMap src.makeMap

/-- `ZipperWriting::graft_src_at`: graft the subtrie `k` bytes below `src`'s
focus. -/
def graftSrcAt (src : PZip V) (k : Path) : PZip V :=
  z.graftMap (src.trie.subtrie (src.focus ++ k))

/-- `ZipperWriting::graft_masked_branches`: graft the source's child branches for
each byte set in `mask`.

Each set bit is a `graft_src_at` of the source's corresponding child, so the
child's *value* travels with it, and a set bit whose branch is absent from the
source leaves that branch absent here — grafting nothing removes.  With
`removeUnset`, branches for clear bits are removed first, so `child_mask`
afterwards is a subset of `mask`; without it they are left alone.

`WriteZipperCore` overrides the trait's default with a native implementation, so
this really compares two implementations of one contract. -/
def graftMaskedBranches (src : PZip V) (mask : ByteMask) (removeUnset : Bool) : PZip V :=
  let z0 := if removeUnset then (z.removeBranches).2 else z
  z0.withTrie <| mask.foldl (fun t b =>
    let child := z0.focus ++ [b]
    let m := src.trie.subtrie (src.focus ++ [b])
    let t1 := t.graftBelow child m
    match m.valAt [] with
    | some v => (t1.setVal child v).2
    | none => (t1.removeVal child).2) z0.trie

/-- `ZipperWriting::take_map`: remove the subtrie at the focus (value included)
and return it as a map.  `none` when there was nothing to take. -/
def takeMap : Option (PrunedMap V) × PZip V :=
  let rv := z.val
  let below := z.focusNode
  let z1 := z.withTrie (z.trie.removeAt z.focus)
  let taken :=
    match rv with
    | some v => (below.setVal [] v).2
    | none => below
  (if below.isEmptyMap && rv.isNone then none else some taken, z1)

/-! ## Path surgery -/

/-- `ZipperWriting::insert_prefix`: put `pre` in front of every path in the
subtrie, the path to the focus value included.  The cursor stays where it is.
An empty prefix is the identity.  Returns whether the focus exists; a focus that
does not leaves the trie unchanged. -/
def insertPrefix (pre : Path) : Bool × PZip V :=
  if !z.pathExists then (false, z)
  else if pre.isEmpty then (true, z)
  else (true, z.graftMap (z.makeMap.prepend pre))

/-- `ZipperWriting::remove_prefix`: move the focused subtrie up by `n` bytes,
replacing the subtrie at the new focus — value included, so the old focus value
replaces the new focus's, or clears it.  Returns how many bytes it ascended. -/
def removePrefix (n : Nat) : Nat × PZip V :=
  let subtrie := z.makeMap
  let (ascended, z1) := z.ascend n
  (ascended, z1.graftMap subtrie)

/-! ## Algebraic operations

`AlgebraicStatus` is decided structurally: `Identity` exactly when the output
equals the input, `None` when the output is empty, `Element` otherwise.
`Identity(COUNTER_IDENT)` — the output equals the *source* — is reported as
`Element` by `pathmap`, and the model agrees, because the output still differs
from `self`. -/

variable (ops : ValOps V)

/-- The status of replacing `before` with `after`. -/
def nodeStatus (before after : PrunedMap V) : AlgStatus :=
  if after.isEmptyMap then .none
  else if PrunedMap.beqT ops after before then .identity
  else .element

/-- `ZipperWriting::join_into`: union the subtrie at the source's focus into the
subtrie at this focus, focus values included. -/
def joinInto (src : PZip V) : AlgStatus × PZip V :=
  let (valStatus, z1) :=
    match z.val, src.val with
    | some sv, some mv =>
        let r := ops.pjoin sv mv
        (AlgStatus.ofValRes r,
          match r.resolve sv mv with
          | some v => (z.setVal v).2
          | none => (z.removeVal).2)
    | none, some mv => (AlgStatus.element, (z.setVal mv).2)
    | some _, none => (AlgStatus.identity, z)
    | none, none => (AlgStatus.none, z)
  let selfB := z1.focusNode
  let srcB := src.focusNode
  let r := PrunedMap.join ops selfB srcB
  let nodeSt :=
    if srcB.isEmptyMap then (if selfB.isEmptyMap then AlgStatus.none else AlgStatus.identity)
    else if PrunedMap.beqT ops r selfB then AlgStatus.identity else AlgStatus.element
  let z2 :=
    if srcB.isEmptyMap then z1
    else if PrunedMap.beqT ops r selfB then z1
    else z1.withTrie (z1.trie.graftBelow z1.focus r)
  (AlgStatus.merge nodeSt valStatus true true, z2)

/-- `ZipperWriting::join_map_into`: union a consumed map into the focus.

It short-circuits: when the map has no root node the node status is
returned directly and the value status computed above is discarded — even though
the value has already been written. -/
def joinMapInto (m : PrunedMap V) : AlgStatus × PZip V :=
  -- `merge` is called with both "was none" flags set, as the crate does, so the
  -- second component is carried only for symmetry with the other operations.
  let (valStatus, _valWasNone, z1) :=
    match z.val, m.valAt [] with
    | some sv, some mv =>
        let r := ops.pjoin sv mv
        (AlgStatus.ofValRes r, false,
          match r.resolve sv mv with
          | some v => (z.setVal v).2
          | none => (z.removeVal).2)
    | none, some mv => (AlgStatus.element, true, (z.setVal mv).2)
    | some _, none => (AlgStatus.identity, false, z)
    | none, none => (AlgStatus.none, true, z)
  let srcB := (m.removeVal []).2
  if srcB.isEmptyMap then
    -- Note the asymmetry with `join_into`: this branch tests
    -- `self.get_focus().is_none()` (does a node exist at all?), not
    -- `node_is_empty()`.  The two coincide here, since a location that exists
    -- has something below it or a value of its own.
    --
    -- The node status is *merged* with the value status rather than returned on
    -- its own.  It used to be returned directly -- an early `return` that
    -- discarded a value the operation had already written -- which is
    -- issue #139, fixed by PR #142 (`276fca0`).
    (AlgStatus.merge
      (if z1.pathExists then AlgStatus.identity else AlgStatus.none) valStatus true true, z1)
  else
    let selfB := z1.focusNode
    let r := PrunedMap.join ops selfB srcB
    let nodeSt := if PrunedMap.beqT ops r selfB then AlgStatus.identity else AlgStatus.element
    let z2 := if nodeSt == .identity then z1 else z1.withTrie (z1.trie.graftBelow z1.focus r)
    (AlgStatus.merge nodeSt valStatus true true, z2)

/-- `ZipperWriting::meet_into`: intersect the focus's subtrie with the source's.

The value step runs first and can prune the focus out from under the node step. -/
def meetInto (src : PZip V) : AlgStatus × PZip V :=
  let (valStatus, valWasNone, z1) :=
    match z.val, src.val with
    | some sv, some ov =>
        let r := ops.pmeet sv ov
        (AlgStatus.ofValRes r, false,
          match r.resolve sv ov with
          | some v => (z.setVal v).2
          | none => (z.removeVal).2)
    | none, some _ => (AlgStatus.none, true, z)
    | some _, none => (AlgStatus.none, false, (z.removeVal).2)
    | none, none => (AlgStatus.none, true, z)
  let selfB := z1.focusNode
  let srcB := src.focusNode
  if selfB.isEmptyMap then
    (AlgStatus.merge .none valStatus true valWasNone, z1)
  else if srcB.isEmptyMap then
    (AlgStatus.merge .none valStatus false valWasNone,
      z1.withTrie (z1.trie.removeBelow z1.focus))
  else
    let r := PrunedMap.meet ops selfB srcB
    let st := nodeStatus ops selfB r
    let z2 := if st == .identity then z1 else z1.withTrie (z1.trie.graftBelow z1.focus r)
    (AlgStatus.merge st valStatus false valWasNone, z2)

/-- `ZipperWriting::subtract_into`: remove the source's subtrie from the focus's.

Pointwise.  `PathMapModel` needs a second rule here — where the source has no
node at all, `self`'s subtree survives untouched, dangling paths included — and
that rule is exactly what the missing `Option` makes unnecessary: with nothing
valueless to preserve, "keep verbatim" and "subtract pointwise" agree. -/
def subtractInto (src : PZip V) : AlgStatus × PZip V :=
  let (valStatus, valWasNone, z1) :=
    match z.val, src.val with
    | some sv, some ov =>
        let r := ops.psub sv ov
        (AlgStatus.ofValRes r, false,
          match r.resolve sv ov with
          | some v => (z.setVal v).2
          | none => (z.removeVal).2)
    | none, some _ => (AlgStatus.none, true, z)
    | some _, none => (AlgStatus.identity, false, z)
    | none, none => (AlgStatus.none, true, z)
  let selfB := z1.focusNode
  let srcB := src.focusNode
  if srcB.isEmptyMap then
    (AlgStatus.merge (if selfB.isEmptyMap then .none else .identity) valStatus
      selfB.isEmptyMap valWasNone, z1)
  else if selfB.isEmptyMap then
    (AlgStatus.merge .none valStatus true valWasNone, z1)
  else
    let r := PrunedMap.sub ops selfB srcB
    let st := nodeStatus ops selfB r
    let z2 := if st == .identity then z1 else z1.withTrie (z1.trie.graftBelow z1.focus r)
    (AlgStatus.merge st valStatus false valWasNone, z2)

/-- `ZipperWriting::meet_2`: replace the subtrie at the focus with the meet of two
source subtries, focus values included.  What is already at the focus is not an
operand, so it reports `Element` or `None`, never `Identity`. -/
def meet2 (a b : PZip V) : AlgStatus × PZip V :=
  let r := PrunedMap.meet ops a.makeMap b.makeMap
  (if r.isEmptyMap then .none else .element, z.graftMap r)

/-- `ZipperWriting::restrict`: keep only the paths in this subtrie that are
prefixed by a path to a value in the source's subtrie, as `PathMap::restrict`
does.  A source focus value keeps the whole subtrie; without one, the focus
value goes.  An empty result reports `None`. -/
def restrict (src : PZip V) : AlgStatus × PZip V :=
  if src.val.isSome then
    (if z.makeMap.isEmptyMap then .none else .identity, z)
  else
    let removedVal := z.val
    let z1 := z.removeVal.2
    let srcB := src.focusNode
    let selfB := z1.focusNode
    if srcB.isEmptyMap then (.none, z1.withTrie (z1.trie.removeBelow z1.focus))
    else if selfB.isEmptyMap then (.none, z1)
    else
      let r := PrunedMap.restrictBelowRoot selfB srcB
      let st := nodeStatus ops selfB r
      if st == .identity then
        (if removedVal.isSome then .element else .identity, z1)
      else (st, z1.withTrie (z1.trie.graftBelow z1.focus r))

/-- `ZipperWriting::restricting`: the mirror image — `self`'s subtrie is replaced
by the source's, restricted by the paths to values in `self`.

`false`, leaving `self` untouched, when either side has nothing below its focus. -/
def restricting (src : PZip V) : Bool × PZip V :=
  if src.focusNodeIsEmpty then (false, z)
  else if z.focusNodeIsEmpty then (false, z)
  else (true, z.withTrie (z.trie.graftBelow z.focus
    (PrunedMap.restrictBelowRoot src.focusNode z.focusNode)))

/-! ## Collapsing path segments -/

/-- `ZipperWriting::join_k_path_into` (a.k.a. `drop_head`): replace the subtrie
at the focus with the join of the subtries `k` bytes below it.  Values at
exactly that depth become the focus value; shallower ones, the old focus value
included, are dropped.  `k = 0` is the identity.  Returns whether the result is
non-empty. -/
def joinKPathInto (k : Nat) : Bool × PZip V :=
  let r := PrunedMap.dropHead ops z.makeMap k
  (!r.isEmptyMap, if k == 0 then z else z.graftMap r)

/-- One step of `meet_k_path_into`: meet in the subtrie at `f ++ q`. -/
def meetStep (t : PrunedMap V) (f : Path) (acc : Option (PrunedMap V)) (q : Path) :
    Option (PrunedMap V) :=
  match acc with
  | none => some (t.subtrie (f ++ q))
  | some a => some (PrunedMap.meet ops a (t.subtrie (f ++ q)))

/-- `ZipperWriting::meet_k_path_into`: strip the leading `k` bytes from every
path below the focus and meet the results.

Values at depth exactly `k` become the focus value.  The meet replaces the whole
subtrie, focus value included: an empty meet is `remove_subtrie`, which is
grafting the empty map.  With `k = 0` the only subtrie is the focus's own, so
it is the identity; a focus with no children meets nothing and is emptied. -/
def meetKPathInto (k : Nat) : Bool × PZip V :=
  let kps := (z.trie.subtrie z.focus).kPaths k
  let result : Option (PrunedMap V) := kps.foldl (meetStep ops z.trie z.focus) none
  match result with
  | some m => (!m.isEmptyMap, z.graftMap m)
  | none => (false, z.graftMap PrunedMap.empty)

end PZip
end PrunedModel
