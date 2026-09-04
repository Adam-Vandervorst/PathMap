import PathMapModel.Zipper

/-!
# The write zipper

Everything here mutates `Zip.trie` through the focus `root ++ path`.  Two
invariants shape the whole API and are worth stating up front:

1. **A node is what lies strictly below a location.**  `get_focus`,
   `graft_internal`, and every `*_dyn` algebraic primitive operate on nodes, so
   they never see or touch the value *at* the focus.  Operations that do affect
   the focus value (`graft`, `graft_map`, `make_map`, `take_map`,
   `join_map_into`, `meet_into`, `subtract_into`) do it in a separate step —
   this is the `graft_root_vals` cargo feature, which is on by default and which
   the model assumes throughout.  Note the resulting asymmetry: `graft` adopts
   the source's focus value but `join_into` does **not** join focus values.

2. **Pruning is opt-in and local.**  A write leaves dangling paths behind unless
   `prune` is passed, and even then `prune_path` only fires when the focus is a
   dangling tip.  Pruning stops at the zipper's root and never rises above it.
-/

namespace PathMapModel
namespace Zip

variable {V : Type} (z : Zip V)

/-- Replace the trie, keeping the cursor. -/
def withTrie (t : PathMap V) : Zip V := { z with trie := t }

/-! ## Values at the focus -/

/-- `ZipperWriting::get_val_mut` — same observation as `val`, mutably.

Returns `some` exactly when `val` does; it never creates anything. -/
def getValMut : Option V := z.val

/-- `ZipperWriting::set_val`: sets the value at the focus, **creating the path**
if it did not exist.  Returns the replaced value. -/
def setVal (v : V) : Option V × Zip V :=
  let (old, t) := z.trie.setVal z.focus v
  (old, z.withTrie t)

/-- Writing through the reference `get_val_mut` returns.

Specified as: when there is a value, this is `set_val`; when there is not, it is
a no-op — in particular it must **not** create the path, which is what separates
it from `set_val`. -/
def getValMutWrite (v : V) : Option V × Zip V :=
  match z.val with
  | some old => (some old, (z.setVal v).2)
  | none => (none, z)

/-- `ZipperWriting::get_val_or_set_mut`: the value at the focus, inserting
`default` if there is none.  Inserting creates the path, as `set_val` does. -/
def getValOrSetMut (d : V) : V × Zip V :=
  match z.val with
  | some v => (v, z)
  | none => (d, (z.setVal d).2)

/-- `ZipperWriting::get_val_or_set_mut_with`: as above, but the value is produced
by a closure.

The documented contract is that the closure supplies the value "if no value
exists", so it must be called **exactly when the focus has no value** — calling
it otherwise would be observable to any caller whose closure has a side effect
(allocating, taking a lock, bumping a counter).  The second component of the
result records whether it ran, and the harness compares that too. -/
def getValOrSetMutWith (d : V) : V × Bool × Zip V :=
  match z.val with
  | some v => (v, false, z)
  | none => (d, true, (z.setVal d).2)

/-- `ZipperWriting::prune_path`: delete the dangling chain ending at the focus,
stopping at the first location above it that carries a value or branches.  The
focus does **not** move.

Two things about this differ from the doc comment on `ZipperWriting::prune_path`,
both verified against `pathmap` 0.3.1:

* **It prunes above the zipper's root.**  The doc says "This method cannot prune
  the trie above the zipper's root", but a write zipper rooted at `ab` whose
  focus is a dangling tip deletes `a` and `ab` too, right up to the nearest
  branch or value in the *whole map*.  The model therefore passes `0`, not
  `z.root.length`, as the stop depth.
* **The returned count is not well-defined** when the zipper's root is non-empty.
  `prune_path` returns `max(node_pruned_bytes, trie_pruned_bytes)`, and
  `node_pruned_bytes` depends on where the internal node holding the focus
  happens to begin.  Empirically, a 40-byte dangling chain under a zipper rooted
  at depth 5 reports 40 (absolute) while a 100-byte one reports 95 (relative).
  The *effect* is the same in both cases; only the number differs.  The model
  reports the absolute count, and the differential harness compares the count
  only for zippers rooted at the map root. -/
def prunePath : Nat × Zip V :=
  let (n, t) := z.trie.prunePath 0 z.focus
  (n, z.withTrie t)

/-- `ZipperWriting::prune_ascend`: `prune_path` followed by ascending that far. -/
def pruneAscend : Nat × Zip V :=
  let (n, z') := z.prunePath
  (n, (z'.ascend n).2)

/-- `ZipperWriting::remove_val`: removes the value, leaving the location as a
dangling path unless `prune` reclaims it.

Pruning only happens when a value was actually removed: `remove_val` returns
early on the `None` branch, so `remove_val(true)` at a location with no value
leaves any dangling path in place. -/
def removeVal (prune : Bool) : Option V × Zip V :=
  match z.entry with
  -- Nothing to remove.  Note the `prune` flag does not fire here: `remove_val`
  -- returns early on this branch, so a dangling path is left in place.
  | .absent | .bare => (none, z)
  | .valued v =>
    let z' := z.withTrie (z.trie.removeVal z.focus).2
    (some v, if prune then (z'.prunePath).2 else z')

/-- `ZipperWriting::create_path`: make the focus exist as a dangling path.
Returns whether new bytes were created.

The guard is on the *absolute* focus, not on `at_root`: `create_path` bails out
when there is no key left to create, which is the map root, not the zipper root.
A zipper rooted at `ab` whose root does not yet exist will happily create it. -/
def createPath : Bool × Zip V :=
  if z.focus.isEmpty then (false, z)
  else
    match z.entry with
    | .absent => (true, z.withTrie (z.trie.addPath z.focus))
    -- Already there, with or without a value: nothing to create, and in
    -- particular an existing value is never disturbed.
    | .bare | .valued _ => (false, z)

/-! ## Removing subtries -/

/-- `ZipperWriting::remove_branches`: delete everything strictly below the focus.
The value at the focus survives.  Returns whether anything was removed. -/
def removeBranches (prune : Bool) : Bool × Zip V :=
  let removed := !z.focusNodeIsEmpty
  let z' := z.withTrie (z.trie.removeBelow z.focus)
  (removed, if prune then (z'.prunePath).2 else z')

/-- `ZipperWriting::remove_unmasked_branches`: keep only the child bytes set in
`mask`; delete the rest along with their subtries. -/
def removeUnmaskedBranches (mask : ByteMask) (prune : Bool) : Zip V :=
  let doomed := z.childMask.filter (fun b => !mask.contains b)
  let t := doomed.foldl (fun t b => t.removeAt (z.focus ++ [b])) z.trie
  let z' := z.withTrie t
  if prune then (z'.prunePath).2 else z'

/-! ## Grafting -/

/-- Replace the subtrie at the focus with `m`, treating `m` as a whole `PathMap`:
its root value becomes the focus value (or clears it), and its branches become
the focus's branches.  This is `ZipperWriting::graft_map`. -/
def graftMap (m : PathMap V) : Zip V :=
  let t := z.trie.graftBelow z.focus m
  z.withTrie <|
    match m.valAt [] with
    | some v => (t.setVal z.focus v).2
    | none => (t.removeVal z.focus).2

/-- `ZipperWriting::graft`: graft the subtrie at `src`'s focus, root value included. -/
def graft (src : Zip V) : Zip V := z.graftMap src.makeMap

/-- `ZipperWriting::graft_src_at`: graft the subtrie `k` bytes below `src`'s focus. -/
def graftSrcAt (src : Zip V) (k : Path) : Zip V :=
  z.graftMap (src.trie.subtrie (src.focus ++ k))

/-- `ZipperWriting::graft_masked_branches`: graft the source's child branches
for each byte set in `mask`.

Each set bit is a `graft_src_at` of the source's corresponding child, so the
child's *value* travels with it, and a set bit whose branch is absent from the
source leaves that branch absent here — grafting nothing removes.  With
`remove_unset`, branches for clear bits are removed first, so `child_mask`
afterwards is a subset of `mask`; without it they are left alone.

`WriteZipperCore` overrides the trait's default implementation with a native
one, so this op is really comparing two implementations of the same contract. -/
def graftMaskedBranches (src : Zip V) (mask : ByteMask) (removeUnset : Bool) : Zip V :=
  let z0 := if removeUnset then (z.removeBranches false).2 else z
  z0.withTrie <| mask.foldl (fun t b =>
    let child := z0.focus ++ [b]
    let m := src.trie.subtrie (src.focus ++ [b])
    let t1 := t.graftBelow child m
    match m.valAt [] with
    | some v => (t1.setVal child v).2
    | none => (t1.removeVal child).2) z0.trie

/-- `ZipperWriting::graft_child_maps`: as above, but the branches come from an
explicit list of maps rather than from a source zipper.

Feeding it the source's own child subtries must therefore produce exactly what
`graft_masked_branches` produces from that source — the harness checks the two
against each other as well as against this definition. -/
def graftChildMaps (maps : List (ByteMask × PathMap V)) (removeUnset : Bool) : Zip V :=
  let z0 := if removeUnset then (z.removeBranches false).2 else z
  z0.withTrie <| maps.foldl (fun t bm =>
    match bm.1 with
    | [b] =>
      let child := z0.focus ++ [b]
      let t1 := t.graftBelow child bm.2
      (match bm.2.valAt [] with
       | some v => (t1.setVal child v).2
       | none => (t1.removeVal child).2)
    | _ => t) z0.trie

/-- `ZipperWriting::take_map`: remove the subtrie at the focus (value included)
and return it as a `PathMap`.  Returns `none` when there was nothing to take. -/
def takeMap (prune : Bool) : Option (PathMap V) × Zip V :=
  let rv := z.entry.val
  let z1 := z.withTrie (z.trie.removeVal z.focus).2
  let z2 := if prune then (z1.prunePath).2 else z1
  let below := z2.focusNode
  let z3 := z2.withTrie (z2.trie.removeBelow z2.focus)
  let z4 := if prune then (z3.prunePath).2 else z3
  let taken :=
    match rv with
    | some v => (below.setVal [] v).2
    | none => below
  (if below.isEmptyMap && rv.isNone then none else some taken, z4)

/-! ## Path surgery -/

/-- `ZipperWriting::insert_prefix`: put `pre` in front of every path below the
focus.  The focus value is untouched.  Returns `false` at a location with no
descendants.

BUG (`pathmap` 0.3.1): with an **empty** prefix this should be the identity, but
`make_parents_in(b"", node)` discards the node — the subtrie below the focus is
destroyed and `true` is still returned.  The model specifies the identity; the
differential harness skips `insert_prefix("")` so the known divergence does not
mask others. -/
def insertPrefix (pre : Path) : Bool × Zip V :=
  if z.focusNodeIsEmpty then (false, z)
  else (true, z.withTrie (z.trie.graftBelow z.focus (z.focusNode.insertPrefixBelow pre)))

/-- `ZipperWriting::remove_prefix`: lift the subtrie below the focus up by `n`
bytes, replacing whatever was below the new (ascended) focus.  Returns whether
the full `n` bytes could be ascended.

Note the value at the old focus is *not* carried up — it belonged to the parent
cell, not to the node that gets moved. -/
def removePrefix (n : Nat) : Bool × Zip V :=
  let below := z.focusNode
  -- `ascend` now reports how far it got, so "were all `n` bytes removed" is a
  -- comparison rather than the flag it used to return directly.
  let (ascended, z1) := z.ascend n
  (ascended == n, z1.withTrie (z1.trie.graftBelow z1.focus below))

/-! ## Algebraic operations

`AlgebraicStatus` is decided structurally: `Identity` exactly when the output
equals the input (`Identity(SELF_IDENT)`), `None` when the output is empty, and
`Element` otherwise.  `Identity(COUNTER_IDENT)` — the output equals the *source* —
is reported as `Element` by `pathmap`, and the model agrees because the output
still differs from `self`. -/

variable (ops : ValOps V)

/-- The status of replacing `before` with `after`. -/
def nodeStatus (before after : PathMap V) : AlgStatus :=
  if after.isEmptyMap then .none
  else if PathMap.beqT ops after before then .identity
  else .element

/-- `ZipperWriting::join_into`: union the source's subtrie into the focus's.

The focus **values are not joined** — only the nodes below the focus are.  (The
map-consuming variant `join_map_into` *does* join root values; see there.) -/
def joinInto (src : Zip V) : AlgStatus × Zip V :=
  let selfB := z.focusNode
  let srcB := src.focusNode
  if srcB.isEmptyMap then (if selfB.isEmptyMap then .none else .identity, z)
  else
    let r := PathMap.join ops selfB srcB
    if PathMap.beqT ops r selfB then (.identity, z)
    else (.element, z.withTrie (z.trie.graftBelow z.focus r))

/-- `ZipperWriting::join_map_into`: union a consumed `PathMap` into the focus.

Unlike `join_into` this *does* join the map's root value into the focus value.
It also short-circuits: when the map has no root node, the node status is
returned directly and the value status computed above is discarded — even though
the value has already been written. -/
def joinMapInto (m : PathMap V) : AlgStatus × Zip V :=
  let (valStatus, valWasNone, z1) :=
    match z.val, m.valAt [] with
    | some sv, some mv =>
        let r := ops.pjoin sv mv
        (AlgStatus.ofValRes r, false,
          match r.resolve sv mv with
          | some v => (z.setVal v).2
          | none => (z.removeVal false).2)
    | none, some mv => (AlgStatus.element, true, (z.setVal mv).2)
    | some _, none => (AlgStatus.identity, false, z)
    | none, none => (AlgStatus.none, true, z)
  let srcB := (m.removeVal []).2
  if srcB.isEmptyMap then
    -- Short-circuit, and note the asymmetry with `join_into`: this branch tests
    -- `self.get_focus().is_none()` (does a node exist at all?), not
    -- `node_is_empty()`.  So a *bare* focus reports `Identity` here, where
    -- `join_into` on the same state reports `None`.
    (match z1.entry with
     | .bare | .valued _ => AlgStatus.identity
     | .absent => AlgStatus.none, z1)
  else
    let selfB := z1.focusNode
    let r := PathMap.join ops selfB srcB
    let nodeStatus := if PathMap.beqT ops r selfB then AlgStatus.identity else AlgStatus.element
    let z2 := if nodeStatus == .identity then z1 else z1.withTrie (z1.trie.graftBelow z1.focus r)
    (AlgStatus.merge nodeStatus valStatus true valWasNone, z2)

/-- `ZipperWriting::join_into_take`: like `join_into`, but the source subtrie is
removed from the source zipper's trie.  Returns the updated destination *and*
source zippers. -/
def joinIntoTake (src : Zip V) (prune : Bool) : AlgStatus × Zip V × Zip V :=
  let srcB := src.focusNode
  let src1 := src.withTrie (src.trie.removeBelow src.focus)
  let src2 := if prune then (src1.prunePath).2 else src1
  let selfB := z.focusNode
  if srcB.isEmptyMap then
    (if selfB.isEmptyMap then .none else .identity, z, src2)
  else
    let r := PathMap.join ops selfB srcB
    let st := if PathMap.beqT ops r selfB then AlgStatus.identity else AlgStatus.element
    (st, z.withTrie (z.trie.graftBelow z.focus r), src2)

/-- `ZipperWriting::meet_into`: intersect the focus's subtrie with the source's.

The value step runs first and can prune the focus out from under the node step.
A meet drops every dangling path, since a location only survives if it leads to
a surviving value. -/
def meetInto (src : Zip V) (prune : Bool) : AlgStatus × Zip V :=
  let (valStatus, valWasNone, z1) :=
    match z.val, src.val with
    | some sv, some ov =>
        let r := ops.pmeet sv ov
        (AlgStatus.ofValRes r, false,
          match r.resolve sv ov with
          | some v => (z.setVal v).2
          | none => (z.removeVal prune).2)
    | none, some _ => (AlgStatus.none, true, z)
    | some _, none => (AlgStatus.none, false, (z.removeVal prune).2)
    | none, none => (AlgStatus.none, true, z)
  let selfB := z1.focusNode
  let srcB := src.focusNode
  if selfB.isEmptyMap then
    (AlgStatus.merge .none valStatus true valWasNone, z1)
  else if srcB.isEmptyMap then
    let z2 := z1.withTrie (z1.trie.removeBelow z1.focus)
    let z3 := if prune then (z2.prunePath).2 else z2
    (AlgStatus.merge .none valStatus false valWasNone, z3)
  else
    let r := PathMap.meet ops selfB srcB
    let st := nodeStatus ops selfB r
    let z2 :=
      if st == .identity then z1
      else
        let zg := z1.withTrie (z1.trie.graftBelow z1.focus r)
        if st == .none && prune then (zg.prunePath).2 else zg
    (AlgStatus.merge st valStatus false valWasNone, z2)

/-- `ZipperWriting::subtract_into`: remove the source's subtrie from the focus's.

Where the source has no node at all, `self`'s subtree survives untouched —
dangling paths included.  Where it does, only locations leading to a surviving
value are kept. -/
def subtractInto (src : Zip V) (prune : Bool) : AlgStatus × Zip V :=
  let (valStatus, valWasNone, z1) :=
    match z.val, src.val with
    | some sv, some ov =>
        let r := ops.psub sv ov
        (AlgStatus.ofValRes r, false,
          match r.resolve sv ov with
          | some v => (z.setVal v).2
          | none => (z.removeVal prune).2)
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
    let r := PathMap.sub ops selfB srcB
    let st := nodeStatus ops selfB r
    let z2 :=
      if st == .identity then z1
      else
        let zg := z1.withTrie (z1.trie.graftBelow z1.focus r)
        if st == .none && prune then (zg.prunePath).2 else zg
    (AlgStatus.merge st valStatus false valWasNone, z2)

/-- `ZipperWriting::meet_2`: meet two *source* subtries and write the result at
the focus.

Two things separate this from `meet_into`.  It does not consult what is already
at the focus, so — as the implementation notes — it never reports `Identity`,
only `Element` or `None`.  And it works on nodes, so neither source's focus value
is consulted and the focus value here is left untouched. -/
def meet2 (a b : Zip V) : AlgStatus × Zip V :=
  let an := a.focusNode
  let bn := b.focusNode
  if an.isEmptyMap || bn.isEmptyMap then
    (.none, z.withTrie (z.trie.removeBelow z.focus))
  else
    let r := PathMap.meet ops an bn
    if r.isEmptyMap then (.none, z.withTrie (z.trie.removeBelow z.focus))
    else (.element, z.withTrie (z.trie.graftBelow z.focus r))

/-- `ZipperWriting::restrict`: keep only the paths below the focus that are
prefixed by a path to a value in the source's subtrie.

The empty prefix does **not** validate here: the source's *focus value* is
invisible to a node-level `prestrict`.  `PathMap::restrict` does consult the
root value (see `Map.restrict`), so the two disagree exactly when the source has
a value at its focus.  The focus value of `self` is never touched. -/
def restrict (src : Zip V) : AlgStatus × Zip V :=
  let srcB := src.focusNode
  let selfB := z.focusNode
  if srcB.isEmptyMap then (.none, z.withTrie (z.trie.removeBelow z.focus))
  else if selfB.isEmptyMap then (.none, z)
  else
    let r := PathMap.restrictBelowRoot selfB srcB
    let st := nodeStatus ops selfB r
    if st == .identity then (.identity, z)
    else (st, z.withTrie (z.trie.graftBelow z.focus r))

/-- `ZipperWriting::restricting`: the mirror image — fill in `self`'s "stem"
paths with the source's subtries.  `self`'s subtrie is replaced by the source's,
restricted by the paths to values in `self`. -/
def restricting (src : Zip V) : Bool × Zip V :=
  -- `false`, leaving `self` untouched, when either side has nothing below its
  -- focus.  Note this is decided by `get_focus().is_none()`, which is true when
  -- there is no node below the focus but *false* when an empty node happens to
  -- have been materialised there by `create_path` or `remove_val` — see
  -- FINDINGS.md #8.  The model specifies the common case.
  if src.focusNodeIsEmpty then (false, z)
  else if z.focusNodeIsEmpty then (false, z)
  else (true, z.withTrie (z.trie.graftBelow z.focus
    (PathMap.restrictBelowRoot src.focusNode z.focusNode)))

/-! ## Collapsing path segments -/

/-- `ZipperWriting::join_k_path_into` (a.k.a. `drop_head`): strip the leading
`k` bytes from every path below the focus and join the results.

Values sitting at depth exactly `k` are **lost**: the joined node has no root
value slot.  Returns whether anything survives below the focus.

BUG (`pathmap` 0.3.1): `k = 0` should be the identity — dropping no bytes — but
`drop_head_dyn(0)` collapses the subtrie instead.  On `{[] ↦ 0, [0] ↦ 0,
[0,0] ↦ 0, [1,0] ↦ 0}` it leaves `{[] ↦ 0, [0] ↦ 0}`.  The model specifies the
identity; the harness skips `k = 0`. -/
def joinKPathInto (k : Nat) (prune : Bool) : Bool × Zip V :=
  let below := z.focusNode
  let (res, z1) :=
    if below.isEmptyMap then (false, z)
    else
      let r := PathMap.dropHead ops below k
      (!r.isEmptyMap, z.withTrie (z.trie.graftBelow z.focus r))
  (res, if prune && !res then (z1.prunePath).2 else z1)

/-- `meet_k_path_into` is **not implementable** for these arguments: its
provisional implementation drives `descend_first_k_path` through the
`ZipperIteration` *default* loop, which spins forever when the focus has no
children, and which escapes the focus's subtree entirely when `k = 0`.
Verified against `pathmap` 0.3.1: `meet_k_path_into(1, false)` on a leaf hangs. -/
def meetKPathUnspecified (k : Nat) : Bool := k == 0 || z.childCount == 0

/-- `ZipperWriting::meet_k_path_into`: strip the leading `k` bytes from every
path below the focus and meet the results.

Unlike `join_k_path_into`, this routes through `take_map`/`graft_map`, so values
at depth exactly `k` *are* carried — they become the focus value.  Only
meaningful when `meetKPathUnspecified` is `false`. -/
def meetKPathInto (k : Nat) (prune : Bool) : Bool × Zip V :=
  let kps := (z.trie.subtrie z.focus).kPaths k
  let result : Option (PathMap V) :=
    kps.foldl (fun acc q =>
      let m := z.trie.subtrie (z.focus ++ q)
      match acc with
      | none => some m
      | some a => some (PathMap.meet ops a m)) none
  match result with
  | some m => if m.isEmptyMap then (false, (z.removeBranches prune).2) else (true, z.graftMap m)
  | none => (false, (z.removeBranches prune).2)

end Zip
end PathMapModel
