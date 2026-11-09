import PathMapModel.Source

/-!
# `DependentProductZipperG`

`DependentProductZipperG::new_enroll(map1.read_zipper_at_path(root1), ctx,
enroll)`, from `differential/src/sources/dependent.rs`.  A product zipper
whose next factor is computed, at each joint, by `enroll(ctx, path, n)`:
`path` is the path from the zipper's root to the joint and `n` the number of
secondary factors already entered.

## What the trie presented is

A **joint** is a leaf of the factor the focus is in: a location that exists
and has no children (`is_path_end`).  At a joint the closure may return a
factor, whose trie is grafted *below* the joint:

* the joint's own value is the earlier factor's (`factor_idx(true)` skips the
  factors entered at the current depth), so a factor's root value is never
  seen;
* the root of the primary counts: a primary rooted at a leaf is a joint;
* a factor with nothing below its root leaves the joint a leaf, so the closure
  is asked again there, with `n + 1`: factors entered at one joint stack.

The crate enters factors lazily, when a descend (or `descend_until`) lands on
a joint, and one per call.  That is invisible except in the last two cases: a
joint at the primary's root is not entered until the first descend, and is
forgotten by `reset` (finding D1); a stacked factor is not entered until a
later call at the same place (finding D2).  Either way what the zipper presents
depends on its history, so neither reading is a consistent specification; the
view is the denotation the doc comment describes ("extending each path in a
primary trie with the computed virtual trie, recursively").

Every read is the native `Zip` specification applied to the view, `val_at`
included: `val_at(p)` is what `descend_to(p)` then `val()` would see.  The
crate's `val_at`/`get_val_at` look only in the focus factor (finding D3).

So the view is map1 with everything below root1 replaced by `expand` of
map1's subtrie at root1: walk the factor's locations, and below every leaf
splice in the expansion of the factor the closure picks there.  This is the
same denotation as the fixed-factor `ProductZipperG` (at every leaf of factor
`i`, factor `i+1` is grafted; the earlier value wins), with the factor chosen
per joint.

## The closure

```text
n >= maxDepth                        -> none
(n + |path| + Σ path) mod 4 = 0      -> map0 (snapshot after the header)
                             = 1      -> map1 at its root
                             = 2      -> map1 at root1
                             = 3      -> none
```

The context carries `maxDepth` and a call counter the choice never reads, so
the view is a function of the seeded maps alone.  `--source dependent` (the
campaign source) adds two guards that keep the closure away from D1 and D2: no
factor at the primary's root (`path = []`), and no factor with nothing below
its root.  `--source dependent-lazy` drops them and replays those findings.

## Capabilities

No `ZipperForking`, no `ZipperInfallibleSubtries` (its `ZipperSubtries` impl
declines: `try_make_map` is `None`), no `ZipperReadOnlyIteration`, and
`val_count` is `unimplemented!`.  `ZipperReadOnlyValues` is implemented.
-/

namespace PathMapModel
namespace Dependent

/-- `MAX_DEPTH` in `dependent.rs`: at most this many secondary factors. -/
def maxDepth : Nat := 2

/-- `choose` in `dependent.rs`. -/
def choose (p : Path) (n : Nat) : Nat :=
  (n + p.length + (p.map (·.toNat)).foldl (· + ·) 0) % 4

/-- The factor the closure returns at joint `p` (relative to root1) with `n`
secondary factors entered.  `strict` adds the two guards of `--source
dependent`: no factor at the primary's root, and no factor with nothing below
its root (`lean/findings/dependent.md`, D1 and D2). -/
def factor (strict : Bool) (m0 m1 : PathMap UInt64) (r1 : Path) (p : Path) (n : Nat) :
    Option (PathMap UInt64) :=
  if n ≥ maxDepth || (strict && p.isEmpty) then none
  else
    let s := match choose p n with
      | 0 => some m0
      | 1 => some m1
      | 2 => some (m1.subtrie r1)
      | _ => none
    s.filter fun t => !strict || t.childCount [] > 0

/-- The entries of factor `t` entered at `base` with `k` factors already on the
stack (`k = 0`: the primary), each joint followed by the expansion below it.
`t.entries` is canonical, so a location is a leaf iff the next entry does not
extend it, and the output is canonical too (an expansion sorts between its
joint and the joint's next sibling).  A secondary factor's root entry is
dropped: the joint is the earlier factor's.  `fuel` bounds the recursion; the
closure stops at `maxDepth`, so `maxDepth + 1` suffices. -/
def expand (fac : Path → Nat → Option (PathMap UInt64)) :
    Nat → PathMap UInt64 → Path → Nat → List (Path × Option UInt64)
  | 0, t, base, _ => t.entries.map fun (q, v) => (base ++ q, v)
  | fuel + 1, t, base, k =>
    let rec go : List (Path × Option UInt64) → List (Path × Option UInt64)
      | [] => []
      | (q, v) :: rest =>
        let leaf := match rest with
          | (q', _) :: _ => !Path.isPrefixOf q q'
          | [] => true
        let here := if k > 0 && q.isEmpty then [] else [(base ++ q, v)]
        let below := if leaf then
            match fac (base ++ q) k with
            | some s => expand fac fuel s (base ++ q) (k + 1)
            | none => []
          else []
        here ++ below ++ go rest
    go t.entries

/-- map1 with its subtrie at `r1` replaced by the product expansion. -/
def view (strict : Bool) (m0 m1 : PathMap UInt64) (_r0 r1 : Path) : PathMap UInt64 × Path :=
  let prod := expand (factor strict m0 m1 r1) (maxDepth + 1) (m1.subtrie r1) [] 0
  let before := m1.entries.filter fun (p, _) => Path.lt p r1
  let after := m1.entries.filter fun (p, _) => !Path.lt p r1 && !Path.isPrefixOf r1 p
  ({ entries := before ++ prod.map (fun (q, v) => (r1 ++ q, v)) ++ after }, r1)

end Dependent

def Dependent.caps : Caps :=
  { fork := false, makeMap := false, merge := false, getValIter := false, valCount := false }

/-- The campaign source: the closure keeps away from D1 and D2. -/
def Source.dependent : Source :=
  { name := "dependent", view := Dependent.view true, caps := Dependent.caps }

/-- The closure without the guards: the same denotation, which the crate
misses whenever D1 or D2 is reached.  For replaying those findings. -/
def Source.dependentLazy : Source :=
  { name := "dependent-lazy", view := Dependent.view false, caps := Dependent.caps }

namespace Dependent

/-! ## Fixtures -/

private def mkT (vs : List (Path × UInt64)) : PathMap UInt64 := PathMap.mk' vs []

/-- The view is canonical: what `mk'` would make of its own entries. -/
private def canonical (t : PathMap UInt64) : Bool :=
  (PathMap.mk' t.vals t.paths).entries == t.entries

-- Primary `{[1]:5}` at root `[]`: the joint `[1]` has `choose [1] 0 = 2`,
-- map1 at root1 (the primary itself); its leaf `[1,1]` has
-- `choose [1,1] 1 = 1`, map1 again; at `[1,1,1]` two factors are entered
-- and the closure stops.
#guard (view false (mkT [([7], 9)]) (mkT [([1], 5)]) [] []).1.vals ==
  [([1], 5), ([1, 1], 5), ([1, 1, 1], 5)]
-- The joint `[3]` (`choose = 0`: map0) keeps the primary's value; map0's root
-- value `3` is hidden.
#guard (view false (mkT [([], 3), ([2], 4)]) (mkT [([], 1), ([3], 6)]) [] []).1.vals ==
  [([], 1), ([3], 6), ([3, 2], 4), ([3, 2, 2], 4)]
-- A primary rooted at a leaf is a joint: `choose [] 0 = 0` grafts map0 there.
#guard (view false (mkT [([2], 4)]) (PathMap.mk' [([9], 1)] [[5]]) [] [5]).1.vals ==
  [([5, 2], 4), ([5, 2, 2], 4), ([9], 1)]
-- An empty factor leaves the joint a leaf, so the next one stacks there: at
-- root1 `[4]` (a leaf), `choose [] 0 = 0` picks map0 (empty), then
-- `choose [] 1 = 1` picks map1 below the same joint.
#guard (view false PathMap.empty (PathMap.mk' [([1], 5)] [[4]]) [] [4]).1.vals ==
  [([1], 5), ([4, 1], 5)]
-- The strict closure declines both: no factor at the primary's root ...
#guard (view true (mkT [([2], 4)]) (PathMap.mk' [([9], 1)] [[5]]) [] [5]).1.vals ==
  [([9], 1)]
-- ... and no empty factor (lazily, map1 would be stacked below `[3]`).
#guard (view true PathMap.empty (mkT [([3], 5)]) [] []).1.vals == [([3], 5)]
#guard (view false PathMap.empty (mkT [([3], 5)]) [] []).1.vals == [([3], 5), ([3, 3], 5)]
#guard canonical (view false (mkT [([2], 4), ([2, 3], 1), ([0], 0)])
  (mkT [([1], 5), ([1, 2], 7), ([3], 0)]) [] []).1

end Dependent
end PathMapModel
