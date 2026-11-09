import PathMapModel.Source

/-!
# `ProductZipper` and `ProductZipperG`

`differential/src/sources/product.rs` builds, for both zipper types,

```text
primary     = map1.read_zipper_at_path(r)        r = productRoot map1 root1
secondaries = [ snap.read_zipper(), map1.read_zipper() ]
```

where `snap` is a `PathMap` clone of map0 taken right after the header, before
any operation runs (so it shares structure with the live map0 that the write
zipper then mutates), and `r` is the longest prefix of root1 at which map1 has
children (`[]` if there is none; see `productRoot` for why not root1 itself).
Every secondary is a root-level zipper, which keeps clear of the documented
"secondary factors must be at node roots" panic.

The two zipper types are two implementations of one meaning, so they share
one view; they differ only in capabilities.

## The denotation (leaf-based)

`prod [t] = t` and `prod (t :: fs) = t` with `prod fs` grafted below every
*leaf* of `t`: every existing path of `t` with no children, valued or dangling.
At a joint the location keeps `t`'s value (or its absence): the root value of
`prod fs` is never visible ("the value from the earlier zipper takes
precedence", `enroll_next_factor`).  A valued path that has children is not a
joint.  If `prod fs` has nothing below its root, a leaf stays a leaf.

The root of a factor is a leaf like any other path when it has no children.
This is the one place the reading is a choice (see
`lean/findings/product.md`, "the empty factor"): it makes an empty factor
transparent, keeps `prod` associative (`prod2 (prod2 a b) c = prod2 a (prod2 b
c)`, checked below), and is the stitch rule both implementations apply
whenever they test a location (`ensure_descend_next_factor`,
`enter_factors`: "path exists and has no children", with no exception for a
factor's root).

The view is map1 with everything strictly below `r` replaced by
`prod [map1.subtrie r, snap, map1]`, rooted at `r`.

## Capabilities

* `ProductZipper`: no `ZipperForking`, no subtries (the closing comment of
  `product_zipper.rs` explains why it cannot be a merge source), only the
  `ZipperReadOnlyConditionalValues` flavour of read-only values (checked
  through `get_val_with_witness`), no read-only iteration.  `val_count` is
  implemented.
* `ProductZipperG`: the same, except that it implements
  `ZipperReadOnlyValues` (`get_val`/`get_val_at`) directly, and its
  `val_count` is `unimplemented!()`.

Both report `ZipperProduct` (`factor_count`, `focus_factor`, `path_indices`)
through `Source.info`: `P<count>:<focus>:<indices>` with the indices strictly
above the focus (`productInfo`).
-/

namespace PathMapModel
namespace Product

open PathMap

variable {V : Type}

/-! ## The product -/

/-- The leaves of a trie: existing paths with no children, valued or dangling.
Includes `[]` when the root has no children. -/
def leaves (t : PathMap V) : List Path := t.paths.filter (fun p => t.childCount p == 0)

/-- The non-root entries of `s`, moved below `l`. -/
def shiftBelow (s : PathMap V) (l : Path) : List (Path × Option V) :=
  s.entries.filterMap fun (q, v) => if q.isEmpty then none else some (l ++ q, v)

/-- `t` with the non-root content of `s` grafted below every leaf of `t`.

Built directly in canonical order: a leaf `l` has no extension in `t`, so
`l ++ q` sorts after `l` and before the next entry of `t`; and every prefix of
`l ++ q` is a prefix of `l` or `l` followed by a prefix of `q`, so the result is
prefix-closed.  (`mk'` would give the same trie, quadratically.) -/
def prod2 (t s : PathMap V) : PathMap V :=
  { entries := t.entries.flatMap fun (p, v) =>
      (p, v) :: (if t.childCount p == 0 then shiftBelow s p else []) }

/-- The leaf-based product of a list of factors. -/
def prod : List (PathMap V) → PathMap V
  | [] => PathMap.empty
  | [t] => t
  | t :: fs => prod2 t (prod fs)

/-- `t` with everything strictly below `r` (which exists in `t`) replaced by the
non-root content of `s`; the value at `r` is untouched. -/
def graftAt (t : PathMap V) (r : Path) (s : PathMap V) : PathMap V :=
  { entries := t.entries.flatMap fun (q, v) =>
      if q == r then (q, v) :: shiftBelow s r
      else if r ≼ q then [] else [(q, v)] }

/-- The primary's root: the longest prefix of `root1` at which map1 has
children, else `[]`.

The header always creates root1, and a random root1 is almost never a path
that map1 already had, so a primary at root1 itself would nearly always be a
lone dangling leaf: every program would test the product of nothing.  Backing
up to the nearest ancestor with children keeps a non-empty primary (it then
holds root1 as a dangling leaf, a joint), and leaves the childless primary root
to the inputs where map1 is genuinely empty and root1 is `[]`. -/
def productRoot (m1 : PathMap V) (r1 : Path) : Path :=
  ((r1.prefixes.filter (fun p => m1.childCount p > 0)).getLast?).getD []

/-- The three factors, from the maps as the header left them. -/
def factors (m0 m1 : PathMap V) (r : Path) : List (PathMap V) :=
  [m1.subtrie r, m0, m1]

/-- The view: what both product zippers present. -/
def view (m0 m1 : PathMap V) (r1 : Path) : PathMap V × Path :=
  let r := productRoot m1 r1
  (graftAt m1 r (prod (factors m0 m1 r)), r)

/-! ## `ZipperProduct` -/

/-- How far `r` exists in `t`: the length of its longest existing prefix. -/
def existingLen (t : PathMap V) (r : Path) : Nat :=
  ((List.range (r.length + 1)).filter (fun j => t.pathExists (r.take j))).getLastD 0

/-- The depths at which the walk along `r` (from depth `base`) enters each later
factor: where the existing part of `r` in the current factor ends at a leaf,
the next factor starts.  An empty factor is entered and immediately left, so
its start repeats. -/
def starts : List (PathMap V) → Path → Nat → List Nat
  | [], _, _ => []
  | [_], _, _ => []
  | t :: fs, r, base =>
      let k := existingLen t r
      if t.childCount (r.take k) == 0 then (base + k) :: starts fs (r.drop k) (base + k)
      else []

/-- `ZipperProduct` at relative path `p`: `factor_count`, `focus_factor` and
those `path_indices` strictly above the focus.

`focus_factor` is the number of factors entered strictly above the focus (at a
joint the focus is still in the earlier factor, whose value it shows).
`path_indices` is documented to have exactly `focus_factor` entries; both
implementations also keep the start of a factor entered *at* the focus, so
only the entries above it are compared (see `lean/findings/product.md`). -/
def info (fs : List (PathMap V)) (p : Path) : String :=
  let es := (starts fs p 0).filter (· < p.length)
  "P" ++ toString fs.length ++ ":" ++ toString es.length ++ ":" ++
    String.intercalate "." (es.map toString)

def productInfo (m0 m1 : PathMap UInt64) (_r0 r1 : Path) (p : Path) : String :=
  info (factors m0 m1 (productRoot m1 r1)) p

/-! ## Named skips (crate bugs, `lean/findings/product.md`) -/

/-- `val_at q` where the path from the focus to `focus ++ q` crosses a joint
(one at depth `d` with `|focus| ≤ d < |focus ++ q|`): neither zipper's
`val_at` follows a path across a joint into the next factor.

For `ProductZipper` (`inFactor`), also every `val_at` with the focus at a joint
or below one: its `val_at` asks the core's `focus_parent`, which looks the
pushed secondary root up in the previous factor's node, and panics (or reads
the wrong node) while the focus is inside the first node of a secondary.
Where that node ends is a layout matter, so the whole region is declined. -/
def skipValAtJoint : String := "skip:product-val-at-joint"

def valAtSkip (inFactor : Bool) (m0 m1 : PathMap UInt64) (_r0 r1 : Path) (focus q : Path) :
    Option String :=
  let full := focus ++ q
  let es := starts (factors m0 m1 (productRoot m1 r1)) full 0
  let crosses := es.any (fun e => focus.length ≤ e && e < full.length)
  let inside := inFactor && es.any (fun e => e ≤ focus.length)
  if crosses || inside then some skipValAtJoint else none

/-- A factor whose root has no children: map0 (the snapshot), or map1 (which
then also leaves the primary root childless).  Both zippers mishandle an empty
factor; `product-full`/`productg-full` run these inputs anyway. -/
def skipEmptyFactor : String := "skip:product-empty-factor"

def inputSkip (m0 m1 : PathMap UInt64) (_r0 _r1 : Path) : Option String :=
  if m0.childCount [] == 0 || m1.childCount [] == 0 then some skipEmptyFactor else none

/-! ## Relation to Zippy's `Composition`

`Composition s t` (`lean/PrunedModel/Zippy.lean` on the zippy branches) is a
fold over the keys `u` of `s` of `descend_to u; join_map_into t`, i.e. on value
paths `keys(s) · keys(t)`.  The product is leaf-based instead:

  keys (prod2 T1 T2) = keys T1 ∪ { l ++ q | l ∈ leaves T1, q ∈ keys T2, q ≠ [] }

When `T1`'s keys are prefix-free and it has no dangling path (so its leaves
are exactly its keys) this is `keys T1 · (keys T2 ∪ {[]})`, and it equals
`Composition` exactly when, in addition, `T2` has a root value.  The four
differences (internal keys of `T1`, `T1`'s leaf values kept, an empty `T2`,
dangling leaves of `T1`) are semantic decisions, listed in
`lean/findings/product.md`. -/

/-- The value paths of a trie, sorted. -/
def keys (t : PathMap V) : List Path := t.vals.map (·.1)

/-- `keys(s) · keys(t)`: Zippy's `Composition` on value paths. -/
def compositionKeys (s t : PathMap V) : List Path :=
  Path.sortDedup ((keys s).flatMap fun u => (keys t).map (u ++ ·))

/-- The right-hand side of the general identity. -/
def leafProductKeys (t1 t2 : PathMap V) : List Path :=
  Path.sortDedup (keys t1 ++ (leaves t1).flatMap fun l =>
    (keys t2).filterMap fun q => if q.isEmpty then none else some (l ++ q))

/-- `Composition s t` as a trie, as Zippy builds it: an empty map, and for each
key `u` of `s`, `t` joined in at `u`.  `s`'s own values are not kept. -/
def composition (s t : PathMap UInt64) : PathMap UInt64 :=
  (keys s).foldl (fun acc u =>
    let tu : PathMap UInt64 :=
      mk' (t.vals.map fun (q, v) => (u ++ q, v)) (t.paths.map (u ++ ·))
    PathMap.join u64Ops acc tu) PathMap.empty

/-- Which semantics the `product`/`productg` view uses.  `leaf` is the model;
`composition` is the alternative the findings compare it with.  Flipping
`semantics` below switches both sources' view (and turns the `ZipperProduct`
report off, which has no meaning under `composition`). -/
inductive Semantics | leaf | composition

def semantics : Semantics := .leaf

/-- The n-ary product under the chosen semantics, right-nested. -/
def prodWith : Semantics → List (PathMap UInt64) → PathMap UInt64
  | .leaf, fs => prod fs
  | .composition, [] => PathMap.empty
  | .composition, [t] => t
  | .composition, t :: fs => composition t (prodWith .composition fs)

def viewWith (sem : Semantics) (m0 m1 : PathMap UInt64) (r1 : Path) :
    PathMap UInt64 × Path :=
  let r := productRoot m1 r1
  (graftAt m1 r (prodWith sem (factors m0 m1 r)), r)

/-! ## Checks -/

section Checks

/-- A trie from `(path, value?)` pairs: `none` makes a dangling path. -/
private def T (es : List (Path × Option Nat)) : PathMap UInt64 :=
  mk' (es.filterMap fun (p, v) => v.map fun n => (p, UInt64.ofNat n)) (es.map (·.1))

private def ents (t : PathMap UInt64) : List (Path × Option UInt64) := t.entries

-- `product_zipper_test1`, in miniature: a leaf value stays, the secondary's
-- paths hang below it.
#guard ents (prod [T [([1], some 0)], T [([7], some 9)]]) ==
  ents (T [([1], some 0), ([1, 7], some 9)])
-- A valued path with children is not a joint.
#guard ents (prod [T [([1], some 0), ([1, 2], some 1)], T [([7], some 9)]]) ==
  ents (T [([1], some 0), ([1, 2], some 1), ([1, 2, 7], some 9)])
-- A dangling leaf is a joint (`product_zipper_testb`).
#guard ents (prod [T [([1], none)], T [([7], some 9)]]) ==
  ents (T [([1], none), ([1, 7], some 9)])
-- The secondary's root value is never visible; the joint keeps its own.
#guard ents (prod [T [([1], none)], T [([], some 5), ([7], some 9)]]) ==
  ents (T [([1], none), ([1, 7], some 9)])
-- An empty secondary leaves a leaf a leaf ...
#guard ents (prod [T [([1], some 0)], T []]) == ents (T [([1], some 0)])
-- ... and is transparent between two factors.
#guard ents (prod [T [([1], some 0)], T [], T [([7], some 9)]]) ==
  ents (T [([1], some 0), ([1, 7], some 9)])
-- A childless primary root is a joint.
#guard ents (prod [T [], T [([7], some 9)]]) == ents (T [([7], some 9)])
#guard ents (prod [T [([], some 3)], T [([], some 4), ([7], some 9)]]) ==
  ents (T [([], some 3), ([7], some 9)])
-- Three factors: below the leaves of the leaves.
#guard ents (prod [T [([1], some 0)], T [([2], some 1)], T [([3], some 2)]]) ==
  ents (T [([1], some 0), ([1, 2], some 1), ([1, 2, 3], some 2)])

-- `prod2` builds a canonical trie: the same entries `mk'` gives.
private def canon (t : PathMap UInt64) : PathMap UInt64 :=
  mk' (t.vals) t.paths

-- `graftAt`: everything strictly below the root is replaced; the rest and the
-- root's value stay.
#guard ents (graftAt (T [([0], some 1), ([1], some 2), ([1, 5], some 3), ([2], some 4)]) [1]
    (T [([], some 7), ([8], some 8)])) ==
  ents (T [([0], some 1), ([1], some 2), ([1, 8], some 8), ([2], some 4)])

-- The primary root backs up from a dangling root1 to the nearest ancestor
-- with children ...
#guard productRoot (T [([0, 1], some 1)]) [0, 1] == [0]
#guard productRoot (T [([0, 1], some 1), ([0, 1, 2], none)]) [0, 1] == [0, 1]
-- ... and is `[]` only for an empty map1.
#guard productRoot (T []) [] == []
#guard productRoot (T [([5], none)]) [5] == []

-- `ZipperProduct`: the inspection test's shape, two levels.
#guard info [T [([1], some 0)], T [([2, 3], some 1)], T [([4], some 2)]] [] == "P3:0:"
#guard info [T [([1], some 0)], T [([2, 3], some 1)], T [([4], some 2)]] [1] == "P3:0:"
#guard info [T [([1], some 0)], T [([2, 3], some 1)], T [([4], some 2)]] [1, 2] == "P3:1:1"
#guard info [T [([1], some 0)], T [([2, 3], some 1)], T [([4], some 2)]] [1, 2, 3, 4] == "P3:2:1.3"
-- A path that leaves the trie stays in the factor it left from.
#guard info [T [([1], some 0)], T [([2, 3], some 1)], T [([4], some 2)]] [1, 9, 9] == "P3:1:1"
#guard info [T [([1], some 0)], T [([2, 3], some 1)], T [([4], some 2)]] [9, 9] == "P3:0:"
-- An empty middle factor is entered and left at the same depth.
#guard info [T [([1], some 0)], T [], T [([4], some 2)]] [1, 4] == "P3:2:1.1"

/-! ### The product against `Composition`, over a battery of shapes -/

/-- Small tries over bytes {1, 2}: empty, root value, internal keys, dangling
leaves, a dangling internal path, prefix-free sets. -/
private def battery : List (PathMap UInt64) :=
  [ T [], T [([], some 1)], T [([1], some 1)], T [([1], none)],
    T [([1], some 1), ([2], some 2)], T [([1], some 1), ([1, 2], some 2)],
    T [([1], some 1), ([2], none)], T [([1, 2], some 1)],
    T [([], some 1), ([1], some 2)], T [([1], none), ([1, 2], some 1), ([2], some 3)],
    T [([], some 5), ([2], some 6), ([2, 1], some 7)], T [([1, 1], some 1), ([2], some 2)] ]

private def pairs : List (PathMap UInt64 × PathMap UInt64) :=
  battery.flatMap fun a => battery.map (a, ·)

/-- Keys prefix-free, and no dangling path (the root included). -/
private def prefixFreeClean (t : PathMap UInt64) : Bool :=
  t.paths.all (fun p => (t.valAt p).isSome || t.childCount p > 0) &&
  (keys t).all (fun u => (keys t).all (fun w => u == w || !(u ≼ w)))

-- The general identity, for every pair.
#guard pairs.all fun (a, b) => keys (prod2 a b) == leafProductKeys a b
-- Prefix-free, clean `T1`: `keys T1 · (keys T2 ∪ {[]})`.
#guard pairs.all fun (a, b) => !prefixFreeClean a ||
  keys (prod2 a b) == Path.sortDedup ((keys a).flatMap fun u => ([] :: keys b).map (u ++ ·))
-- ... which is `Composition` exactly when `T2` has a root value (for a
-- non-empty `T1`).
#guard pairs.all fun (a, b) => !prefixFreeClean a || (keys a).isEmpty ||
  ((keys (prod2 a b) == compositionKeys a b) == (b.valAt []).isSome)
-- `composition` the trie has `compositionKeys` as its keys.
#guard pairs.all fun (a, b) => keys (composition a b) == compositionKeys a b
-- `prod2` is canonical and associative.
#guard pairs.all fun (a, b) => ents (prod2 a b) == ents (canon (prod2 a b))
#guard battery.all fun a => pairs.all fun (b, c) =>
  ents (prod2 (prod2 a b) c) == ents (prod2 a (prod2 b c))

-- The four counterexamples, one each.
-- 1. An internal key of `T1` gets no copy of `T2`.
#guard keys (prod2 (T [([1], some 1), ([1, 2], some 2)]) (T [([], some 0), ([5], some 5)])) ==
  [[1], [1, 2], [1, 2, 5]]
#guard compositionKeys (T [([1], some 1), ([1, 2], some 2)]) (T [([], some 0), ([5], some 5)]) ==
  [[1], [1, 2], [1, 2, 5], [1, 5]]
-- 2. A leaf's value is kept even when `T2` has no root value.
#guard keys (prod2 (T [([1], some 1)]) (T [([5], some 5)])) == [[1], [1, 5]]
#guard compositionKeys (T [([1], some 1)]) (T [([5], some 5)]) == [[1, 5]]
-- 3. An empty `T2` leaves `T1` as it is.
#guard keys (prod2 (T [([1], some 1)]) (T [])) == [[1]]
#guard compositionKeys (T [([1], some 1)]) (T []) == []
-- 4. A dangling leaf of `T1` is a joint.
#guard keys (prod2 (T [([1], none)]) (T [([], some 0), ([5], some 5)])) == [[1, 5]]
#guard compositionKeys (T [([1], none)]) (T [([], some 0), ([5], some 5)]) == []

end Checks

end Product

open Product in
/-- `ProductZipper` and `ProductZipperG` share the view and the skips; `full`
drops both skips (the `-full` sources reproduce every product finding). -/
def Source.productLike (name : String) (generic full : Bool) : Source :=
  { name := name
    view := fun m0 m1 _ r1 => viewWith semantics m0 m1 r1
    info := match semantics with
      | .leaf => some productInfo
      | .composition => none
    valAtSkip := if full then none else some (Product.valAtSkip (!generic))
    inputSkip := if full then none else some Product.inputSkip
    caps := { fork := false, makeMap := false, merge := false, getValIter := false,
              valCount := !generic } }

/-- `ProductZipper` over [map1 at `productRoot`, map0 snapshot, map1]. -/
def Source.product : Source := Source.productLike "product" false false
/-- `ProductZipperG` over the same factors: the same view, no `val_count`. -/
def Source.productg : Source := Source.productLike "productg" true false
def Source.productFull : Source := Source.productLike "product-full" false true
def Source.productgFull : Source := Source.productLike "productg-full" true true

end PathMapModel
