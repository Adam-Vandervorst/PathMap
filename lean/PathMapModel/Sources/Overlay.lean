import PathMapModel.Source

/-!
# `OverlayZipper`

`differential/src/sources/overlay.rs`: an `OverlayZipper` over

* `a` = `map1.read_zipper_at_path(root1)`, and
* `b` = a read zipper at **root0** over a clone of map0 taken right after the
  header (the write zipper's later edits to map0 never reach it).

The sources sit at different roots on purpose (the crate's own
`overlay_sources_at_different_roots` case).  The overlay presents its trie at
root1 (that is the root its `ZipperAbsolutePath` adapter reports).

## Meaning

`OverlayZipper` "traverses a virtual trie formed by fusing the tries of two
other zippers" (its doc comment).  Its accessors say what fusing means:
`path_exists` is `a || b`, `child_mask` is `a | b`, and `val` is
`mapping(a.val(), b.val())`, with `is_val` defined as `val().is_some()` so that a
mapping may *remove* a value.  So the view is:

* **existence** — the union: a location exists iff it exists under either
  source.  A dangling path of either source is a dangling path of the overlay,
  and so is a location whose value the mapping nullified.
* **values** — `mapping (valA p) (valB p)` at every location, the root included:
  the overlay's root value is `mapping (map1 @ root1) (map0 @ root0)`.

Every movement and iteration op is then the native `Zip` spec on that trie.  In
particular `descend_to_val` stops at the first location strictly below the
focus where the *overlay* has a value (a value of a source that the mapping
filters out does not stop it), or at the deepest existing prefix of the path —
exactly the native contract.

## Capabilities

`OverlayZipper` implements `Zipper`, `ZipperMoving`, `ZipperPath`,
`ZipperValues`, `ZipperValuesAt` and `ZipperIteration`; no forking, subtries,
read-only values or read-only iteration, and `val_count` is `todo!()`.
-/

namespace PathMapModel

/-- The fused trie of `a` and `b` under `f`, relative coordinates: the union of
the locations, `f (a p) (b p)` as the value. -/
def overlayTrie (f : Option UInt64 → Option UInt64 → Option UInt64)
    (a b : PathMap UInt64) : PathMap UInt64 :=
  let ps := Path.sortDedup (a.paths ++ b.paths)
  PathMap.mk' (ps.filterMap fun p => (f (a.valAt p) (b.valAt p)).map (p, ·))
    (a.paths ++ b.paths)

/-- The overlay view: map1 below root1 fused with map0 below root0, placed at
root1. -/
def overlayView (f : Option UInt64 → Option UInt64 → Option UInt64)
    (m0 m1 : PathMap UInt64) (r0 r1 : Path) : PathMap UInt64 × Path :=
  let o := overlayTrie f (m1.subtrie r1) (m0.subtrie r0)
  (PathMap.mk' (o.vals.map fun kv => (r1 ++ kv.1, kv.2)) (o.paths.map (r1 ++ ·)), r1)

/-- `OverlayZipper::new`'s mapping (`identity_ref`): `a`'s value where it has one,
else `b`'s. -/
def overlayDefault (a b : Option UInt64) : Option UInt64 := a <|> b

/-- `overlay-filter`'s mapping (`b_unless_a` in overlay.rs): `b`'s value, but only
where `a` has none. -/
def overlayBUnlessA (a b : Option UInt64) : Option UInt64 := if a.isSome then none else b

def overlayCaps : Caps :=
  { fork := false, makeMap := false, merge := false, getVal := false,
    getValIter := false, valCount := false }

def Source.overlay : Source :=
  { name := "overlay", view := fun m0 m1 r0 r1 => overlayView overlayDefault m0 m1 r0 r1,
    caps := overlayCaps }

def Source.overlayFilter : Source :=
  { name := "overlay-filter", view := fun m0 m1 r0 r1 => overlayView overlayBUnlessA m0 m1 r0 r1,
    caps := overlayCaps }

/-! ## Fixtures -/

namespace OverlayFixtures

/-- map1: `[1] = 5`, dangling `[1,2]`; root1 = `[]`. -/
def m1 : PathMap UInt64 := PathMap.mk' [([1], 5), ([4], 8)] [[1, 2]]
/-- map0: `[9] = 3`, `[9,1] = 6`, `[9,3] = 7`, `[9,4] = 9`; root0 = `[9]`. -/
def m0 : PathMap UInt64 := PathMap.mk' [([9], 3), ([9, 1], 6), ([9, 3], 7), ([9, 4], 9)] []

-- Default mapping: union of locations, `a` wins a collision, the root value comes
-- from map0 at root0 because map1 has none at root1.
#guard (overlayView overlayDefault m0 m1 [9] []).1.entries ==
  [([], some 3), ([1], some 5), ([1, 2], none), ([3], some 7), ([4], some 8)]
-- b-unless-a: a collision loses its value but the location stays.
#guard (overlayView overlayBUnlessA m0 m1 [9] []).1.entries ==
  [([], some 3), ([1], none), ([1, 2], none), ([3], some 7), ([4], none)]
-- Placed at root1.
#guard (overlayView overlayDefault m0 m1 [9] [7]).1.entries ==
  [([], none), ([7], some 3), ([7, 1], some 6), ([7, 3], some 7), ([7, 4], some 9)]
-- `descend_to_val` skips a value the mapping filtered out ([1]) and stops at the
-- deepest existing prefix ([1,2]) rather than running off the trie.
#guard (({ trie := (overlayView overlayBUnlessA m0 m1 [9] []).1, root := [], path := [] } : Zip UInt64).descendToVal [1, 2, 3]).1 == 2
#guard (({ trie := (overlayView overlayDefault m0 m1 [9] []).1, root := [], path := [] } : Zip UInt64).descendToVal [1, 2, 3]).1 == 1

end OverlayFixtures

end PathMapModel
