import PathMapModel.Source

/-!
# `PathTracker` (the template source)

`differential/src/sources/tracker.rs`.  A path tracker re-creates the path
buffer of a "blind" zipper; around a zipper that already has one it must be
invisible.  It implements the read, movement, iteration and
`ZipperReadOnlyValues` traits, but not forking, subtries or
`ZipperReadOnlyIteration`.

Two constructors, chosen from the header roots (`trackerNew`):

* `PathTracker::with_origin(map1.read_zipper_at_path(root1), root1)`: the
  native view, map1 at root1.
* `PathTracker::new(map1.read_zipper_at_path(root1))`: "tracking the path from
  the zipper's root", with an empty root prefix.  The tracker's paths are then
  relative to the wrapped zipper's root, so what it presents is map1's subtrie
  at root1 as a trie of its own, rooted at `[]`.  The header always creates
  root1, so that subtrie's root exists.
-/

namespace PathMapModel

/-- `tracker_new` in `sources/tracker.rs`. -/
def trackerNew (r0 r1 : Path) : Bool := (r0.length + r1.length) % 2 == 1

def Source.tracker : Source :=
  { name := "tracker"
    view := fun _ m1 r0 r1 => if trackerNew r0 r1 then (m1.subtrie r1, []) else (m1, r1)
    caps := { fork := false, makeMap := false, merge := false, getValIter := false } }

-- `new` re-roots: the subtrie at root1, its root value included, at `[]`.
#guard (Source.tracker.view PathMap.empty (PathMap.mk' [([1], 5), ([1, 2], 6)] []) [] [1]).1.vals
  == [([], 5), ([2], 6)]
#guard (Source.tracker.view PathMap.empty (PathMap.mk' [([1], 5)] []) [] [1]).2 == []
#guard (Source.tracker.view PathMap.empty (PathMap.mk' [([1], 5)] []) [0] [1]).2 == [1]

end PathMapModel
