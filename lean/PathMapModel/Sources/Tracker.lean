import PathMapModel.Source

/-!
# `PathTracker` (the template source)

`PathTracker::with_origin(map1.read_zipper_at_path(root1), root1)`, from
`differential/src/sources/tracker.rs`.  A path tracker re-creates the path
buffer of a "blind" zipper; around a zipper that already has one it must be
invisible, so the view is the native one.  It implements the read, movement,
iteration and `ZipperReadOnlyValues` traits, but not forking, subtries or
`ZipperReadOnlyIteration`.
-/

namespace PathMapModel

def Source.tracker : Source :=
  { name := "tracker"
    caps := { fork := false, makeMap := false, merge := false, getValIter := false } }

end PathMapModel
