import PathMapModel.Source

/-!
# `EmptyZipper`

`EmptyZipper::new_at_path(p)`, from `differential/src/sources/empty.rs`: a
zipper over a completely empty trie, rooted at `p`.  Nothing exists there, not
even the root, so the view is the empty trie (only the absolute root `[]`
exists) with the zipper's root at `p`, which must therefore be non-empty: the
model cannot express an absent `[]`.  `p` is root1, or `[3]` when root1 is
empty.

`EmptyZipper` implements forking (every fork is `None`: the focus never
exists), `ZipperReadOnlyValues`, `ZipperReadOnlyIteration` and `val_count`, but
not `ZipperSubtries`, so it cannot make a map or be a merge source.
-/

namespace PathMapModel

/-- Where the `EmptyZipper` is rooted (`empty_root` in `sources/empty.rs`). -/
def emptyRoot (r1 : Path) : Path := if r1.isEmpty then [3] else r1

def Source.empty : Source :=
  { name := "empty"
    view := fun _ _ _ r1 => (PathMap.empty, emptyRoot r1)
    caps := { makeMap := false, merge := false, witnessIter := true } }

/-- `EmptyZipper::new()` behind `PathTracker::with_origin(_, emptyRoot r1)`
(`run_new` in `sources/empty.rs`).  `new()` is the same zipper as
`new_at_path` with an empty root prefix, and its root is a *missing* `[]`: the
model's tries always contain `[]`, so the root prefix comes from the tracker
instead (which resets the zipper and only tracks the path).  Everything but the
path is `new()`'s own answer, held to `empty`'s view.  `PathTracker` has no
forking and no `ZipperReadOnlyIteration`.  See `lean/findings/ctors.md` for the
decision on the root. -/
def Source.emptyNew : Source :=
  { Source.empty with
    name := "empty-new"
    caps := { fork := false, makeMap := false, merge := false, getValIter := false } }

#guard emptyRoot [] = [3]
#guard emptyRoot [0, 1] = [0, 1]
#guard (PathMap.empty : PathMap UInt64).pathExists (emptyRoot []) = false

end PathMapModel
