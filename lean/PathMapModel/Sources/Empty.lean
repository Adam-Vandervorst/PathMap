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
    caps := { makeMap := false, merge := false } }

#guard emptyRoot [] = [3]
#guard emptyRoot [0, 1] = [0, 1]
#guard (PathMap.empty : PathMap UInt64).pathExists (emptyRoot []) = false

end PathMapModel
