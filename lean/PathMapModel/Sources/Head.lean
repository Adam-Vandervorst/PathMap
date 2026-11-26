import PathMapModel.Source

/-!
# `ZipperHead`'s tracked zippers (`--source head`)

`differential/src/sources/head.rs`: the write zipper is the `WriteZipperTracked`
a head over map0 hands out at `root0` (`write_zipper_at_exclusive_path`), the
read zipper the `ReadZipperTracked` a head over map1 hands out at `root1`
(`read_zipper_at_path`, or `read_zipper_at_borrowed_path`).  The heads come
from `PathMap::zipper_head`, `PathMap::into_zipper_head` or a write zipper's
`zipper_head`, chosen per input.

These are native zippers handed out under the head's exclusivity tracking, so
a head is invisible to everything the program can observe: the view is the
native one (map1 at root1) and the capabilities are the native read zipper's.
`ReadZipperTracked` has the *witness* forms of `ZipperReadOnlyValues` and
`ZipperReadOnlyIteration` (`get_val_with_witness`, `to_next_get_val_with_witness`);
they must answer exactly as the plain forms do, so ops 51 and 52 keep their
native specification.  It implements `ZipperReadOnlySubtries`, so op 75 runs on
the read side.

One teardown is observable: when `hdr / 6` is odd the write zipper is handed back
with `ZipperCreation::cleanup_write_zipper` instead of being dropped.  That is
documented to prune the zipper's root path if it is left dangling ("the act of
creating a write zipper at a path will create the parent path from the zipper
head, but then a dangling path may remain"), which is `prune_path` at `root0` by
the head's inner zipper, rooted at the map root.
-/

namespace PathMapModel

/-- `cleanup_write_zipper`'s effect on map0, when the input selects it. -/
def headFinalMap0 (hdr : Nat) (r0 : Path) (m : PathMap UInt64) : PathMap UInt64 :=
  if (hdr / 6) % 2 == 1 then (m.prunePath 0 r0).2 else m

def Source.head : Source :=
  { name := "head"
    caps := { trieRef := true, witnessIter := true, coldKPath := false }
    finalMap0 := headFinalMap0 }

-- The root path left dangling is pruned back to the nearest value...
#guard (headFinalMap0 6 [1, 2] (PathMap.mk' [([1], 7)] [[1, 2]])).paths == [[], [1]]
-- ...not when the root has a value or children, nor when cleanup is not selected.
#guard (headFinalMap0 6 [1, 2] (PathMap.mk' [([1, 2], 7)] [])).paths == [[], [1], [1, 2]]
#guard (headFinalMap0 6 [1] (PathMap.mk' [([1, 2], 7)] [])).paths == [[], [1], [1, 2]]
#guard (headFinalMap0 0 [1, 2] (PathMap.mk' [] [[1, 2]])).paths == [[], [1], [1, 2]]
#guard (headFinalMap0 6 [1, 2] (PathMap.mk' [] [[1, 2]])).paths == [[]]

end PathMapModel
