import PathMapModel.Source

/-!
# `DiffZipper`

`differential/src/sources/diff.rs`: `pathmap::utils::debug::DiffZipper` over two
read zippers at root1, one of map1 and one of `map1.clone()`.  A `DiffZipper`
runs both in lockstep and `assert_eq!`s every answer, returning the first
zipper's.  Two zippers over the same trie must agree, so the view is the native
one: map1 at root1.

`DiffZipper` forwards `Zipper`, `ZipperMoving` (with `val_count`), `ZipperPath`,
`ZipperAbsolutePath` and `ZipperIteration`.  It has no `ZipperValues`; the Rust
adapter answers `val`/`val_at` with map1's value at the `DiffZipper`'s reported
origin path, which the native view predicts as well.  No forking, subtries or
read-only values.
-/

namespace PathMapModel

def Source.diff : Source :=
  { name := "diff"
    caps := { fork := false, makeMap := false, merge := false, getVal := false,
              getValIter := false } }

end PathMapModel
