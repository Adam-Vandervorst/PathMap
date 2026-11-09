//! `EmptyZipper`: a zipper over a completely empty trie.
//!
//! `EmptyZipper::new_at_path(p)` presents the empty trie with its root at `p`:
//! nothing exists, not even the root (`path_exists` is `false` everywhere), and
//! every movement that needs an existing child fails.  `p` is [`empty_root`],
//! which is never the empty path: the model's tries always contain the
//! absolute root `[]`, so an `EmptyZipper` at `[]` (whose root does not exist)
//! has no view (`lean/findings/prefix.md`, open question).
//!
//! It implements forking (`fork_read_zipper` is always `None`, so `dump` prints
//! the empty-root marker), `ZipperReadOnlyValues` and
//! `ZipperReadOnlyIteration`, but no subtries: it cannot make a map or be a
//! merge source (`skip:empty`).  `Sources/Empty.lean` mirrors this.

use pathmap::zipper::*;

use crate::harness::*;
use crate::sources::trailer;

/// Where the `EmptyZipper` is rooted: root1, or `[3]` when root1 is empty.
/// `Source.empty` in `Sources/Empty.lean` computes the same path.
pub fn empty_root(root1: &[u8]) -> Vec<u8> {
    if root1.is_empty() { vec![3] } else { root1.to_vec() }
}

impl ReadSource for EmptyZipper {
    const SKIP: &'static str = "skip:empty";
    fn dump_fork(&self) -> Option<String> {
        Some(dump_fork(self))
    }
    fn make_map_val_count(&self) -> Option<usize> {
        None
    }
    fn get_val_probe(&self, path: &[u8]) -> Option<(Option<u64>, Option<u64>, bool)> {
        let g = <Self as ZipperReadOnlyValues<u64>>::get_val(self).copied();
        let ga = <Self as ZipperReadOnlyValues<u64>>::get_val_at(self, path).copied();
        let agree = g == <Self as ZipperValues<u64>>::val(self).copied()
            && ga == <Self as ZipperValuesAt<u64>>::val_at(self, path).copied();
        Some((g, ga, agree))
    }
    fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)> {
        let got = <Self as ZipperReadOnlyIteration<u64>>::to_next_get_val(self).copied();
        let agree = got == <Self as ZipperValues<u64>>::val(self).copied()
            || (got.is_none() && self.at_root());
        Some((got.is_some(), got, agree))
    }
}

pub fn run(bytes: &[u8], check: bool) -> String {
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
    let Some((mut map0, map1, root0, root1)) = decode_header(&mut d) else {
        return "EMPTY\n".to_string();
    };
    let mut out = String::new();
    // `ROOT1` in the trailer is the read zipper's root, as in the model.
    let root = empty_root(&root1);
    {
        let mut rz = EmptyZipper::new_at_path(&root);
        let mut wz = map0.write_zipper_at_path(&root0);
        run_ops(&mut d, &mut out, &mut wz, &root0, &mut rz, &root, check);
    }
    trailer(&mut out, &map0, &map1, &root0, &root);
    out
}
