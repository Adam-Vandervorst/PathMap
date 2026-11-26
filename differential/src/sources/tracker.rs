//! `PathTracker` over the native read zipper: the template source.
//!
//! `PathTracker` re-creates a path buffer for "blind" zippers.  Wrapped around
//! a zipper that already has one, it must be invisible: the view is map1 at
//! root1, exactly as for `native`.  It implements the read, movement,
//! iteration and `ZipperReadOnlyValues` traits but not forking, subtries or
//! `ZipperReadOnlyIteration`, so `dump`, `make_map`, every merge and
//! `to_next_get_val` read `skip:tracker` (`Sources/Tracker.lean` mirrors this).
//!
//! Two constructors, chosen by [`tracker_new`] from the header roots (so the
//! wire format is unchanged and the model can compute the same choice):
//!
//! * `PathTracker::with_origin(map1.read_zipper_at_path(root1), root1)`: the
//!   native view, map1 at root1;
//! * `PathTracker::new(map1.read_zipper_at_path(root1))`: "tracking the path
//!   from the zipper's root" with no root prefix, so the tracker presents the
//!   subtrie of map1 at root1 as a trie of its own, rooted at `[]`
//!   (`origin_path` is the path below root1, `root_prefix_path` is empty).

use pathmap::zipper::*;

use crate::harness::*;
use crate::sources::trailer;

impl<'a, 'p> ReadSource for PathTracker<ReadZipperUntracked<'a, 'p, u64>> {
    const SKIP: &'static str = "skip:tracker";
    fn dump_fork(&self) -> Option<String> {
        None
    }
    fn make_map_val_count(&self) -> Option<usize> {
        None
    }
    fn get_val_probe(&self, path: &[u8]) -> Option<(Option<u64>, Option<u64>, bool)> {
        let (g, ga) = (self.get_val().copied(), self.get_val_at(path).copied());
        let agree = g == self.val().copied() && ga == self.val_at(path).copied();
        Some((g, ga, agree))
    }
    fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)> {
        None
    }
}

/// Whether this input builds the tracker with `PathTracker::new` (else
/// `with_origin`).  `trackerNew` in `Sources/Tracker.lean`.
pub fn tracker_new(root0: &[u8], root1: &[u8]) -> bool {
    (root0.len() + root1.len()) % 2 == 1
}

pub fn run(bytes: &[u8], check: bool) -> String {
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
    let Some((mut map0, map1, root0, root1)) = decode_header(&mut d) else {
        return "EMPTY\n".to_string();
    };
    let mut out = String::new();
    // `ROOT1` in the trailer is the read zipper's root, as in the model.
    let new = tracker_new(&root0, &root1);
    let root: &[u8] = if new { &[] } else { &root1 };
    {
        let mut rz = if new {
            PathTracker::new(map1.read_zipper_at_path(&root1))
        } else {
            PathTracker::with_origin(map1.read_zipper_at_path(&root1), &root1)
        };
        let mut wz = map0.write_zipper_at_path(&root0);
        run_ops(&mut d, &mut out, &mut wz, &root0, &mut rz, root, check);
    }
    trailer(&mut out, &map0, &map1, &root0, root);
    out
}
