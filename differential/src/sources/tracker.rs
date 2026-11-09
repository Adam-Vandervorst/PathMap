//! `PathTracker` over the native read zipper: the template source.
//!
//! `PathTracker` re-creates a path buffer for "blind" zippers.  Wrapped around
//! a zipper that already has one, it must be invisible: the view is map1 at
//! root1, exactly as for `native`.  It implements the read, movement,
//! iteration and `ZipperReadOnlyValues` traits but not forking, subtries or
//! `ZipperReadOnlyIteration`, so `dump`, `make_map`, every merge and
//! `to_next_get_val` read `skip:tracker` (`Sources/Tracker.lean` mirrors this).

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

pub fn run(bytes: &[u8], check: bool) -> String {
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
    let Some((mut map0, map1, root0, root1)) = decode_header(&mut d) else {
        return "EMPTY\n".to_string();
    };
    let mut out = String::new();
    {
        let mut rz = PathTracker::with_origin(map1.read_zipper_at_path(&root1), &root1);
        let mut wz = map0.write_zipper_at_path(&root0);
        run_ops(&mut d, &mut out, &mut wz, &root0, &mut rz, &root1, check);
    }
    trailer(&mut out, &map0, &map1, &root0, &root1);
    out
}
