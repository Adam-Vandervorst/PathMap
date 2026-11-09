//! Read sources and write targets beyond the native `PathMap` zippers.
//!
//! The operation table in [`crate::harness::run_ops`] is generic over what the
//! read zipper (`rz`) is and what the write zipper (`wz`) is.  Each module here
//! builds one alternative -- a virtual zipper over map1 (`ProductZipper`,
//! `PrefixZipper`, ...), or a differently-owned zipper (`ZipperHead`'s tracked
//! zippers, the owned zippers) -- and runs the same program through it.
//!
//! The Lean model mirrors every source in `lean/PathMapModel/Sources/`: a
//! source there is a *view* (the trie the read zipper presents, computed from
//! the seeded maps) plus the capabilities it has.  Selecting a source is
//! `pathmap_trace --source NAME` on this side and `pathmap-oracle --source NAME`
//! on the other; `lean/differential.py --source NAME` drives both.
//!
//! Adding a source:
//!
//! 1. `sources/<name>.rs` with `pub fn run(bytes: &[u8], check: bool) -> String`
//!    (copy `tracker.rs`) and, if the zipper type is new, its `ReadSource` impl
//!    with `const SKIP = "skip:<name>"`;
//! 2. a `mod` line and a `SOURCES` row below;
//! 3. `lean/PathMapModel/Sources/<Name>.lean` and a row in `Sources.lean`'s
//!    `Source.all`.

use crate::harness::*;

pub mod tracker;
pub mod overlay;
pub mod diff;

/// A runner: decode and execute one input, return the trace.
pub type Runner = fn(&[u8], bool) -> String;

/// Every source, by the name both front ends use.  `native` and `act` are the
/// two original front ends.
pub const SOURCES: &[(&str, Runner)] = &[
    ("native", run),
    ("act", crate::act::run_act),
    ("tracker", tracker::run),
    ("overlay", overlay::run),
    ("overlay-filter", overlay::run_filter),
    ("diff", diff::run),
    // Not a read source: the map-level fuzzer, a different op table.
    ("map", crate::mapfuzz::run),
];

pub fn runner(name: &str) -> Option<Runner> {
    SOURCES.iter().find(|(n, _)| *n == name).map(|(_, r)| *r)
}

/// Implement [`ReadSource`] for a zipper that has the native read zipper's whole
/// trait surface (subtries, forking, read-only values and iteration), under the
/// given skip token.  Every merge operation reads it as a source.  The impl
/// site needs `pathmap::zipper::*` in scope (for the trait methods).
#[macro_export]
macro_rules! full_read_source {
    ($skip:expr) => {
        const SKIP: &'static str = $skip;
        fn dump_fork(&self) -> Option<String> {
            Some($crate::harness::dump_fork(self))
        }
        fn make_map_val_count(&self) -> Option<usize> {
            Some(self.make_map().val_count())
        }
        fn get_val_probe(&self, path: &[u8]) -> Option<(Option<u64>, Option<u64>, bool)> {
            let (g, ga) = (self.get_val().copied(), self.get_val_at(path).copied());
            let agree = g == self.val().copied() && ga == self.val_at(path).copied();
            Some((g, ga, agree))
        }
        fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)> {
            let got = self.to_next_get_val().copied();
            let agree = got == self.val().copied() || (got.is_none() && self.at_root());
            Some((got.is_some(), got, agree))
        }
        fn do_graft<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W) -> bool {
            wz.graft(self);
            true
        }
        fn do_graft_masked<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W, m: ::pathmap::utils::ByteMask, ru: bool) -> bool {
            wz.graft_masked_branches(self, m, ru);
            true
        }
        fn do_graft_child_maps<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W, m: ::pathmap::utils::ByteMask, ru: bool) -> bool {
            let maps: Vec<::pathmap::PathMap<u64>> = m
                .iter()
                .map(|b| {
                    let mut c = self.fork_read_zipper();
                    c.descend_to_byte(b);
                    c.make_map()
                })
                .collect();
            wz.graft_child_maps(m, maps, ru);
            true
        }
        fn do_meet_2<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W, path: &[u8]) -> Option<::pathmap::ring::AlgebraicStatus> {
            let mut b = self.fork_read_zipper();
            b.descend_to(path);
            Some(wz.meet_2(self, &b))
        }
        fn do_graft_src_at<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W, p: &[u8]) -> bool {
            wz.graft_src_at(self, p);
            true
        }
        fn do_join_into<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W) -> Option<::pathmap::ring::AlgebraicStatus> {
            Some(wz.join_into(self))
        }
        fn do_join_map_into<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W) -> Option<::pathmap::ring::AlgebraicStatus> {
            Some(wz.join_map_into(self.make_map()))
        }
        fn do_meet_into<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W, prune: bool) -> Option<::pathmap::ring::AlgebraicStatus> {
            Some(wz.meet_into(self, prune))
        }
        fn do_subtract_into<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W, prune: bool) -> Option<::pathmap::ring::AlgebraicStatus> {
            Some(wz.subtract_into(self, prune))
        }
        fn do_restrict<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W) -> Option<::pathmap::ring::AlgebraicStatus> {
            Some(wz.restrict(self))
        }
        fn do_restricting<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W) -> Option<bool> {
            Some(wz.restricting(self))
        }
    };
}

/// The trailer every runner prints: both maps, both roots.  `map1` is dumped
/// from the map itself, not through the source (the source's own walk is the
/// `SRC` line `run_ops` prints).
pub fn trailer(out: &mut String, map0: &PathMap<u64>, map1: &PathMap<u64>, root0: &[u8], root1: &[u8]) {
    use core::fmt::Write as _;
    let _ = writeln!(out, "MAP0 {}", dump(&mut map0.read_zipper()));
    let _ = writeln!(out, "MAP1 {}", dump(&mut map1.read_zipper()));
    let _ = writeln!(out, "ROOT0 {}", hex_path(root0));
    let _ = writeln!(out, "ROOT1 {}", hex_path(root1));
}

use pathmap::PathMap;
