//! The `ArenaCompactTree` read source.
//!
//! `ReadSource` is this crate's trait, so its impl for `ACTZipper` has to live
//! here rather than in `bin/act_trace.rs`.

use core::fmt::Write as _;
use pathmap::arena_compact::{ACTZipper, ArenaCompactTree};
use pathmap::zipper::*;

use crate::harness::*;

impl<'t, S: AsRef<[u8]>> ReadSource for ACTZipper<'t, S, u64> {
    fn dump_fork(&self) -> String {
        dump(&mut self.fork_read_zipper())
    }
    /// ACT implements `ZipperSubtries` only for `Value = ()`, and
    /// `ZipperInfallibleSubtries` not at all, so a subtrie cannot be
    /// materialised from a `u64` ACT zipper.
    fn make_map_val_count(&self) -> Option<usize> {
        None
    }
    /// ACT does implement `ZipperReadOnlyValues`, so this probe applies.
    fn get_val_probe(&self, path: &[u8]) -> (Option<u64>, Option<u64>, bool) {
        let (g, ga) = (self.get_val().copied(), self.get_val_at(path).copied());
        let agree = g == self.val().copied() && ga == self.val_at(path).copied();
        (g, ga, agree)
    }
    /// ACT does *not* implement `ZipperReadOnlyIteration`, so this one is
    /// unavailable and the harness emits `skip`.
    fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)> {
        None
    }
    // The merge operations keep the trait defaults: `None` / `false`, rendered
    // as `skip`.  See the `ReadSource` docs for why ACT cannot serve them.
}

/// Decode and execute a fuzzer input with an ACT built from map1 as the read
/// source.  See `bin/act_trace.rs` for what this does and does not exercise.
pub fn run_act(bytes: &[u8], check: bool) -> String {
    let mut d = Dec { bytes, pos: 0 };
    let (mut map0, map1, root0, root1) = match decode_header(&mut d) {
        Some(x) => x,
        None => return "EMPTY\n".to_string(),
    };
    let act = ArenaCompactTree::from_zipper(map1.read_zipper(), |&v| v);
    let mut out = String::new();
    {
        let mut rz = act.read_zipper_at_path_u64(&root1);
        run_ops(&mut d, &mut out, &mut map0, &root0, &mut rz, &root1, check);
    }
    let _ = writeln!(out, "MAP0 {}", dump(&mut map0.read_zipper()));
    // Dumped from the ACT, not from map1, so `from_zipper` is under test too.
    let _ = writeln!(out, "MAP1 {}", dump(&mut act.read_zipper_u64()));
    let _ = writeln!(out, "ROOT0 {}", hex_path(&root0));
    let _ = writeln!(out, "ROOT1 {}", hex_path(&root1));
    out
}
