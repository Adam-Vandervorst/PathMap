//! Differential trace producer with an `ArenaCompactTree` as the read source.
//!
//!     act_trace <input-file>          # or read the bytes from stdin
//!     act_trace --check <input-file>  # also assert the structural invariants
//!
//! Same wire format, same operation table and same trace format as
//! `pathmap_trace`; the only difference is that the read side is an ACT built
//! from map1 rather than the `PathMap` itself.  The Lean model produces the
//! matching trace with `pathmap-oracle --act`, which skips the operations ACT
//! cannot serve.
//!
//! What this exercises:
//!
//!   * `ArenaCompactTree::from_zipper` -- the final `MAP1` line is dumped from
//!     the ACT, so the round trip through the arena format is compared against
//!     the model's view of the source trie, dangling paths and root value
//!     included.
//!   * every read, movement and iteration operation on `ACTZipper`, against the
//!     same specification the `PathMap` read zipper is held to.
//!
//! What it cannot exercise: ACT is read-only and, more restrictively, is not a
//! `ZipperInfallibleSubtries`, so it cannot be the *source* of a graft or an
//! algebraic merge.  Those operations report `skip`.

use differential::*;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let check = args.iter().any(|a| a == "--check");
    let file = args.into_iter().find(|a| a != "--check");
    let bytes: Vec<u8> = match file {
        Some(p) => std::fs::read(p).expect("cannot read input"),
        None => {
            use std::io::Read;
            let mut v = Vec::new();
            std::io::stdin().read_to_end(&mut v).unwrap();
            v
        }
    };
    print!("{}", run_act(&bytes, check));
}
