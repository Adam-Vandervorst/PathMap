//! Prints the dangling-path-free differential trace for a fuzzer input, from
//! the real crate.
//!
//!     pruned_trace <input-file>      # or read the bytes from stdin
//!
//! `lean/.lake/build/bin/pruned-oracle` prints the same trace from
//! `PrunedModel`; `lean/pruned_differential.py` runs both and diffs them.
//!
//! `--check` needs no oracle: it asserts the zipper invariants after every
//! operation and, at the end of the run, that the write target contains no
//! dangling path -- which is the whole claim this harness's operation subset
//! makes.  See `differential::pruned`.

use differential::pruned::run;
use differential::serve;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let check = args.iter().any(|a| a == "--check");
    // Resident mode: one process, many inputs over stdin.  See `serve`.
    if args.iter().any(|a| a == "--server") {
        serve(check, run);
        return;
    }
    let file = args.iter().find(|a| !a.starts_with("--")).cloned();
    let bytes: Vec<u8> = match file {
        Some(p) => std::fs::read(p).expect("cannot read input"),
        None => {
            use std::io::Read;
            let mut v = Vec::new();
            std::io::stdin().read_to_end(&mut v).unwrap();
            v
        }
    };
    print!("{}", run(&bytes, check));
}
