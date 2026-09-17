//! Prints the differential trace for a fuzzer input, from the **Rust reference
//! model** — the port of `lean/PathMapModel/` in `differential/src/reference/`.
//!
//!     reference <input-file>          # or read the bytes from stdin
//!     reference --act <input-file>    # ACT-mode skips
//!
//! There are three front ends over one wire format:
//!
//! | binary | drives |
//! |---|---|
//! | `lean/.lake/build/bin/pathmap-oracle` | the Lean model (`lean/PathMapModel/Fuzz.lean`) |
//! | `pathmap_trace`                       | the real crate (`differential/src/harness.rs`) |
//! | this                                  | the Rust model (`differential/src/reference/`) |
//!
//! `lean/differential.py` diffs any two of them.  Model-against-model —
//! `differential.py --model` — is the acceptance test for the port: the two are
//! independent transcriptions of the same specification in different languages,
//! so a diff means one of them is wrong and nothing about the crate is in
//! question.  The `KNOWN` table of tolerated crate defects therefore does not
//! apply in that mode, and `differential.py` does not consult it.
//!
//! Once the two models are known to agree, `in_process` drops the pipes
//! entirely and compares the Rust model against the crate in memory.

use differential::reference::fuzz::run;
use differential::server::serve;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let act = args.iter().any(|a| a == "--act");
    // Resident mode: one process, many inputs over stdin.  See `serve`.
    if args.iter().any(|a| a == "--server") {
        serve(act, run);
        return;
    }
    let file = args.into_iter().find(|a| a != "--act" && a != "--server");
    let bytes: Vec<u8> = match file {
        Some(p) => std::fs::read(p).expect("cannot read input"),
        None => {
            use std::io::Read;
            let mut v = Vec::new();
            std::io::stdin().read_to_end(&mut v).unwrap();
            v
        }
    };
    print!("{}", run(&bytes, act));
}
