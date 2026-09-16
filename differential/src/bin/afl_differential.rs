//! Coverage-guided differential fuzzing: the Rust reference model against the
//! real crate, driven by AFL++ instead of by a random byte generator.
//!
//! ```text
//! cargo install cargo-afl                                  # once
//! cargo afl build --release -p differential --features afl
//! ./lean/afl-seed.sh out/afl-in                            # or any corpus
//! cargo afl fuzz -i out/afl-in -o out/afl-out \
//!     target/release/afl_differential
//! ```
//!
//! # Why a second front end at all
//!
//! `in_process` generates uniformly random bytes.  That is the right shape for
//! *measuring* — a rate over a known distribution, comparable with
//! `differential.py`'s — and the wrong shape for *finding*: the divergence
//! classes it turns up sit between 1 in 30,000 and 1 in 2,250,000 inputs, which
//! is what a blind sampler costs when the interesting programs are a thin set.
//! AFL keeps the inputs that reached new edges and mutates those, so a 40-op
//! program that got a write zipper into an unusual node representation becomes
//! the stem for the next thousand.  Same comparison, same two op tables, better
//! search.
//!
//! The wire format suits it: every operand is a byte, reduced mod a small number
//! at the point of use, so AFL's byte flips, arithmetic and splices all land on
//! op selectors and path bytes rather than being rejected by a parser. There is
//! no checksum, no length prefix over the whole input, and a truncated input is
//! a valid shorter program.
//!
//! # Why this is safe where `in_process` has to be careful
//!
//! `in_process` runs every input in one long-lived process, so a panic out of
//! the middle of a trie mutation cannot be caught and recovered from —
//! `pathmap` is not unwind-safe, and dropping half-updated refcounted nodes
//! while the stack unwinds corrupts the heap.  It therefore reports from a panic
//! *hook* and exits.
//!
//! AFL removes the problem rather than working around it.  Each input runs in a
//! child forked from the fork server, and `afl::fuzz!` installs a hook that
//! **aborts** rather than unwinds.  So a panicking input kills one child, is
//! written to `out/afl-out/default/crashes/`, and fuzzing continues from the
//! next one.  Corruption cannot outlive the input that caused it.  That is the
//! same property the subprocess design in `differential.py` bought, at a
//! fraction of the cost, and it is why this file does not reproduce
//! `in_process`'s panic-hook dance.
//!
//! A *divergence* is reported the same way a panic is — by panicking — so AFL
//! saves the input.  Replay one with the plain comparator, which prints the
//! differing line rather than a backtrace:
//!
//! ```text
//! target/release/in_process out/afl-out/default/crashes/id:* out/afl-out/default/hangs/id:*
//! ./lean/differential.py out/afl-out/default/crashes/* # KNOWN-table breakdown
//! ```
//!
//! # Look in `hangs/` as well as `crashes/`
//!
//! Which of the two a divergence lands in is a property of the *machine*, not of
//! the finding.  AFL decides "crashed" by reaping the child and reading its
//! signal, and when `/proc/sys/kernel/core_pattern` is a pipe — apport, systemd
//! -coredump, any distro default — the kernel hands the corpse to that helper
//! first, so AFL's wait races the helper and times out instead.  It says so at
//! startup ("To avoid having crashes misinterpreted as timeouts...") and
//! `AFL_I_DONT_CARE_ABOUT_MISSING_CRASHES=1` only silences the refusal to start.
//!
//! Measured here: a 180s run saved **0 crashes and 18 hangs**, and all 18 hangs
//! replay through `in_process` as real divergences.  So always sweep both
//! directories; a genuine timeout (an infinite loop in the crate, itself a
//! finding) is then the input in `hangs/` that `in_process` does *not* flag.
//!
//! `echo core | sudo tee /proc/sys/kernel/core_pattern` (or `cargo afl
//! system-config`) puts them back in `crashes/`, and needs root.
//!
//! # `crashes/` is not a list of new bugs
//!
//! It fills up with the *known* residual defects (`meet_keeps_dangling` and
//! friends) within the first minute, because to this target they are
//! indistinguishable from a new finding.  Triage is `differential.py`'s job: it
//! owns the one `KNOWN` table.

use differential::harness::run as crate_run;
use differential::reference::fuzz::run as model_run;

fn main() {
    afl::fuzz!(|data: &[u8]| {
        // An empty or near-empty input decodes to `EMPTY` on both sides; let AFL
        // keep it as a seed anyway, it costs one comparison.
        let model = model_run(data, false);
        let real = crate_run(data, false);
        if model == real {
            return;
        }
        // Panicking is the reporting channel: `afl::fuzz!`'s hook turns it into
        // an abort, which AFL records as a crash and saves the input for.
        let first = model
            .lines()
            .zip(real.lines())
            .enumerate()
            .find(|(_, (a, b))| a != b)
            .map(|(i, (a, b))| format!("line {i}\n  model: {a}\n  crate: {b}"))
            .unwrap_or_else(|| {
                format!(
                    "length {} (model) vs {} (crate) lines",
                    model.lines().count(),
                    real.lines().count()
                )
            });
        panic!("model/crate divergence:\n{first}");
    });
}
