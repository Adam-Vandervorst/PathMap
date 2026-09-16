//! The Rust side of the differential fuzzing harness for `pathmap`'s zipper
//! API.  The Lean model in `../lean` is the oracle; `lean/differential.py`
//! drives the binaries in `src/bin/` against it.  See `lean/README.md`.
//!
//! * [`harness`] decodes a fuzzer input into a program over two maps and two
//!   zippers, runs it, and renders the trace.  Its wire format and operation
//!   table are a contract shared with `lean/PathMapModel/Fuzz.lean`.
//! * [`server`] is the resident-process protocol the driver speaks.
//! * [`repro`] turns an input back into standalone `pathmap` calls.
//! * [`source`] generates random inputs by index, for the in-process front ends.
//! * [`crash`] is a second op table that only has to not crash; see `bin/crash_fuzz.rs`.
//! * [`act`] is the `ArenaCompactTree` read source behind `act_trace`.
//! * [`reference`] is a second executable model: a Rust transcription of the
//!   same Lean specification, sharing no code with `pathmap`.  It is what
//!   `bin/reference.rs` and `bin/in_process.rs` drive, and what
//!   `differential.py --model` validates against the Lean oracle.

pub mod act;
pub mod harness;
pub mod reference;
pub mod repro;
pub mod server;
pub mod source;
pub mod crash;

pub use act::*;
pub use harness::*;
pub use repro::*;
pub use server::*;

// `reference` is deliberately *not* glob re-exported: it defines its own
// `PathMap`, `run`, `hex_path` and `show_val`, which are the model's and must
// never be confused with the crate's.  Name it by path.
