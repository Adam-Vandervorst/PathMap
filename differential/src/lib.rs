//! The Rust side of the differential fuzzing harness for `pathmap`'s zipper
//! API.  The Lean model in `../lean` is the oracle; the binaries in `src/bin/`
//! print the trace it is compared against.  See `lean/README.md`.
//!
//! * [`harness`] decodes a fuzzer input into a program over two maps and two
//!   zippers, runs it, and renders the trace.  Its wire format and operation
//!   table are a contract shared with `lean/PathMapModel/Fuzz.lean`.
//! * [`act`] is the `ArenaCompactTree` read source behind `act_trace`.

pub mod act;
pub mod harness;

pub use act::*;
pub use harness::*;
