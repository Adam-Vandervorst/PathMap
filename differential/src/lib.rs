//! The Rust side of the differential fuzzing harness for `pathmap`'s zipper
//! API.  The Lean model in `../lean` is the oracle; `lean/differential.py`
//! drives the binaries in `src/bin/` against it.  See `lean/README.md`.
//!
//! * [`harness`] decodes a fuzzer input into a program over two maps and two
//!   zippers, runs it, and renders the trace.  Its wire format and operation
//!   table are a contract shared with `lean/PathMapModel/Fuzz.lean`.
//! * [`server`] is the resident-process protocol the driver speaks.
//! * [`repro`] turns an input back into standalone `pathmap` calls.
//! * [`act`] is the `ArenaCompactTree` read source behind `act_trace`.
//! * [`pruned`] is a second, smaller harness: the subset of the API that
//!   cannot leave a dangling path, checked against `lean/PrunedModel` and
//!   driven by `lean/pruned_differential.py`.  See its module docs for why it
//!   is not `harness` with a flag.

pub mod act;
pub mod harness;
pub mod pruned;
pub mod repro;
pub mod server;

pub use act::*;
pub use harness::*;
pub use repro::*;
pub use server::*;
