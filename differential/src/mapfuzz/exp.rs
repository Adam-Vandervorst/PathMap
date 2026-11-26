//! Map fuzzer, ops 70–79: experimental zippers.  Mirrors `MapFuzz/Exp.lean`.
//!
//! Every selector in the range is a `nop`, on purpose.  The group was meant for
//! `FullZipper` and `NullZipper` in `src/experimental.rs`, but both are private
//! (`struct FullZipper` / `struct NullZipper`, no `pub`, no public constructor
//! or function returning one), so nothing outside the crate can build them.
//! They need a `pub` before they can be fuzzed (lean/findings/overlay-exp.md).

use super::*;

pub fn step(_op: usize, _d: &mut Dec, _st: &mut MapState) -> StepResult {
    Some(("nop", "-".to_string()))
}
