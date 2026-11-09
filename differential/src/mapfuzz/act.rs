//! Map fuzzer, ops 40–49: ArenaCompactTree files, merge, stream.  Mirrors `MapFuzz/Act.lean`.
//!
//! Not written yet: every selector in the range is a `nop`.

use super::*;

pub fn step(_op: usize, _d: &mut Dec, _st: &mut MapState) -> StepResult {
    Some(("nop", "-".to_string()))
}
