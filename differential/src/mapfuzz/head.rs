//! Map fuzzer, ops 60–69: ZipperHead sessions.  Mirrors `MapFuzz/Head.lean`.
//!
//! Not written yet: every selector in the range is a `nop`.

use super::*;

pub fn step(_op: usize, _d: &mut Dec, _st: &mut MapState) -> StepResult {
    Some(("nop", "-".to_string()))
}
