//! Map fuzzer, ops 30–39: serialization round trips.  Mirrors `MapFuzz/Serial.lean`.
//!
//! Not written yet: every selector in the range is a `nop`.

use super::*;

pub fn step(_op: usize, _d: &mut Dec, _st: &mut MapState) -> StepResult {
    Some(("nop", "-".to_string()))
}
