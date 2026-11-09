//! Util fuzzer, ops 60–79: `utils/ints.rs`: PathInteger.  Mirrors `UtilFuzz/Ints.lean`.
//!
//! Not written yet: every selector in the range is a `nop`.

use super::*;

pub fn step(_op: usize, _d: &mut Dec) -> StepResult {
    Some(("nop", "-".to_string()))
}
