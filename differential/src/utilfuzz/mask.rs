//! Util fuzzer, ops 0–29: ByteMask, BitMask for [u64; 4], other utils/mod.rs items.  Mirrors `UtilFuzz/Mask.lean`.
//!
//! Not written yet: every selector in the range is a `nop`.

use super::*;

pub fn step(_op: usize, _d: &mut Dec) -> StepResult {
    Some(("nop", "-".to_string()))
}
