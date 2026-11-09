//! Map fuzzer, ops 50–59: catamorphisms, anamorphisms.  Mirrors `MapFuzz/Morph.lean`.
//!
//! Not written yet: every selector in the range is a `nop`.

use super::*;

pub fn step(_op: usize, _d: &mut Dec, _st: &mut MapState) -> StepResult {
    Some(("nop", "-".to_string()))
}
