//! Util fuzzer, ops 80–99: path sorting (sort_paths, sort_paths_par) and the rest.  Mirrors `UtilFuzz/Misc.lean`.
//!
//! Not written yet: every selector in the range is a `nop`.

use super::*;

pub fn step(_op: usize, _d: &mut Dec) -> StepResult {
    Some(("nop", "-".to_string()))
}
