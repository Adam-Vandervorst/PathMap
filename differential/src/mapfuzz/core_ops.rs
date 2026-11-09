//! Map fuzzer, ops 0–19: the `PathMap` surface.  Mirrors `MapFuzz/Core.lean`.

use super::*;

pub fn step(op: usize, d: &mut Dec, st: &mut MapState) -> StepResult {
    Some(match op {
        0 => {
            let (i, p) = (map_ix(d)?, d.path(6)?);
            ("get", show_val(st.maps[i].get(&p)))
        }
        1 => {
            let (i, p, v) = (map_ix(d)?, d.path(6)?, val(d)?);
            ("insert", show_val(st.maps[i].set_val_at(&p, v).as_ref()))
        }
        2 => {
            let (i, p) = (map_ix(d)?, d.path(6)?);
            ("remove", show_val(st.maps[i].remove(&p).as_ref()))
        }
        3 => {
            let (i, p) = (map_ix(d)?, d.path(6)?);
            ("contains", show_bool(st.maps[i].contains(&p)).to_string())
        }
        _ => ("nop", "-".to_string()),
    })
}
