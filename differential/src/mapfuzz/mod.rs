//! The map-level fuzzer (`--source map`).
//!
//! A second differential program for everything that is not a zipper walking a
//! trie: the `PathMap` surface, whole-map lattice ops, serialization round
//! trips, `ArenaCompactTree` files and streams, catamorphisms/anamorphisms,
//! `ZipperHead` sessions and the experimental zippers.  The Lean side is
//! `lean/PathMapModel/MapFuzz*.lean`, which documents the wire and trace
//! formats and the op ranges.  Each group of ops owns a selector range and a
//! file here; the two sides must decode the same bytes the same way.

use core::fmt::Write as _;
use pathmap::PathMap;

use crate::harness::*;

pub mod core_ops;
pub mod lattice;
pub mod serial;
pub mod act;
pub mod morph;
pub mod head;
pub mod exp;

/// Selector count for new map-fuzzer inputs.  `mapNops` in
/// `lean/PathMapModel/MapFuzz/Base.lean`, `MAP_NOPS` in `lean/input_format.py`.
pub const MAP_NOPS: usize = 80;

/// The three maps a program works on.
pub struct MapState {
    pub maps: [PathMap<u64>; 3],
}

/// One step's name and rendered return value; `None` when the input ran out.
pub type StepResult = Option<(&'static str, String)>;

/// Read a map operand (`u8 % 3`).
pub fn map_ix(d: &mut Dec) -> Option<usize> {
    d.modn(3)
}

/// Read a value (`u8` as `u64`).
pub fn val(d: &mut Dec) -> Option<u64> {
    Some(d.u8()? as u64)
}

/// Render `(path, value)` pairs as `path:val,...`, `_` when empty.
pub fn show_pairs<'a, I: IntoIterator<Item = (Vec<u8>, u64)>>(xs: I) -> String {
    let v: Vec<String> = xs.into_iter().map(|(p, v)| format!("{}:{}", hex_path(&p), v)).collect();
    if v.is_empty() { "_".to_string() } else { v.join(",") }
}

/// Render a list of paths, `-` when empty.
pub fn show_paths<I: IntoIterator<Item = Vec<u8>>>(xs: I) -> String {
    let v: Vec<String> = xs.into_iter().map(|p| hex_path(&p)).collect();
    if v.is_empty() { "-".to_string() } else { v.join(",") }
}

fn seed(d: &mut Dec) -> Option<PathMap<u64>> {
    let mut m = PathMap::<u64>::new();
    let n = d.modn(8)?;
    for _ in 0..n {
        let p = d.path(6)?;
        let v = d.u8()? as u64;
        m.set_val_at(&p, v);
    }
    Some(m)
}

pub fn run(bytes: &[u8], _check: bool) -> String {
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
    let header = (|| Some([seed(&mut d)?, seed(&mut d)?, seed(&mut d)?]))();
    let Some(maps) = header else { return "EMPTY\n".to_string(); };
    let mut st = MapState { maps };
    let mut out = String::new();
    for step in 0..MAX_STEPS {
        let Some(op) = d.op() else { break };
        let r = match op {
            0..=19 => core_ops::step(op, &mut d, &mut st),
            20..=29 => lattice::step(op, &mut d, &mut st),
            30..=39 => serial::step(op, &mut d, &mut st),
            40..=49 => act::step(op, &mut d, &mut st),
            50..=59 => morph::step(op, &mut d, &mut st),
            60..=69 => head::step(op, &mut d, &mut st),
            70..=79 => exp::step(op, &mut d, &mut st),
            _ => Some(("nop", "-".to_string())),
        };
        let Some((name, ret)) = r else { break };
        let _ = writeln!(
            out,
            "{step} {name} ret={ret} n={},{},{}",
            st.maps[0].val_count(),
            st.maps[1].val_count(),
            st.maps[2].val_count()
        );
    }
    for (i, m) in st.maps.iter().enumerate() {
        let _ = writeln!(out, "M{i} {}", dump(&mut m.read_zipper()));
    }
    out
}
