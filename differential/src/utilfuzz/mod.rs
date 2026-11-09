//! The value-level fuzzer (`--source util`).
//!
//! A third differential program, for the public parts of `pathmap` that are
//! neither a zipper nor a `PathMap`: `ByteMask` and the `BitMask` impls, the
//! `Lattice` / `DistributiveLattice` / `Quantale` impls and `AlgebraicResult`
//! in `ring.rs`, `PathInteger` in `utils/ints.rs`, the path sorters in
//! `paths_serialization`, and whatever else in that category has a checkable
//! answer.  Ops are stateless: each decodes its operands, calls the crate, and
//! renders the full answer.  The Lean side is `lean/PathMapModel/UtilFuzz*.lean`,
//! which documents the format and the selector ranges; the two must decode the
//! same bytes the same way.

use core::fmt::Write as _;

use crate::harness::*;

pub mod mask;
pub mod lattice;
pub mod ints;
pub mod misc;

/// Selector count for new util-fuzzer inputs.  `utilNops` in
/// `lean/PathMapModel/UtilFuzz/Base.lean`, `UTIL_NOPS` in `lean/input_format.py`.
pub const UTIL_NOPS: usize = 100;

/// One step's name and rendered result; `None` when the input ran out.
pub type StepResult = Option<(&'static str, String)>;

/// Read a `ByteMask` operand: `n := u8 % 12`, then `n` member bytes (the full
/// 0..=255 range, not the path alphabet).  `maskBytes` in `UtilFuzz/Base.lean`.
pub fn mask_bytes(d: &mut Dec) -> Option<Vec<u8>> {
    let n = d.modn(12)?;
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(d.u8()?);
    }
    Some(v)
}

pub fn run(bytes: &[u8], _check: bool) -> String {
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
    let mut out = String::new();
    for step in 0..MAX_STEPS {
        let Some(op) = d.op() else { break };
        let r = match op {
            0..=29 => mask::step(op, &mut d),
            30..=59 => lattice::step(op, &mut d),
            60..=79 => ints::step(op, &mut d),
            80..=99 => misc::step(op, &mut d),
            _ => Some(("nop", "-".to_string())),
        };
        let Some((name, ret)) = r else { break };
        let _ = writeln!(out, "{step} {name} ret={ret}");
    }
    out
}
