//! Value-level reference semantics, as a fourth opinion.
//!
//! The routes in `routes.rs` all go through `pathmap`, so a defect common to
//! the whole algebra layer would make them agree with each other and still be
//! wrong.  This module computes the same expression over a plain
//! `BTreeMap<Vec<u8>, u64>` with no trie involved, which gives the comparison
//! something to anchor against.
//!
//! It deliberately models only *which path carries which value* and abstains
//! on structure: a flat map cannot represent a dangling path, and whether a
//! dangling path survives an operation is unsettled in the crate (see
//! `../../SPEC_WARTS.md`).  `shape.rs` explains the split.
//!
//! The semantics below are the ones `u64`'s lattice instances in
//! `pathmap::ring` actually define, not the ones set notation would suggest:
//!
//! * `pjoin` is left-biased, so a join keeps the left value where both sides
//!   have one.  Join is therefore **not** commutative in its values, only in
//!   its path set.
//! * `pmeet` returns `Identity(SELF_IDENT)` unconditionally, so a meet also
//!   keeps the left value -- even where the two values differ.
//! * `psubtract` is `None` when the values are equal and the left value
//!   otherwise, so subtracting a path whose value differs is a no-op.
//! * symmetric difference cancels *any* pair of values at a coincident path.
//!   That follows from the two above rather than from parity of presence: with
//!   `pjoin` and `pmeet` both `Identity`, `SymDiff::combine_impl` reaches
//!   `join == meet` for distinct values and `subtract_impl(a, b)` with `a ==
//!   b` for equal ones, and both yield nothing.

use super::expr::{Expr, Op};
use super::shape::Values;

pub fn eval(e: &Expr, operands: &[Values]) -> Values {
    match e {
        Expr::Var(i) => operands[*i].clone(),
        Expr::Bin(op, l, r) => {
            let a = eval(l, operands);
            let b = eval(r, operands);
            apply(*op, &a, &b)
        }
    }
}

pub fn apply(op: Op, a: &Values, b: &Values) -> Values {
    match op {
        Op::Join => join(a, b),
        Op::Meet => meet(a, b),
        Op::Subtract => subtract(a, b),
        Op::SymDiff => sym_diff(a, b),
        Op::Restrict => restrict(a, b),
    }
}

/// Union of paths; the left value wins where both sides have one.
pub fn join(a: &Values, b: &Values) -> Values {
    let mut out = b.clone();
    for (k, v) in a {
        out.insert(k.clone(), *v);
    }
    out
}

/// Paths present in both; the left value, even when the two differ.
pub fn meet(a: &Values, b: &Values) -> Values {
    a.iter()
        .filter(|(k, _)| b.contains_key(*k))
        .map(|(k, v)| (k.clone(), *v))
        .collect()
}

/// Left paths, dropping only those the right side carries the *same* value at.
pub fn subtract(a: &Values, b: &Values) -> Values {
    a.iter()
        .filter(|(k, v)| b.get(*k) != Some(*v))
        .map(|(k, v)| (k.clone(), *v))
        .collect()
}

/// Paths present in exactly one side.  Coincident paths cancel whatever their
/// values; see the module comment.
pub fn sym_diff(a: &Values, b: &Values) -> Values {
    let mut out = Values::new();
    for (k, v) in a {
        if !b.contains_key(k) {
            out.insert(k.clone(), *v);
        }
    }
    for (k, v) in b {
        if !a.contains_key(k) {
            out.insert(k.clone(), *v);
        }
    }
    out
}

/// Left paths that some path-to-a-value in the right side is a prefix of.
///
/// The prefix is inclusive at both ends: the empty path counts, so a root value
/// in `b` admits all of `a`, and `k` counts as a prefix of itself.  Both follow
/// from the note on `PathMap::restrict`.
pub fn restrict(a: &Values, b: &Values) -> Values {
    a.iter()
        .filter(|(k, _)| (0..=k.len()).any(|n| b.contains_key(&k[..n])))
        .map(|(k, v)| (k.clone(), *v))
        .collect()
}
