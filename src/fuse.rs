//! Fused evaluation of expression trees over trie nodes.
//!
//! Evaluates compound set-operation expressions (e.g. `(A | B) & C`)
//! without materializing intermediate subexpressions as full `PathMap`s.
//! Each binary op delegates to the existing optimized node-level
//! operations (`pjoin_dyn`, `pmeet_dyn`, `psubtract_dyn`).

use crate::alloc::{Allocator, GlobalAlloc, global_alloc};
use crate::trie_node::TrieNodeODRc;
use crate::ring::*;
use crate::PathMap;

/// Binary set operation kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FuseOp {
    Or,
    And,
    Xor,
    AndNot,
}

/// Expression tree node describing a fused computation.
#[derive(Clone, Debug)]
pub enum FuseExpr {
    /// Leaf: index into the inputs array.
    Leaf(usize),
    /// Binary operation on two sub-expressions.
    Op(FuseOp, Box<FuseExpr>, Box<FuseExpr>),
}

impl FuseExpr {
    pub fn leaf(i: usize) -> Self { FuseExpr::Leaf(i) }
    pub fn or(l: FuseExpr, r: FuseExpr) -> Self { FuseExpr::Op(FuseOp::Or, Box::new(l), Box::new(r)) }
    pub fn and(l: FuseExpr, r: FuseExpr) -> Self { FuseExpr::Op(FuseOp::And, Box::new(l), Box::new(r)) }
    pub fn xor(l: FuseExpr, r: FuseExpr) -> Self { FuseExpr::Op(FuseOp::Xor, Box::new(l), Box::new(r)) }
    pub fn and_not(l: FuseExpr, r: FuseExpr) -> Self { FuseExpr::Op(FuseOp::AndNot, Box::new(l), Box::new(r)) }
}

/// Evaluate a fused expression tree over multiple input `PathMap`s.
///
/// The expression tree is evaluated bottom-up: leaf nodes reference
/// inputs by index, binary op nodes combine their children using the
/// optimized node-level operations.  No intermediate `PathMap` is
/// ever constructed — only `TrieNodeODRc` nodes are produced and
/// immediately consumed by the parent operation.
pub fn fuse_eval<V>(
    expr: &FuseExpr,
    inputs: &[&PathMap<V>],
) -> PathMap<V>
where
    V: Clone + Send + Sync + Unpin + Lattice + DistributiveLattice,
{
    let nodes: Vec<Option<TrieNodeODRc<V, GlobalAlloc>>> = inputs
        .iter()
        .map(|m| m.root().cloned())
        .collect();

    let vals: Vec<Option<V>> = inputs
        .iter()
        .map(|m| m.root_val().cloned())
        .collect();

    let (result_node, result_val) = eval_expr(expr, &nodes, &vals);
    PathMap::new_with_root_in(result_node, result_val, global_alloc())
}

// ── Core evaluator ───────────────────────────────────────────────────

fn eval_expr<V, A>(
    expr: &FuseExpr,
    nodes: &[Option<TrieNodeODRc<V, A>>],
    vals: &[Option<V>],
) -> (Option<TrieNodeODRc<V, A>>, Option<V>)
where
    V: Clone + Send + Sync + Unpin + Lattice + DistributiveLattice,
    A: Allocator,
{
    match expr {
        FuseExpr::Leaf(i) => (nodes[*i].clone(), vals[*i].clone()),
        FuseExpr::Op(op, lhs, rhs) => {
            let (l_node, l_val) = eval_expr(lhs, nodes, vals);
            let (r_node, r_val) = eval_expr(rhs, nodes, vals);
            let result_val = combine_val(*op, l_val, r_val);
            let result_node = combine_node(*op, l_node, r_node);
            (result_node, result_val)
        }
    }
}

fn combine_val<V: Clone>(op: FuseOp, lv: Option<V>, rv: Option<V>) -> Option<V> {
    match op {
        FuseOp::Or => lv.or(rv),
        FuseOp::And => match (lv, rv) {
            (Some(_), Some(v)) => Some(v),
            _ => None,
        },
        FuseOp::Xor => match (lv, rv) {
            (Some(v), None) | (None, Some(v)) => Some(v),
            _ => None,
        },
        FuseOp::AndNot => match (lv, rv) {
            (Some(v), None) => Some(v),
            _ => None,
        },
    }
}

fn combine_node<V, A>(
    op: FuseOp,
    l: Option<TrieNodeODRc<V, A>>,
    r: Option<TrieNodeODRc<V, A>>,
) -> Option<TrieNodeODRc<V, A>>
where
    V: Clone + Send + Sync + Unpin + Lattice + DistributiveLattice,
    A: Allocator,
{
    match op {
        FuseOp::Or => match (l, r) {
            (None, x) | (x, None) => x,
            (Some(l), Some(r)) => resolve(l.as_tagged().pjoin_dyn(r.as_tagged()), l, r),
        },
        FuseOp::And => match (l, r) {
            (None, _) | (_, None) => None,
            (Some(l), Some(r)) => resolve(l.as_tagged().pmeet_dyn(r.as_tagged()), l, r),
        },
        FuseOp::Xor => match (l, r) {
            (None, x) | (x, None) => x,
            (Some(l), Some(r)) => {
                let l_minus_r = resolve(l.as_tagged().psubtract_dyn(r.as_tagged()), l.clone(), r.clone());
                let r_minus_l = resolve(r.as_tagged().psubtract_dyn(l.as_tagged()), r, l);
                combine_node(FuseOp::Or, l_minus_r, r_minus_l)
            }
        },
        FuseOp::AndNot => match (l, r) {
            (None, _) => None,
            (l, None) => l,
            (Some(l), Some(r)) => resolve(l.as_tagged().psubtract_dyn(r.as_tagged()), l, r),
        },
    }
}

#[inline]
fn resolve<V, A>(
    result: AlgebraicResult<TrieNodeODRc<V, A>>,
    l: TrieNodeODRc<V, A>,
    r: TrieNodeODRc<V, A>,
) -> Option<TrieNodeODRc<V, A>>
where
    V: Clone + Send + Sync,
    A: Allocator,
{
    match result {
        AlgebraicResult::Element(n) => Some(n),
        AlgebraicResult::Identity(mask) => {
            if mask & SELF_IDENT > 0 { Some(l) } else { Some(r) }
        }
        AlgebraicResult::None => None,
    }
}
