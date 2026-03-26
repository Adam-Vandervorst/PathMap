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
pub fn fuse_eval<V>(
    expr: &FuseExpr,
    inputs: &[&PathMap<V>],
) -> PathMap<V>
where
    V: Clone + Send + Sync + Unpin + Lattice + DistributiveLattice,
{
    let nodes: Vec<Option<&TrieNodeODRc<V, GlobalAlloc>>> = inputs
        .iter()
        .map(|m| m.root())
        .collect();

    let vals: Vec<Option<&V>> = inputs
        .iter()
        .map(|m| m.root_val())
        .collect();

    let (result_node, result_val) = eval_expr(expr, &nodes, &vals);
    PathMap::new_with_root_in(result_node, result_val, global_alloc())
}

// ── Core evaluator ───────────────────────────────────────────────────

/// Evaluate an expression tree. Leaf nodes borrow from inputs (cheap
/// Arc refcount bump only when entering a binary op that needs ownership).
fn eval_expr<V, A>(
    expr: &FuseExpr,
    nodes: &[Option<&TrieNodeODRc<V, A>>],
    vals: &[Option<&V>],
) -> (Option<TrieNodeODRc<V, A>>, Option<V>)
where
    V: Clone + Send + Sync + Unpin + Lattice + DistributiveLattice,
    A: Allocator,
{
    match expr {
        FuseExpr::Leaf(i) => {
            (nodes[*i].cloned(), vals[*i].cloned())
        }
        FuseExpr::Op(op, lhs, rhs) => {
            // Distributive law: And(Or(A,B), C) → Or(And(A,C), And(B,C))
            // This avoids building the large Or(A,B) intermediate only to
            // discard most of it in the And with C.
            if *op == FuseOp::And {
                if let FuseExpr::Op(FuseOp::Or, a, b) = lhs.as_ref() {
                    // And(Or(A,B), C) → Or(And(A,C), And(B,C))
                    let (r_node, r_val) = eval_expr(rhs, nodes, vals);
                    if r_node.is_none() && r_val.is_none() {
                        return (None, None);
                    }
                    let (a_node, a_val) = eval_expr(a, nodes, vals);
                    let ac_node = combine_node(FuseOp::And, a_node, r_node.clone());
                    let ac_val = combine_val(FuseOp::And, a_val, r_val.clone());

                    let (b_node, b_val) = eval_expr(b, nodes, vals);
                    let bc_node = combine_node(FuseOp::And, b_node, r_node);
                    let bc_val = combine_val(FuseOp::And, b_val, r_val);

                    return (combine_node(FuseOp::Or, ac_node, bc_node),
                            combine_val(FuseOp::Or, ac_val, bc_val));
                }
                if let FuseExpr::Op(FuseOp::Or, a, b) = rhs.as_ref() {
                    // And(C, Or(A,B)) → Or(And(C,A), And(C,B))
                    let (l_node, l_val) = eval_expr(lhs, nodes, vals);
                    if l_node.is_none() && l_val.is_none() {
                        return (None, None);
                    }
                    let (a_node, a_val) = eval_expr(a, nodes, vals);
                    let ca_node = combine_node(FuseOp::And, l_node.clone(), a_node);
                    let ca_val = combine_val(FuseOp::And, l_val.clone(), a_val);

                    let (b_node, b_val) = eval_expr(b, nodes, vals);
                    let cb_node = combine_node(FuseOp::And, l_node, b_node);
                    let cb_val = combine_val(FuseOp::And, l_val, b_val);

                    return (combine_node(FuseOp::Or, ca_node, cb_node),
                            combine_val(FuseOp::Or, ca_val, cb_val));
                }
            }

            // Short-circuit: for And/AndNot, if lhs produces nothing, skip rhs.
            match op {
                FuseOp::And => {
                    let (l_node, l_val) = eval_expr(lhs, nodes, vals);
                    if l_node.is_none() && l_val.is_none() {
                        return (None, None);
                    }
                    let (r_node, r_val) = eval_expr(rhs, nodes, vals);
                    if r_node.is_none() && r_val.is_none() {
                        return (None, None);
                    }
                    (combine_node(*op, l_node, r_node), combine_val(*op, l_val, r_val))
                }
                FuseOp::AndNot => {
                    let (l_node, l_val) = eval_expr(lhs, nodes, vals);
                    if l_node.is_none() && l_val.is_none() {
                        return (None, None);
                    }
                    let (r_node, r_val) = eval_expr(rhs, nodes, vals);
                    (combine_node(*op, l_node, r_node), combine_val(*op, l_val, r_val))
                }
                _ => {
                    let (l_node, l_val) = eval_expr(lhs, nodes, vals);
                    let (r_node, r_val) = eval_expr(rhs, nodes, vals);
                    (combine_node(*op, l_node, r_node), combine_val(*op, l_val, r_val))
                }
            }
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
            (Some(l), Some(r)) => {
                if l.ptr_eq(&r) { return Some(l); }
                resolve(l.as_tagged().pjoin_dyn(r.as_tagged()), l, r)
            }
        },
        FuseOp::And => match (l, r) {
            (None, _) | (_, None) => None,
            (Some(l), Some(r)) => {
                if l.ptr_eq(&r) { return Some(l); }
                resolve(l.as_tagged().pmeet_dyn(r.as_tagged()), l, r)
            }
        },
        FuseOp::Xor => match (l, r) {
            (None, x) | (x, None) => x,
            (Some(l), Some(r)) => {
                if l.ptr_eq(&r) { return None; }
                // Compute L\R, then join R\L into it in-place.
                let l_minus_r = resolve(l.as_tagged().psubtract_dyn(r.as_tagged()), l.clone(), r.clone());
                let r_minus_l = resolve(r.as_tagged().psubtract_dyn(l.as_tagged()), r, l);
                match (l_minus_r, r_minus_l) {
                    (None, x) | (x, None) => x,
                    (Some(mut a), Some(b)) => {
                        let (status, _) = a.make_mut().join_into_dyn(b);
                        match status {
                            AlgebraicStatus::None => None,
                            _ => Some(a),
                        }
                    }
                }
            }
        },
        FuseOp::AndNot => match (l, r) {
            (None, _) => None,
            (l, None) => l,
            (Some(l), Some(r)) => {
                if l.ptr_eq(&r) { return None; }
                resolve(l.as_tagged().psubtract_dyn(r.as_tagged()), l, r)
            }
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
