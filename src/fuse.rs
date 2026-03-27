//! Fused evaluation of set-operation DAGs over trie nodes.
//!
//! Two representations are provided:
//!
//! - **`FuseProgram`** (SSA-style): a flat array of operations that
//!   reference earlier results by index.  Supports diamonds / DAGs —
//!   a shared subexpression is computed once and reused.
//!
//! - **`FuseExpr`** (tree): convenience builder that compiles into a
//!   `FuseProgram`.  Each node owns its children, so sharing requires
//!   `Clone` which duplicates the subtree (no diamond support).

use crate::alloc::{Allocator, GlobalAlloc, global_alloc};
use crate::trie_node::TrieNodeODRc;
use crate::ring::*;
use crate::PathMap;

// ── Op kind ──────────────────────────────────────────────────────────

/// Binary set operation kind.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FuseOp {
    Or,
    And,
    Xor,
    AndNot,
}

// ── SSA-style program ────────────────────────────────────────────────

/// Reference to a value in the program: either an input PathMap or
/// the result of a prior step.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FuseRef {
    /// Index into the inputs array.
    Input(usize),
    /// Index into the steps array (must refer to an earlier step).
    Step(usize),
}

/// A single operation in the program.
#[derive(Clone, Copy, Debug)]
pub struct FuseStep {
    pub op: FuseOp,
    pub lhs: FuseRef,
    pub rhs: FuseRef,
}

/// A DAG of fused set operations in SSA form.
///
/// Steps are evaluated in order; each step may reference any input or
/// any earlier step's result.  Diamond shapes (multiple steps
/// referencing the same prior result) are supported — the result is
/// computed once and shared via `TrieNodeODRc` (Arc clone).
///
/// ```ignore
/// let mut p = FuseProgram::new();
/// let ab = p.push(FuseOp::Or, FuseRef::Input(0), FuseRef::Input(1));
/// let cd = p.push(FuseOp::And, FuseRef::Input(2), FuseRef::Input(3));
/// // Diamond: ab is used twice
/// let out1 = p.push(FuseOp::And, ab, cd);
/// let out2 = p.push(FuseOp::AndNot, ab, cd);
/// let results = p.eval(&[&a, &b, &c, &d], &[out1, out2]);
/// ```
pub struct FuseProgram {
    steps: Vec<FuseStep>,
}

impl FuseProgram {
    pub fn new() -> Self {
        FuseProgram { steps: Vec::new() }
    }

    /// Append a step and return a `FuseRef` to its result.
    pub fn push(&mut self, op: FuseOp, lhs: FuseRef, rhs: FuseRef) -> FuseRef {
        let idx = self.steps.len();
        self.steps.push(FuseStep { op, lhs, rhs });
        FuseRef::Step(idx)
    }

    /// Convenience: wrap an input index as a `FuseRef`.
    pub fn input(i: usize) -> FuseRef {
        FuseRef::Input(i)
    }

    /// Evaluate the program, returning one `PathMap` per output ref.
    pub fn eval<V>(
        &self,
        inputs: &[&PathMap<V>],
        outputs: &[FuseRef],
    ) -> Vec<PathMap<V>>
    where
        V: Clone + Send + Sync + Unpin + Lattice + DistributiveLattice,
    {
        let input_nodes: Vec<Option<&TrieNodeODRc<V, GlobalAlloc>>> =
            inputs.iter().map(|m| m.root()).collect();
        let input_vals: Vec<Option<&V>> =
            inputs.iter().map(|m| m.root_val()).collect();

        // Evaluate all steps in order, storing results.
        let mut results: Vec<(Option<TrieNodeODRc<V, GlobalAlloc>>, Option<V>)> =
            Vec::with_capacity(self.steps.len());

        for step in &self.steps {
            let (l_node, l_val) = get_ref(step.lhs, &input_nodes, &input_vals, &results);
            // Short-circuit And/AndNot when lhs is empty.
            if matches!(step.op, FuseOp::And | FuseOp::AndNot)
                && l_node.is_none() && l_val.is_none()
            {
                results.push((None, None));
                continue;
            }
            let (r_node, r_val) = get_ref(step.rhs, &input_nodes, &input_vals, &results);
            // Short-circuit And when rhs is empty.
            if step.op == FuseOp::And && r_node.is_none() && r_val.is_none() {
                results.push((None, None));
                continue;
            }
            let node = combine_node(step.op, l_node, r_node);
            let val = combine_val(step.op, l_val, r_val);
            results.push((node, val));
        }

        // Collect outputs.
        outputs.iter().map(|r| {
            let (node, val) = get_ref(*r, &input_nodes, &input_vals, &results);
            PathMap::new_with_root_in(node, val, global_alloc())
        }).collect()
    }
}

/// Resolve a `FuseRef` to a (node, val) pair, cloning from the source.
fn get_ref<V: Clone + Send + Sync + Unpin>(
    r: FuseRef,
    input_nodes: &[Option<&TrieNodeODRc<V, GlobalAlloc>>],
    input_vals: &[Option<&V>],
    results: &[(Option<TrieNodeODRc<V, GlobalAlloc>>, Option<V>)],
) -> (Option<TrieNodeODRc<V, GlobalAlloc>>, Option<V>) {
    match r {
        FuseRef::Input(i) => (input_nodes[i].cloned(), input_vals[i].cloned()),
        FuseRef::Step(i) => results[i].clone(),
    }
}

// ── Tree expression (convenience, compiles to FuseProgram) ───────────

/// Expression tree node — convenience API that compiles to `FuseProgram`.
///
/// Does **not** support diamonds: each node owns its children via `Box`.
/// For DAGs with shared subexpressions, use `FuseProgram` directly.
#[derive(Clone, Debug)]
pub enum FuseExpr {
    Leaf(usize),
    Op(FuseOp, Box<FuseExpr>, Box<FuseExpr>),
}

impl FuseExpr {
    pub fn leaf(i: usize) -> Self { FuseExpr::Leaf(i) }
    pub fn or(l: FuseExpr, r: FuseExpr) -> Self { FuseExpr::Op(FuseOp::Or, Box::new(l), Box::new(r)) }
    pub fn and(l: FuseExpr, r: FuseExpr) -> Self { FuseExpr::Op(FuseOp::And, Box::new(l), Box::new(r)) }
    pub fn xor(l: FuseExpr, r: FuseExpr) -> Self { FuseExpr::Op(FuseOp::Xor, Box::new(l), Box::new(r)) }
    pub fn and_not(l: FuseExpr, r: FuseExpr) -> Self { FuseExpr::Op(FuseOp::AndNot, Box::new(l), Box::new(r)) }

    /// Compile this tree into an SSA program and return the output ref.
    pub fn compile(&self) -> (FuseProgram, FuseRef) {
        let mut prog = FuseProgram::new();
        let out = compile_expr(self, &mut prog);
        (prog, out)
    }
}

fn compile_expr(expr: &FuseExpr, prog: &mut FuseProgram) -> FuseRef {
    match expr {
        FuseExpr::Leaf(i) => FuseRef::Input(*i),
        FuseExpr::Op(op, lhs, rhs) => {
            let l = compile_expr(lhs, prog);
            let r = compile_expr(rhs, prog);
            prog.push(*op, l, r)
        }
    }
}

/// Evaluate a `FuseExpr` tree (convenience wrapper around `FuseProgram`).
pub fn fuse_eval<V>(
    expr: &FuseExpr,
    inputs: &[&PathMap<V>],
) -> PathMap<V>
where
    V: Clone + Send + Sync + Unpin + Lattice + DistributiveLattice,
{
    let (prog, out) = expr.compile();
    prog.eval(inputs, &[out]).into_iter().next().unwrap()
}

// ── Node-level operations ────────────────────────────────────────────

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
