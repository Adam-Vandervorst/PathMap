//! Fused evaluation of set-operation DAGs over trie nodes.
//!
//! An expression over several input tries, evaluated once.  Write it as a
//! `FuseExpr` tree and `compile` it, or build a `FuseProgram` directly in SSA
//! form, which is what lets subexpressions be shared and several outputs be
//! produced from one program.
//!
//! # What this evaluator does and does not do
//!
//! It is a **bottom-up whole-node evaluator**.  Each step combines its two
//! operands with the existing node-level primitives -- `pjoin_dyn`,
//! `pmeet_dyn`, `psubtract_dyn` -- short-circuiting when an operand is empty
//! and taking the `ptr_eq` fast path when both sides are the same allocation.
//! It avoids the `PathMap` wrapper overhead, but it still materialises an
//! intermediate node per subexpression.
//!
//! It is **not** the fused byte-by-byte walk the name suggests, and an earlier
//! revision that tried to be was reverted.  Computing an effective child mask
//! per byte and recursing cannot be done through the `TrieNode` trait:
//! `LineListNode` stores compressed multi-byte keys, so
//! `node_get_child(&[byte])` returns `None` for a byte that
//! `node_branches_mask` reports as present.  Doing it properly means writing
//! the walk inside `ByteNode`'s mask-and-values loop with a separate path for
//! the compressed-key case.
//!
//! # Root values are combined separately
//!
//! Note that `combine_val` decides the root value by presence alone, while
//! the node levels below it go through the lattice operations.  The two do not
//! agree for every value type -- see `differential/ALGEBRAIC_FUZZING.md`, which
//! fuzzes this module against the rest of the algebra.

use crate::alloc::{GlobalAlloc, global_alloc};
use crate::trie_node::TrieNodeODRc;
use crate::ring::*;
use crate::PathMap;

// ── Op kind ──────────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FuseOp {
    Or,
    And,
    Xor,
    AndNot,
}

// ── SSA program ──────────────────────────────────────────────────────

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FuseRef {
    Input(usize),
    Step(usize),
}

#[derive(Clone, Copy, Debug)]
pub struct FuseStep {
    pub op: FuseOp,
    pub lhs: FuseRef,
    pub rhs: FuseRef,
}

pub struct FuseProgram {
    steps: Vec<FuseStep>,
}

impl FuseProgram {
    pub fn new() -> Self {
        FuseProgram { steps: Vec::new() }
    }

    pub fn push(&mut self, op: FuseOp, lhs: FuseRef, rhs: FuseRef) -> FuseRef {
        let idx = self.steps.len();
        self.steps.push(FuseStep { op, lhs, rhs });
        FuseRef::Step(idx)
    }

    pub fn input(i: usize) -> FuseRef {
        FuseRef::Input(i)
    }

    /// Evaluate the program.
    ///
    /// At each trie node level, the expression's effective child mask
    /// is computed.  Children outside the mask are skipped entirely —
    /// no merge work or allocation occurs for them.
    pub fn eval<V>(
        &self,
        inputs: &[&PathMap<V>],
        outputs: &[FuseRef],
    ) -> Vec<PathMap<V>>
    where
        V: Clone + Send + Sync + Unpin + Lattice + DistributiveLattice,
    {
        let input_nodes: Vec<Option<TrieNodeODRc<V, GlobalAlloc>>> =
            inputs.iter().map(|m| m.root().cloned()).collect();
        let input_vals: Vec<Option<V>> =
            inputs.iter().map(|m| m.root_val().cloned()).collect();

        // Evaluate all steps bottom-up, storing intermediate nodes.
        // Mask-based skipping: before computing a step, check if either
        // operand is fully empty (node + val both None) and short-circuit.
        let mut step_results: Vec<(Option<TrieNodeODRc<V, GlobalAlloc>>, Option<V>)> =
            Vec::with_capacity(self.steps.len());

        for step in &self.steps {
            let (l_node, l_val) = get_ref(step.lhs, &input_nodes, &input_vals, &step_results);
            if matches!(step.op, FuseOp::And | FuseOp::AndNot)
                && l_node.is_none() && l_val.is_none()
            {
                step_results.push((None, None));
                continue;
            }
            let (r_node, r_val) = get_ref(step.rhs, &input_nodes, &input_vals, &step_results);
            if step.op == FuseOp::And && r_node.is_none() && r_val.is_none() {
                step_results.push((None, None));
                continue;
            }
            let node = combine_node(step.op, l_node, r_node);
            let val = combine_val(step.op, l_val, r_val);
            step_results.push((node, val));
        }

        outputs.iter().map(|r| {
            let (node, val) = get_ref(*r, &input_nodes, &input_vals, &step_results);
            PathMap::new_with_root_in(node, val, global_alloc())
        }).collect()
    }

    /// Apply distributive law then evaluate.
    pub fn eval_distributed<V>(
        &self,
        inputs: &[&PathMap<V>],
        outputs: &[FuseRef],
    ) -> Vec<PathMap<V>>
    where
        V: Clone + Send + Sync + Unpin + Lattice + DistributiveLattice,
    {
        let (new_prog, map) = self.distribute_and_over_or();
        let new_outputs: Vec<FuseRef> = outputs.iter().map(|r| match r {
            FuseRef::Input(i) => FuseRef::Input(*i),
            FuseRef::Step(i) => map[*i],
        }).collect();
        new_prog.eval(inputs, &new_outputs)
    }

    pub fn distribute_and_over_or(&self) -> (FuseProgram, Vec<FuseRef>) {
        let mut new_prog = FuseProgram::new();
        let mut map: Vec<FuseRef> = Vec::with_capacity(self.steps.len());
        let remap = |r: FuseRef, map: &[FuseRef]| match r {
            FuseRef::Input(i) => FuseRef::Input(i),
            FuseRef::Step(i) => map[i],
        };
        for step in &self.steps {
            let lhs = remap(step.lhs, &map);
            let rhs = remap(step.rhs, &map);
            if step.op == FuseOp::And {
                if let FuseRef::Step(li) = step.lhs {
                    if self.steps[li].op == FuseOp::Or {
                        let a = remap(self.steps[li].lhs, &map);
                        let b = remap(self.steps[li].rhs, &map);
                        let ac = new_prog.push(FuseOp::And, a, rhs);
                        let bc = new_prog.push(FuseOp::And, b, rhs);
                        map.push(new_prog.push(FuseOp::Or, ac, bc));
                        continue;
                    }
                }
                if let FuseRef::Step(ri) = step.rhs {
                    if self.steps[ri].op == FuseOp::Or {
                        let a = remap(self.steps[ri].lhs, &map);
                        let b = remap(self.steps[ri].rhs, &map);
                        let ca = new_prog.push(FuseOp::And, lhs, a);
                        let cb = new_prog.push(FuseOp::And, lhs, b);
                        map.push(new_prog.push(FuseOp::Or, ca, cb));
                        continue;
                    }
                }
            }
            map.push(new_prog.push(step.op, lhs, rhs));
        }
        (new_prog, map)
    }
}

// ── Helpers ──────────────────────────────────────────────────────────

fn get_ref<V: Clone + Send + Sync + Unpin>(
    r: FuseRef,
    input_nodes: &[Option<TrieNodeODRc<V, GlobalAlloc>>],
    input_vals: &[Option<V>],
    step_results: &[(Option<TrieNodeODRc<V, GlobalAlloc>>, Option<V>)],
) -> (Option<TrieNodeODRc<V, GlobalAlloc>>, Option<V>) {
    match r {
        FuseRef::Input(i) => (input_nodes[i].clone(), input_vals[i].clone()),
        FuseRef::Step(i) => step_results[i].clone(),
    }
}

/// Combine the root values of two operands.
///
/// Delegates to the same lattice operations the node levels use, through the
/// `Option<V>` impls in [`crate::ring`], and mirrors `combine_node` arm for
/// arm.
///
/// This used to decide the root value by presence alone: `And` kept the
/// *right* value, and `AndNot` dropped the left value whenever the right side
/// had any value at all.  That is correct for a set, but it disagreed with the
/// `pmeet_dyn`/`psubtract_dyn` calls one level down for every value type whose
/// operations are not presence-based -- so a root value and a value one byte
/// deeper were combined by different rules.  `u64` is such a type: `pmeet` is
/// `Identity(SELF_IDENT)`, so the *left* value must win, and `psubtract` is
/// `None` only for *equal* values, so subtracting a differing value is a
/// no-op.  The algebraic fuzzer in `differential/` found it.
fn combine_val<V>(op: FuseOp, lv: Option<V>, rv: Option<V>) -> Option<V>
where
    V: Clone + Lattice + DistributiveLattice,
{
    match op {
        FuseOp::Or => resolve_val(lv.pjoin(&rv), lv, rv),
        FuseOp::And => resolve_val(lv.pmeet(&rv), lv, rv),
        FuseOp::AndNot => resolve_val(lv.psubtract(&rv), lv, rv),
        // `(l - r) join (r - l)`, the same construction `combine_node` uses, so
        // the two levels stay in step.  Note this is not the same convention as
        // `zipper_sym_diff`'s value policy, which cancels a coincident path
        // whatever the two values are; here distinct values survive.
        FuseOp::Xor => {
            let a = resolve_val(lv.psubtract(&rv), lv.clone(), rv.clone());
            let b = resolve_val(rv.psubtract(&lv), rv, lv);
            resolve_val(a.pjoin(&b), a, b)
        }
    }
}

/// [`resolve`] for values rather than nodes.
#[inline]
fn resolve_val<V: Clone>(
    result: AlgebraicResult<Option<V>>,
    l: Option<V>,
    r: Option<V>,
) -> Option<V> {
    match result {
        AlgebraicResult::Element(v) => v,
        AlgebraicResult::Identity(mask) => {
            if mask & SELF_IDENT > 0 { l } else { r }
        }
        AlgebraicResult::None => None,
    }
}

fn combine_node<V, A>(
    op: FuseOp,
    l: Option<TrieNodeODRc<V, A>>,
    r: Option<TrieNodeODRc<V, A>>,
) -> Option<TrieNodeODRc<V, A>>
where
    V: Clone + Send + Sync + Unpin + Lattice + DistributiveLattice,
    A: crate::alloc::Allocator,
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
                        match status { AlgebraicStatus::None => None, _ => Some(a) }
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
where V: Clone + Send + Sync, A: crate::alloc::Allocator,
{
    match result {
        AlgebraicResult::Element(n) => Some(n),
        AlgebraicResult::Identity(mask) => {
            if mask & SELF_IDENT > 0 { Some(l) } else { Some(r) }
        }
        AlgebraicResult::None => None,
    }
}

// ── Tree expression (convenience) ────────────────────────────────────

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

#[cfg(test)]
mod tests {
    use super::*;
    // `ZipperPath` is named explicitly: it was reachable without naming it on
    // the branch this module came from, and is not any more.
    use crate::zipper::{ZipperIteration, ZipperPath};

    fn keys_of(m: &PathMap<i32>) -> Vec<i32> {
        let mut rz = m.read_zipper();
        let mut out = Vec::new();
        while rz.to_next_val() {
            let p = rz.path();
            if p.len() == 4 {
                out.push(i32::from_be_bytes([p[0], p[1], p[2], p[3]]));
            }
        }
        out
    }

    fn make(keys: &[i32]) -> PathMap<i32> {
        let mut m = PathMap::new();
        for &k in keys {
            m.set_val_at(k.to_be_bytes(), k);
        }
        m
    }

    impl Lattice for i32 {
        fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
            if self == other { AlgebraicResult::Identity(SELF_IDENT) }
            else { AlgebraicResult::Element(*self.max(other)) }
        }
        fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> {
            if self == other { AlgebraicResult::Identity(SELF_IDENT) }
            else { AlgebraicResult::Element(*self.min(other)) }
        }
    }

    impl DistributiveLattice for i32 {
        fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> {
            if self <= other { AlgebraicResult::None }
            else { AlgebraicResult::Identity(SELF_IDENT) }
        }
    }

    #[test]
    fn leaf_passthrough() {
        let a = make(&[10, 20, 30]);
        let result = fuse_eval(&FuseExpr::leaf(0), &[&a]);
        assert_eq!(keys_of(&result), vec![10, 20, 30]);
    }

    #[test]
    fn or_basic() {
        let a = make(&[1, 3, 5]);
        let b = make(&[2, 4, 6]);
        let result = fuse_eval(&FuseExpr::or(FuseExpr::leaf(0), FuseExpr::leaf(1)), &[&a, &b]);
        assert_eq!(keys_of(&result), vec![1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn and_basic() {
        let a = make(&[1, 2, 3, 5]);
        let b = make(&[2, 4, 5]);
        let result = fuse_eval(&FuseExpr::and(FuseExpr::leaf(0), FuseExpr::leaf(1)), &[&a, &b]);
        assert_eq!(keys_of(&result), vec![2, 5]);
    }

    #[test]
    fn and_not_basic() {
        let a = make(&[1, 2, 3, 5]);
        let b = make(&[2, 3, 6]);
        let result = fuse_eval(&FuseExpr::and_not(FuseExpr::leaf(0), FuseExpr::leaf(1)), &[&a, &b]);
        assert_eq!(keys_of(&result), vec![1, 5]);
    }

    #[test]
    fn or_then_and() {
        let a = make(&[1, 3, 5]);
        let b = make(&[2, 4, 6]);
        let c = make(&[2, 3, 7]);
        let expr = FuseExpr::and(
            FuseExpr::or(FuseExpr::leaf(0), FuseExpr::leaf(1)),
            FuseExpr::leaf(2),
        );
        let result = fuse_eval(&expr, &[&a, &b, &c]);
        assert_eq!(keys_of(&result), vec![2, 3]);
    }
}
