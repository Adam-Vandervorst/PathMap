//! The expression language the fuzzer evaluates.
//!
//! An expression is a tree over a handful of generated operand tries.  It is
//! deliberately small: the point is not to cover a rich language but to give
//! each expression as many *distinct implementation routes* as possible, and a
//! route only exists where the crate offers one.  So the operator set is
//! exactly the crate's algebra -- join, meet, subtract, symmetric difference,
//! restrict -- and the interesting structure is the shape of the tree, because
//! that is what decides which routes apply:
//!
//! * any tree at all can be walked bottom-up with two-operand calls, so the
//!   pairwise routes always apply;
//! * a chain of three of the same associative operator unlocks the `*3` forms;
//! * a chain of `n` unlocks the n-ary forms;
//! * a join of meets of operands is a DNF, which unlocks
//!   [`zipper_merge_dnf`](pathmap::experimental::zipper_algebra::zipper_merge_dnf).
//!
//! [`Expr::dnf`] and [`Expr::chain`] are the recognisers for the last three.

use core::fmt;

/// Maximum operand tries in a case.  Bounded because the n-ary and DNF routes
/// are const-generic over it and have to be dispatched by a `match` over
/// monomorphisations; see `routes::nary`.
pub const MAX_VARS: usize = 4;

/// Maximum DNF clauses dispatched to `zipper_merge_dnf`.
pub const MAX_CLAUSES: usize = 4;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Op {
    Join,
    Meet,
    Subtract,
    SymDiff,
    Restrict,
}

impl Op {
    pub const ALL: [Op; 5] = [Op::Join, Op::Meet, Op::Subtract, Op::SymDiff, Op::Restrict];

    pub fn sym(self) -> &'static str {
        match self {
            Op::Join => "|",
            Op::Meet => "&",
            Op::Subtract => "-",
            Op::SymDiff => "^",
            Op::Restrict => "/",
        }
    }

    /// Whether `(a op b) op c == a op (b op c)` holds, which is what makes a
    /// chain of this operator collapsible to one n-ary call.
    ///
    /// Subtract is listed as associative in the sense the n-ary routes mean it:
    /// `zipper_n_subtract` is documented as *left*-associative, so it matches a
    /// left-nested chain only.  [`Expr::chain`] enforces that nesting.
    pub fn chainable(self) -> bool {
        matches!(self, Op::Join | Op::Meet | Op::SymDiff | Op::Subtract)
    }

    /// Whether a chain of this operator may nest to the right as well as the
    /// left, and still mean what the n-ary call computes.
    ///
    /// Join and meet may: `pjoin` and `pmeet` on `u64` are left-biased, so both
    /// nestings select the leftmost present operand's value and agree with the
    /// left fold the n-ary routes perform.
    ///
    /// Subtract and symmetric difference may not.  Subtract obviously -- `a -
    /// (b - c)` is a different function.  Symmetric difference less obviously:
    /// the n-ary form folds values left, so for root values `a = 2`, `b = 1`,
    /// `a ^ (a ^ b)` is `a ^ nothing = 2` while the fold is `(2 ^ 2) ^ 1 = 1`.
    /// Both are defensible; they are not equal, so a right-nested symmetric
    /// difference is not a chain.  `laws.rs` states the associativity that does
    /// hold, which is on paths.
    pub fn right_nestable(self) -> bool {
        matches!(self, Op::Join | Op::Meet)
    }
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum Expr {
    Var(usize),
    Bin(Op, Box<Expr>, Box<Expr>),
}

impl Expr {
    pub fn bin(op: Op, l: Expr, r: Expr) -> Expr {
        Expr::Bin(op, Box::new(l), Box::new(r))
    }

    pub fn nodes(&self) -> usize {
        match self {
            Expr::Var(_) => 1,
            Expr::Bin(_, l, r) => 1 + l.nodes() + r.nodes(),
        }
    }

    /// Operand indices the expression mentions, ascending.
    pub fn vars(&self) -> Vec<usize> {
        let mut v = Vec::new();
        self.collect_vars(&mut v);
        v.sort();
        v.dedup();
        v
    }

    fn collect_vars(&self, out: &mut Vec<usize>) {
        match self {
            Expr::Var(i) => out.push(*i),
            Expr::Bin(_, l, r) => {
                l.collect_vars(out);
                r.collect_vars(out);
            }
        }
    }

    /// If the whole expression is a chain of one chainable operator over bare
    /// operands, return that operator and the operands in evaluation order.
    ///
    /// Only bare operands qualify, not arbitrary subexpressions: the n-ary
    /// routes take read zippers, and a subexpression would have to be
    /// materialised into a temporary trie first, at which point the route is no
    /// longer testing the n-ary call against the same inputs the pairwise route
    /// saw.  Keeping it to operands keeps the comparison exact.
    pub fn chain(&self) -> Option<(Op, Vec<usize>)> {
        let Expr::Bin(op, _, _) = self else { return None };
        if !op.chainable() {
            return None;
        }
        let mut operands = Vec::new();
        self.collect_chain(*op, &mut operands).then_some((*op, operands))
    }

    fn collect_chain(&self, op: Op, out: &mut Vec<usize>) -> bool {
        match self {
            Expr::Var(i) => {
                out.push(*i);
                true
            }
            Expr::Bin(o, l, r) if *o == op => {
                // The left spine may always recurse.  The right spine may only
                // recurse for operators that nest both ways, so `a - (b - c)`
                // is not mistaken for the chain `a - b - c`.
                if !l.collect_chain(op, out) {
                    return false;
                }
                match &**r {
                    Expr::Var(i) => {
                        out.push(*i);
                        true
                    }
                    Expr::Bin(..) => op.right_nestable() && r.collect_chain(op, out),
                }
            }
            Expr::Bin(..) => false,
        }
    }

    /// If the expression is a join of meets of operands, return one bitmask of
    /// operand indices per clause.
    ///
    /// This is the form `zipper_merge_dnf` evaluates directly.  A clause is a
    /// *set*, so `a & a` collapses to `a`; that is sound because meet is
    /// idempotent, which is itself one of the laws checked in `laws.rs`.
    pub fn dnf(&self) -> Option<Vec<u64>> {
        match self {
            Expr::Bin(Op::Join, l, r) => {
                let mut cs = l.dnf()?;
                cs.extend(r.dnf()?);
                Some(cs)
            }
            _ => Some(vec![self.meet_mask()?]),
        }
    }

    /// If the expression is a meet of operands, return their index bitmask.
    ///
    /// Rejects a meet whose operands are not in ascending index order, even
    /// though the bitmask would be the same.  A [`Clause`] is a *set*: it
    /// records which zippers take part, not in what order, and
    /// `zipper_merge_dnf` meets a clause's members in slot order, which is
    /// ascending operand index.  Because `pmeet` on `u64` is left-biased, `b &
    /// a` and `a & b` carry different values, so only one of them is what the
    /// clause actually computes.  Returning a mask for the other would make the
    /// DNF route report a divergence that is the route's own fault.
    ///
    /// [`Clause`]: pathmap::experimental::zipper_algebra::Clause
    fn meet_mask(&self) -> Option<u64> {
        let mut vs = Vec::new();
        self.meet_vars(&mut vs).then_some(())?;
        if vs.windows(2).any(|w| w[0] > w[1]) {
            return None;
        }
        Some(vs.iter().fold(0u64, |m, i| m | 1u64 << i))
    }

    /// Operands of a meet-only subexpression, left to right.
    fn meet_vars(&self, out: &mut Vec<usize>) -> bool {
        match self {
            Expr::Var(i) => {
                out.push(*i);
                true
            }
            Expr::Bin(Op::Meet, l, r) => l.meet_vars(out) && r.meet_vars(out),
            _ => false,
        }
    }
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::Var(i) => write!(f, "{}", (b'a' + *i as u8) as char),
            Expr::Bin(op, l, r) => write!(f, "({l} {} {r})", op.sym()),
        }
    }
}
