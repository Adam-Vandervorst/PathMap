//! Identities that must hold whatever the operands are.
//!
//! The route comparison in `routes.rs` catches an implementation that disagrees
//! with its siblings.  It cannot catch a mistake they all share.  Laws are the
//! other half: each one is two *different expressions* that must evaluate to
//! the same trie, so a wrong answer is visible even when every route computes
//! it the same wrong way.
//!
//! A law is written as a pair of [`Expr`]s and evaluated by the ordinary route
//! machinery, which keeps this file declarative and means a law automatically
//! inherits whatever the expression evaluator can do.
//!
//! # Strength depends on the value type
//!
//! [`laws`] is parameterised by the value type, and returns a *stronger* set for
//! one whose instances actually form a distributive lattice with a relative
//! complement -- see [`FuzzValue::LAWFUL`].  Three things change:
//!
//! * The laws marked [`Level::Paths`] are promoted to [`Level::Values`].  They
//!   are weakened for `u64` only because its `pjoin` and `pmeet` both return the
//!   left operand, so swapping the operands swaps the result's value and
//!   commutativity cannot hold on values there.
//!
//! * Three further identities are added, listed in [`lawful_only`].  They are
//!   laws in any distributive lattice and fail for `u64`, again because join and
//!   meet have collapsed into one function.
//!
//! * Symmetric difference becomes associative on values, not merely on paths.
//!
//! So the difference between the two sets is a measurement: a law that holds for
//! `bits` and fails for `u64` is telling you about `u64`, and one that fails for
//! `bits` is telling you about the crate.  That split is the whole reason for
//! running both.

use super::expr::{Expr, Op};
use super::value::FuzzValue;

/// Operand slot holding the empty trie, appended after the case's own
/// operands so identities can mention it.  See [`LAW_OPERANDS`].
pub const EMPTY: usize = 3;

/// Operands a law may mention: three from the case, then the empty trie.
pub const LAW_OPERANDS: usize = 4;

/// How much of the result a law constrains.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Level {
    /// Which path carries which value.
    Values,
    /// Which paths survive, values unconstrained.
    Paths,
}

pub struct Law {
    pub name: &'static str,
    pub lhs: Expr,
    pub rhs: Expr,
    pub level: Level,
}

fn v(i: usize) -> Expr {
    Expr::Var(i)
}
fn j(a: Expr, b: Expr) -> Expr {
    Expr::bin(Op::Join, a, b)
}
fn m(a: Expr, b: Expr) -> Expr {
    Expr::bin(Op::Meet, a, b)
}
fn s(a: Expr, b: Expr) -> Expr {
    Expr::bin(Op::Subtract, a, b)
}
fn x(a: Expr, b: Expr) -> Expr {
    Expr::bin(Op::SymDiff, a, b)
}
fn r(a: Expr, b: Expr) -> Expr {
    Expr::bin(Op::Restrict, a, b)
}

/// The laws to check for value type `V`.
///
/// For a lawful `V` every `Paths` level is promoted to `Values` and
/// [`lawful_only`] is appended.
pub fn laws<V: FuzzValue>() -> Vec<Law> {
    let mut out = base();
    if V::LAWFUL {
        for law in &mut out {
            law.level = Level::Values;
        }
        out.extend(lawful_only());
    }
    out
}

/// Identities that hold whatever the value type.
fn base() -> Vec<Law> {
    use Level::{Paths, Values};
    let (a, b, c, e) = (0usize, 1usize, 2usize, EMPTY);
    vec![
        // --- lattice basics
        Law { name: "join-idempotent", lhs: j(v(a), v(a)), rhs: v(a), level: Values },
        Law { name: "meet-idempotent", lhs: m(v(a), v(a)), rhs: v(a), level: Values },
        Law { name: "join-unit", lhs: j(v(a), v(e)), rhs: v(a), level: Values },
        Law { name: "meet-zero", lhs: m(v(a), v(e)), rhs: v(e), level: Values },
        // Path set only: both `pjoin` and `pmeet` return the left operand, so
        // swapping the operands swaps which value lands.  A real lattice would
        // make these value-level laws; see the module comment.
        Law { name: "join-commutative", lhs: j(v(a), v(b)), rhs: j(v(b), v(a)), level: Paths },
        Law { name: "meet-commutative", lhs: m(v(a), v(b)), rhs: m(v(b), v(a)), level: Paths },
        // Associativity does hold on values even here: both nestings select the
        // leftmost present operand's value.
        Law {
            name: "join-associative",
            lhs: j(j(v(a), v(b)), v(c)),
            rhs: j(v(a), j(v(b), v(c))),
            level: Values,
        },
        Law {
            name: "meet-associative",
            lhs: m(m(v(a), v(b)), v(c)),
            rhs: m(v(a), m(v(b), v(c))),
            level: Values,
        },
        Law { name: "absorb-meet-join", lhs: m(v(a), j(v(a), v(b))), rhs: v(a), level: Values },
        Law { name: "absorb-join-meet", lhs: j(v(a), m(v(a), v(b))), rhs: v(a), level: Values },
        Law {
            name: "meet-distributes-over-join",
            lhs: m(v(a), j(v(b), v(c))),
            rhs: j(m(v(a), v(b)), m(v(a), v(c))),
            level: Values,
        },
        Law {
            name: "join-distributes-over-meet",
            lhs: j(v(a), m(v(b), v(c))),
            rhs: m(j(v(a), v(b)), j(v(a), v(c))),
            level: Values,
        },
        // --- subtraction
        Law { name: "subtract-self", lhs: s(v(a), v(a)), rhs: v(e), level: Values },
        Law { name: "subtract-unit", lhs: s(v(a), v(e)), rhs: v(a), level: Values },
        Law { name: "subtract-from-empty", lhs: s(v(e), v(a)), rhs: v(e), level: Values },
        // Each step drops the paths whose value the subtrahend matches, and
        // "matches b or matches c" does not depend on the order.
        Law {
            name: "subtract-steps-commute",
            lhs: s(s(v(a), v(b)), v(c)),
            rhs: s(s(v(a), v(c)), v(b)),
            level: Values,
        },
        // Subtracting cannot add a path: re-joining the removed part recovers
        // no more than the original.
        Law { name: "subtract-shrinks", lhs: j(s(v(a), v(b)), v(a)), rhs: v(a), level: Values },
        // --- symmetric difference
        Law { name: "sym-diff-self", lhs: x(v(a), v(a)), rhs: v(e), level: Values },
        Law { name: "sym-diff-unit", lhs: x(v(a), v(e)), rhs: v(a), level: Values },
        // Fully commutative, values included: a coincident path cancels on both
        // sides, so each surviving value comes from the single side that has it.
        Law { name: "sym-diff-commutative", lhs: x(v(a), v(b)), rhs: x(v(b), v(a)), level: Values },
        Law {
            name: "sym-diff-associative-paths",
            lhs: x(x(v(a), v(b)), v(c)),
            rhs: x(v(a), x(v(b), v(c))),
            level: Paths,
        },
        // The definition `zipper_sym_diff`'s own documentation gives.
        Law {
            name: "sym-diff-is-join-minus-meet",
            lhs: x(v(a), v(b)),
            rhs: s(j(v(a), v(b)), m(v(a), v(b))),
            level: Values,
        },
        // --- restrict
        // Every path is a prefix of itself, so restricting by its own operand
        // admits everything.
        Law { name: "restrict-self", lhs: r(v(a), v(a)), rhs: v(a), level: Values },
        Law { name: "restrict-empty", lhs: r(v(a), v(e)), rhs: v(e), level: Values },
        Law { name: "restrict-of-empty", lhs: r(v(e), v(a)), rhs: v(e), level: Values },
        Law { name: "restrict-idempotent", lhs: r(r(v(a), v(b)), v(b)), rhs: r(v(a), v(b)), level: Values },
        // A path present in both operands is admitted by itself, so the meet is
        // contained in the restriction.
        Law {
            name: "meet-under-restrict",
            lhs: m(m(v(a), v(b)), r(v(a), v(b))),
            rhs: m(v(a), v(b)),
            level: Values,
        },
        // --- majority, the worked example in `zipper_majority`'s docs, written
        // out as the DNF it claims to equal.  Exercised here so the DNF engine
        // is checked against a hand-written join of meets as well as against
        // the pointwise routes.
        Law {
            name: "majority-is-pairwise-meets",
            lhs: j(j(m(v(a), v(b)), m(v(a), v(c))), m(v(b), v(c))),
            rhs: j(m(v(a), v(b)), j(m(v(a), v(c)), m(v(b), v(c)))),
            level: Values,
        },
    ]
}

/// Identities that need the value type to be a real distributive lattice with a
/// relative complement.
///
/// Each of these fails for `u64`, and each failure is explained by the same
/// thing: `pjoin` and `pmeet` both return the left operand, so `a | b == a & b`,
/// and `psubtract` is `None` exactly on equality.
fn lawful_only() -> Vec<Law> {
    use Level::Values;
    let (a, b, c) = (0usize, 1usize, 2usize);
    vec![
        // De Morgan for relative complement.  Fails for `u64` because `b | c`
        // carries `b`'s value where both are present, so the left side keeps a
        // path whose value matches `c` but not `b`.
        Law {
            name: "subtract-over-join",
            lhs: s(v(a), j(v(b), v(c))),
            rhs: m(s(v(a), v(b)), s(v(a), v(c))),
            level: Values,
        },
        Law {
            name: "subtract-over-meet",
            lhs: s(v(a), m(v(b), v(c))),
            rhs: j(s(v(a), v(b)), s(v(a), v(c))),
            level: Values,
        },
        // Subtracting the overlap is the same as subtracting the whole.  Fails
        // for `u64` because `a & b` carries *`a`'s* value, so the right side
        // drops every shared path rather than only the equal ones.
        Law {
            name: "subtract-is-subtract-meet",
            lhs: s(v(a), v(b)),
            rhs: s(v(a), m(v(a), v(b))),
            level: Values,
        },
        // Symmetric difference is the XOR of a Boolean ring, so it is
        // associative on values and not merely on paths.
        Law {
            name: "sym-diff-associative",
            lhs: x(x(v(a), v(b)), v(c)),
            rhs: x(v(a), x(v(b), v(c))),
            level: Values,
        },
    ]
}
