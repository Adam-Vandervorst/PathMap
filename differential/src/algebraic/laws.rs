//! Identities that must hold whatever the operands are.
//!
//! The route comparison in `routes.rs` catches an implementation that disagrees
//! with its siblings.  It cannot catch a mistake they all share.  Laws are the
//! other half: each one is two *different expressions* that must evaluate to
//! the same trie, so a wrong answer is visible even when every route computes
//! it the same wrong way.
//!
//! # Where the laws come from
//!
//! Not from this file.  They are the theorems of `lean/PrunedModel/Zippy.lean`
//! (branch `spec/zippy-laws`), which proves Adam Vandervorst's `formal.egg` --
//! the reference semantics of Zippy's space algebra -- over the pruned model.
//! `lean/ZippyLaws.lean` reads the *elaborated* theorems, keeps every equation
//! between spaces whose operators the expression language has, and prints them
//! as [`zippy_laws`](super::zippy_laws).  So each law here is a theorem, not a
//! belief, and adding one means proving it.
//!
//! A theorem may quantify over paths and bytes as well as spaces, and may have
//! hypotheses.  Hence [`ZippyLaw`] is a template: [`instantiate`] binds its
//! spaces to the case's operands and its paths and bytes to ones the case
//! carries for the purpose ([`super::Case::law_paths`]), and a law whose
//! hypotheses are false for that binding is skipped for that case.
//!
//! # More instances than the theorems state
//!
//! Two rules turn each theorem into many checks, with no new proof:
//!
//! * **Substitution.**  A theorem holds for *every* space, and any expression
//!   denotes one, so a space variable can be bound to an expression rather than
//!   an operand ([`super::Case::law_spaces`]).  The point is the operands a law
//!   then sees: tries the crate itself produced, with whatever sharing, node
//!   layout and root values its operations leave behind, instead of only the
//!   ones the generator writes.  Binding two variables to the same operand
//!   (`a, b := a, a`) is a case of it, and makes both sides share nodes.
//!
//! * **Congruence.**  If `l = r` then `C[l] = C[r]` for any context `C`
//!   ([`Ctx`], [`super::Case::law_ctx`]).  Both sides hold the same set and were
//!   built differently, so this asks whether an operation's answer depends on
//!   anything but the set it is given -- the question behind the layout and
//!   sharing defects, which nothing else asks directly.
//!
//! Each is reported under its own signature (`law:<name>+subst`, `+ctx`,
//! `+subst+ctx`), and a context is applied only to an instance whose sides
//! already agreed, so a defect is reported in the simplest form that shows it.
//!
//! # Only for `()`
//!
//! The theorems are about `PrunedMap Unit`, a finite set of paths.  They are
//! checked for the value type whose maps *are* sets -- [`FuzzValue::IS_SET`] --
//! and no other.  Under `u64` or `bits` several are false for reasons that
//! have nothing to do with the crate: subtraction removes a path only when the
//! values cancel, and a meet of two values can be bottom.  Laws over values
//! need a value-generic source (`Lattice.lean` has one); that is not this file.

use super::expr::{Expr, Op, Un};
use super::value::FuzzValue;

/// A space-valued term of a law.
#[derive(Clone, Debug)]
pub enum T {
    /// The `i`th space the theorem quantifies over.
    S(usize),
    Empty,
    Singleton(P),
    Bin(Op, Box<T>, Box<T>),
    Wrap(P, Box<T>),
    Unwrap(Box<T>, P),
    Un(Un, Box<T>),
}

/// A path-valued term.
#[derive(Clone, Debug)]
pub enum P {
    Var(usize),
    Nil,
    Cons(B, Box<P>),
    App(Box<P>, Box<P>),
}

/// A byte-valued term.
#[derive(Clone, Copy, Debug)]
pub enum B {
    Var(usize),
    Lit(u8),
}

/// A hypothesis of the theorem.
#[derive(Clone, Debug)]
pub enum Pre {
    NePath(P, P),
    NeByte(B, B),
    Mem(P, T),
    NotMem(P, T),
    EqSpace(T, T),
}

/// One theorem of `Zippy.lean`, as generated.
pub struct ZippyLaw {
    /// The theorem's name in `PrunedModel.Zippy`.
    pub name: &'static str,
    /// How many spaces, paths and bytes it quantifies over.
    pub spaces: usize,
    pub paths: usize,
    pub bytes: usize,
    pub pre: Vec<Pre>,
    pub lhs: T,
    pub rhs: T,
}

/// The builders `zippy_laws.rs` is written in.  Named after the Lean
/// definitions, so the generated file reads like the theorems it came from.
pub mod zippy {
    pub use super::{Pre, ZippyLaw, B, P, T};
    use super::{Op, Un};

    fn bin(op: Op, a: T, b: T) -> T {
        T::Bin(op, Box::new(a), Box::new(b))
    }

    pub fn s(i: usize) -> T {
        T::S(i)
    }
    pub fn empty() -> T {
        T::Empty
    }
    pub fn singleton(p: P) -> T {
        T::Singleton(p)
    }
    pub fn union(a: T, b: T) -> T {
        bin(Op::Join, a, b)
    }
    pub fn inter(a: T, b: T) -> T {
        bin(Op::Meet, a, b)
    }
    pub fn subtr(a: T, b: T) -> T {
        bin(Op::Subtract, a, b)
    }
    pub fn restriction(a: T, b: T) -> T {
        bin(Op::Restrict, a, b)
    }
    /// Egg *defines* `Raffination x y` as `x \ (x <| y)`, and so does
    /// `Zippy.lean`; the crate has no operation of its own for it.
    pub fn raffination(a: T, b: T) -> T {
        subtr(a.clone(), restriction(a, b))
    }
    pub fn composition(a: T, b: T) -> T {
        bin(Op::Compose, a, b)
    }
    pub fn iter_c(a: T, b: T) -> T {
        bin(Op::IterC, a, b)
    }
    pub fn wrap(p: P, a: T) -> T {
        T::Wrap(p, Box::new(a))
    }
    pub fn unwrap(a: T, p: P) -> T {
        T::Unwrap(Box::new(a), p)
    }
    pub fn head(a: T) -> T {
        T::Un(Un::Head, Box::new(a))
    }
    pub fn tails_union(a: T) -> T {
        T::Un(Un::TailsUnion, Box::new(a))
    }
    pub fn tails_inter(a: T) -> T {
        T::Un(Un::TailsInter, Box::new(a))
    }

    pub fn pv(i: usize) -> P {
        P::Var(i)
    }
    pub fn nil() -> P {
        P::Nil
    }
    pub fn cons(b: B, p: P) -> P {
        P::Cons(b, Box::new(p))
    }
    pub fn app(a: P, b: P) -> P {
        P::App(Box::new(a), Box::new(b))
    }

    pub fn bv(i: usize) -> B {
        B::Var(i)
    }
    pub fn lit(n: u8) -> B {
        B::Lit(n)
    }

    pub fn ne_path(a: P, b: P) -> Pre {
        Pre::NePath(a, b)
    }
    pub fn ne_byte(a: B, b: B) -> Pre {
        Pre::NeByte(a, b)
    }
    pub fn mem(p: P, s: T) -> Pre {
        Pre::Mem(p, s)
    }
    pub fn not_mem(p: P, s: T) -> Pre {
        Pre::NotMem(p, s)
    }
    pub fn eq_space(a: T, b: T) -> Pre {
        Pre::EqSpace(a, b)
    }
}

/// What a case offers for a law's variables.
pub struct Binding<'a> {
    /// What space `i` stands for: `Var(i)` for the plain law, any expression
    /// for a substitution instance.
    pub spaces: &'a [Expr],
    pub paths: &'a [Vec<u8>],
    pub bytes: &'a [u8],
}

impl Binding<'_> {
    pub fn byte(&self, b: B) -> u8 {
        match b {
            B::Var(i) => self.bytes[i],
            B::Lit(n) => n,
        }
    }

    pub fn path(&self, p: &P) -> Vec<u8> {
        match p {
            P::Var(i) => self.paths[*i].clone(),
            P::Nil => Vec::new(),
            P::Cons(b, t) => {
                let mut out = vec![self.byte(*b)];
                out.extend(self.path(t));
                out
            }
            P::App(a, b) => [self.path(a), self.path(b)].concat(),
        }
    }

    /// The expression a term denotes, its space `i` being `spaces[i]`.
    pub fn expr(&self, t: &T) -> Expr {
        match t {
            T::S(i) => self.spaces[*i].clone(),
            T::Empty => Expr::Empty,
            T::Singleton(p) => Expr::Singleton(self.path(p)),
            T::Bin(op, a, b) => Expr::bin(*op, self.expr(a), self.expr(b)),
            T::Wrap(p, a) => Expr::wrap(self.path(p), self.expr(a)),
            T::Unwrap(a, p) => Expr::unwrap(self.expr(a), self.path(p)),
            T::Un(u, a) => Expr::un(*u, self.expr(a)),
        }
    }
}

/// A law with its variables bound: the two sides, and the hypotheses as
/// expressions still to be decided against the operands.
pub struct Instance {
    pub lhs: Expr,
    pub rhs: Expr,
    pub pre: Vec<Hyp>,
}

/// A hypothesis with its variables bound.
pub enum Hyp {
    /// Decided already: it compared paths or bytes.
    Holds(bool),
    /// `path ∈ expr`, or `∉` when the flag is false.
    Mem(Vec<u8>, Expr, bool),
    /// `lhs = rhs` as spaces.
    Eq(Expr, Expr),
}

pub fn instantiate(law: &ZippyLaw, bind: &Binding) -> Instance {
    let pre = law
        .pre
        .iter()
        .map(|h| match h {
            Pre::NePath(a, b) => Hyp::Holds(bind.path(a) != bind.path(b)),
            Pre::NeByte(a, b) => Hyp::Holds(bind.byte(*a) != bind.byte(*b)),
            Pre::Mem(p, s) => Hyp::Mem(bind.path(p), bind.expr(s), true),
            Pre::NotMem(p, s) => Hyp::Mem(bind.path(p), bind.expr(s), false),
            Pre::EqSpace(a, b) => Hyp::Eq(bind.expr(a), bind.expr(b)),
        })
        .collect();
    Instance { lhs: bind.expr(&law.lhs), rhs: bind.expr(&law.rhs), pre }
}

/// The laws to check for value type `V`: all of `Zippy.lean`'s for the set
/// type, none otherwise.  See the module comment.
pub fn laws<V: FuzzValue>() -> &'static [ZippyLaw] {
    use std::sync::OnceLock;
    static LAWS: OnceLock<Vec<ZippyLaw>> = OnceLock::new();
    if V::IS_SET { LAWS.get_or_init(super::zippy_laws::laws) } else { &[] }
}

/// Whether `spaces` binds any of `law`'s space variables to something other
/// than the operand of the same index -- that is, whether the substitution
/// instance differs from the plain one.
pub fn substituted(law: &ZippyLaw, spaces: &[Expr]) -> bool {
    spaces[..law.spaces].iter().enumerate().any(|(i, e)| !matches!(e, Expr::Var(j) if *j == i))
}

/// An expression with one hole: the context a law's two sides are put in to
/// check congruence.  See the module comment.
#[derive(Clone, Debug)]
pub enum Ctx {
    Hole,
    /// `(C op e)`.
    Left(Op, Box<Ctx>, Expr),
    /// `(e op C)`.
    Right(Op, Expr, Box<Ctx>),
    Wrap(Vec<u8>, Box<Ctx>),
    Unwrap(Box<Ctx>, Vec<u8>),
    Un(Un, Box<Ctx>),
}

impl Ctx {
    pub fn is_hole(&self) -> bool {
        matches!(self, Ctx::Hole)
    }

    /// `C[e]`.
    pub fn plug(&self, e: Expr) -> Expr {
        match self {
            Ctx::Hole => e,
            Ctx::Left(op, c, r) => Expr::bin(*op, c.plug(e), r.clone()),
            Ctx::Right(op, l, c) => Expr::bin(*op, l.clone(), c.plug(e)),
            Ctx::Wrap(p, c) => Expr::wrap(p.clone(), c.plug(e)),
            Ctx::Unwrap(c, p) => Expr::unwrap(c.plug(e), p.clone()),
            Ctx::Un(u, c) => Expr::un(*u, c.plug(e)),
        }
    }
}

/// Written like [`Expr`], with `_` for the hole.
impl std::fmt::Display for Ctx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        use super::expr::show_path;
        match self {
            Ctx::Hole => write!(f, "_"),
            Ctx::Left(Op::IterC, c, r) => write!(f, "iter_c({c}, {r})"),
            Ctx::Right(Op::IterC, l, c) => write!(f, "iter_c({l}, {c})"),
            Ctx::Left(op, c, r) => write!(f, "({c} {} {r})", op.sym()),
            Ctx::Right(op, l, c) => write!(f, "({l} {} {c})", op.sym()),
            Ctx::Wrap(p, c) => write!(f, "wrap{}({c})", show_path(p)),
            Ctx::Unwrap(c, p) => write!(f, "unwrap({c}){}", show_path(p)),
            Ctx::Un(u, c) => write!(f, "{}({c})", u.name()),
        }
    }
}

/// The most of each kind of variable any generated law uses.  The case has to
/// supply at least this many; `tests/algebraic.rs` checks the bound.
pub fn arity() -> (usize, usize, usize) {
    super::zippy_laws::laws()
        .iter()
        .fold((0, 0, 0), |(s, p, b), l| (s.max(l.spaces), p.max(l.paths), b.max(l.bytes)))
}
