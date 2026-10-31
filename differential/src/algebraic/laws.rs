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

/// Paths and bytes a case offers for a law's path and byte variables.
pub struct Binding<'a> {
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

    /// The expression a term denotes, its space `i` being operand `i`.
    pub fn expr(&self, t: &T) -> Expr {
        match t {
            T::S(i) => Expr::Var(*i),
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

/// The most of each kind of variable any generated law uses.  The case has to
/// supply at least this many; `tests/algebraic.rs` checks the bound.
pub fn arity() -> (usize, usize, usize) {
    super::zippy_laws::laws()
        .iter()
        .fold((0, 0, 0), |(s, p, b), l| (s.max(l.spaces), p.max(l.paths), b.max(l.bytes)))
}
