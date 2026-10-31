//! Flat reference semantics, as a fourth opinion.
//!
//! Every route in `routes.rs` goes through `pathmap`, so a defect common to the
//! whole algebra layer would make them agree with each other and still be wrong.
//! This computes the same expression over a plain `BTreeMap<Vec<u8>, V>` with no
//! trie involved, which gives the comparison something to anchor against.
//!
//! It models only *which path carries which value* and abstains on structure: a
//! flat map cannot represent a dangling path, and whether a dangling path
//! survives an operation is unsettled in the crate.  `shape.rs` explains the
//! split.
//!
//! # The value algebra is not restated here
//!
//! Each operation delegates to the value type's own `pjoin`, `pmeet` or
//! `psubtract` through the `Option<V>` impls in `pathmap::ring`.  An earlier
//! version spelled out `u64`'s behaviour by hand -- left-biased join, left-biased
//! meet, subtract-on-equality -- which worked only because it happened to match,
//! and which meant the model was asserting the harness author's idea of the
//! algebra rather than the type's.  Delegating means this file is correct for
//! any [`FuzzValue`] without changes, and that a disagreement between the model
//! and a route is always about *where a value ends up*, never about what
//! combining two values means.
//!
//! What remains genuinely this file's own is the set structure: which paths an
//! operation visits at all, and `restrict`, which is not a lattice operation.

use pathmap::ring::{DistributiveLattice, Lattice};

use super::expr::{Expr, Op, Un};
use super::shape::Values;
use super::value::{resolve, FuzzValue};

pub fn eval<V: FuzzValue>(e: &Expr, operands: &[Values<V>]) -> Values<V> {
    match e {
        Expr::Var(i) => operands[*i].clone(),
        Expr::Empty => Values::new(),
        Expr::Singleton(p) => singleton(p),
        Expr::Bin(op, l, r) => {
            let a = eval(l, operands);
            let b = eval(r, operands);
            apply(*op, &a, &b)
        }
        Expr::Wrap(p, e) => wrap(p, &eval(e, operands)),
        Expr::Unwrap(e, p) => unwrap(&eval(e, operands), p),
        Expr::Un(u, e) => unary(*u, &eval(e, operands)),
    }
}

pub fn unary<V: FuzzValue>(u: Un, a: &Values<V>) -> Values<V> {
    match u {
        Un::Head => head(a),
        Un::TailsUnion => tails_union(a),
        Un::TailsInter => tails_inter(a),
    }
}

pub fn apply<V: FuzzValue>(op: Op, a: &Values<V>, b: &Values<V>) -> Values<V> {
    match op {
        Op::Join => join(a, b),
        Op::Meet => meet(a, b),
        Op::Subtract => subtract(a, b),
        Op::SymDiff => sym_diff(a, b),
        Op::Restrict => restrict(a, b),
        Op::Compose => compose(a, b),
        Op::IterC => iter_c(a, b),
    }
}

/// Every path either side mentions.
fn keys<V: FuzzValue>(a: &Values<V>, b: &Values<V>) -> Vec<Vec<u8>> {
    let mut k: Vec<Vec<u8>> = a.keys().chain(b.keys()).cloned().collect();
    k.sort();
    k.dedup();
    k
}

/// Combine both sides pointwise with one of the value operations, dropping the
/// paths where the result is bottom.
fn pointwise<V: FuzzValue, F>(a: &Values<V>, b: &Values<V>, f: F) -> Values<V>
where
    F: Fn(&Option<V>, &Option<V>) -> Option<V>,
{
    let mut out = Values::new();
    for k in keys(a, b) {
        let (lv, rv) = (a.get(&k).cloned(), b.get(&k).cloned());
        if let Some(v) = f(&lv, &rv) {
            out.insert(k, v);
        }
    }
    out
}

pub fn join<V: FuzzValue>(a: &Values<V>, b: &Values<V>) -> Values<V> {
    pointwise(a, b, |l, r| resolve(l.pjoin(r), l, r))
}

pub fn meet<V: FuzzValue>(a: &Values<V>, b: &Values<V>) -> Values<V> {
    pointwise(a, b, |l, r| resolve(l.pmeet(r), l, r))
}

pub fn subtract<V: FuzzValue>(a: &Values<V>, b: &Values<V>) -> Values<V> {
    pointwise(a, b, |l, r| resolve(l.psubtract(r), l, r))
}

/// `(a | b) \ (a & b)`, the definition `zipper_sym_diff`'s own documentation
/// gives.
///
/// In a distributive lattice with a relative complement this equals
/// `(a \ b) | (b \ a)`, and `laws.rs` checks that -- for a lawful value type it
/// is a law, and for `u64` the two differ, which is a fact about `u64` rather
/// than about symmetric difference.
pub fn sym_diff<V: FuzzValue>(a: &Values<V>, b: &Values<V>) -> Values<V> {
    subtract(&join(a, b), &meet(a, b))
}

/// Left paths that some path-to-a-value in the right side is a prefix of.
///
/// Not a lattice operation, so there is nothing to delegate to: the value is
/// carried across unchanged, and only the path set is decided.  The prefix is
/// inclusive at both ends -- the empty path counts, so a root value in `b`
/// admits all of `a`, and `k` counts as a prefix of itself -- both of which
/// follow from the note on `PathMap::restrict`.
pub fn restrict<V: FuzzValue>(a: &Values<V>, b: &Values<V>) -> Values<V> {
    a.iter()
        .filter(|(k, _)| (0..=k.len()).any(|n| b.contains_key(&k[..n])))
        .map(|(k, v)| (k.clone(), v.clone()))
        .collect()
}

// ---------------------------------------------------------------- Zippy
//
// Each of these is the membership lemma `Zippy.lean` proves for the operator
// (`mem_wrap`, `mem_unwrap`, `mem_head`, ...), read as a definition.  Values
// come along with the paths they sit on; where several paths land on one, they
// are joined in ascending key order, which is the order every crate route
// visits them in too.

pub fn singleton<V: FuzzValue>(p: &[u8]) -> Values<V> {
    Values::from([(p.to_vec(), V::canonical())])
}

/// `p ∈ wrap q s ↔ ∃ r, p = q ++ r ∧ r ∈ s`.
pub fn wrap<V: FuzzValue>(p: &[u8], a: &Values<V>) -> Values<V> {
    a.iter().map(|(k, v)| ([p, &k[..]].concat(), v.clone())).collect()
}

/// `p ∈ unwrap s q ↔ q ++ p ∈ s`.
pub fn unwrap<V: FuzzValue>(a: &Values<V>, p: &[u8]) -> Values<V> {
    a.iter().filter_map(|(k, v)| k.strip_prefix(p).map(|r| (r.to_vec(), v.clone()))).collect()
}

/// The first bytes of `a`'s non-empty paths, ascending.  A space has no
/// dangling paths, so this is also what `child_mask` would say of one.
pub fn heads<V: FuzzValue>(a: &Values<V>) -> Vec<u8> {
    let mut hs: Vec<u8> = a.keys().filter_map(|k| k.first().copied()).collect();
    hs.dedup();
    hs
}

/// `p ∈ head s ↔ ∃ b r, p = [b] ∧ b :: r ∈ s`.
pub fn head<V: FuzzValue>(a: &Values<V>) -> Values<V> {
    heads(a).into_iter().map(|b| (vec![b], V::canonical())).collect()
}

/// `p ∈ tailsUnion s ↔ ∃ b, b :: p ∈ s`, folded with `join` over the heads.
pub fn tails_union<V: FuzzValue>(a: &Values<V>) -> Values<V> {
    heads(a).into_iter().fold(Values::new(), |acc, b| join(&acc, &unwrap(a, &[b])))
}

/// The tails under the first head, met with each later one's in turn; nothing
/// when there is no head.  This is egg's `tails-intersection-acc` fold.
pub fn tails_inter<V: FuzzValue>(a: &Values<V>) -> Values<V> {
    let mut hs = heads(a).into_iter();
    let Some(first) = hs.next() else { return Values::new() };
    hs.fold(unwrap(a, &[first]), |acc, b| meet(&acc, &unwrap(a, &[b])))
}

/// `t` under every path of `s`, joined in ascending order of those paths.
/// `s`'s own values are not carried: Composition reads only its paths.
pub fn compose<V: FuzzValue>(s: &Values<V>, t: &Values<V>) -> Values<V> {
    s.keys().fold(Values::new(), |acc, u| join(&acc, &wrap(u, t)))
}

/// `p ∈ iterC src b ↔ (∃ h r, h :: r ∈ src) ∧ p ∈ b`.
pub fn iter_c<V: FuzzValue>(src: &Values<V>, b: &Values<V>) -> Values<V> {
    if src.keys().any(|k| !k.is_empty()) { b.clone() } else { Values::new() }
}
