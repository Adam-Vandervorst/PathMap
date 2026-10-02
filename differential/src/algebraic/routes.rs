//! The different ways to compute the same thing.
//!
//! `pathmap` offers each algebraic operation several times over: once eagerly
//! on whole maps, once in place through a write zipper, once as a lockstep
//! traversal of two read zippers, and -- for the associative ones -- again as
//! an n-ary traversal, a DNF evaluator, and a lazy zipper over a virtual trie.
//! Those are not alternative spellings of one implementation; they are separate
//! implementations with separate pruning, grafting and value-combining logic,
//! which is exactly why they are worth running against each other.
//!
//! A *route* is one consistent way to evaluate a whole expression.  There are
//! two kinds:
//!
//! * **pointwise** routes walk the expression bottom-up and evaluate each node
//!   with a two-operand call, materialising each intermediate into a trie.
//!   Route `k` picks strategy `k % n` for an operator with `n` strategies, so
//!   every strategy is covered by some route and the routes mix them.
//! * **whole-expression** routes recognise a shape -- a chain of one
//!   associative operator, or a join of meets -- and hand the entire thing to
//!   one call that does it in a single traversal.  These are the routes with
//!   real independence from the pointwise ones: no intermediate trie is ever
//!   built, so they exercise code the pointwise routes never reach.
//!
//! Every route must produce the same trie.  `shape.rs` says what "same" means
//! and why dangling-path divergence is reported separately.

use pathmap::PathMap;
use pathmap::experimental::zipper_algebra::{
    Clause, zipper_join, zipper_join3, zipper_meet, zipper_meet3, zipper_merge_dnf,
    zipper_n_join, zipper_n_meet, zipper_n_subtract, zipper_n_sym_diff, zipper_subtract,
    zipper_subtract3, zipper_sym_diff, zipper_sym_diff3, ZipperMergeF,
};
use pathmap::zipper::{
    OverlayZipper, ReadZipperUntracked, ZipperMoving, ZipperPath, ZipperValues, ZipperWriting,
};

use super::expr::{Expr, Op};
use super::model;
use super::shape::{shape_of_map, shape_of_zipper, values_of_shape, Shape, Values, ESCAPED_ROOT, TRUNCATED};

/// Names of the per-operator strategies, in the order route `k % n` indexes
/// them.  Kept as tables so a route's name can say which strategy it used for
/// each operator the expression contains.
pub const JOIN_STRATEGIES: &[&str] =
    &["map", "join_into", "join_map_into", "join_into_take", "zipper_join", "overlay"];
pub const MEET_STRATEGIES: &[&str] = &["map", "meet_into", "meet_2", "zipper_meet"];
pub const SUBTRACT_STRATEGIES: &[&str] = &["map", "subtract_into", "zipper_subtract"];
pub const SYM_DIFF_STRATEGIES: &[&str] = &["zipper_sym_diff", "join_minus_meet"];
pub const RESTRICT_STRATEGIES: &[&str] = &["map", "wz_restrict"];

pub fn strategies(op: Op) -> &'static [&'static str] {
    match op {
        Op::Join => JOIN_STRATEGIES,
        Op::Meet => MEET_STRATEGIES,
        Op::Subtract => SUBTRACT_STRATEGIES,
        Op::SymDiff => SYM_DIFF_STRATEGIES,
        Op::Restrict => RESTRICT_STRATEGIES,
    }
}

/// How many pointwise routes exist: enough that every strategy of every
/// operator is reached by at least one of them.
pub const POINTWISE_ROUTES: usize = 6;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Route {
    /// Bottom-up two-operand evaluation, strategy `k % n` per operator.
    Pointwise(usize),
    /// `zipper_join3` / `zipper_meet3` / `zipper_subtract3` / `zipper_sym_diff3`
    /// on a chain of exactly three operands.
    Ternary,
    /// `zipper_n_*` on a chain of operands, via the slice-of-zippers entry point.
    Nary,
    /// The same chain through the `ZipperMergeF` tuple entry point, which goes
    /// via the `PolyZipper`-derived enum rather than a homogeneous array.
    NaryPoly,
    /// `zipper_merge_dnf` on a join of meets.
    Dnf,
    /// Flat `BTreeMap` semantics, no trie.  Values only; abstains on structure.
    Model,
}

impl Route {
    pub fn all() -> Vec<Route> {
        let mut v: Vec<Route> = (0..POINTWISE_ROUTES).map(Route::Pointwise).collect();
        v.extend([Route::Ternary, Route::Nary, Route::NaryPoly, Route::Dnf, Route::Model]);
        v
    }

    /// Name including, for a pointwise route, the strategy it picked for each
    /// operator the expression actually uses.  A failure report needs this to
    /// be actionable: "pw#3" alone does not name a function to go and read.
    pub fn name(&self, e: &Expr) -> String {
        match self {
            Route::Pointwise(k) => {
                let mut used: Vec<Op> = Vec::new();
                collect_ops(e, &mut used);
                let picks: Vec<String> = Op::ALL
                    .iter()
                    .filter(|op| used.contains(op))
                    .map(|op| {
                        let t = strategies(*op);
                        format!("{}={}", op.sym(), t[k % t.len()])
                    })
                    .collect();
                format!("pw#{k}[{}]", picks.join(","))
            }
            Route::Ternary => "ternary".into(),
            Route::Nary => "nary".into(),
            Route::NaryPoly => "nary_poly".into(),
            Route::Dnf => "dnf".into(),
            Route::Model => "model".into(),
        }
    }
}

fn collect_ops(e: &Expr, out: &mut Vec<Op>) {
    if let Expr::Bin(op, l, r) = e {
        if !out.contains(op) {
            out.push(*op);
        }
        collect_ops(l, out);
        collect_ops(r, out);
    }
}

/// What a route produced.  `shape` is `None` for a route that cannot represent
/// dangling paths, which is only [`Route::Model`].
pub struct Outcome {
    pub values: Values,
    pub shape: Option<Shape>,
}

impl Outcome {
    fn from_map(m: &PathMap<u64>) -> Outcome {
        let shape = shape_of_map(m);
        Outcome { values: values_of_shape(&shape), shape: Some(shape) }
    }
}

/// Evaluate `e` over `operands` by `route`, or `None` if the route does not
/// apply to this expression's shape.
pub fn eval(route: Route, e: &Expr, operands: &[PathMap<u64>]) -> Option<Outcome> {
    match route {
        Route::Pointwise(k) => Some(Outcome::from_map(&pointwise(k, e, operands))),
        Route::Ternary => ternary(e, operands).map(|m| Outcome::from_map(&m)),
        Route::Nary => nary(e, operands, false).map(|m| Outcome::from_map(&m)),
        Route::NaryPoly => nary(e, operands, true).map(|m| Outcome::from_map(&m)),
        Route::Dnf => dnf(e, operands).map(|m| Outcome::from_map(&m)),
        Route::Model => {
            let vals: Vec<Values> =
                operands.iter().map(|m| values_of_shape(&shape_of_map(m))).collect();
            Some(Outcome { values: model::eval(e, &vals), shape: None })
        }
    }
}

// ---------------------------------------------------------------- pointwise

fn pointwise(k: usize, e: &Expr, operands: &[PathMap<u64>]) -> PathMap<u64> {
    match e {
        Expr::Var(i) => operands[*i].clone(),
        Expr::Bin(op, l, r) => {
            let a = pointwise(k, l, operands);
            let b = pointwise(k, r, operands);
            apply(*op, k, &a, &b)
        }
    }
}

/// One operator, one strategy.  Every arm is a different code path in the
/// crate, not a different way of calling the same one.
pub fn apply(op: Op, k: usize, a: &PathMap<u64>, b: &PathMap<u64>) -> PathMap<u64> {
    let n = strategies(op).len();
    match (op, k % n) {
        // -- join
        (Op::Join, 0) => a.join(b),
        (Op::Join, 1) => {
            let mut out = a.clone();
            {
                let mut wz = out.write_zipper();
                wz.join_into(&b.read_zipper());
            }
            out
        }
        (Op::Join, 2) => {
            let mut out = a.clone();
            {
                let mut wz = out.write_zipper();
                wz.join_map_into(b.clone());
            }
            out
        }
        (Op::Join, 3) => {
            // Consumes the source.  `prune = false` keeps whatever dangling
            // structure the operation leaves, so this route is comparable with
            // the grafting ones rather than silently tidier than them.
            let mut out = a.clone();
            let mut src = b.clone();
            {
                let mut wz = out.write_zipper();
                let mut sz = src.write_zipper();
                wz.join_into_take(&mut sz, false);
            }
            out
        }
        (Op::Join, 4) => {
            let mut out = PathMap::new();
            {
                let mut lz = a.read_zipper();
                let mut rz = b.read_zipper();
                let mut wz = out.write_zipper();
                zipper_join(&mut lz, &mut rz, &mut wz);
            }
            out
        }
        (Op::Join, 5) => {
            // `OverlayZipper`'s default mapping is `a.or(b)`, which is the same
            // left bias `u64`'s `pjoin` has, so the virtual trie it walks
            // should be exactly the join.  It never builds a trie, so it has to
            // be materialised to be composed into a larger expression; the walk
            // records dangling paths too, so nothing is lost in the round trip.
            let overlay = OverlayZipper::new(a.read_zipper(), b.read_zipper());
            materialize(overlay)
        }

        // -- meet
        (Op::Meet, 0) => a.meet(b),
        (Op::Meet, 1) => {
            let mut out = a.clone();
            {
                let mut wz = out.write_zipper();
                wz.meet_into(&b.read_zipper(), false);
            }
            out
        }
        (Op::Meet, 2) => {
            // Writes the intersection of two sources into a fresh destination,
            // rather than intersecting a destination with one source.
            let mut out = PathMap::new();
            {
                let mut wz = out.write_zipper();
                wz.meet_2(&a.read_zipper(), &b.read_zipper());
            }
            out
        }
        (Op::Meet, 3) => {
            let mut out = PathMap::new();
            {
                let mut lz = a.read_zipper();
                let mut rz = b.read_zipper();
                let mut wz = out.write_zipper();
                zipper_meet(&mut lz, &mut rz, &mut wz);
            }
            out
        }

        // -- subtract
        (Op::Subtract, 0) => a.subtract(b),
        (Op::Subtract, 1) => {
            let mut out = a.clone();
            {
                let mut wz = out.write_zipper();
                wz.subtract_into(&b.read_zipper(), false);
            }
            out
        }
        (Op::Subtract, 2) => {
            let mut out = PathMap::new();
            {
                let mut lz = a.read_zipper();
                let mut rz = b.read_zipper();
                let mut wz = out.write_zipper();
                zipper_subtract(&mut lz, &mut rz, &mut wz);
            }
            out
        }

        // -- symmetric difference
        (Op::SymDiff, 0) => {
            let mut out = PathMap::new();
            {
                let mut lz = a.read_zipper();
                let mut rz = b.read_zipper();
                let mut wz = out.write_zipper();
                zipper_sym_diff(&mut lz, &mut rz, &mut wz);
            }
            out
        }
        (Op::SymDiff, 1) => {
            // The definition `zipper_sym_diff`'s doc comment gives, built out
            // of the other three operations.  Where this disagrees with the
            // specialised traversal, one of the two is wrong.
            let j = a.join(b);
            let m = a.meet(b);
            j.subtract(&m)
        }

        // -- restrict
        (Op::Restrict, 0) => a.restrict(b),
        (Op::Restrict, 1) => {
            let mut out = a.clone();
            {
                let mut wz = out.write_zipper();
                wz.restrict(&b.read_zipper());
            }
            out
        }

        _ => unreachable!("strategy index out of range for {op:?}"),
    }
}

/// Walk a zipper over a virtual trie and build the real trie it describes.
///
/// `create_path` is what keeps this faithful: a path with no value still has to
/// appear in the output, or materialising would quietly erase exactly the
/// dangling structure the comparison is trying to detect.
fn materialize<Z>(mut z: Z) -> PathMap<u64>
where
    Z: ZipperMoving + ZipperPath + ZipperValues<u64>,
{
    let shape = shape_of_zipper(&mut z);
    let mut out = PathMap::new();
    {
        let mut wz = out.write_zipper();
        for (p, v) in &shape {
            if &p[..] == ESCAPED_ROOT || &p[..] == TRUNCATED {
                continue;
            }
            wz.reset();
            wz.descend_to(p);
            match v {
                Some(v) => {
                    wz.set_val(*v);
                }
                None => {
                    wz.create_path();
                }
            }
        }
    }
    out
}

// -------------------------------------------------------- whole-expression

/// Chain of exactly three operands through the `*3` entry points.
fn ternary(e: &Expr, operands: &[PathMap<u64>]) -> Option<PathMap<u64>> {
    let (op, idx) = e.chain()?;
    if idx.len() != 3 {
        return None;
    }
    let (a, b, c) = (&operands[idx[0]], &operands[idx[1]], &operands[idx[2]]);
    let mut out = PathMap::new();
    {
        let mut za = a.read_zipper();
        let mut zb = b.read_zipper();
        let mut zc = c.read_zipper();
        let mut wz = out.write_zipper();
        match op {
            Op::Join => zipper_join3(&mut za, &mut zb, &mut zc, &mut wz),
            Op::Meet => zipper_meet3(&mut za, &mut zb, &mut zc, &mut wz),
            Op::Subtract => zipper_subtract3(&mut za, &mut zb, &mut zc, &mut wz),
            Op::SymDiff => zipper_sym_diff3(&mut za, &mut zb, &mut zc, &mut wz),
            Op::Restrict => return None,
        }
    }
    Some(out)
}

/// A chain of any length through the n-ary entry points.
///
/// Two of them: the slice form (`zipper_n_*`, const-generic over a homogeneous
/// array) and the tuple form (`ZipperMergeF::*_n`, which routes through the
/// `PolyZipper`-derived enum).  They are separate monomorphisations of the
/// merge engine and are worth distinguishing, so `poly` selects between them.
fn nary(e: &Expr, operands: &[PathMap<u64>], poly: bool) -> Option<PathMap<u64>> {
    let (op, idx) = e.chain()?;
    if op == Op::Restrict {
        return None;
    }
    let mut out = PathMap::new();
    {
        let mut wz = out.write_zipper();
        // Const-generic arity has to be dispatched by hand: there is one
        // monomorphisation per operand count, and the count is only known at
        // run time.  The tuple form additionally has one impl per arity.
        macro_rules! slice_arm {
            ($n:literal) => {{
                let mut zs: [ReadZipperUntracked<'_, '_, u64>; $n] =
                    core::array::from_fn(|i| operands[idx[i]].read_zipper());
                match op {
                    Op::Join => zipper_n_join(&mut zs, &mut wz),
                    Op::Meet => zipper_n_meet(&mut zs, &mut wz),
                    Op::Subtract => zipper_n_subtract(&mut zs, &mut wz),
                    Op::SymDiff => zipper_n_sym_diff(&mut zs, &mut wz),
                    Op::Restrict => unreachable!(),
                }
            }};
        }
        macro_rules! tuple_arm {
            ($($i:literal),+) => {{
                let t = ( $( &mut operands[idx[$i]].read_zipper() ),+ );
                match op {
                    Op::Join => t.join_n(&mut wz),
                    Op::Meet => t.meet_n(&mut wz),
                    Op::Subtract => t.subtract_n(&mut wz),
                    Op::SymDiff => t.sym_diff_n(&mut wz),
                    Op::Restrict => unreachable!(),
                }
            }};
        }
        match (poly, idx.len()) {
            (false, 2) => slice_arm!(2),
            (false, 3) => slice_arm!(3),
            (false, 4) => slice_arm!(4),
            (false, 5) => slice_arm!(5),
            (false, 6) => slice_arm!(6),
            (true, 2) => tuple_arm!(0, 1),
            (true, 3) => tuple_arm!(0, 1, 2),
            (true, 4) => tuple_arm!(0, 1, 2, 3),
            // The tuple impls go higher, but there is nothing to learn from
            // arities the slice form already covers at the same width.
            _ => return None,
        }
    }
    Some(out)
}

/// A join of meets through `zipper_merge_dnf`.
///
/// The operand indices are compacted first: the clause masks are indices into
/// the array handed to the call, so an expression over operands `a` and `c`
/// becomes a two-zipper call with the masks renumbered, not a four-zipper call
/// with two unused slots -- an unused slot would change what the traversal
/// prunes on and make the route test something else.
fn dnf(e: &Expr, operands: &[PathMap<u64>]) -> Option<PathMap<u64>> {
    let clauses = e.dnf()?;
    let vars = e.vars();
    if vars.is_empty() || vars.len() > super::expr::MAX_VARS || clauses.len() > super::expr::MAX_CLAUSES {
        return None;
    }
    // Remap each clause's bits from operand index to position in `vars`.
    let packed: Vec<u64> = clauses
        .iter()
        .map(|m| {
            vars.iter()
                .enumerate()
                .filter(|(_, v)| m >> **v & 1 == 1)
                .fold(0u64, |acc, (i, _)| acc | 1 << i)
        })
        .collect();

    let mut out = PathMap::new();
    {
        let mut wz = out.write_zipper();
        macro_rules! dnf_arm {
            ($n:literal, $m:literal) => {{
                let mut zs: [ReadZipperUntracked<'_, '_, u64>; $n] =
                    core::array::from_fn(|i| operands[vars[i]].read_zipper());
                let cs: [Clause<$n>; $m] = core::array::from_fn(|i| Clause::from_mask(packed[i]));
                zipper_merge_dnf(&mut zs, cs, &mut wz);
            }};
        }
        macro_rules! dnf_m {
            ($n:literal) => {
                match packed.len() {
                    1 => dnf_arm!($n, 1),
                    2 => dnf_arm!($n, 2),
                    3 => dnf_arm!($n, 3),
                    4 => dnf_arm!($n, 4),
                    _ => return None,
                }
            };
        }
        match vars.len() {
            1 => dnf_m!(1),
            2 => dnf_m!(2),
            3 => dnf_m!(3),
            4 => dnf_m!(4),
            _ => return None,
        }
    }
    Some(out)
}
