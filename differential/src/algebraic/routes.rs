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
    OverlayZipper, PrefixZipper, ReadZipperUntracked, SubtractZipper, Zipper,
    ZipperInfallibleSubtries, ZipperMoving, ZipperPath, ZipperValues, ZipperWriting,
};

use super::expr::{Expr, Kind, Op, Un};
use super::model;
use super::shape::{shape_of_map, shape_of_zipper, values_of_shape, Shape, Values, ESCAPED_ROOT, TRUNCATED};
use super::value::FuzzValue;

/// Names of the per-operator strategies, in the order route `k % n` indexes
/// them.  Kept as tables so a route's name can say which strategy it used for
/// each operator the expression contains.
pub const JOIN_STRATEGIES: &[&str] =
    &["map", "join_into", "join_map_into", "join_into_take", "zipper_join", "overlay"];
pub const MEET_STRATEGIES: &[&str] = &["map", "meet_into", "meet_2", "zipper_meet"];
pub const SUBTRACT_STRATEGIES: &[&str] = &["map", "subtract_into", "zipper_subtract"];
pub const SYM_DIFF_STRATEGIES: &[&str] = &["zipper_sym_diff", "join_minus_meet"];
pub const RESTRICT_STRATEGIES: &[&str] = &["map", "wz_restrict"];
pub const COMPOSE_STRATEGIES: &[&str] = &["join_map_into", "wrap_join"];
pub const ITER_C_STRATEGIES: &[&str] = &["val_count", "iter"];
pub const SINGLETON_STRATEGIES: &[&str] = &["single", "set_val"];
pub const WRAP_STRATEGIES: &[&str] = &["graft_map", "prefix_zipper", "insert_prefix"];
pub const UNWRAP_STRATEGIES: &[&str] = &["read_zipper_at_path", "descend_make_map", "take_map"];
pub const HEAD_STRATEGIES: &[&str] = &["child_mask", "iter"];
pub const TAILS_UNION_STRATEGIES: &[&str] = &["map", "join_map_into"];
pub const TAILS_INTER_STRATEGIES: &[&str] = &["map", "meet_into"];

/// The strategy table is the same for every value type, so route `k` means the
/// same thing under each of them.
///
/// That matters more than it looks.  An earlier version shortened the join table
/// for value types that cannot use the `OverlayZipper` strategy, which silently
/// renumbered every later route -- so `pw4` and `pw5` meant different strategy
/// mixes under `u64` and under `bits`, and comparing their findings across the
/// two types was comparing different things.  A strategy that does not apply to
/// a value type now *declines* instead, which leaves the numbering alone and
/// simply makes that route absent for that type.
pub fn strategies(op: Op) -> &'static [&'static str] {
    match op {
        Op::Join => JOIN_STRATEGIES,
        Op::Meet => MEET_STRATEGIES,
        Op::Subtract => SUBTRACT_STRATEGIES,
        Op::SymDiff => SYM_DIFF_STRATEGIES,
        Op::Restrict => RESTRICT_STRATEGIES,
        Op::Compose => COMPOSE_STRATEGIES,
        Op::IterC => ITER_C_STRATEGIES,
    }
}

/// [`strategies`] for any node kind, Zippy's unary ones included.
pub fn kind_strategies(kind: Kind) -> &'static [&'static str] {
    match kind {
        Kind::Op(op) => strategies(op),
        Kind::Singleton => SINGLETON_STRATEGIES,
        Kind::Wrap => WRAP_STRATEGIES,
        Kind::Unwrap => UNWRAP_STRATEGIES,
        Kind::Un(Un::Head) => HEAD_STRATEGIES,
        Kind::Un(Un::TailsUnion) => TAILS_UNION_STRATEGIES,
        Kind::Un(Un::TailsInter) => TAILS_INTER_STRATEGIES,
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
    /// Every subtraction through the lazy `SubtractZipper`, materialised, and
    /// every other operator through the baseline's whole-map call.
    ///
    /// A route of its own rather than a fourth subtract strategy: adding a
    /// strategy would renumber which mix each `pw#k` route uses, and a new
    /// finding would land under a `pw` signature `KNOWN` already attributes to
    /// another cause.  Holding the other operators at the baseline also means a
    /// divergence here can only come from `SubtractZipper`.
    SubtractZipper,
    /// Nested `SubtractZipper`s, materialised once at the end: a left spine of
    /// subtractions `x - y - z ...` with each zipper the left input of the
    /// next, or `x - (y - z)` with one as the right input.  This is the route
    /// that tests a `SubtractZipper` reading from another one.
    SubtractZipperNested,
    /// Flat `BTreeMap` semantics, no trie.  Values only; abstains on structure.
    Model,
}

impl Route {
    pub fn all() -> Vec<Route> {
        let mut v: Vec<Route> = (0..POINTWISE_ROUTES).map(Route::Pointwise).collect();
        v.extend([
            Route::Ternary,
            Route::Nary,
            Route::NaryPoly,
            Route::Dnf,
            Route::Model,
            Route::SubtractZipper,
            Route::SubtractZipperNested,
        ]);
        v
    }

    /// Name including, for a pointwise route, the strategy it picked for each
    /// operator the expression actually uses.  A failure report needs this to
    /// be actionable: "pw#3" alone does not name a function to go and read.
    pub fn name(&self, e: &Expr) -> String {
        match self {
            Route::Pointwise(k) => {
                let used = e.kinds();
                let picks: Vec<String> = Kind::ALL
                    .iter()
                    .filter(|kind| used.contains(kind))
                    .map(|kind| {
                        let t = kind_strategies(*kind);
                        format!("{}={}", kind.sym(), t[k % t.len()])
                    })
                    .collect();
                format!("pw#{k}[{}]", picks.join(","))
            }
            Route::Ternary => "ternary".into(),
            Route::Nary => "nary".into(),
            Route::NaryPoly => "nary_poly".into(),
            Route::Dnf => "dnf".into(),
            Route::Model => "model".into(),
            Route::SubtractZipper => "subtract_zipper".into(),
            Route::SubtractZipperNested => "subtract_zipper_nested".into(),
        }
    }
}

fn uses_op(e: &Expr, op: Op) -> bool {
    e.kinds().contains(&Kind::Op(op))
}

/// What a route produced.  `shape` is `None` for a route that cannot represent
/// dangling paths, which is only [`Route::Model`].
pub struct Outcome<V: FuzzValue> {
    pub values: Values<V>,
    pub shape: Option<Shape<V>>,
}

impl<V: FuzzValue> Outcome<V> {
    fn from_map(m: &PathMap<V>) -> Outcome<V> {
        let shape = shape_of_map(m);
        Outcome { values: values_of_shape(&shape), shape: Some(shape) }
    }
}

/// Evaluate `e` over `operands` by `route`, or `None` if the route does not
/// apply to this expression's shape.
pub fn eval<V: FuzzValue>(route: Route, e: &Expr, operands: &[PathMap<V>]) -> Option<Outcome<V>> {
    match route {
        Route::Pointwise(k) => pointwise(k, e, operands).map(|m| Outcome::from_map(&m)),
        Route::Ternary => ternary(e, operands).map(|m| Outcome::from_map(&m)),
        Route::Nary => nary(e, operands, false).map(|m| Outcome::from_map(&m)),
        Route::NaryPoly => nary(e, operands, true).map(|m| Outcome::from_map(&m)),
        Route::Dnf => dnf(e, operands).map(|m| Outcome::from_map(&m)),
        Route::Model => {
            let vals: Vec<Values<V>> =
                operands.iter().map(|m| values_of_shape(&shape_of_map(m))).collect();
            Some(Outcome { values: model::eval(e, &vals), shape: None })
        }
        Route::SubtractZipper => subtract_zipper(e, operands).map(|m| Outcome::from_map(&m)),
        Route::SubtractZipperNested => subtract_zipper_nested(e, operands).map(|m| Outcome::from_map(&m)),
    }
}

// ---------------------------------------------------------------- pointwise

/// `None` when the strategy route `k` selects for some operator in `e` does not
/// apply to this value type.
fn pointwise<V: FuzzValue>(k: usize, e: &Expr, operands: &[PathMap<V>]) -> Option<PathMap<V>> {
    walk(e, operands, &mut |op, a, b| apply(op, k, a, b), k)
}

/// Bottom-up evaluation with `bin` for the binary nodes and strategy `k` for
/// Zippy's unary ones.  Shared by every route that materialises intermediates,
/// so the unary nodes go through the same code whichever route reaches them.
fn walk<V: FuzzValue>(
    e: &Expr,
    operands: &[PathMap<V>],
    bin: &mut dyn FnMut(Op, &PathMap<V>, &PathMap<V>) -> Option<PathMap<V>>,
    k: usize,
) -> Option<PathMap<V>> {
    Some(match e {
        Expr::Var(i) => operands[*i].clone(),
        Expr::Empty => PathMap::new(),
        Expr::Singleton(p) => singleton(k, p),
        Expr::Bin(op, l, r) => {
            let a = walk(l, operands, bin, k)?;
            let b = walk(r, operands, bin, k)?;
            bin(*op, &a, &b)?
        }
        Expr::Wrap(p, e) => wrap(k, p, &walk(e, operands, bin, k)?),
        Expr::Unwrap(e, p) => unwrap(k, &walk(e, operands, bin, k)?, p),
        Expr::Un(u, e) => unary(*u, k, &walk(e, operands, bin, k)?),
    })
}

/// One operator, one strategy.  Every arm is a different code path in the
/// crate, not a different way of calling the same one.
pub fn apply<V: FuzzValue>(op: Op, k: usize, a: &PathMap<V>, b: &PathMap<V>) -> Option<PathMap<V>> {
    let n = strategies(op).len();
    Some(match (op, k % n) {
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
            // the other write-zipper forms rather than silently tidier.
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
            // Declines rather than answering wrongly: see
            // `FuzzValue::JOIN_PICKS_LEFT`.
            if !V::JOIN_PICKS_LEFT {
                return None;
            }
            // `OverlayZipper`'s default mapping is `a.or(b)`, which is the same
            // bias a left-picking `pjoin` has, so for such a value type the
            // virtual trie it walks is exactly the join.  Only reachable when
            // `V::JOIN_PICKS_LEFT`; see `strategies`.  It never builds a trie, so
            // it has to be materialised to be composed into a larger expression;
            // the walk records dangling paths too, so nothing is lost.
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

        // -- composition: `b` under every value path of `a`.  Visited in
        // `iter` order, ascending, so a path two copies land on is joined the
        // same way round as the model joins it.
        (Op::Compose, 0) => {
            // Zippy's own definition: `descend_to u`, `join_map_into t`.
            let mut out = PathMap::new();
            {
                let mut wz = out.write_zipper();
                for (u, _) in a.iter() {
                    wz.reset();
                    wz.descend_to(&u);
                    wz.join_map_into(b.clone());
                }
            }
            out
        }
        (Op::Compose, 1) => {
            let mut out = PathMap::new();
            for (u, _) in a.iter() {
                out = out.join(&wrap(0, &u, b));
            }
            out
        }

        // -- IterC: `b` when `a` has a value below its root.
        (Op::IterC, s) => {
            let below = if s == 0 {
                let rz = a.read_zipper();
                rz.val_count() > rz.is_val() as usize
            } else {
                a.iter().any(|(k, _)| !k.is_empty())
            };
            if below { b.clone() } else { PathMap::new() }
        }

        _ => unreachable!("strategy index out of range for {op:?}"),
    })
}

// ---------------------------------------------------------------- Zippy

/// `Singleton p`, carrying [`FuzzValue::canonical`].
fn singleton<V: FuzzValue>(k: usize, p: &[u8]) -> PathMap<V> {
    match k % SINGLETON_STRATEGIES.len() {
        0 => PathMap::single(p, V::canonical()),
        _ => {
            let mut out = PathMap::new();
            {
                let mut wz = out.write_zipper();
                wz.descend_to(p);
                wz.set_val(V::canonical());
            }
            out
        }
    }
}

/// `Wrap p s`.
fn wrap<V: FuzzValue>(k: usize, p: &[u8], s: &PathMap<V>) -> PathMap<V> {
    match k % WRAP_STRATEGIES.len() {
        0 => {
            // Zippy's definition: `descend_to p` in an empty map, `graft_map s`.
            // With `graft_root_vals` (a default feature) the root value moves too.
            let mut out = PathMap::new();
            {
                let mut wz = out.write_zipper();
                wz.descend_to(p);
                wz.graft_map(s.clone());
            }
            out
        }
        1 => materialize(PrefixZipper::new(p.to_vec(), s.read_zipper())),
        _ => {
            // `insert_prefix` moves the node and, by its documentation, leaves
            // the focus value where it is (Zippy §10, `rawWrap_ne_wrap`).  So
            // that value is moved by hand, and what this tests is the node move.
            let mut out = s.clone();
            {
                let mut wz = out.write_zipper();
                let root = wz.remove_val(false);
                wz.insert_prefix(p);
                if let Some(v) = root {
                    wz.descend_to(p);
                    wz.set_val(v);
                }
            }
            out
        }
    }
}

/// `Unwrap s p`: the subtrie at `p`, its value included.
fn unwrap<V: FuzzValue>(k: usize, s: &PathMap<V>, p: &[u8]) -> PathMap<V> {
    match k % UNWRAP_STRATEGIES.len() {
        0 => s.read_zipper_at_path(p).make_map(),
        1 => {
            let mut rz = s.read_zipper();
            rz.descend_to(p);
            rz.make_map()
        }
        _ => {
            let mut src = s.clone();
            let mut wz = src.write_zipper();
            wz.descend_to(p);
            wz.take_map(false).unwrap_or_default()
        }
    }
}

/// The bytes one level down that lead to a value, ascending.
///
/// Strategy 0 reads `child_mask` and checks each child for a value; strategy 1
/// collects first bytes from `iter`.  A child that is dangling-only is in the
/// mask and not in a Zippy space, so it is dropped: the dangling-path question
/// is `shape.rs`'s, and letting it in here would turn it into a value
/// divergence.
fn heads<V: FuzzValue>(k: usize, s: &PathMap<V>) -> Vec<u8> {
    if k % 2 == 0 {
        let rz = s.read_zipper();
        rz.child_mask()
            .iter()
            .filter(|b| s.read_zipper_at_path([*b]).val_count() > 0)
            .collect()
    } else {
        let mut hs: Vec<u8> = s.iter().filter_map(|(p, _)| p.first().copied()).collect();
        hs.dedup();
        hs
    }
}

fn unary<V: FuzzValue>(u: Un, k: usize, s: &PathMap<V>) -> PathMap<V> {
    match u {
        Un::Head => {
            let hs = heads(k % HEAD_STRATEGIES.len(), s);
            let mut out = PathMap::new();
            for b in hs {
                out.set_val_at([b], V::canonical());
            }
            out
        }
        Un::TailsUnion => {
            let hs = heads(k, s);
            let tail = |b: u8| s.read_zipper_at_path([b]).make_map();
            if k % TAILS_UNION_STRATEGIES.len() == 0 {
                hs.into_iter().fold(PathMap::new(), |acc, b| acc.join(&tail(b)))
            } else {
                // Zippy's definition: `join_map_into` at the root, one child at
                // a time.
                let mut out = PathMap::new();
                {
                    let mut wz = out.write_zipper();
                    for b in hs {
                        wz.join_map_into(tail(b));
                    }
                }
                out
            }
        }
        Un::TailsInter => {
            let mut hs = heads(k, s).into_iter();
            let tail = |b: u8| s.read_zipper_at_path([b]).make_map();
            let Some(first) = hs.next() else { return PathMap::new() };
            if k % TAILS_INTER_STRATEGIES.len() == 0 {
                hs.fold(tail(first), |acc, b| acc.meet(&tail(b)))
            } else {
                let mut out = tail(first);
                {
                    let mut wz = out.write_zipper();
                    for b in hs {
                        let t = tail(b);
                        wz.meet_into(&t.read_zipper(), false);
                    }
                }
                out
            }
        }
    }
}

/// Walk a zipper over a virtual trie and build the real trie it describes.
///
/// `create_path` is what keeps this faithful: a path with no value still has to
/// appear in the output, or materialising would quietly erase exactly the
/// dangling structure the comparison is trying to detect.
fn materialize<V: FuzzValue, Z>(mut z: Z) -> PathMap<V>
where
    Z: ZipperMoving + ZipperPath + ZipperValues<V>,
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
                    wz.set_val(v.clone());
                }
                None => {
                    wz.create_path();
                }
            }
        }
    }
    out
}

/// [`Route::SubtractZipper`].  `None` when `e` has no subtraction, because the
/// route would then be the baseline over again.
fn subtract_zipper<V: FuzzValue>(e: &Expr, operands: &[PathMap<V>]) -> Option<PathMap<V>> {
    let mut bin = |op: Op, a: &PathMap<V>, b: &PathMap<V>| {
        Some(if op == Op::Subtract {
            materialize(SubtractZipper::new(a.read_zipper(), b.read_zipper()))
        } else {
            apply(op, 0, a, b).expect("strategy 0 applies to every value type")
        })
    };
    if !uses_op(e, Op::Subtract) {
        return None;
    }
    walk(e, operands, &mut bin, 0)
}

// -------------------------------------------------------- whole-expression

/// [`Route::SubtractZipperNested`].
///
/// The expression's left spine of subtractions, `x0 - x1 - ... - xk`, becomes
/// `k` nested zippers when `k >= 2`.  With a single subtraction whose right
/// operand is itself one, `x - (y - z)`, the inner zipper is the right input
/// instead.  The `x`s may be any subexpression; they go through the baseline.
fn subtract_zipper_nested<V: FuzzValue>(e: &Expr, operands: &[PathMap<V>]) -> Option<PathMap<V>> {
    let mut spine: Vec<&Expr> = Vec::new();
    let mut cur = e;
    while let Expr::Bin(Op::Subtract, l, r) = cur {
        spine.push(r);
        cur = l;
    }
    spine.push(cur);
    spine.reverse();
    let base = |x: &Expr| pointwise(0, x, operands).expect("strategy 0 applies to every value type");

    if spine.len() == 2 {
        let Expr::Bin(Op::Subtract, y, z) = spine[1] else { return None };
        let (x, y, z) = (base(spine[0]), base(y), base(z));
        let rhs = SubtractZipper::new(y.read_zipper(), z.read_zipper());
        return Some(materialize(SubtractZipper::new(x.read_zipper(), rhs)));
    }

    let maps: Vec<PathMap<V>> = spine.iter().map(|x| base(x)).collect();
    let rz = |i: usize| maps[i].read_zipper();
    // Each level of nesting is a different type, so the chain is spelled out
    // per length.
    macro_rules! nest {
        ($z:expr) => { $z };
        ($z:expr, $next:expr $(, $rest:expr)*) => {
            nest!(SubtractZipper::new($z, $next) $(, $rest)*)
        };
    }
    Some(match maps.len() {
        3 => materialize(nest!(rz(0), rz(1), rz(2))),
        4 => materialize(nest!(rz(0), rz(1), rz(2), rz(3))),
        5 => materialize(nest!(rz(0), rz(1), rz(2), rz(3), rz(4))),
        6 => materialize(nest!(rz(0), rz(1), rz(2), rz(3), rz(4), rz(5))),
        _ => return None,
    })
}

/// Chain of exactly three operands through the `*3` entry points.
fn ternary<V: FuzzValue>(e: &Expr, operands: &[PathMap<V>]) -> Option<PathMap<V>> {
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
            Op::Restrict | Op::Compose | Op::IterC => return None,
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
fn nary<V: FuzzValue>(e: &Expr, operands: &[PathMap<V>], poly: bool) -> Option<PathMap<V>> {
    let (op, idx) = e.chain()?;
    if !matches!(op, Op::Join | Op::Meet | Op::Subtract | Op::SymDiff) {
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
                let mut zs: [ReadZipperUntracked<'_, '_, V>; $n] =
                    core::array::from_fn(|i| operands[idx[i]].read_zipper());
                match op {
                    Op::Join => zipper_n_join(&mut zs, &mut wz),
                    Op::Meet => zipper_n_meet(&mut zs, &mut wz),
                    Op::Subtract => zipper_n_subtract(&mut zs, &mut wz),
                    Op::SymDiff => zipper_n_sym_diff(&mut zs, &mut wz),
                    Op::Restrict | Op::Compose | Op::IterC => unreachable!(),
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
                    Op::Restrict | Op::Compose | Op::IterC => unreachable!(),
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
fn dnf<V: FuzzValue>(e: &Expr, operands: &[PathMap<V>]) -> Option<PathMap<V>> {
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
                let mut zs: [ReadZipperUntracked<'_, '_, V>; $n] =
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
