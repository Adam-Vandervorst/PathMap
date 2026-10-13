//! Regression gate for the algebraic equivalence fuzzer.
//!
//! Three things, cheap enough for `cargo test`:
//!
//! * the committed corpus still reproduces only what `KNOWN` documents;
//! * a short random sweep from a fixed seed turns up nothing new;
//! * the expression recognisers that decide which route applies to which shape
//!   agree with what the n-ary and DNF entry points actually compute.
//!
//! The last one is not incidental.  Both recognisers were wrong when this
//! fuzzer was first run, and both failures looked exactly like crate defects:
//! flattening `a ^ (b ^ c)` into the n-ary call, which folds values left, and
//! letting a DNF clause stand for `b & a` when a clause is an unordered set and
//! `pmeet` is left-biased.  A harness that reports its own mistakes as findings
//! is worse than no harness, so the recognisers are pinned here.

use differential::algebraic::{
    self,
    expr::{Expr, Op},
    known, signatures,
    value::{Bits, FuzzValue},
};
use pathmap::ring::{AlgebraicResult, DistributiveLattice, Lattice};

/// Collect the signatures an input produces that `KNOWN` does not document.
///
/// Returns them rather than asserting, because `install_panic_hook` silences
/// the panic hook for the duration -- which is the point, since the inputs make
/// `pathmap` panic -- and a silenced hook would swallow the assertion message
/// too.  So every caller gathers first, restores the hook, then asserts.
fn unknown_signatures(bytes: &[u8]) -> Vec<String> {
    signatures(bytes).into_iter().filter(|s| known(s).is_none()).collect()
}

fn complain(found: &[(String, String)]) -> String {
    let mut m = String::from("unexpected signature(s):\n");
    for (sig, where_) in found {
        m.push_str(&format!("  {sig}  from {where_}\n"));
    }
    m.push_str(
        "\nIf a defect was just fixed, drop its entry from algebraic::KNOWN.\n\
         If it is new, shrink it with\n\
         \x20 cargo run --release -p differential --bin alg_fuzz -- \\\n\
         \x20     --shrink <input> --target <signature>\n\
         and add a reproducer to bin/alg_bug_repros.rs.\n",
    );
    m
}

/// Serialises the tests that install a panic hook.
///
/// `set_hook` and `take_hook` are process-global while `cargo test` runs tests
/// on several threads, so two of these running at once interleave: one restores
/// the default hook under the other, the other's panics stop being recorded,
/// and the signature it reports is whatever site was recorded last.  That shows
/// up as a phantom unexpected signature in whichever test lost the race.
static PANIC_HOOK: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Run `f` with the fuzzer's panic hook installed, restoring the previous hook
/// afterwards so a later assertion can still report itself.
fn with_quiet_panics<T>(f: impl FnOnce() -> T) -> T {
    // A failing test panics *outside* this function, so the lock is never
    // poisoned by the assertion itself -- but `f` runs code that panics by
    // design, so recover from poisoning rather than propagating it.
    let _guard = PANIC_HOOK.lock().unwrap_or_else(|e| e.into_inner());
    let prev = std::panic::take_hook();
    algebraic::install_panic_hook();
    let out = f();
    std::panic::set_hook(prev);
    out
}

#[test]
fn corpus_reproduces_only_known_findings() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/algebraic-corpus");
    let (seen, found) = with_quiet_panics(|| {
        let mut seen = 0;
        let mut found = Vec::new();
        for entry in std::fs::read_dir(dir).expect("corpus directory") {
            let path = entry.expect("corpus entry").path();
            if path.extension().is_none_or(|e| e != "bin") {
                continue;
            }
            let bytes = std::fs::read(&path).expect("corpus file");
            for sig in unknown_signatures(&bytes) {
                found.push((sig, path.display().to_string()));
            }
            seen += 1;
        }
        (seen, found)
    });
    assert!(seen > 0, "corpus is empty: {dir}");
    assert!(found.is_empty(), "{}", complain(&found));
}

#[test]
fn random_sweep_turns_up_nothing_new() {
    // Small, because this runs unoptimised under `cargo test` and is only a
    // tripwire.  The real sweep is `alg_fuzz --random`, which does a million
    // cases in under twenty seconds.
    const CASES: usize = 5_000;
    let found = with_quiet_panics(|| {
        let mut rng = algebraic::Rng::for_job(20261002, 0);
        let mut found = Vec::new();
        for i in 0..CASES {
            let bytes = rng.input();
            for sig in unknown_signatures(&bytes) {
                found.push((sig, format!("case {i} of seed 20261002")));
            }
        }
        found
    });
    assert!(found.is_empty(), "{}", complain(&found));
}

// --------------------------------------------------- recogniser invariants

fn var(i: usize) -> Expr {
    Expr::Var(i)
}

#[test]
fn chain_flattens_left_nesting_for_every_chainable_operator() {
    for op in [Op::Join, Op::Meet, Op::Subtract, Op::SymDiff] {
        let e = Expr::bin(op, Expr::bin(op, var(0), var(1)), var(2));
        assert_eq!(e.chain(), Some((op, vec![0, 1, 2])), "{op:?} left-nested");
    }
}

#[test]
fn chain_rejects_right_nesting_where_the_n_ary_fold_would_differ() {
    // `zipper_n_subtract` is left-associative and the symmetric-difference fold
    // combines values left to right, so neither may be matched right-nested.
    for op in [Op::Subtract, Op::SymDiff] {
        let e = Expr::bin(op, var(0), Expr::bin(op, var(1), var(2)));
        assert_eq!(e.chain(), None, "{op:?} right-nested must not be a chain");
    }
    // Join and meet are left-biased in their values, so both nestings agree
    // with the fold and both are chains.
    for op in [Op::Join, Op::Meet] {
        let e = Expr::bin(op, var(0), Expr::bin(op, var(1), var(2)));
        assert_eq!(e.chain(), Some((op, vec![0, 1, 2])), "{op:?} right-nested");
    }
}

#[test]
fn chain_rejects_a_mixed_tree() {
    let e = Expr::bin(Op::Join, Expr::bin(Op::Meet, var(0), var(1)), var(2));
    assert_eq!(e.chain(), None);
}

#[test]
fn dnf_recognises_a_join_of_meets() {
    // (a & b) | c
    let e = Expr::bin(Op::Join, Expr::bin(Op::Meet, var(0), var(1)), var(2));
    assert_eq!(e.dnf(), Some(vec![0b011, 0b100]));
}

#[test]
fn dnf_rejects_a_clause_whose_operands_are_out_of_slot_order() {
    // A clause is a bitmask, so it cannot distinguish `b & a` from `a & b`,
    // and `pmeet` on u64 keeps the left value, so the two differ.
    assert_eq!(Expr::bin(Op::Meet, var(0), var(1)).dnf(), Some(vec![0b011]));
    assert_eq!(Expr::bin(Op::Meet, var(1), var(0)).dnf(), None);
}

#[test]
fn dnf_rejects_non_monotone_operators() {
    for op in [Op::Subtract, Op::SymDiff, Op::Restrict] {
        assert_eq!(Expr::bin(op, var(0), var(1)).dnf(), None, "{op:?}");
    }
}

/// The lawful value type has to actually be lawful, or every "real defect" the
/// comparison attributes to the crate could be its fault instead.
/// The `shape` class's characterisation, as `bin/alg_bug_repros` case 7 states it:
/// the lockstep traversals discard dangling structure and the whole-map
/// operations preserve it.
///
/// Pinned because the write-up had it backwards at first, and because if either
/// family changes, the right outcome is this test failing and the question being
/// settled -- not the claim quietly going stale.
#[test]
fn zipper_traversals_drop_dangling_paths_and_map_ops_keep_them() {
    use pathmap::experimental::zipper_algebra::{zipper_join, zipper_meet};
    use pathmap::zipper::{ZipperMoving, ZipperPath, ZipperWriting};
    use pathmap::PathMap;

    fn dangling(paths: &[&[u8]]) -> PathMap<u64> {
        let mut m = PathMap::new();
        let mut wz = m.write_zipper();
        for p in paths {
            wz.reset();
            wz.descend_to(*p);
            wz.create_path();
        }
        drop(wz);
        m
    }
    fn paths(m: &PathMap<u64>) -> Vec<Vec<u8>> {
        let mut z = m.read_zipper();
        let mut out = Vec::new();
        z.reset();
        while z.to_next_step() {
            out.push(z.path().to_vec());
        }
        out
    }

    let d2 = dangling(&[&[0], &[1]]);
    let dv = {
        let mut m = dangling(&[&[0, 0]]);
        m.write_zipper_at_path(&[1]).set_val(7);
        m
    };

    let mut zj = PathMap::<u64>::new();
    {
        let (mut a, mut b) = (d2.read_zipper(), dv.read_zipper());
        let mut wz = zj.write_zipper();
        zipper_join(&mut a, &mut b, &mut wz);
    }
    // The traversal keeps only the path that carries a value.
    assert_eq!(paths(&zj), vec![vec![1]]);
    // The whole-map operation keeps the dangling structure too.
    assert_eq!(paths(&d2.join(&dv)), vec![vec![0], vec![0, 0], vec![1]]);

    let mut zm = PathMap::<u64>::new();
    {
        let (mut a, mut b) = (d2.read_zipper(), dv.read_zipper());
        let mut wz = zm.write_zipper();
        zipper_meet(&mut a, &mut b, &mut wz);
    }
    assert!(paths(&zm).is_empty());
    assert_eq!(paths(&d2.meet(&dv)), vec![vec![0], vec![1]]);

    // The write-zipper forms side with the whole-map operations.
    let mut wi = d2.clone();
    {
        let mut wz = wi.write_zipper();
        wz.meet_into(&dv.read_zipper(), false);
    }
    assert_eq!(paths(&wi), paths(&d2.meet(&dv)));
}

/// The zipper algebra over `PathMap<()>`, which `zipper_algebra.rs` does not
/// test at all -- every test there uses `u64`.
///
/// `()` is lawful, so these are plain set operations and the expected answers
/// are not open to interpretation.  Spelled out rather than compared against
/// `PathMap::join` and friends, because those have defects of their own.
#[test]
fn zipper_algebra_over_the_unit_type() {
    use pathmap::experimental::zipper_algebra::{
        zipper_join, zipper_meet, zipper_n_meet, zipper_n_sym_diff, zipper_subtract,
        zipper_sym_diff,
    };
    use pathmap::zipper::{ZipperMoving, ZipperPath, ZipperValues};
    use pathmap::PathMap;

    fn mk(paths: &[&[u8]]) -> PathMap<()> {
        let mut m = PathMap::new();
        for p in paths {
            m.set_val_at(p, ());
        }
        m
    }
    fn set(m: &PathMap<()>) -> Vec<Vec<u8>> {
        let mut z = m.read_zipper();
        let mut out = Vec::new();
        z.reset();
        while z.to_next_step() {
            if z.val().is_some() {
                out.push(z.path().to_vec());
            }
        }
        out
    }

    let a = mk(&[&[0, 1], &[0, 2], &[3]]);
    let b = mk(&[&[0, 2], &[3], &[4]]);
    let c = mk(&[&[0, 2], &[5]]);

    macro_rules! pair {
        ($f:ident) => {{
            let mut out = PathMap::<()>::new();
            {
                let (mut za, mut zb) = (a.read_zipper(), b.read_zipper());
                let mut wz = out.write_zipper();
                $f(&mut za, &mut zb, &mut wz);
            }
            set(&out)
        }};
    }
    assert_eq!(pair!(zipper_join), vec![vec![0, 1], vec![0, 2], vec![3], vec![4]]);
    assert_eq!(pair!(zipper_meet), vec![vec![0, 2], vec![3]]);
    assert_eq!(pair!(zipper_subtract), vec![vec![0, 1]]);
    // Present in exactly one side.
    assert_eq!(pair!(zipper_sym_diff), vec![vec![0, 1], vec![4]]);

    macro_rules! triple {
        ($f:ident) => {{
            let mut out = PathMap::<()>::new();
            {
                let mut zs = [a.read_zipper(), b.read_zipper(), c.read_zipper()];
                let mut wz = out.write_zipper();
                $f(&mut zs, &mut wz);
            }
            set(&out)
        }};
    }
    // Only [0,2] is in all three.
    assert_eq!(triple!(zipper_n_meet), vec![vec![0, 2]]);
    // Odd number of occurrences: [0,1] in one, [0,2] in three, [3] in two, [4]
    // and [5] in one each.
    assert_eq!(
        triple!(zipper_n_sym_diff),
        vec![vec![0, 1], vec![0, 2], vec![4], vec![5]]
    );
}

#[test]
fn bits_is_a_boolean_algebra() {
    let sample: Vec<Bits> = (1u64..16).map(Bits).collect();
    let r = |x: AlgebraicResult<Bits>, l: Bits, rr: Bits| match x {
        AlgebraicResult::Element(v) => Some(v),
        // SELF_IDENT == 1
        AlgebraicResult::Identity(m) => Some(if m & 1 != 0 { l } else { rr }),
        AlgebraicResult::None => None,
    };
    let raw = |v: Option<Bits>| v.map(|b| b.0).unwrap_or(0);

    for &a in &sample {
        for &b in &sample {
            // The operations are the bitwise ones, and bottom is absence.
            assert_eq!(raw(r(a.pjoin(&b), a, b)), a.0 | b.0, "join {a:?} {b:?}");
            assert_eq!(raw(r(a.pmeet(&b), a, b)), a.0 & b.0, "meet {a:?} {b:?}");
            assert_eq!(raw(r(a.psubtract(&b), a, b)), a.0 & !b.0, "sub {a:?} {b:?}");
            // Commutative, which is exactly what makes the u64 value bias
            // invisible here and so must hold.
            assert_eq!(a.0 | b.0, b.0 | a.0);
            assert_eq!(a.0 & b.0, b.0 & a.0);
            // The two formulas for symmetric difference agree -- the identity
            // whose failure under u64 started this.
            assert_eq!((a.0 | b.0) & !(a.0 & b.0), (a.0 & !b.0) | (b.0 & !a.0));
            for &c in &sample {
                // Distributive, both ways round.
                assert_eq!(a.0 & (b.0 | c.0), (a.0 & b.0) | (a.0 & c.0));
                assert_eq!(a.0 | (b.0 & c.0), (a.0 | b.0) & (a.0 | c.0));
            }
        }
    }
}

/// The reason for preferring a bitmask over some other lawful lattice: it has to
/// produce values that are not simply one of the operands, or the code that
/// stores a combined value is never reached.  See `bin/alg_lattice_check`.
#[test]
fn bits_reaches_the_element_path_and_u64_does_not() {
    let bits: Vec<Bits> = (1u64..16).map(Bits).collect();
    let mut bits_join_element = false;
    let mut bits_meet_element = false;
    for &a in &bits {
        for &b in &bits {
            bits_join_element |= matches!(a.pjoin(&b), AlgebraicResult::Element(_));
            bits_meet_element |= matches!(a.pmeet(&b), AlgebraicResult::Element(_));
        }
    }
    assert!(bits_join_element, "Bits::pjoin must be able to return Element");
    assert!(bits_meet_element, "Bits::pmeet must be able to return Element");

    // u64 cannot, which is the coverage gap the lawful type exists to close.
    for a in 1u64..8 {
        for b in 1u64..8 {
            assert!(!matches!(a.pjoin(&b), AlgebraicResult::Element(_)));
            assert!(!matches!(a.pmeet(&b), AlgebraicResult::Element(_)));
        }
    }
}

/// Route `k` must mean the same strategies under every value type, or the
/// per-type comparison compares different things.
#[test]
fn route_numbering_is_the_same_for_every_value_type() {
    for op in Op::ALL {
        let n = algebraic::routes::strategies(op).len();
        for k in 0..algebraic::routes::POINTWISE_ROUTES {
            // `strategies` takes no type parameter precisely so this holds; the
            // assertion is here to stop that being reintroduced.
            assert_eq!(k % n, k % algebraic::routes::strategies(op).len());
        }
    }
    assert!(<Bits as FuzzValue>::LAWFUL);
    assert!(<() as FuzzValue>::LAWFUL);
    assert!(!<u64 as FuzzValue>::LAWFUL);
    // The overlay join strategy cannot work for a type whose join creates
    // values, because OverlayZipper's mapping returns a reference.
    assert!(!<Bits as FuzzValue>::JOIN_PICKS_LEFT);
    assert!(<u64 as FuzzValue>::JOIN_PICKS_LEFT);
}

#[test]
fn every_strategy_index_is_reachable_from_some_pointwise_route() {
    // Route `k` picks strategy `k % n` per operator, so POINTWISE_ROUTES has to
    // be at least as large as the widest operator's strategy table or some
    // implementation would never be exercised.
    for op in Op::ALL {
        let n = algebraic::routes::strategies(op).len();
        assert!(
            n <= algebraic::routes::POINTWISE_ROUTES,
            "{op:?} has {n} strategies but only {} pointwise routes",
            algebraic::routes::POINTWISE_ROUTES
        );
        for s in 0..n {
            assert!(
                (0..algebraic::routes::POINTWISE_ROUTES).any(|k| k % n == s),
                "{op:?} strategy {s} is unreachable"
            );
        }
    }
}
