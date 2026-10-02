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

use differential::algebraic::{self, expr::{Expr, Op}, known, signatures};

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
