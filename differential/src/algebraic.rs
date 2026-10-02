//! Equivalence fuzzer for the algebraic operations.
//!
//! The other two fuzzers in this crate ask *is the answer right?* -- the Lean
//! model in `../lean` is an oracle, and `bin/pathmap_trace.rs` is diffed
//! against it.  This one asks a different question: **does it matter which way
//! you compute it?**  It should not, and `pathmap` offers enough different ways
//! that the question has teeth.
//!
//! Each case is one algebraic expression over a few generated operand tries,
//! evaluated by every route in `routes.rs` that applies to it -- eagerly on
//! whole maps, in place through a write zipper, as a lockstep traversal of two
//! read zippers, as a single n-ary traversal, through the DNF engine, through a
//! lazy `OverlayZipper` over a virtual trie, and over a flat `BTreeMap` with no
//! trie at all.  Then `laws.rs` evaluates pairs of expressions that must agree
//! whatever the operands, which catches the mistakes every route shares.
//!
//! No Lean build is needed and there is no oracle: a divergence says the
//! implementations disagree, not which one is wrong.
//!
//! The wire format here is **not** the one `harness.rs` shares with
//! `PathMapModel.Fuzz`; this fuzzer has no model to stay in step with, so its
//! inputs are free to be whatever generates interesting tries.  It does reuse
//! `harness::Dec` for byte decoding.
//!
//! See `../ALGEBRAIC_FUZZING.md`.

pub mod expr;
pub mod laws;
pub mod model;
pub mod routes;
pub mod shape;

use pathmap::PathMap;
use pathmap::zipper::{ZipperMoving, ZipperWriting};

use crate::harness::Dec;
use expr::{Expr, Op, MAX_VARS};
use laws::{Level, EMPTY, LAW_OPERANDS};
use routes::Route;
use shape::{shape_of_map, show_shape, Shape, Values};

/// Operand tries per case.  Fixed rather than generated so the expression
/// generator can always name any of them, and so [`MAX_VARS`] is the only
/// bound the const-generic route dispatch has to respect.
pub const OPERANDS: usize = MAX_VARS;

/// Upper bound on entries written into one operand.  Small on purpose: the
/// interesting cases are the ones where operands overlap at a node boundary,
/// and small tries over a small alphabet collide far more often than large
/// ones.
pub const MAX_ENTRIES: usize = 7;

/// Upper bound on a generated path's length.
pub const MAX_PATH_LEN: usize = 5;

/// Distinct values in circulation.  Deliberately tiny: `psubtract` on `u64` is
/// `None` only when the two values are *equal*, and symmetric difference
/// cancels on coincident paths, so a large value space would make both
/// operations degenerate into set difference and set union and never exercise
/// the value-combining paths at all.
pub const VALUES: u64 = 3;

/// Byte decoding with the out-of-input behaviour this fuzzer wants.
///
/// `harness::Dec` returns `None` when the input runs out, because the Lean
/// harness stops executing there.  Here every input has to decode to *some*
/// case or shrinking would have to care about length, so exhaustion saturates
/// to zero instead.
pub struct Gen<'a> {
    dec: Dec<'a>,
    /// Size of the path alphabet.  A small one makes operands share prefixes
    /// and collide; the full 256 exercises wide nodes.
    alphabet: u16,
}

impl<'a> Gen<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Gen { dec: Dec { bytes, pos: 0 }, alphabet: 3 }
    }
    pub fn byte(&mut self) -> u8 {
        self.dec.u8().unwrap_or(0)
    }
    pub fn modn(&mut self, m: usize) -> usize {
        if m == 0 { 0 } else { self.byte() as usize % m }
    }
    pub fn boolean(&mut self) -> bool {
        self.byte() % 2 == 1
    }
    /// True with probability `pct`/100.
    pub fn chance(&mut self, pct: u8) -> bool {
        (self.byte() as u16 * 100 / 256) < pct as u16
    }
    pub fn path_byte(&mut self) -> u8 {
        (self.byte() as u16 % self.alphabet) as u8
    }
    pub fn path(&mut self, max_len: usize) -> Vec<u8> {
        let n = self.modn(max_len + 1);
        (0..n).map(|_| self.path_byte()).collect()
    }
    pub fn val(&mut self) -> u64 {
        self.byte() as u64 % VALUES + 1
    }
}

/// How one operand trie was built.  Recorded so a failure report can say
/// whether the case depended on structural sharing or on node layout, which is
/// the difference between a logic bug and a representation bug.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Build {
    /// Entries written into a fresh map.
    Fresh,
    /// A clone of an earlier operand, then mutated.  Clones share nodes, so
    /// this is how a case gets two operands whose subtries are the *same*
    /// allocation rather than merely equal -- the distinction several of the
    /// defects in `../lean/FINDINGS.md` turned on.
    CloneOf(usize),
    /// The same `(path, value)` entries as an earlier operand, rewritten into a
    /// fresh map in a different order.  Equal content, possibly different node
    /// layout and certainly no shared nodes: the counterpart to `CloneOf`, and
    /// the shape that catches an operation whose answer depends on how its
    /// input happens to be stored.
    ReinsertOf(usize),
    /// A clone of an earlier operand with `merkleize` run over it, which
    /// factors equal subtries into one shared allocation.
    MerkleizedOf(usize),
}

pub struct Case {
    pub expr: Expr,
    pub operands: Vec<PathMap<u64>>,
    pub builds: Vec<Build>,
    pub alphabet: u16,
}

/// Decode a byte string into a case.  Total: every input decodes.
pub fn decode(bytes: &[u8]) -> Case {
    let mut g = Gen::new(bytes);
    // A 3-letter alphabet is the default because collisions are the point; the
    // wider ones are sampled to keep node-type coverage honest, since `pathmap`
    // switches node representation on child count.
    g.alphabet = match g.modn(10) {
        0 => 256,
        1 => 16,
        2 => 2,
        _ => 3,
    };
    let alphabet = g.alphabet;

    let mut operands: Vec<PathMap<u64>> = Vec::with_capacity(OPERANDS);
    let mut builds: Vec<Build> = Vec::with_capacity(OPERANDS);
    for i in 0..OPERANDS {
        let build = pick_build(&mut g, i);
        operands.push(build_operand(&mut g, build, &operands));
        builds.push(build);
    }

    let expr = gen_expr(&mut g, 3);
    Case { expr, operands, builds, alphabet }
}

fn pick_build(g: &mut Gen, i: usize) -> Build {
    if i == 0 {
        return Build::Fresh;
    }
    match g.modn(8) {
        0 | 1 | 2 | 3 => Build::Fresh,
        4 | 5 => Build::CloneOf(g.modn(i)),
        6 => Build::ReinsertOf(g.modn(i)),
        _ => Build::MerkleizedOf(g.modn(i)),
    }
}

fn build_operand(g: &mut Gen, build: Build, prior: &[PathMap<u64>]) -> PathMap<u64> {
    match build {
        Build::Fresh => fresh(g),
        Build::CloneOf(j) => {
            let mut m = prior[j].clone();
            mutate(g, &mut m);
            m
        }
        Build::ReinsertOf(j) => {
            // Collect the entries, then write them back in a rotated order.
            // Rotation rather than a full shuffle because it is enough to
            // change which insert splits which node, and it keeps the decoding
            // cost one byte.
            let entries: Vec<(Vec<u8>, u64)> =
                shape::values_of_shape(&shape_of_map(&prior[j])).into_iter().collect();
            let mut out = PathMap::new();
            if !entries.is_empty() {
                let r = g.modn(entries.len());
                let mut wz = out.write_zipper();
                for off in 0..entries.len() {
                    let (p, v) = &entries[(off + r) % entries.len()];
                    wz.reset();
                    wz.descend_to(p);
                    wz.set_val(*v);
                }
            }
            out
        }
        Build::MerkleizedOf(j) => {
            let mut m = prior[j].clone();
            m.merkleize();
            mutate(g, &mut m);
            m
        }
    }
}

fn fresh(g: &mut Gen) -> PathMap<u64> {
    let n = g.modn(MAX_ENTRIES + 1);
    let mut out = PathMap::new();
    {
        let mut wz = out.write_zipper();
        for _ in 0..n {
            let p = g.path(MAX_PATH_LEN);
            wz.reset();
            wz.descend_to(&p);
            // A path written with `create_path` and no value is a dangling
            // path: structure with nothing under it.  Operations disagree about
            // whether those survive, so they are generated on purpose and the
            // comparison reports them as their own class.
            if g.chance(20) {
                wz.create_path();
            } else {
                wz.set_val(g.val());
            }
        }
    }
    out
}

fn mutate(g: &mut Gen, m: &mut PathMap<u64>) {
    let n = g.modn(3);
    let mut wz = m.write_zipper();
    for _ in 0..n {
        let p = g.path(MAX_PATH_LEN);
        wz.reset();
        wz.descend_to(&p);
        match g.modn(4) {
            0 => {
                wz.remove_val(false);
            }
            1 => {
                wz.create_path();
            }
            2 => {
                wz.remove_branches(false);
            }
            _ => {
                wz.set_val(g.val());
            }
        }
    }
}

fn gen_expr(g: &mut Gen, depth: usize) -> Expr {
    // Leaf at depth 0, and otherwise often enough that the chain and DNF
    // recognisers fire regularly -- a tree that is always maximally deep is
    // never a chain of operands, so the whole-expression routes would almost
    // never apply.
    if depth == 0 || g.chance(35) {
        return Expr::Var(g.modn(OPERANDS));
    }
    let op = match g.modn(12) {
        0 | 1 | 2 | 3 => Op::Join,
        4 | 5 | 6 => Op::Meet,
        7 | 8 => Op::Subtract,
        9 | 10 => Op::SymDiff,
        _ => Op::Restrict,
    };
    Expr::bin(op, gen_expr(g, depth - 1), gen_expr(g, depth - 1))
}

// ------------------------------------------------------------- comparison

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Class {
    /// Two routes put different values on a path, or disagree about whether a
    /// path carries one.  Settled semantics: one of them is wrong.
    Values,
    /// Two routes agree on every value and differ only in dangling paths --
    /// structure with nothing under it.  Unsettled semantics (see
    /// `../SPEC_WARTS.md`), so this is reported apart from `Values` rather than
    /// mixed in with it.
    Shape,
    /// An identity that must hold whatever the operands are does not.
    Law,
}

impl Class {
    pub fn tag(self) -> &'static str {
        match self {
            Class::Values => "values",
            Class::Shape => "shape",
            Class::Law => "law",
        }
    }
}

pub struct Divergence {
    pub class: Class,
    /// Stable short key for grouping findings across runs: the class and the
    /// route, and nothing else.
    ///
    /// Coarse on purpose.  An earlier version appended the operators the
    /// expression used, which looked more informative and was much worse: one
    /// root cause in `meet` produced dozens of signatures because it surfaced
    /// under every combination of operators that happened to contain a meet,
    /// and a known-findings table over them was unmaintainable.  The operators,
    /// the operands and the diff all live in `detail`; the signature's only job
    /// is to collapse a million inputs onto a handful of lines.
    pub signature: String,
    pub detail: String,
}

/// Evaluate every applicable route and every law, and return what disagrees.
///
/// The baseline every route is compared against is `Pointwise(0)` -- the whole
/// expression through `PathMap::join`/`meet`/`subtract`/`restrict`.  Those are
/// the oldest and most heavily used entry points in the crate, which makes them
/// the right thing to hold still, though the choice only affects which side of
/// a disagreement gets named, not whether it is found.
pub fn check(case: &Case) -> Vec<Divergence> {
    let mut out = Vec::new();

    let baseline_route = Route::Pointwise(0);
    let baseline = routes::eval(baseline_route, &case.expr, &case.operands)
        .expect("the pointwise route applies to every expression");
    let base_name = baseline_route.name(&case.expr);

    for route in Route::all() {
        if route == baseline_route {
            continue;
        }
        let Some(got) = routes::eval(route, &case.expr, &case.operands) else { continue };
        let name = route.name(&case.expr);

        if got.values != baseline.values {
            out.push(Divergence {
                class: Class::Values,
                signature: format!("values:{}", route_key(route)),
                detail: format!(
                    "{} vs {name} evaluating {}: {}\n  {base_name}: {}\n  {name}: {}",
                    base_name,
                    case.expr,
                    shape::first_values_diff(&baseline.values, &got.values).unwrap_or_default(),
                    shape::show_values(&baseline.values),
                    shape::show_values(&got.values),
                ),
            });
            // One class per route is enough; a value divergence will usually
            // show up as a shape divergence too, and reporting both would
            // double every finding.
            continue;
        }

        if let (Some(bs), Some(gs)) = (&baseline.shape, &got.shape) {
            if bs != gs {
                out.push(Divergence {
                    class: Class::Shape,
                    signature: format!("shape:{}", route_key(route)),
                    detail: format!(
                        "{} vs {name} evaluating {}: {}\n  {base_name}: {}\n  {name}: {}",
                        base_name,
                        case.expr,
                        shape::first_shape_diff(bs, gs).unwrap_or_default(),
                        show_shape(bs),
                        show_shape(gs),
                    ),
                });
            }
        }
    }

    out.extend(check_laws(case));
    out
}

/// Evaluate each law's two sides and report the ones that disagree.
///
/// Laws run through the baseline route only.  A law that fails under one route
/// and holds under another is already a route disagreement, which the loop
/// above reports; running every law through every route would multiply the cost
/// of a case by the number of laws for no new coverage.
pub fn check_laws(case: &Case) -> Vec<Divergence> {
    // Operands 0..3 from the case, then the empty trie, which is what lets a
    // law state a unit or annihilator.
    let mut ops: Vec<PathMap<u64>> = (0..EMPTY).map(|i| case.operands[i].clone()).collect();
    ops.push(PathMap::new());
    debug_assert_eq!(ops.len(), LAW_OPERANDS);

    let mut out = Vec::new();
    for law in laws::laws() {
        let l = routes::eval(Route::Pointwise(0), &law.lhs, &ops).unwrap();
        let r = routes::eval(Route::Pointwise(0), &law.rhs, &ops).unwrap();
        let (ok, detail) = match law.level {
            Level::Values => (
                l.values == r.values,
                format!(
                    "{}\n  lhs {}: {}\n  rhs {}: {}",
                    shape::first_values_diff(&l.values, &r.values).unwrap_or_default(),
                    law.lhs,
                    shape::show_values(&l.values),
                    law.rhs,
                    shape::show_values(&r.values),
                ),
            ),
            Level::Paths => {
                // Compare the value-carrying paths only.  Comparing every path
                // in the shape would drag the dangling-path question into laws
                // that are not about it.
                let lk: Vec<&Vec<u8>> = l.values.keys().collect();
                let rk: Vec<&Vec<u8>> = r.values.keys().collect();
                (
                    lk == rk,
                    format!(
                        "lhs {}: {}\n  rhs {}: {}",
                        law.lhs,
                        shape::show_values(&l.values),
                        law.rhs,
                        shape::show_values(&r.values),
                    ),
                )
            }
        };
        if !ok {
            out.push(Divergence {
                class: Class::Law,
                signature: format!("law:{}", law.name),
                detail: format!("{} ({:?}): {detail}", law.name, law.level),
            });
        }
    }
    out
}

fn route_key(r: Route) -> String {
    match r {
        Route::Pointwise(k) => format!("pw{k}"),
        _ => r.name(&Expr::Var(0)),
    }
}

// ---------------------------------------------------------------- known findings

/// A finding that already reproduces on `master` and has a reproducer of its
/// own, so a run that only hits these is not a regression.
pub struct Known {
    pub signature: &'static str,
    /// Which defect it traces to.  Several signatures share one entry: a single
    /// wrong value inside `join` surfaces on every route that reaches a join
    /// and in every law that mentions one, so the table maps many signatures
    /// onto few causes.
    pub cause: &'static str,
}

/// Findings confirmed on `master`, with the defect each traces to.
/// `bin/alg_bug_repros.rs` reproduces every cause in a dozen lines, without the
/// fuzzer; run it to see which still stand.
///
/// This table decides the **exit status** and nothing else.  Counts are always
/// printed, known and unknown alike, so a known defect that starts firing ten
/// times more often is still visible even though it does not turn the run red.
/// `--strict` ignores the table entirely.
///
/// # The causes
///
/// 1. **Value bias by node layout** (`bias`).  `pjoin` on `u64` is
///    `left_biased_pjoin` and `pmeet` is `Identity(SELF_IDENT)`, so where both
///    operands carry a value the *left* one must win.  `PathMap::join` and
///    `PathMap::meet` take the right one when the two operands' nodes are laid
///    out differently -- in the reproducer, because one side has a chain of
///    dangling descendants below the shared path.  Every zipper route gets this
///    right, so it shows up as *laws* failing and as the `model` route
///    disagreeing, not as one route out of step with the others: the defect is
///    in the baseline the others are compared against.
///
/// 2. **`join` loses a value across shared structure** (`loss`).  With `b` a
///    clone of `a` plus one extra value, `a | b` drops that value and `b | a`
///    keeps it.  A join is a least upper bound, so no ordering may lose a path;
///    this is the one finding that needs no argument about value bias.  It
///    needs the operands to *share nodes* -- rebuilding `b`'s entries into a
///    fresh map makes it go away -- which is why the generator clones and
///    merkleizes operands instead of only writing them fresh.
///
/// 3. **Root values lost by the write-zipper forms** (`root`).  `join_into`
///    into an empty destination drops the source's root value, and `meet_2`
///    drops root values outright.  These are routes disagreeing with the
///    baseline in the ordinary way.
///
/// 4. **Dangling paths** (`dangling`).  Routes that graft whole subtries keep
///    structure that routes walking path by path do not.  Unsettled rather than
///    wrong -- see `../SPEC_WARTS.md` -- hence its own class, `shape`, which
///    does not fail a run unless `--shape` says so.
///
/// 5. **`merkleize` panics on dangling-only structure** (`merkleize`).  Not an
///    algebraic defect: it fires while the operands are still being written,
///    before any operation runs, which is what the `build` in its signature
///    means.
const BIAS: &str = "value bias by node layout (repro 3)";
const LOSS: &str = "join loses a value across shared structure (repro 4)";
const ROOT: &str = "write-zipper forms lose root values (repros 1, 2)";
const DANGLING: &str = "dangling-path treatment differs by route";
const MERKLEIZE: &str = "merkleize panics on dangling-only structure (repro 5)";
/// Re-nesting a join moves which operand is on the left *and* which pair of
/// tries meets a shared node first, so both cause 1 and cause 2 reach these.
const BIAS_OR_LOSS: &str = "value bias or lost value (repros 3, 4)";

pub const KNOWN: &[Known] = &[
    // Routes disagreeing with the baseline: `join_into` and `meet_2` losing
    // root values, plus the baseline's own bias showing up as the zipper routes
    // "disagreeing" with it.
    Known { signature: "values:pw1", cause: ROOT },
    Known { signature: "values:pw2", cause: ROOT },
    Known { signature: "values:pw3", cause: ROOT },
    Known { signature: "values:pw4", cause: BIAS },
    Known { signature: "values:pw5", cause: BIAS },
    Known { signature: "values:ternary", cause: BIAS },
    Known { signature: "values:nary", cause: BIAS },
    Known { signature: "values:nary_poly", cause: BIAS },
    Known { signature: "values:dnf", cause: BIAS },
    // The reference model has no trie and no bias, so it disagrees with the
    // baseline exactly where the baseline is wrong.
    Known { signature: "values:model", cause: BIAS },
    // Dangling structure.
    Known { signature: "shape:pw1", cause: DANGLING },
    Known { signature: "shape:pw2", cause: DANGLING },
    Known { signature: "shape:pw3", cause: DANGLING },
    Known { signature: "shape:pw4", cause: DANGLING },
    Known { signature: "shape:pw5", cause: DANGLING },
    Known { signature: "shape:ternary", cause: DANGLING },
    Known { signature: "shape:nary", cause: DANGLING },
    Known { signature: "shape:nary_poly", cause: DANGLING },
    Known { signature: "shape:dnf", cause: DANGLING },
    // Laws.  Every value-level lattice law that puts the operands on different
    // sides of a join or meet is sensitive to cause 1.
    Known { signature: "law:join-associative", cause: BIAS_OR_LOSS },
    Known { signature: "law:meet-associative", cause: BIAS },
    Known { signature: "law:join-distributes-over-meet", cause: BIAS },
    Known { signature: "law:meet-distributes-over-join", cause: BIAS },
    Known { signature: "law:absorb-join-meet", cause: BIAS },
    Known { signature: "law:absorb-meet-join", cause: BIAS },
    Known { signature: "law:sym-diff-is-join-minus-meet", cause: BIAS },
    // Join associativity again, with meets for leaves.  Reached by cause 2:
    // `a & b` over an all-dangling `b` is a dangling-only trie, and joining
    // that with a trie carrying values below the same paths loses them -- the
    // same shape as repro 4.
    Known { signature: "law:majority-is-pairwise-meets", cause: BIAS_OR_LOSS },
    // Commutativity is checked on paths only, so a bias cannot break it -- only
    // a lost path can.  This is cause 2, and the only law that detects it.
    Known { signature: "law:join-commutative", cause: LOSS },
    Known { signature: "panic:build:line_list_node.rs:1745", cause: MERKLEIZE },
    // Debug-assertions builds only, and the sharpest view of cause 2 there is:
    // joining a list node into a dense node reports `AlgebraicStatus::None`
    // -- an empty result -- from two nodes that are not empty, which is the
    // mechanism by which `a | b` loses a value in repro 4.
    Known { signature: "panic:eval:line_list_node.rs:2669", cause: LOSS },
    // The same defect at a different node type: joining two dense nodes, a
    // cofree `pjoin` returns `None` while the left side still has a non-empty
    // onward node, so the join discards that subtrie.  Where the subtrie holds
    // values this is repro 4; where it holds only dangling paths the loss is
    // invisible to a release build, which is why debug assertions are a mode of
    // their own.
    Known { signature: "panic:eval:dense_byte_node.rs:2080", cause: LOSS },
    // `merge_from_list_node` returning `None` again, from `join_into_dyn` this
    // time.  Three assertion sites, one story: join's "the result is empty"
    // path is reachable from nodes that are not empty.
    Known { signature: "panic:eval:line_list_node.rs:2720", cause: LOSS },
];

pub fn known(signature: &str) -> Option<&'static Known> {
    KNOWN.iter().find(|k| k.signature == signature)
}

// ------------------------------------------------------------------ running

/// Which half of a case was running when it panicked.
///
/// Worth separating, because the two mean different things.  `Build` is a panic
/// while *writing the operand tries* -- plain `set_val`, `create_path`,
/// `remove_branches`, `merkleize` on a write zipper, before any algebra has
/// run.  That is a crash in the write path and belongs to the crash fuzzer;
/// this fuzzer just happens to reach it.  `Eval` is a panic inside an algebraic
/// operation, which is this fuzzer's own business.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Phase {
    Build,
    Eval,
}

impl Phase {
    pub fn tag(self) -> &'static str {
        match self {
            Phase::Build => "build",
            Phase::Eval => "eval",
        }
    }
}

/// What one input produced.  A panic is kept distinct from a divergence: it
/// means a route never got as far as producing an answer, so there is nothing
/// to compare and the finding is the crash itself.
pub enum Outcome {
    Clean,
    Diverged(Vec<Divergence>),
    Panicked(Phase, String, String),
}

std::thread_local! {
    /// Where the last panic came from.  The payload of an `unwrap` on `None`
    /// carries no location, and the location is the whole value of a crash
    /// signature -- without it every distinct panic site collapses onto one
    /// line called "panic".  A hook is the only way to see it.
    static PANIC_SITE: core::cell::RefCell<String> =
        const { core::cell::RefCell::new(String::new()) };
}

/// Replace the panic hook with one that records the panic site and prints
/// nothing.
///
/// Both halves matter for a long run: the default hook would print a backtrace
/// notice per panicking case and drown the output, and `catch_unwind` alone
/// cannot see where the panic came from.
pub fn install_panic_hook() {
    std::panic::set_hook(Box::new(|info| {
        let site = info
            .location()
            .map(|l| {
                // Just the file name and line: the absolute path would make
                // signatures depend on where the checkout lives.
                let f = l.file();
                let f = f.rsplit('/').next().unwrap_or(f);
                format!("{f}:{}", l.line())
            })
            .unwrap_or_else(|| "?".to_string());
        PANIC_SITE.with(|s| *s.borrow_mut() = site);
    }));
}

fn panic_msg(e: Box<dyn core::any::Any + Send>) -> (String, String) {
    let msg = e
        .downcast_ref::<String>()
        .cloned()
        .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_else(|| "<non-string panic>".to_string());
    let site = PANIC_SITE.with(|s| s.borrow().clone());
    (site, msg)
}

/// Decode an input, run every route and every law over it, and say what
/// disagreed.
///
/// Two `catch_unwind`s rather than one, so a crash can say which phase it was
/// in.  The case has to outlive the first, hence the separation.
pub fn run(bytes: &[u8]) -> Outcome {
    let case = match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| decode(bytes))) {
        Err(e) => {
            let (site, msg) = panic_msg(e);
            return Outcome::Panicked(Phase::Build, site, msg);
        }
        Ok(c) => c,
    };
    match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| check(&case))) {
        Err(e) => {
            let (site, msg) = panic_msg(e);
            Outcome::Panicked(Phase::Eval, site, msg)
        }
        Ok(divs) if divs.is_empty() => Outcome::Clean,
        Ok(divs) => Outcome::Diverged(divs),
    }
}

/// Signatures an input produces: the grouping keys, without the detail.  Also
/// the invariant the shrinker preserves.
pub fn signatures(bytes: &[u8]) -> Vec<String> {
    match run(bytes) {
        Outcome::Clean => Vec::new(),
        Outcome::Diverged(d) => d.into_iter().map(|d| d.signature).collect(),
        Outcome::Panicked(p, site, _) => vec![panic_signature(p, &site)],
    }
}

pub fn panic_signature(phase: Phase, site: &str) -> String {
    format!("panic:{}:{site}", phase.tag())
}

/// Reproducible input generation, so a seed names a run.
///
/// xorshift64*, rather than `rand`: this crate depends on nothing but `pathmap`
/// and is worth keeping that way.
pub struct Rng(pub u64);

impl Rng {
    /// Derive a stream for job `job` of a run seeded with `seed`.  The odd
    /// multiplier keeps jobs from sharing a stream.
    pub fn for_job(seed: u64, job: usize) -> Rng {
        Rng((seed
            .wrapping_mul(0x9E37_79B9_7F4A_7C15)
            .wrapping_add(job as u64 * 0x1234_5679))
            | 1)
    }

    pub fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    /// An input long enough that the decoder rarely runs out mid-case -- which
    /// would saturate the rest to zeros and waste the draw -- and short enough
    /// to shrink quickly.
    pub fn input(&mut self) -> Vec<u8> {
        let n = 48 + (self.next() % 96) as usize;
        (0..n).map(|_| (self.next() >> 24) as u8).collect()
    }
}

/// Human-readable rendering of a case, for a failure report and for replay.
pub fn describe(case: &Case) -> String {
    let mut s = String::new();
    s.push_str(&format!("expr:     {}\n", case.expr));
    s.push_str(&format!("alphabet: {}\n", case.alphabet));
    for (i, (m, b)) in case.operands.iter().zip(&case.builds).enumerate() {
        let sh: Shape = shape_of_map(m);
        s.push_str(&format!(
            "operand {}: {:?}\n  {}\n",
            (b'a' + i as u8) as char,
            b,
            show_shape(&sh)
        ));
    }
    s
}

/// Values of each operand, for a report that only needs the settled part.
pub fn operand_values(case: &Case) -> Vec<Values> {
    case.operands
        .iter()
        .map(|m| shape::values_of_shape(&shape_of_map(m)))
        .collect()
}
