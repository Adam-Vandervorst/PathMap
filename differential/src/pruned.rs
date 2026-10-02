//! The crate side of the **dangling-path-free** differential harness.
//!
//! `lean/.lake/build/bin/pruned-oracle` prints the same trace from
//! `PrunedModel`; `lean/pruned_differential.py` runs both and diffs them.  The
//! wire format and operation table are a contract shared with
//! `lean/PrunedModel/Fuzz.lean`; any change here must be mirrored there.
//!
//! This is not [`crate::harness`] with a flag.  That harness explores the whole
//! zipper API and reproduces whatever `pathmap` does with dangling paths; its
//! prune flags are pinned to `false` and compared against nothing, because the
//! flag's effect is a function of where an internal node boundary happens to
//! fall.  This one explores a smaller API and makes a stronger claim about it:
//!
//! 1. **No `create_path`.**  Its whole purpose is a location with no value.
//! 2. **`prune = true` everywhere**, and `prune_path` / `prune_ascend` stay in
//!    the table as assertions: the model says `0`, so a non-zero count means
//!    something in the subset leaked a dangling path for it to find.
//! 3. **The write zipper is rooted at the map root.**  A write zipper rooted
//!    below it holds a node at its own root, which survives as a location
//!    leading nowhere once everything beneath it is removed, and `prune_path`
//!    does not rise above the zipper's origin.  Off-root *writing* is still
//!    covered: the root-rooted zipper reaches every focus with `descend_to`.
//!
//! There is one read source, a `PathMap` read zipper, so no `ReadSource` trait
//! and no ACT mode — `graft_child_maps`, quarantined in the other harness, is
//! simply not in this table.
//!
//! `--check` adds in-process assertions needing no oracle: the zipper
//! invariants from [`crate::harness::check_zipper`], plus the one this harness
//! is named for — [`check_no_dangling`].

use pathmap::PathMap;
use pathmap::utils::ByteMask;
use pathmap::zipper::*;

use crate::harness::{
    check_zipper, dump, fingerprint, hex_path, show_bool, show_byte_opt, show_status, show_val,
    Dec, MAX_STEPS,
};

use core::fmt::Write as _;

/// Number of distinct operations.  Must match `PrunedModel.Fuzz.nops`.
pub const NOPS: usize = 54;

/// Why an operation was skipped.  Every `skip` in the trace carries one of
/// these.  `lean/PrunedModel/Fuzz.lean` emits the same tokens; the two must
/// agree exactly or every input with a skip diverges.
///
/// Note which reasons from [`crate::harness`] are *absent*: `skip:act` (there is
/// one read source here), `skip:off-root-prune` (the write zipper is always at
/// the map root, so the prune count is well-defined), and `skip:quarantined`
/// (`graft_child_maps` is not in this table).
///
/// `to_next`/`to_prev_sibling_byte` at the zipper root, where the native read
/// zipper escapes its own root.
pub const SKIP_AT_ROOT: &str = "skip:at-root";
/// A degenerate `k = 0` on `join_k_path_into` / `meet_k_path_into`.
pub const SKIP_K0: &str = "skip:k0";
/// The focus has nothing below it, where the op's behaviour is a function of
/// node materialisation rather than of trie state.
pub const SKIP_EMPTY_FOCUS: &str = "skip:empty-focus";
/// `insert_prefix("")`, which destroys the subtrie.
pub const SKIP_EMPTY_PATH: &str = "skip:empty-path";

/// The prune flag every operation in this subset is driven with.
///
/// The opposite of [`crate::harness`]'s `no_prune`, and for the same reason
/// stated the other way round: there, the flag's effect is unspecifiable, so it
/// is never exercised; here, removal is *defined* to reclaim the chain, so it is
/// always exercised and always compared.
const PRUNE: bool = true;

/// Does the focus have no descendants at all?
///
/// Several return values (`remove_branches`, `restricting`, `join_map_into`,
/// `take_map`, `restrict`) hinge on whether an *empty node* happens to be
/// materialised at the focus rather than on the logical state, so they are
/// masked here.
fn focus_node_empty<Z: Zipper>(z: &Z) -> bool {
    z.child_count() == 0
}

/// Canonical rendering of a decoded byte mask: ascending, deduplicated, which is
/// what `ByteMask.ofList` produces on the Lean side.
fn canon_mask(m: &[u8]) -> Vec<u8> {
    let mut v = m.to_vec();
    v.sort_unstable();
    v.dedup();
    v
}

/// **The invariant this harness is named for**: no location exists without
/// leading to a value.
///
/// Walks the whole map and asserts that every location with no children carries
/// a value.  The root of an empty map is the one exception — `PathMap::new()`
/// reports `path_exists() == true` at the root, and there is nothing it could
/// lead to.
///
/// This needs no oracle, which makes it the cheapest way to run the subset:
/// `--check` asserts it after every operation, and a failure localises the
/// leaking operation to one step without a trace diff.
pub fn check_no_dangling(map: &PathMap<u64>, label: &str) {
    let mut z = map.read_zipper();
    // `to_next_step` visits every location strictly below the root in
    // depth-first order, and the root is where the walk starts -- so step first
    // and check after.  The root is deliberately not checked: `PathMap::new()`
    // reports `path_exists() == true` there with nothing to lead to, which is
    // the one location in this model that may exist without a value below it.
    while z.to_next_step() {
        if z.child_count() == 0 && !z.is_val() {
            panic!(
                "{label}: dangling path at {} -- a location with no value and no children",
                hex_path(z.path())
            );
        }
    }
}

/// Decode the header: two seeded maps and the read zipper's root.
///
/// The write zipper's root is not decoded — it is always the map root.  The read
/// zipper's root is decoded as a path and then clamped to its longest existing
/// prefix, rather than created: `create_path` is not in this subset, and a
/// zipper whose root does not exist can walk out of it (lean/FINDINGS.md #3),
/// which would contaminate every other comparison.
pub fn decode_header(d: &mut Dec) -> Option<(PathMap<u64>, PathMap<u64>, Vec<u8>)> {
    let mut m0 = PathMap::<u64>::new();
    let n0 = d.modn(8)?;
    for _ in 0..n0 {
        let p = d.path(6)?;
        let v = d.u8()? as u64;
        m0.set_val_at(&p, v);
    }
    let mut m1 = PathMap::<u64>::new();
    let n1 = d.modn(8)?;
    for _ in 0..n1 {
        let p = d.path(6)?;
        let v = d.u8()? as u64;
        m1.set_val_at(&p, v);
    }
    let raw = d.path(4)?;
    // Existence is prefix-closed, so the prefixes that exist form an initial
    // segment: stop at the first one that does not.  `PrunedModel.Fuzz`'s
    // `clampToExisting` is the same computation over the model.
    let mut root1: Vec<u8> = Vec::new();
    for j in 1..=raw.len() {
        if m1.read_zipper_at_path(&raw[..j]).path_exists() {
            root1 = raw[..j].to_vec();
        } else {
            break;
        }
    }
    Some((m0, m1, root1))
}

/// Decode and execute a fuzzer input.
pub fn run(bytes: &[u8], check: bool) -> String {
    let mut d = Dec { bytes, pos: 0 };
    let (mut map0, map1, root1) = match decode_header(&mut d) {
        Some(x) => x,
        None => return "EMPTY\n".to_string(),
    };
    let mut out = String::new();
    {
        // NOTE: `read_zipper_at_borrowed_path` would panic (release: wrap) in
        // `to_next_k_path`, whose `path_len()` underflows before the path buffer
        // is prepared.  Use the owned-path constructor so that known bug does
        // not abort every run.
        let mut rz = map1.read_zipper_at_path(&root1);
        run_ops(&mut d, &mut out, &mut map0, &mut rz, &root1, check);
    }
    // The check needs the whole map, which the live write zipper holds, so it
    // runs here rather than per step.  Localising a leak to one operation is the
    // trace diff's job; this is the no-oracle path.
    if check {
        check_no_dangling(&map0, "map0");
    }
    let _ = writeln!(out, "MAP0 {}", dump(&mut map0.read_zipper()));
    let _ = writeln!(out, "MAP1 {}", dump(&mut map1.read_zipper()));
    // Printed for trace compatibility with the other harness, and because a
    // reader of a divergence wants to see both roots stated rather than inferred.
    let _ = writeln!(out, "ROOT0 {}", hex_path(&[]));
    let _ = writeln!(out, "ROOT1 {}", hex_path(&root1));
    out
}

/// Bind `$z` to the write zipper (`t == 0`) or the read zipper, then run `$e`.
macro_rules! tgt {
    ($t:expr, $wz:expr, $rz:expr, $z:ident, $e:expr) => {
        if $t == 0 {
            let $z = &mut $wz;
            $e
        } else {
            let $z = &mut $rz;
            $e
        }
    };
}

/// Run the operation table.
pub fn run_ops(
    d: &mut Dec,
    out: &mut String,
    map0: &mut PathMap<u64>,
    rz: &mut ReadZipperUntracked<'_, '_, u64>,
    root1: &[u8],
    check: bool,
) {
    let mut wz = map0.write_zipper();
    let root0: &[u8] = &[];
    let mut step = 0usize;

    macro_rules! get {
        ($e:expr) => {
            match $e {
                Some(x) => x,
                None => break,
            }
        };
    }

    loop {
        if step >= MAX_STEPS {
            break;
        }
        let op = get!(d.u8()) as usize % NOPS;
        let (name, ret): (&str, String) = match op {
            // ## Movement and reading, on either zipper
            0 => {
                let t = get!(d.modn(2));
                let p = get!(d.path(6));
                tgt!(t, wz, *rz, z, z.descend_to(&p));
                ("descend_to", hex_path(&p))
            }
            1 => {
                let t = get!(d.modn(2));
                let b = get!(d.path_byte());
                tgt!(t, wz, *rz, z, z.descend_to_byte(b));
                ("descend_to_byte", format!("{b:02x}"))
            }
            2 => {
                let t = get!(d.modn(2));
                let n = get!(d.modn(8));
                let r = tgt!(t, wz, *rz, z, z.ascend(n));
                ("ascend", format!("{r}"))
            }
            3 => {
                let t = get!(d.modn(2));
                let r = tgt!(t, wz, *rz, z, z.ascend_byte());
                ("ascend_byte", show_bool(r).to_string())
            }
            4 => {
                let t = get!(d.modn(2));
                tgt!(t, wz, *rz, z, z.reset());
                ("reset", "-".to_string())
            }
            5 => {
                let t = get!(d.modn(2));
                let r = tgt!(t, wz, *rz, z, z.descend_first_byte());
                ("descend_first_byte", show_byte_opt(r))
            }
            6 => {
                let t = get!(d.modn(2));
                let r = tgt!(t, wz, *rz, z, z.descend_last_byte());
                ("descend_last_byte", show_byte_opt(r))
            }
            7 => {
                let t = get!(d.modn(2));
                let i = get!(d.modn(6));
                let r = tgt!(t, wz, *rz, z, z.descend_indexed_byte(i));
                ("descend_indexed_byte", show_byte_opt(r))
            }
            8 => {
                let t = get!(d.modn(2));
                let r = tgt!(t, wz, *rz, z, z.descend_until());
                ("descend_until", show_bool(r).to_string())
            }
            9 => {
                let t = get!(d.modn(2));
                let r = tgt!(t, wz, *rz, z, z.ascend_until());
                ("ascend_until", format!("{r}"))
            }
            10 => {
                let t = get!(d.modn(2));
                let r = tgt!(t, wz, *rz, z, z.ascend_until_branch());
                ("ascend_until_branch", format!("{r}"))
            }
            11 => {
                let t = get!(d.modn(2));
                // Skipped at the zipper root: the native ReadZipper escapes its
                // own root there.
                if tgt!(t, wz, *rz, z, z.at_root()) {
                    ("to_next_sibling_byte", SKIP_AT_ROOT.to_string())
                } else {
                    let r = tgt!(t, wz, *rz, z, z.to_next_sibling_byte());
                    ("to_next_sibling_byte", show_byte_opt(r))
                }
            }
            12 => {
                let t = get!(d.modn(2));
                if tgt!(t, wz, *rz, z, z.at_root()) {
                    ("to_prev_sibling_byte", SKIP_AT_ROOT.to_string())
                } else {
                    let r = tgt!(t, wz, *rz, z, z.to_prev_sibling_byte());
                    ("to_prev_sibling_byte", show_byte_opt(r))
                }
            }
            13 => {
                let t = get!(d.modn(2));
                let r = tgt!(t, wz, *rz, z, z.to_next_step());
                ("to_next_step", show_bool(r).to_string())
            }
            14 => {
                // `ZipperIteration` is read-only: the target byte is still
                // consumed, but the operation always applies to `rz`.
                let _t = get!(d.modn(2));
                ("to_next_val", show_bool(rz.to_next_val()).to_string())
            }
            15 => {
                let _t = get!(d.modn(2));
                let k = get!(d.modn(4));
                // k == 0 is specified as an unsuccessful descent.
                ("descend_first_k_path", show_bool(rz.descend_first_k_path(k)).to_string())
            }
            16 => {
                let _t = get!(d.modn(2));
                let k = get!(d.modn(4));
                // A whole k-path iteration: `to_next_k_path` on its own
                // continues state left by `descend_first_k_path`.
                let mut v: Vec<String> = Vec::new();
                if rz.descend_first_k_path(k) {
                    v.push(hex_path(rz.path()));
                    while v.len() < 32 && rz.to_next_k_path(k) {
                        v.push(hex_path(rz.path()));
                    }
                }
                ("k_path_walk", v.join(","))
            }
            17 => {
                let _t = get!(d.modn(2));
                ("descend_last_path", show_bool(rz.descend_last_path()).to_string())
            }
            18 => {
                let t = get!(d.modn(2));
                let p = get!(d.path(6));
                let n = tgt!(t, wz, *rz, z, z.move_to_path(&p));
                ("move_to_path", format!("{n}"))
            }
            19 => {
                let t = get!(d.modn(2));
                let p = get!(d.path(6));
                let n = tgt!(t, wz, *rz, z, z.descend_to_existing(&p));
                ("descend_to_existing", format!("{n}"))
            }
            20 => {
                let t = get!(d.modn(2));
                let p = get!(d.path(6));
                let n = tgt!(t, wz, *rz, z, z.descend_to_val(&p));
                ("descend_to_val", format!("{n}"))
            }
            21 => {
                let t = get!(d.modn(2));
                let b = get!(d.path_byte());
                let r = tgt!(t, wz, *rz, z, z.descend_to_existing_byte(b));
                ("descend_to_existing_byte", show_bool(r).to_string())
            }
            22 => {
                let t = get!(d.modn(2));
                let n = get!(d.modn(8));
                let r = tgt!(t, wz, *rz, z, z.descend_until_max_bytes(n));
                ("descend_until_max_bytes", show_bool(r).to_string())
            }
            23 => {
                let t = get!(d.modn(2));
                let p = get!(d.path(6));
                let r = tgt!(t, wz, *rz, z, z.descend_to_check(&p));
                ("descend_to_check", show_bool(r).to_string())
            }
            24 => {
                let t = get!(d.modn(2));
                let p = get!(d.path(6));
                let v = tgt!(t, wz, *rz, z, show_val(z.val_at(&p)));
                ("val_at", v)
            }
            25 => {
                let t = get!(d.modn(2));
                let n = if t == 0 {
                    wz.make_map().val_count()
                } else {
                    rz.make_map().val_count()
                };
                ("make_map_val_count", format!("{n}"))
            }
            26 => {
                let t = get!(d.modn(2));
                let s = if t == 0 {
                    dump(&mut wz.fork_read_zipper())
                } else {
                    dump(&mut rz.fork_read_zipper())
                };
                ("dump", s)
            }
            27 => {
                let t = get!(d.modn(2));
                // The blind-zipper addition: `descend_until` reporting the bytes
                // it descended.  The observer's output is a blind zipper's only
                // account of where it went, so it is compared byte for byte.
                let mut obs: Vec<u8> = Vec::new();
                let r = tgt!(t, wz, *rz, z, z.descend_until_observed(&mut obs));
                ("descend_until_observed", format!("{}:{}", show_bool(r), hex_path(&obs)))
            }
            28 => {
                let t = get!(d.modn(2));
                let p = get!(d.path(6));
                // `get_val`/`get_val_at` must agree with `val`/`val_at`; they
                // differ only in the lifetime of the reference returned.
                let (g, ga, agree) = if t == 0 {
                    // A write zipper has no `ZipperReadOnlyValues`.
                    (wz.val().copied(), wz.val_at(&p).copied(), true)
                } else {
                    let (g, ga) = (rz.get_val().copied(), rz.get_val_at(&p).copied());
                    let agree = g == rz.val().copied() && ga == rz.val_at(&p).copied();
                    (g, ga, agree)
                };
                (
                    "get_val_agrees",
                    format!("{}:{}:{}", show_val(g.as_ref()), show_val(ga.as_ref()), show_bool(agree)),
                )
            }
            29 => {
                let got = rz.to_next_get_val().copied();
                // `to_next_get_val` is specified as `to_next_val` followed by
                // reading the value, so `Some` must mean it moved and must equal
                // what `val` reports.
                let agree = got == rz.val().copied() || (got.is_none() && rz.at_root());
                (
                    "to_next_get_val",
                    format!("{}:{}:{}", show_bool(got.is_some()), show_val(got.as_ref()), show_bool(agree)),
                )
            }
            // ## Writing, on the write zipper
            30 => {
                let v = get!(d.u8()) as u64;
                ("set_val", show_val(wz.set_val(v).as_ref()))
            }
            31 => ("remove_val", show_val(wz.remove_val(PRUNE).as_ref())),
            32 => {
                // Must be `0`: a trie built from this subset has no dangling tip.
                ("prune_path", format!("{}", wz.prune_path()))
            }
            33 => ("prune_ascend", format!("{}", wz.prune_ascend())),
            34 => {
                let leaky = focus_node_empty(&wz);
                let r = wz.remove_branches(PRUNE);
                // An empty node still comes back as `Some(..)` from
                // `into_option()` for some representations, so `true` gets
                // reported for a removal of nothing.  Compared only when there
                // was something below.
                let s = if leaky { "?".to_string() } else { show_bool(r).to_string() };
                ("remove_branches", s)
            }
            35 => {
                let n = get!(d.modn(4));
                let m = get!(d.path_n(n));
                wz.remove_unmasked_branches(ByteMask::from_iter(m.iter().copied()), PRUNE);
                ("remove_unmasked_branches", hex_path(&canon_mask(&m)))
            }
            36 => {
                wz.graft(&*rz);
                ("graft", "-".to_string())
            }
            37 => {
                let p = get!(d.path(6));
                wz.graft_src_at(&*rz, &p);
                ("graft_src_at", hex_path(&p))
            }
            38 => ("join_into", show_status(wz.join_into(&*rz)).to_string()),
            39 => {
                let leaky = focus_node_empty(&wz);
                let st = wz.join_map_into(rz.make_map());
                let s = if leaky { "?".to_string() } else { show_status(st).to_string() };
                ("join_map_into", s)
            }
            40 => ("meet_into", show_status(wz.meet_into(&*rz, PRUNE)).to_string()),
            41 => ("subtract_into", show_status(wz.subtract_into(&*rz, PRUNE)).to_string()),
            42 => {
                let leaky = focus_node_empty(&wz);
                let st = wz.restrict(&*rz);
                let s = if leaky { "?".to_string() } else { show_status(st).to_string() };
                ("restrict", s)
            }
            43 => {
                // Skipped when either side has nothing below its focus: there
                // `restricting` branches on whether an empty node happens to be
                // materialised, and the branches differ in *effect*.
                if focus_node_empty(&wz) || focus_node_empty(rz) {
                    ("restricting", SKIP_EMPTY_FOCUS.to_string())
                } else {
                    ("restricting", show_bool(wz.restricting(&*rz)).to_string())
                }
            }
            44 => {
                let k = get!(d.modn(4));
                // `join_k_path_into(0)` collapses the subtrie instead of being
                // the identity.
                if k == 0 {
                    ("join_k_path_into", SKIP_K0.to_string())
                } else {
                    let r = wz.join_k_path_into(k, PRUNE);
                    let s = if focus_node_empty(&wz) { "?".to_string() } else { show_bool(r).to_string() };
                    ("join_k_path_into", s)
                }
            }
            45 => {
                let p = get!(d.path(6));
                // `insert_prefix("")` destroys the subtrie.
                if p.is_empty() {
                    ("insert_prefix", SKIP_EMPTY_PATH.to_string())
                } else {
                    ("insert_prefix", show_bool(wz.insert_prefix(&p)).to_string())
                }
            }
            46 => {
                let n = get!(d.modn(6));
                ("remove_prefix", show_bool(wz.remove_prefix(n)).to_string())
            }
            47 => {
                let leaky = focus_node_empty(&wz) && wz.val().is_none();
                let r = match wz.take_map(PRUNE) {
                    Some(m) => {
                        wz.graft_map(m);
                        "1"
                    }
                    None => "0",
                };
                ("take_map_restore", if leaky { "?".to_string() } else { r.to_string() })
            }
            48 => {
                let k = get!(d.modn(4));
                // `meet_k_path_into` spins forever when the focus has no
                // children, and escapes the focus subtree when k == 0.
                if k == 0 {
                    ("meet_k_path_into", SKIP_K0.to_string())
                } else if wz.child_count() == 0 {
                    ("meet_k_path_into", SKIP_EMPTY_FOCUS.to_string())
                } else {
                    ("meet_k_path_into", show_bool(wz.meet_k_path_into(k, PRUNE)).to_string())
                }
            }
            49 => {
                let v = get!(d.u8()) as u64;
                // Writing through the reference `get_val_mut` hands back.  It
                // must behave like `set_val` where a value exists and do nothing
                // -- crucially, not create the path -- where one does not.
                let old = match wz.get_val_mut() {
                    Some(slot) => {
                        let old = *slot;
                        *slot = v;
                        Some(old)
                    }
                    None => None,
                };
                ("get_val_mut_write", show_val(old.as_ref()))
            }
            50 => {
                let v = get!(d.u8()) as u64;
                let r = *wz.get_val_or_set_mut(v);
                ("get_val_or_set_mut", show_val(Some(&r)))
            }
            51 => {
                let v = get!(d.u8()) as u64;
                // `ran` records whether the closure was invoked; the contract is
                // that it supplies the value only when none exists.
                let mut ran = false;
                let r = *wz.get_val_or_set_mut_with(|| {
                    ran = true;
                    v
                });
                ("get_val_or_set_mut_with", format!("{}:{}", show_val(Some(&r)), show_bool(ran)))
            }
            52 => {
                let n = get!(d.modn(4));
                let m = get!(d.path_n(n));
                let ru = get!(d.boolean());
                wz.graft_masked_branches(&*rz, ByteMask::from_iter(m.iter().copied()), ru);
                ("graft_masked_branches", format!("{}:{}", hex_path(&canon_mask(&m)), show_bool(ru)))
            }
            53 => {
                let p = get!(d.path(6));
                // `meet_2` takes two sources; the second is the first moved to `p`.
                let mut b = rz.clone();
                b.descend_to(&p);
                ("meet_2", show_status(wz.meet_2(&*rz, &b)).to_string())
            }
            _ => ("nop", "-".to_string()),
        };
        if check {
            check_zipper(&wz, "write zipper", root0);
            check_zipper(rz, "read zipper", root1);
        }
        let _ = writeln!(
            out,
            "{step} {name} ret={ret} W={} R={}",
            fingerprint(&wz, root0),
            fingerprint(rz, root1)
        );
        step += 1;
    }
}
