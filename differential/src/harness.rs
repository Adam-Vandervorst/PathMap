//! Shared fuzzing harness for `pathmap`'s zipper API.
//!
//! One decoder, used by two front ends:
//!
//! * `bin/pathmap_trace.rs` prints a trace, which `lean/differential.py`
//!   diffs against the Lean model's trace for the same bytes.
//! * `bin/act_trace.rs` does the same with an `ArenaCompactTree` as the
//!   read source.
//!
//! Either one, given `--check`, also asserts structural invariants in-process
//! after every operation (no oracle needed).
//!
//! The wire format and operation table are a contract shared with
//! `lean/PathMapModel/Fuzz.lean`; any change here must be mirrored there.

use pathmap::PathMap;
use pathmap::ring::AlgebraicStatus;
use pathmap::utils::ByteMask;
use pathmap::zipper::*;

// The trace is written into one growable buffer rather than a `Vec<String>`.
// It used to be ~260 separately allocated `String`s per input, thrown away as
// soon as they were printed; only a divergence needs the individual lines, and
// `str::lines()` recovers them then.
use core::fmt::Write as _;

/// Number of distinct operations. Must match `PathMapModel.Fuzz.nops`.
pub const NOPS: usize = 56;
/// Maximum operations executed. Must match the `maxSteps` default in `Fuzz.run`.
pub const MAX_STEPS: usize = 256;
/// Maximum entries in a `dump`. Must match `Fuzz.dumpAt`.
pub const DUMP_CAP: usize = 64;

pub struct Dec<'a> {
    pub bytes: &'a [u8],
    pub pos: usize,
}

impl<'a> Dec<'a> {
    pub fn u8(&mut self) -> Option<u8> {
        let b = *self.bytes.get(self.pos)?;
        self.pos += 1;
        Some(b)
    }
    pub fn modn(&mut self, m: usize) -> Option<usize> {
        let b = self.u8()?;
        Some(if m == 0 { 0 } else { (b as usize) % m })
    }
    /// Path bytes live in a 4-letter alphabet so generated tries share prefixes.
    pub fn path_byte(&mut self) -> Option<u8> {
        Some(self.u8()? % 4)
    }
    pub fn path_n(&mut self, n: usize) -> Option<Vec<u8>> {
        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            v.push(self.path_byte()?);
        }
        Some(v)
    }
    pub fn path(&mut self, lim: usize) -> Option<Vec<u8>> {
        let n = self.modn(lim)?;
        self.path_n(n)
    }
    pub fn boolean(&mut self) -> Option<bool> {
        Some(self.u8()? % 2 == 1)
    }
}

pub fn hex_path(p: &[u8]) -> String {
    if p.is_empty() {
        "_".to_string()
    } else {
        p.iter().map(|b| format!("{b:02x}")).collect()
    }
}

pub fn show_val(v: Option<&u64>) -> String {
    match v {
        None => "-".to_string(),
        Some(v) => format!("{v}"),
    }
}

/// Render a status the read source may have declined to produce.
pub fn show_status_opt(s: Option<AlgebraicStatus>) -> String {
    match s {
        Some(s) => show_status(s).to_string(),
        None => "skip".to_string(),
    }
}

pub fn show_status(s: AlgebraicStatus) -> &'static str {
    match s {
        AlgebraicStatus::Element => "Element",
        AlgebraicStatus::Identity => "Identity",
        AlgebraicStatus::None => "None",
    }
}

pub fn show_bool(b: bool) -> &'static str {
    if b { "1" } else { "0" }
}

/// Render the `Option<u8>` the movement operations now return under the
/// blind-zipper contract: the byte moved to, or `-` for "did not move".
pub fn show_byte_opt(b: Option<u8>) -> String {
    match b {
        None => "-".to_string(),
        Some(b) => format!("{b:02x}"),
    }
}

/// Per-step fingerprint of a zipper.
///
/// `expected_root` is the root the zipper was created at.  A zipper must never
/// leave it, so a mismatch is tagged `ESCAPED-ROOT` — the model can never
/// produce that tag, which lets `differential.py` recognise the escape bug
/// instead of reporting it as an unexplained state divergence.
pub fn fingerprint<Z: ZipperMoving + ZipperPath + ZipperValues<u64> + ZipperAbsolutePath>(
    z: &Z,
    expected_root: &[u8],
) -> String {
    format!(
        "{}{} o{} e{} v{} c{} n{} f{}",
        if z.root_prefix_path() == expected_root { "" } else { "ESCAPED-ROOT " },
        hex_path(z.path()),
        hex_path(z.origin_path()),
        show_bool(z.path_exists()),
        show_val(z.val()),
        z.child_count(),
        z.val_count(),
        // `focus_byte` is unspecified at the root, so it is only compared below it.
        if z.at_root() { "?".to_string() } else { show_byte_opt(z.focus_byte()) }
    )
}

/// Does the focus have no descendants at all?
///
/// Several return values (`remove_branches`, `restricting`, `join_map_into`,
/// `take_map`, `restrict`) hinge on whether an *empty node* happens to be
/// materialised at the focus rather than on the logical state, so the harness
/// masks them here.  See lean/README.md.
pub fn focus_node_empty<Z: Zipper>(z: &Z) -> bool {
    z.child_count() == 0
}

/// Depth-first dump of everything at and below the zipper's root, relative to it.
pub fn dump<Z: ZipperMoving + ZipperPath + ZipperValues<u64>>(z: &mut Z) -> String {
    z.reset();
    let mut lines = vec![format!("{}:{}", hex_path(z.path()), show_val(z.val()))];
    while lines.len() < DUMP_CAP && z.to_next_step() {
        // A depth-first step from the root must go deeper.  Coming back to the
        // empty path means the zipper walked out of its own root -- the escape
        // in lean/FINDINGS.md #3, which would otherwise show up here as a
        // traversal that visits the same location repeatedly.
        if z.path().is_empty() {
            lines.push("ESCAPED-ROOT".to_string());
            break;
        }
        lines.push(format!("{}:{}", hex_path(z.path()), show_val(z.val())));
    }
    lines.join(",")
}

/// The read side of the harness: whatever the write zipper is reading *from*.
///
/// Two implementations exist.  A `PathMap` read zipper supports everything.  An
/// `ArenaCompactTree` zipper supports the whole read and iteration API but
/// **cannot be a merge source**: `ZipperInfallibleSubtries` is not implemented
/// for it (and `ZipperSubtries` only for `Value = ()`), so `graft`, `join_into`,
/// `meet_into`, `subtract_into`, `restrict` and `restricting` cannot take one.
/// Those methods return `None`/`false` there and the harness emits `skip`, which
/// the Lean model mirrors in ACT mode.
///
/// Keeping this behind a trait means there is still exactly one operation table,
/// so the two front ends cannot drift apart.
pub trait ReadSource:
    Zipper + ZipperMoving + ZipperPath + ZipperValues<u64> + ZipperAbsolutePath + ZipperIteration
{
    /// Depth-first dump of everything below the focus (`fork_read_zipper` + walk).
    fn dump_fork(&self) -> String;
    /// `make_map().val_count()`, or `None` if subtries cannot be materialised.
    fn make_map_val_count(&self) -> Option<usize>;

    /// `ZipperReadOnlyValues::get_val` / `get_val_at`, paired with whether they
    /// agree with `val` / `val_at`.  The two differ only in the lifetime of the
    /// reference returned, so a disagreement is a defect.
    fn get_val_probe(&self, path: &[u8]) -> (Option<u64>, Option<u64>, bool);

    /// `ZipperReadOnlyIteration::to_next_get_val`: advance and hand back the
    /// value, with whether it agrees with `to_next_val` followed by `val`.
    /// `None` when the zipper does not implement the trait.
    fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)>;

    fn do_graft<W: ZipperWriting<u64>>(&self, _wz: &mut W) -> bool { false }
    fn do_graft_masked<W: ZipperWriting<u64>>(&self, _wz: &mut W, _m: ByteMask, _ru: bool) -> bool { false }
    /// Currently unused: op 54 is quarantined (lean/FINDINGS.md #15).  Kept so
    /// the op can be re-enabled with one line once the method is fixed.
    #[allow(dead_code)]
    fn do_graft_child_maps<W: ZipperWriting<u64>>(&self, _wz: &mut W, _m: ByteMask, _ru: bool) -> bool { false }
    /// `meet_2` needs two sources; the second is this zipper moved to `path`.
    fn do_meet_2<W: ZipperWriting<u64>>(&self, _wz: &mut W, _path: &[u8]) -> Option<AlgebraicStatus> { None }
    fn do_graft_src_at<W: ZipperWriting<u64>>(&self, _wz: &mut W, _p: &[u8]) -> bool { false }
    fn do_join_into<W: ZipperWriting<u64>>(&self, _wz: &mut W) -> Option<AlgebraicStatus> { None }
    fn do_join_map_into<W: ZipperWriting<u64>>(&self, _wz: &mut W) -> Option<AlgebraicStatus> { None }
    fn do_meet_into<W: ZipperWriting<u64>>(&self, _wz: &mut W, _prune: bool) -> Option<AlgebraicStatus> { None }
    fn do_subtract_into<W: ZipperWriting<u64>>(&self, _wz: &mut W, _prune: bool) -> Option<AlgebraicStatus> { None }
    fn do_restrict<W: ZipperWriting<u64>>(&self, _wz: &mut W) -> Option<AlgebraicStatus> { None }
    fn do_restricting<W: ZipperWriting<u64>>(&self, _wz: &mut W) -> Option<bool> { None }
}

impl<'a, 'p> ReadSource for ReadZipperUntracked<'a, 'p, u64> {
    fn dump_fork(&self) -> String {
        dump(&mut self.fork_read_zipper())
    }
    fn make_map_val_count(&self) -> Option<usize> {
        Some(self.make_map().val_count())
    }
    fn get_val_probe(&self, path: &[u8]) -> (Option<u64>, Option<u64>, bool) {
        let (g, ga) = (self.get_val().copied(), self.get_val_at(path).copied());
        let agree = g == self.val().copied() && ga == self.val_at(path).copied();
        (g, ga, agree)
    }
    fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)> {
        let got = self.to_next_get_val().copied();
        // `to_next_get_val` is specified as `to_next_val` followed by reading the
        // value, so `Some` must mean it moved and must equal what `val` reports.
        let agree = got == self.val().copied() || (got.is_none() && self.at_root());
        Some((got.is_some(), got, agree))
    }
    fn do_graft<W: ZipperWriting<u64>>(&self, wz: &mut W) -> bool {
        wz.graft(self);
        true
    }
    fn do_graft_masked<W: ZipperWriting<u64>>(&self, wz: &mut W, m: ByteMask, ru: bool) -> bool {
        wz.graft_masked_branches(self, m, ru);
        true
    }
    fn do_graft_child_maps<W: ZipperWriting<u64>>(&self, wz: &mut W, m: ByteMask, ru: bool) -> bool {
        // Fed this zipper's own child subtries, so the result must equal what
        // `graft_masked_branches` produces from the same mask.
        let maps: Vec<PathMap<u64>> = m
            .iter()
            .map(|b| {
                let mut c = self.clone();
                c.descend_to_byte(b);
                c.make_map()
            })
            .collect();
        wz.graft_child_maps(m, maps, ru);
        true
    }
    fn do_meet_2<W: ZipperWriting<u64>>(&self, wz: &mut W, path: &[u8]) -> Option<AlgebraicStatus> {
        let mut b = self.clone();
        b.descend_to(path);
        Some(wz.meet_2(self, &b))
    }
    fn do_graft_src_at<W: ZipperWriting<u64>>(&self, wz: &mut W, p: &[u8]) -> bool {
        wz.graft_src_at(self, p);
        true
    }
    fn do_join_into<W: ZipperWriting<u64>>(&self, wz: &mut W) -> Option<AlgebraicStatus> {
        Some(wz.join_into(self))
    }
    fn do_join_map_into<W: ZipperWriting<u64>>(&self, wz: &mut W) -> Option<AlgebraicStatus> {
        Some(wz.join_map_into(self.make_map()))
    }
    fn do_meet_into<W: ZipperWriting<u64>>(&self, wz: &mut W, prune: bool) -> Option<AlgebraicStatus> {
        Some(wz.meet_into(self, prune))
    }
    fn do_subtract_into<W: ZipperWriting<u64>>(&self, wz: &mut W, prune: bool) -> Option<AlgebraicStatus> {
        Some(wz.subtract_into(self, prune))
    }
    fn do_restrict<W: ZipperWriting<u64>>(&self, wz: &mut W) -> Option<AlgebraicStatus> {
        Some(wz.restrict(self))
    }
    fn do_restricting<W: ZipperWriting<u64>>(&self, wz: &mut W) -> Option<bool> {
        Some(wz.restricting(self))
    }
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


/// Structural invariants every zipper must satisfy at every moment.
///
/// These need no oracle, so `--check` can assert them on every step.
/// Violations are `pathmap` bugs by construction: each is either stated in the
/// trait documentation or forced by the meaning of the accessors.
pub fn check_zipper<Z>(z: &Z, label: &str, expected_root: &[u8])
where
    Z: ZipperMoving + ZipperPath + ZipperValues<u64> + ZipperAbsolutePath,
{
    // `at_root` is defined as "the path back to the root is empty".
    assert_eq!(
        z.at_root(),
        z.path().is_empty(),
        "{label}: at_root disagrees with path()"
    );
    // Documented on `ZipperAbsolutePath`: origin = root_prefix ++ path.
    let mut want = z.root_prefix_path().to_vec();
    want.extend_from_slice(z.path());
    assert_eq!(
        z.origin_path(),
        &want[..],
        "{label}: origin_path != root_prefix_path ++ path"
    );
    // A zipper may never leave the subtrie it was granted.
    assert_eq!(
        z.root_prefix_path(),
        expected_root,
        "{label}: the zipper escaped its own root"
    );
    // Below the root, `focus_byte` must be the last byte of the path.  (At the
    // root the trait leaves it unspecified, so nothing is checked there.)
    if !z.at_root() {
        assert_eq!(
            z.focus_byte(),
            z.path().last().copied(),
            "{label}: focus_byte disagrees with path()"
        );
    }
    // A value can only sit on a path that exists.
    if z.is_val() {
        assert!(z.path_exists(), "{label}: value on a non-existent path");
    }
    // `child_count` is the population count of `child_mask`.
    assert_eq!(
        z.child_count(),
        z.child_mask().iter().count(),
        "{label}: child_count != |child_mask|"
    );
    // Children imply the parent exists.
    if z.child_count() > 0 {
        assert!(z.path_exists(), "{label}: children under a non-existent path");
    }
    // `val_count` counts the focus itself.
    if z.is_val() {
        assert!(z.val_count() >= 1, "{label}: val_count omits the focus value");
    }
    // Nothing below means nothing to count except the focus.
    if z.child_count() == 0 {
        assert_eq!(
            z.val_count(),
            z.is_val() as usize,
            "{label}: val_count on a leaf"
        );
    }
}
/// Decode and execute a fuzzer input.
///
/// With `check`, every zipper is validated against `check_zipper` after every
/// operation; that is what `--check` does.  A differential pass runs
/// with `check == false`, because it is comparing against the model rather than
/// asserting, and a crate that violates an invariant should show up as a trace
/// diff rather than as an abort.
/// Decode the header: two seeded maps and the two zipper roots.
pub fn decode_header(d: &mut Dec) -> Option<(PathMap<u64>, PathMap<u64>, Vec<u8>, Vec<u8>)> {
    {
        let mut m0 = PathMap::<u64>::new();
        let n0 = d.modn(8)?;
        for _ in 0..n0 {
            let p = d.path(6)?;
            let v = d.u8()? as u64;
            let mut wz = m0.write_zipper_at_path(&p);
            wz.set_val(v);
            drop(wz);
        }
        let mut m1 = PathMap::<u64>::new();
        let n1 = d.modn(8)?;
        for _ in 0..n1 {
            let p = d.path(6)?;
            let v = d.u8()? as u64;
            let mut wz = m1.write_zipper_at_path(&p);
            wz.set_val(v);
            drop(wz);
        }
        let r0 = d.path(4)?;
        let r1 = d.path(4)?;
        // Both zipper roots are created if absent: a zipper whose root does not
        // exist can walk out of it (see `Zip.toNextSiblingByte`), which would
        // contaminate every other comparison.
        if !r0.is_empty() { m0.create_path(&r0); }
        if !r1.is_empty() { m1.create_path(&r1); }
        Some((m0, m1, r0, r1))
    }
}

/// Decode and execute a fuzzer input against a `PathMap` read source.
///
pub fn run(bytes: &[u8], check: bool) -> String {
    let mut d = Dec { bytes, pos: 0 };
    let (mut map0, map1, root0, root1) = match decode_header(&mut d) {
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
        run_ops(&mut d, &mut out, &mut map0, &root0, &mut rz, &root1, check);
    }
    let _ = writeln!(out, "MAP0 {}", dump(&mut map0.read_zipper()));
    let _ = writeln!(out, "MAP1 {}", dump(&mut map1.read_zipper()));
    let _ = writeln!(out, "ROOT0 {}", hex_path(&root0));
    let _ = writeln!(out, "ROOT1 {}", hex_path(&root1));
    out
}

/// Run the operation table.  This is the single shared body: the two front ends
/// differ only in what they hand in as `rz`.
pub fn run_ops<R: ReadSource>(
    d: &mut Dec,
    out: &mut String,
    map0: &mut PathMap<u64>,
    root0: &[u8],
    rz: &mut R,
    root1: &[u8],
    check: bool,
) {
    {
        let mut wz = map0.write_zipper_at_path(root0);
        let mut step = 0usize;
        // Explicit pruning is only well-defined for a zipper at the map root;
        // off it the depth pruned depends on internal node layout.
        let pruneable = root0.is_empty();
        // The `prune` flag on the other operations is passed straight to
        // `node_remove_*`, which prunes within the node even when it finds
        // nothing and reports `None` -- so its effect is a function of node
        // layout, not of the trie.  Always false.  See lean/FINDINGS.md #7.
        let no_prune = false;

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
                    // Skipped at the zipper root: the native ReadZipper escapes
                    // its own root there. See `Zip.toNextSiblingByte`.
                    if tgt!(t, wz, *rz, z, z.at_root()) {
                        ("to_next_sibling_byte", "skip".to_string())
                    } else {
                        let r = tgt!(t, wz, *rz, z, z.to_next_sibling_byte());
                        ("to_next_sibling_byte", show_byte_opt(r))
                    }
                }
                12 => {
                    let t = get!(d.modn(2));
                    if tgt!(t, wz, *rz, z, z.at_root()) {
                        ("to_prev_sibling_byte", "skip".to_string())
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
                    let r = (*rz).to_next_val();
                    ("to_next_val", show_bool(r).to_string())
                }
                15 => {
                    let _t = get!(d.modn(2));
                    let k = get!(d.modn(4));
                    // k == 0 is degenerate; see Fuzz.lean.
                    if k == 0 {
                        ("descend_first_k_path", "skip".to_string())
                    } else {
                        let r = (*rz).descend_first_k_path(k);
                        ("descend_first_k_path", show_bool(r).to_string())
                    }
                }
                16 => {
                    let _t = get!(d.modn(2));
                    let k = get!(d.modn(4));
                    // A whole k-path iteration: `to_next_k_path` on its own is
                    // unspecified (it continues state left by
                    // `descend_first_k_path`).
                    let mut v: Vec<String> = Vec::new();
                    if k == 0 {
                        let _ = writeln!(out, 
                            "{step} k_path_walk ret=skip W={} R={}",
                            fingerprint(&wz, root0), fingerprint(rz, root1));
                        step += 1;
                        continue;
                    }
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
                    let r = (*rz).descend_last_path();
                    ("descend_last_path", show_bool(r).to_string())
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
                        Some(wz.make_map().val_count())
                    } else {
                        (*rz).make_map_val_count()
                    };
                    match n {
                        Some(n) => ("make_map_val_count", format!("{n}")),
                        None => ("make_map_val_count", "skip".to_string()),
                    }
                }
                26 => {
                    let t = get!(d.modn(2));
                    let s = if t == 0 {
                        dump(&mut wz.fork_read_zipper())
                    } else {
                        (*rz).dump_fork()
                    };
                    ("dump", s)
                }
                27 => {
                    let v = get!(d.u8()) as u64;
                    ("set_val", show_val(wz.set_val(v).as_ref()))
                }
                28 => {
                    let _pr = get!(d.boolean()); // decoded for stream alignment; see `no_prune`
                    ("remove_val", show_val(wz.remove_val(no_prune).as_ref()))
                }
                29 => ("create_path", show_bool(wz.create_path()).to_string()),
                30 => {
                    if pruneable {
                        ("prune_path", format!("{}", wz.prune_path()))
                    } else {
                        ("prune_path", "skip".to_string())
                    }
                }
                31 => {
                    if pruneable {
                        ("prune_ascend", format!("{}", wz.prune_ascend()))
                    } else {
                        ("prune_ascend", "skip".to_string())
                    }
                }
                32 => {
                    let _pr = get!(d.boolean()); // decoded for stream alignment; see `no_prune`
                    let leaky = focus_node_empty(&wz);
                    let r = wz.remove_branches(no_prune);
                    let s = if leaky { "?".to_string() } else { show_bool(r).to_string() };
                    ("remove_branches", s)
                }
                33 => {
                    let n = get!(d.modn(4));
                    let m = get!(d.path_n(n));
                    let _pr = get!(d.boolean()); // decoded for stream alignment; see `no_prune`
                    let mask = ByteMask::from_iter(m.iter().copied());
                    wz.remove_unmasked_branches(mask, no_prune);
                    let mut canon: Vec<u8> = m.clone();
                    canon.sort_unstable();
                    canon.dedup();
                    ("remove_unmasked_branches", hex_path(&canon))
                }
                34 => {
                    let s = if (*rz).do_graft(&mut wz) { "-" } else { "skip" };
                    ("graft", s.to_string())
                }
                35 => {
                    let p = get!(d.path(6));
                    let s = if (*rz).do_graft_src_at(&mut wz, &p) {
                        hex_path(&p)
                    } else {
                        "skip".to_string()
                    };
                    ("graft_src_at", s)
                }
                36 => ("join_into", show_status_opt((*rz).do_join_into(&mut wz))),
                37 => {
                    let leaky = focus_node_empty(&wz);
                    let st = (*rz).do_join_map_into(&mut wz);
                    let s = if leaky && st.is_some() {
                        "?".to_string()
                    } else {
                        show_status_opt(st)
                    };
                    ("join_map_into", s)
                }
                38 => {
                    let _pr = get!(d.boolean()); // decoded for stream alignment; see `no_prune`
                    ("meet_into", show_status_opt((*rz).do_meet_into(&mut wz, no_prune)))
                }
                39 => {
                    let _pr = get!(d.boolean()); // decoded for stream alignment; see `no_prune`
                    (
                        "subtract_into",
                        show_status_opt((*rz).do_subtract_into(&mut wz, no_prune)),
                    )
                }
                40 => {
                    let leaky = focus_node_empty(&wz);
                    let st = (*rz).do_restrict(&mut wz);
                    let s = if leaky && st.is_some() {
                        "?".to_string()
                    } else {
                        show_status_opt(st)
                    };
                    ("restrict", s)
                }
                41 => {
                    // Skipped when either side has nothing below its focus; see
                    // Fuzz.lean and lean/FINDINGS.md #8.
                    if focus_node_empty(&wz) || focus_node_empty(rz) {
                        ("restricting", "skip".to_string())
                    } else {
                        match (*rz).do_restricting(&mut wz) {
                            Some(b) => ("restricting", show_bool(b).to_string()),
                            None => ("restricting", "skip".to_string()),
                        }
                    }
                }
                42 => {
                    let k = get!(d.modn(4));
                    let _pr = get!(d.boolean()); // decoded for stream alignment; see `no_prune`
                    // `join_k_path_into(0)` destroys the subtrie in pathmap 0.3.1.
                    if k == 0 {
                        ("join_k_path_into", "skip".to_string())
                    } else {
                        // The bool leaks node materialisation; see FINDINGS.md #8.
                        let r = wz.join_k_path_into(k, no_prune);
                        let s = if focus_node_empty(&wz) {
                            "?".to_string()
                        } else {
                            show_bool(r).to_string()
                        };
                        ("join_k_path_into", s)
                    }
                }
                43 => {
                    let p = get!(d.path(6));
                    // `insert_prefix("")` destroys the subtrie in pathmap 0.3.1.
                    if p.is_empty() {
                        ("insert_prefix", "skip".to_string())
                    } else {
                        ("insert_prefix", show_bool(wz.insert_prefix(&p)).to_string())
                    }
                }
                44 => {
                    let n = get!(d.modn(6));
                    ("remove_prefix", show_bool(wz.remove_prefix(n)).to_string())
                }
                45 => {
                    let _pr = get!(d.boolean()); // decoded for stream alignment; see `no_prune`
                    let leaky = focus_node_empty(&wz) && wz.val().is_none();
                    let r = match wz.take_map(no_prune) {
                        Some(m) => {
                            wz.graft_map(m);
                            "1"
                        }
                        None => "0",
                    };
                    ("take_map_restore", if leaky { "?".to_string() } else { r.to_string() })
                }
                46 => {
                    let k = get!(d.modn(4));
                    let _pr = get!(d.boolean()); // decoded for stream alignment; see `no_prune`
                    // `meet_k_path_into` spins forever when the focus has no
                    // children, and escapes the focus subtree when k == 0.
                    // See `Zip.meetKPathUnspecified`.
                    if k == 0 || wz.child_count() == 0 {
                        ("meet_k_path_into", "skip".to_string())
                    } else {
                        (
                            "meet_k_path_into",
                            show_bool(wz.meet_k_path_into(k, no_prune)).to_string(),
                        )
                    }
                }
                48 => {
                    let v = get!(d.u8()) as u64;
                    // Writing through the reference `get_val_mut` hands back.
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
                49 => {
                    let v = get!(d.u8()) as u64;
                    let r = *wz.get_val_or_set_mut(v);
                    ("get_val_or_set_mut", show_val(Some(&r)))
                }
                50 => {
                    let v = get!(d.u8()) as u64;
                    // `ran` records whether the closure was invoked; the contract
                    // is that it supplies the value only when none exists.
                    let mut ran = false;
                    let r = *wz.get_val_or_set_mut_with(|| {
                        ran = true;
                        v
                    });
                    (
                        "get_val_or_set_mut_with",
                        format!("{}:{}", show_val(Some(&r)), show_bool(ran)),
                    )
                }
                51 => {
                    let t = get!(d.modn(2));
                    let p = get!(d.path(6));
                    // `get_val`/`get_val_at` must agree with `val`/`val_at`; they
                    // differ only in the lifetime of the reference returned.
                    let (g, ga, agree) = if t == 0 {
                        let (g, ga) = (wz.val().copied(), wz.val_at(&p).copied());
                        (g, ga, true) // a write zipper has no ZipperReadOnlyValues
                    } else {
                        rz.get_val_probe(&p)
                    };
                    (
                        "get_val_agrees",
                        format!(
                            "{}:{}:{}",
                            show_val(g.as_ref()),
                            show_val(ga.as_ref()),
                            show_bool(agree)
                        ),
                    )
                }
                52 => match rz.to_next_get_val_probe() {
                    Some((moved, v, agree)) => (
                        "to_next_get_val",
                        format!(
                            "{}:{}:{}",
                            show_bool(moved),
                            show_val(v.as_ref()),
                            show_bool(agree)
                        ),
                    ),
                    None => ("to_next_get_val", "skip".to_string()),
                },
                53 => {
                    let n = get!(d.modn(4));
                    let m = get!(d.path_n(n));
                    let ru = get!(d.boolean());
                    let mask = ByteMask::from_iter(m.iter().copied());
                    let mut canon: Vec<u8> = m.clone();
                    canon.sort_unstable();
                    canon.dedup();
                    let s = if (*rz).do_graft_masked(&mut wz, mask, ru) {
                        format!("{}:{}", hex_path(&canon), show_bool(ru))
                    } else {
                        "skip".to_string()
                    };
                    ("graft_masked_branches", s)
                }
                54 => {
                    let n = get!(d.modn(4));
                    let m = get!(d.path_n(n));
                    let ru = get!(d.boolean());
                    let mask = ByteMask::from_iter(m.iter().copied());
                    let mut canon: Vec<u8> = m.clone();
                    canon.sort_unstable();
                    canon.dedup();
                    // Skipped outright: `graft_child_maps` is broken three ways
                    // (lean/FINDINGS.md #15) and the node representations it
                    // leaves behind degrade the AlgebraicStatus that *later*
                    // operations report, contaminating the rest of the run.
                    let _ = (mask, ru, &canon);
                    ("graft_child_maps", "skip".to_string())
                }
                55 => {
                    let p = get!(d.path(6));
                    ("meet_2", show_status_opt((*rz).do_meet_2(&mut wz, &p)))
                }
                47 => {
                    let t = get!(d.modn(2));
                    // The blind-zipper addition: `descend_until` reporting the
                    // bytes it descended.  The observer's output is a blind
                    // zipper's only account of where it went, so it is compared
                    // byte for byte.
                    let mut obs: Vec<u8> = Vec::new();
                    let r = tgt!(t, wz, *rz, z, z.descend_until_observed(&mut obs));
                    (
                        "descend_until_observed",
                        format!("{}:{}", show_bool(r), hex_path(&obs)),
                    )
                }
                _ => ("nop", "-".to_string()),
            };
            if check {
                check_zipper(&wz, "write zipper", root0);
                check_zipper(rz, "read zipper", root1);
            }
            let _ = writeln!(out, 
                "{step} {name} ret={ret} W={} R={}",
                fingerprint(&wz, root0),
                fingerprint(rz, root1)
            );
            step += 1;
        }
    }

}
