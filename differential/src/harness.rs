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

pub(crate) const PATH_SET_NAMES: [&str; 10] = [
    "basis", "hull", "retain", "divergence", "branches",
    "zipper_basis", "zipper_hull", "zipper_retain", "zipper_divergence", "zipper_branches",
];

// The trace is written into one growable buffer rather than a `Vec<String>`.
// It used to be ~260 separately allocated `String`s per input, thrown away as
// soon as they were printed; only a divergence needs the individual lines, and
// `str::lines()` recovers them then.
use core::fmt::Write as _;

/// Selector count for newly generated inputs. Keep in sync with `lean/input_format.py`.
/// Keep operation IDs permanently assigned.
pub const NOPS: usize = 75;
/// Unversioned inputs retain their original operation decoding.
pub const LEGACY_NOPS: usize = 56;
/// Input header marker, followed by a little-endian u16 selector count (1..=256).
pub const WIRE_MAGIC: &[u8] = b"PMFUZZ\x01\x00";

/// Header for new inputs. Decoding always uses the recorded count, never `NOPS`.
pub fn input_header() -> Vec<u8> {
    assert!((1..=256).contains(&NOPS));
    let mut header = WIRE_MAGIC.to_vec();
    header.extend_from_slice(&(NOPS as u16).to_le_bytes());
    header
}
/// Maximum operations executed. Must match the `maxSteps` default in `Fuzz.run`.
pub const MAX_STEPS: usize = 256;
/// Maximum entries in a `dump`. Must match `Fuzz.dumpAt`.
pub const DUMP_CAP: usize = 64;

pub struct Dec<'a> {
    pub bytes: &'a [u8],
    pub pos: usize,
    op_count: usize,
}

impl<'a> Dec<'a> {
    pub fn new(bytes: &'a [u8]) -> Option<Self> {
        Self::with_format(bytes, WIRE_MAGIC, LEGACY_NOPS)
    }
    /// Decode an input in this wire format with another marker and op table:
    /// `magic`, then a little-endian u16 selector count (1..=256), or no header
    /// at all, which selects among `legacy_ops`.  The pruned fuzzer uses it.
    pub fn with_format(bytes: &'a [u8], magic: &[u8], legacy_ops: usize) -> Option<Self> {
        let (pos, op_count) = if bytes.starts_with(magic) {
            let count_bytes = bytes.get(magic.len()..magic.len() + 2)?;
            let count = u16::from_le_bytes([count_bytes[0], count_bytes[1]]) as usize;
            if !(1..=256).contains(&count) { return None; }
            (magic.len() + 2, count)
        } else {
            (0, legacy_ops)
        };
        Some(Self { bytes, pos, op_count })
    }
    /// A decoder with no header handling, for streams whose caller picks the
    /// operation itself (the pruned fuzzer).
    pub fn legacy(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0, op_count: LEGACY_NOPS }
    }
    pub fn op(&mut self) -> Option<usize> {
        self.modn(self.op_count)
    }
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
///
/// Only the default `ReadSource` impls return `None`, and only the ACT zipper
/// uses them, so the reason is always ACT mode.  See `SKIP_REASONS`.
pub fn show_status_opt<R: ReadSource>(s: Option<AlgebraicStatus>) -> String {
    match s {
        Some(s) => show_status(s).to_string(),
        None => R::SKIP.to_string(),
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
    fingerprint_with(z, expected_root, true)
}

/// [`fingerprint`], with `val_count` rendered as `?` when `val_count` is false
/// (the read source does not implement it; see `ReadSource::VAL_COUNT`).
pub fn fingerprint_with<Z: ZipperMoving + ZipperPath + ZipperValues<u64> + ZipperAbsolutePath>(
    z: &Z,
    expected_root: &[u8],
    val_count: bool,
) -> String {
    format!(
        "{}{} o{} e{} v{} c{} n{} f{}",
        if z.root_prefix_path() == expected_root { "" } else { "ESCAPED-ROOT " },
        hex_path(z.path()),
        hex_path(z.origin_path()),
        show_bool(z.path_exists()),
        show_val(z.val()),
        z.child_count(),
        if val_count { z.val_count().to_string() } else { "?".to_string() },
        // `focus_byte` is unspecified at the root, so it is only compared below it.
        if z.at_root() { "?".to_string() } else { show_byte_opt(z.focus_byte()) }
    )
}

/// Why an operation was skipped.  Every `skip` in the trace carries one of
/// these, so a skipped op says which rule declined it rather than just that
/// something declined it.  `lean/PathMapModel/Fuzz.lean` emits the same
/// tokens; the two must agree exactly or every input with a skip diverges.
///
/// * `skip:act` — the ACT read source cannot be a merge source
///   (`ZipperInfallibleSubtries` is not implemented for it) or does not
///   implement the trait the op needs.
/// * `skip:at-root` — `to_next`/`to_prev_sibling_byte` at the zipper root,
///   where the native read zipper escapes its own root.
/// * `skip:empty-focus` — the focus has nothing below it, where the op's
///   behaviour is a function of node materialisation rather than trie state.
/// * `skip:quarantined` — the op is disabled outright (op 54).
///
/// Each is recorded in lean/FINDINGS.md and commented at its site.
pub const SKIP_ACT: &str = "skip:act";
pub const SKIP_AT_ROOT: &str = "skip:at-root";
pub const SKIP_EMPTY_FOCUS: &str = "skip:empty-focus";
pub const SKIP_QUARANTINED: &str = "skip:quarantined";

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

/// Dump a fork at the current focus. A missing path retains the trace's empty
/// root marker, matching `Fuzz.dumpAt` on an absent subtree.
pub fn dump_fork<Z: ZipperForking<u64>>(z: &Z) -> String {
    match z.fork_read_zipper() {
        Some(mut fork) => dump(&mut fork),
        None => "_:-".to_string(),
    }
}

/// The values at and below the focus, from [dump_fork], without the dangling locations
pub fn fork_values<Z: ZipperForking<u64>>(z: &Z) -> Vec<String> {
    dump_fork(z).split(',').filter(|e| !e.ends_with(":-")).map(str::to_string).collect()
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
    Zipper + ZipperMoving + ZipperPath + ZipperValues<u64> + ZipperValuesAt<u64> + ZipperAbsolutePath + ZipperIteration
{
    /// The skip token emitted when this source cannot serve an operation (a
    /// method below returned `None`/`false`).  `skip:<source name>`; the Lean
    /// model's `Source.skip` must produce the same string.
    const SKIP: &'static str = SKIP_ACT;
    /// Whether `ZipperMoving::val_count` is implemented.  Several virtual
    /// zippers leave it `todo!()`/`unimplemented!()`; their per-step
    /// fingerprint then prints `n?` (the model's `Caps.valCount`).
    const VAL_COUNT: bool = true;
    /// Depth-first dump of everything below the focus (`fork_read_zipper` + walk),
    /// or `None` if the source does not implement `ZipperForking`.
    fn dump_fork(&self) -> Option<String>;
    /// `make_map().val_count()`, or `None` if subtries cannot be materialised.
    fn make_map_val_count(&self) -> Option<usize>;

    /// `ZipperReadOnlyValues::get_val` / `get_val_at`, paired with whether they
    /// agree with `val` / `val_at`.  The two differ only in the lifetime of the
    /// reference returned, so a disagreement is a defect.
    /// `None` when the source does not implement `ZipperReadOnlyValues`.
    fn get_val_probe(&self, path: &[u8]) -> Option<(Option<u64>, Option<u64>, bool)>;

    /// `ZipperReadOnlyIteration::to_next_get_val`: advance and hand back the
    /// value, with whether it agrees with `to_next_val` followed by `val`.
    /// `None` when the zipper does not implement the trait.
    fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)>;

    /// Convex operations use valued paths. ACT cannot materialise the RHS.
    fn convex(
        &mut self,
        _left: &PathMap<u64>,
        _subtract: bool,
        _zipper: bool,
    ) -> Option<PathMap<u64>> {
        None
    }

    /// Binary path-set operations require a native read source, as convex ops do.
    fn path_set(&mut self, _left: &PathMap<u64>, _op: usize) -> Option<PathMap<u64>> { None }

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
    fn convex(&mut self, left: &PathMap<u64>, subtract: bool, zipper: bool) -> Option<PathMap<u64>> {
        use pathmap::experimental::convex::*;
        Some(if zipper {
            let mut out = PathMap::new();
            if subtract {
                zipper_convex_subtract(&mut left.read_zipper(), self, &mut out.write_zipper());
            } else {
                zipper_convex_meet(&mut left.read_zipper(), self, &mut out.write_zipper());
            }
            out
        } else if subtract {
            convex_subtract(left, &self.make_map())
        } else {
            convex_meet(left, &self.make_map())
        })
    }

    fn path_set(&mut self, left: &PathMap<u64>, op: usize) -> Option<PathMap<u64>> {
        use pathmap::experimental::path_sets::*;
        Some(match op {
            67 => retain(left, &self.make_map()),
            68 => divergence(left, &self.make_map()).iter().map(|(p, ())| (p, 1)).collect(),
            72 => {
                let mut out = PathMap::new();
                zipper_retain(&mut left.read_zipper(), self, &mut out.write_zipper());
                out
            }
            73 => {
                let mut out = PathMap::new();
                zipper_divergence(&mut left.read_zipper(), self, &mut out.write_zipper());
                out.iter().map(|(p, ())| (p, 1)).collect()
            }
            _ => unreachable!("not a binary path-set operation"),
        })
    }


    const SKIP: &'static str = "skip:native";
    fn dump_fork(&self) -> Option<String> {
        Some(dump_fork(self))
    }
    fn make_map_val_count(&self) -> Option<usize> {
        Some(self.make_map().val_count())
    }
    fn get_val_probe(&self, path: &[u8]) -> Option<(Option<u64>, Option<u64>, bool)> {
        let (g, ga) = (self.get_val().copied(), self.get_val_at(path).copied());
        let agree = g == self.val().copied() && ga == self.val_at(path).copied();
        Some((g, ga, agree))
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

/// The write side of the harness: any write zipper over a `PathMap<u64>`.
///
/// `WriteZipperUntracked` (the default), `WriteZipperTracked` (from a
/// `ZipperHead`) and `WriteZipperOwned` all qualify, and the Lean model does not
/// distinguish them: they are three implementations of one specification.
pub trait WriteTarget:
    ZipperWriting<u64> + ZipperMoving + ZipperPath + ZipperValues<u64> + ZipperValuesAt<u64>
    + ZipperAbsolutePath + ZipperForking<u64> + ZipperInfallibleSubtries<u64>
{
}
impl<T> WriteTarget for T where
    T: ZipperWriting<u64> + ZipperMoving + ZipperPath + ZipperValues<u64> + ZipperValuesAt<u64>
        + ZipperAbsolutePath + ZipperForking<u64> + ZipperInfallibleSubtries<u64>
{
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
pub fn check_zipper<Z>(z: &Z, label: &str, expected_root: &[u8], val_count: bool)
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
    if val_count && z.is_val() {
        assert!(z.val_count() >= 1, "{label}: val_count omits the focus value");
    }
    // Nothing below means nothing to count except the focus.
    if val_count && z.child_count() == 0 {
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
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
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
        let mut wz = map0.write_zipper_at_path(&root0);
        run_ops(&mut d, &mut out, &mut wz, &root0, &mut rz, &root1, check);
    }
    let _ = writeln!(out, "MAP0 {}", dump(&mut map0.read_zipper()));
    let _ = writeln!(out, "MAP1 {}", dump(&mut map1.read_zipper()));
    let _ = writeln!(out, "ROOT0 {}", hex_path(&root0));
    let _ = writeln!(out, "ROOT1 {}", hex_path(&root1));
    out
}

/// Run the operation table.  This is the single shared body: the two front ends
/// differ only in what they hand in as `rz`.
/// Drops every dangling path below the focus, keeping the values and the focus
/// itself.  A meet with `prune = false` may leave some dangling paths, and which
/// ones is unspecified (see `PathMap.meet` in the model), so they are dropped
/// before anything can observe them.
pub fn drop_dangling_below<W: ZipperWriting<u64>>(wz: &mut W) {
    if let Some(m) = wz.take_map(false) {
        let mut fresh = PathMap::<u64>::new();
        if let Some(v) = m.val_at::<&[u8]>(&[]) {
            fresh.set_val_at::<&[u8]>(&[], *v);
        }
        for (k, v) in m.iter() {
            fresh.set_val_at(&k, *v);
        }
        wz.graft_map(fresh);
    }
}

pub fn run_ops<W: WriteTarget, R: ReadSource>(
    d: &mut Dec,
    out: &mut String,
    wz: &mut W,
    root0: &[u8],
    rz: &mut R,
    root1: &[u8],
    check: bool,
) {
    {
        let mut step = 0usize;
        // Run pruning at every zipper root so layout-dependent defects remain
        // visible to the differential comparison.

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
            let op = get!(d.op());
            let (name, ret): (&str, String) = match op {
                0 => {
                    let t = get!(d.modn(2));
                    let p = get!(d.path(6));
                    tgt!(t, *wz, *rz, z, z.descend_to(&p));
                    ("descend_to", hex_path(&p))
                }
                1 => {
                    let t = get!(d.modn(2));
                    let b = get!(d.path_byte());
                    tgt!(t, *wz, *rz, z, z.descend_to_byte(b));
                    ("descend_to_byte", format!("{b:02x}"))
                }
                2 => {
                    let t = get!(d.modn(2));
                    let n = get!(d.modn(8));
                    let r = tgt!(t, *wz, *rz, z, z.ascend(n));
                    ("ascend", format!("{r}"))
                }
                3 => {
                    let t = get!(d.modn(2));
                    let r = tgt!(t, *wz, *rz, z, z.ascend_byte());
                    ("ascend_byte", show_bool(r).to_string())
                }
                4 => {
                    let t = get!(d.modn(2));
                    tgt!(t, *wz, *rz, z, z.reset());
                    ("reset", "-".to_string())
                }
                5 => {
                    let t = get!(d.modn(2));
                    let r = tgt!(t, *wz, *rz, z, z.descend_first_byte());
                    ("descend_first_byte", show_byte_opt(r))
                }
                6 => {
                    let t = get!(d.modn(2));
                    let r = tgt!(t, *wz, *rz, z, z.descend_last_byte());
                    ("descend_last_byte", show_byte_opt(r))
                }
                7 => {
                    let t = get!(d.modn(2));
                    let i = get!(d.modn(6));
                    let r = tgt!(t, *wz, *rz, z, z.descend_indexed_byte(i));
                    ("descend_indexed_byte", show_byte_opt(r))
                }
                8 => {
                    let t = get!(d.modn(2));
                    let r = tgt!(t, *wz, *rz, z, z.descend_until());
                    ("descend_until", show_bool(r).to_string())
                }
                9 => {
                    let t = get!(d.modn(2));
                    let r = tgt!(t, *wz, *rz, z, z.ascend_until());
                    ("ascend_until", format!("{r}"))
                }
                10 => {
                    let t = get!(d.modn(2));
                    let r = tgt!(t, *wz, *rz, z, z.ascend_until_branch());
                    ("ascend_until_branch", format!("{r}"))
                }
                11 => {
                    let t = get!(d.modn(2));
                    // Skipped at the zipper root: the native ReadZipper escapes
                    // its own root there. See `Zip.toNextSiblingByte`.
                    if false {
                        ("to_next_sibling_byte", SKIP_AT_ROOT.to_string())
                    } else {
                        let r = tgt!(t, *wz, *rz, z, z.to_next_sibling_byte());
                        ("to_next_sibling_byte", show_byte_opt(r))
                    }
                }
                12 => {
                    let t = get!(d.modn(2));
                    if false {
                        ("to_prev_sibling_byte", SKIP_AT_ROOT.to_string())
                    } else {
                        let r = tgt!(t, *wz, *rz, z, z.to_prev_sibling_byte());
                        ("to_prev_sibling_byte", show_byte_opt(r))
                    }
                }
                13 => {
                    let t = get!(d.modn(2));
                    let r = tgt!(t, *wz, *rz, z, z.to_next_step());
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
                    // k == 0 is specified as an unsuccessful descent; see Fuzz.lean.
                    let r = (*rz).descend_first_k_path(k);
                    ("descend_first_k_path", show_bool(r).to_string())
                }
                16 => {
                    let _t = get!(d.modn(2));
                    let k = get!(d.modn(4));
                    // A whole k-path iteration: `to_next_k_path` on its own is
                    // unspecified (it continues state left by
                    // `descend_first_k_path`).
                    let mut v: Vec<String> = Vec::new();
                    // With k == 0 the descent fails and the walk is empty.
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
                    let n = tgt!(t, *wz, *rz, z, z.move_to_path(&p));
                    ("move_to_path", format!("{n}"))
                }
                19 => {
                    let t = get!(d.modn(2));
                    let p = get!(d.path(6));
                    let n = tgt!(t, *wz, *rz, z, z.descend_to_existing(&p));
                    ("descend_to_existing", format!("{n}"))
                }
                20 => {
                    let t = get!(d.modn(2));
                    let p = get!(d.path(6));
                    let n = tgt!(t, *wz, *rz, z, z.descend_to_val(&p));
                    ("descend_to_val", format!("{n}"))
                }
                21 => {
                    let t = get!(d.modn(2));
                    let b = get!(d.path_byte());
                    let r = tgt!(t, *wz, *rz, z, z.descend_to_existing_byte(b));
                    ("descend_to_existing_byte", show_bool(r).to_string())
                }
                22 => {
                    let t = get!(d.modn(2));
                    let n = get!(d.modn(8));
                    let r = tgt!(t, *wz, *rz, z, z.descend_until_max_bytes(n));
                    ("descend_until_max_bytes", show_bool(r).to_string())
                }
                23 => {
                    let t = get!(d.modn(2));
                    let p = get!(d.path(6));
                    let r = tgt!(t, *wz, *rz, z, z.descend_to_check(&p));
                    ("descend_to_check", show_bool(r).to_string())
                }
                24 => {
                    let t = get!(d.modn(2));
                    let p = get!(d.path(6));
                    let v = tgt!(t, *wz, *rz, z, show_val(z.val_at(&p)));
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
                        None => ("make_map_val_count", R::SKIP.to_string()),
                    }
                }
                26 => {
                    let t = get!(d.modn(2));
                    let s = if t == 0 {
                        Some(dump_fork(&*wz))
                    } else {
                        (*rz).dump_fork()
                    };
                    ("dump", s.unwrap_or_else(|| R::SKIP.to_string()))
                }
                27 => {
                    let v = get!(d.u8()) as u64;
                    ("set_val", show_val(wz.set_val(v).as_ref()))
                }
                28 => {
                    let pr = get!(d.boolean());
                    ("remove_val", show_val(wz.remove_val(pr).as_ref()))
                }
                29 => ("create_path", show_bool(wz.create_path()).to_string()),
                30 => ("prune_path", format!("{}", wz.prune_path())),
                31 => ("prune_ascend", format!("{}", wz.prune_ascend())),
                32 => {
                    let pr = get!(d.boolean());
                    let leaky = focus_node_empty(&*wz);
                    let r = wz.remove_branches(pr);
                    let s = if false && leaky { "?".to_string() } else { show_bool(r).to_string() };
                    ("remove_branches", s)
                }
                33 => {
                    let n = get!(d.modn(4));
                    let m = get!(d.path_n(n));
                    let pr = get!(d.boolean());
                    let mut canon: Vec<u8> = m.clone();
                    canon.sort_unstable();
                    canon.dedup();
                    let mask = ByteMask::from_iter(m.iter().copied());
                    wz.remove_unmasked_branches(mask, pr);
                    ("remove_unmasked_branches", hex_path(&canon))
                }
                34 => {
                    let s = if (*rz).do_graft(&mut *wz) { "-" } else { R::SKIP };
                    ("graft", s.to_string())
                }
                35 => {
                    let p = get!(d.path(6));
                    let s = if (*rz).do_graft_src_at(&mut *wz, &p) {
                        hex_path(&p)
                    } else {
                        R::SKIP.to_string()
                    };
                    ("graft_src_at", s)
                }
                36 => ("join_into", show_status_opt::<R>((*rz).do_join_into(&mut *wz))),
                37 => {
                    let leaky = focus_node_empty(&*wz);
                    let st = (*rz).do_join_map_into(&mut *wz);
                    let s = if false && leaky && st.is_some() {
                        "?".to_string()
                    } else {
                        show_status_opt::<R>(st)
                    };
                    ("join_map_into", s)
                }
                38 => {
                    let pr = get!(d.boolean());
                    let before = fork_values(&*wz);
                    let mut st = (*rz).do_meet_into(&mut *wz, pr);
                    // A meet that leaves the values alone may report `Element` as well as
                    // `Identity`: it is allowed to drop dangling paths, which is a change
                    if st == Some(AlgebraicStatus::Element) && fork_values(&*wz) == before {
                        st = Some(AlgebraicStatus::Identity);
                    }
                    if st.is_some() && !pr { drop_dangling_below(&mut *wz); }
                    ("meet_into", show_status_opt::<R>(st))
                }
                39 => {
                    let pr = get!(d.boolean());
                    ("subtract_into", show_status_opt::<R>((*rz).do_subtract_into(&mut *wz, pr)))
                }
                40 => {
                    let leaky = focus_node_empty(&*wz);
                    let st = (*rz).do_restrict(&mut *wz);
                    let s = if false && leaky && st.is_some() {
                        "?".to_string()
                    } else {
                        show_status_opt::<R>(st)
                    };
                    ("restrict", s)
                }
                41 => {
                    // Skipped when either side has nothing below its focus; see
                    // Fuzz.lean and lean/FINDINGS.md #8.
                    if false {
                        ("restricting", SKIP_EMPTY_FOCUS.to_string())
                    } else {
                        match (*rz).do_restricting(&mut *wz) {
                            Some(b) => ("restricting", show_bool(b).to_string()),
                            None => ("restricting", R::SKIP.to_string()),
                        }
                    }
                }
                42 => {
                    let k = get!(d.modn(4));
                    let pr = get!(d.boolean());
                    // The bool leaks node materialisation; see FINDINGS.md #8.
                    let r = wz.join_k_path_into(k, pr);
                    let s = if false {
                        "?".to_string()
                    } else {
                        show_bool(r).to_string()
                    };
                    ("join_k_path_into", s)
                }
                43 => {
                    let p = get!(d.path(6));
                    ("insert_prefix", show_bool(wz.insert_prefix(&p)).to_string())
                }
                44 => {
                    let n = get!(d.modn(6));
                    ("remove_prefix", wz.remove_prefix(n).to_string())
                }
                45 => {
                    let pr = get!(d.boolean());
                    let leaky = focus_node_empty(&*wz) && wz.val().is_none();
                    let r = match wz.take_map(pr) {
                        Some(m) => {
                            wz.graft_map(m);
                            "1"
                        }
                        None => "0",
                    };
                    ("take_map_restore", if false && leaky { "?".to_string() } else { r.to_string() })
                }
                46 => {
                    let k = get!(d.modn(4));
                    let pr = get!(d.boolean());
                    let r = wz.meet_k_path_into(k, pr);
                    if !pr { drop_dangling_below(&mut *wz); }
                    ("meet_k_path_into", show_bool(r).to_string())
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
                    let probe = if t == 0 {
                        let (g, ga) = (wz.val().copied(), wz.val_at(&p).copied());
                        Some((g, ga, true)) // a write zipper has no ZipperReadOnlyValues
                    } else {
                        rz.get_val_probe(&p)
                    };
                    match probe {
                        Some((g, ga, agree)) => (
                            "get_val_agrees",
                            format!(
                                "{}:{}:{}",
                                show_val(g.as_ref()),
                                show_val(ga.as_ref()),
                                show_bool(agree)
                            ),
                        ),
                        None => ("get_val_agrees", R::SKIP.to_string()),
                    }
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
                    None => ("to_next_get_val", R::SKIP.to_string()),
                },
                53 => {
                    let n = get!(d.modn(4));
                    let m = get!(d.path_n(n));
                    let ru = get!(d.boolean());
                    let mask = ByteMask::from_iter(m.iter().copied());
                    let mut canon: Vec<u8> = m.clone();
                    canon.sort_unstable();
                    canon.dedup();
                    let s = if (*rz).do_graft_masked(&mut *wz, mask, ru) {
                        format!("{}:{}", hex_path(&canon), show_bool(ru))
                    } else {
                        R::SKIP.to_string()
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
                    let _ = SKIP_QUARANTINED;
                    let s = if (*rz).do_graft_child_maps(&mut *wz, mask, ru) { format!("{}:{}", hex_path(&canon), show_bool(ru)) } else { R::SKIP.to_string() };
                    ("graft_child_maps", s)
                }
                55 => {
                    let p = get!(d.path(6));
                    // `meet_2` has no prune flag: it may leave dangling paths, like `prune = false`
                    let st = (*rz).do_meet_2(&mut *wz, &p);
                    if st.is_some() { drop_dangling_below(&mut *wz); }
                    ("meet_2", show_status_opt::<R>(st))
                }
                56 => {
                    let pr = get!(d.boolean());
                    ("remove_subtrie", show_bool(wz.remove_subtrie(pr)).to_string())
                }
                57 => {
                    let _t = get!(d.modn(2));
                    ("descend_last_val", show_bool(rz.descend_last_val()).to_string())
                }
                58 => {
                    let t = get!(d.modn(2));
                    let r = tgt!(t, *wz, *rz, z, z.to_prev_step());
                    ("to_prev_step", show_bool(r).to_string())
                }
                59 => {
                    let _t = get!(d.modn(2));
                    ("to_prev_val", show_bool(rz.to_prev_val()).to_string())
                }
                60 => {
                    let p = get!(d.path(6));
                    let v = get!(d.u8()) as u64;
                    ("set_val_at", show_val(wz.set_val_at(&p, v).as_ref()))
                }
                61..=64 => {
                    let name = match op {
                        61 => "convex_meet",
                        62 => "convex_subtract",
                        63 => "zipper_convex_meet",
                        _ => "zipper_convex_subtract",
                    };
                    let ret = if let Some(result) = rz.convex(&wz.make_map(), op % 2 == 0, op >= 63) {
                        // Convex algebra specifies values, not bare structure.
                        // Rebuild the result's valued projection before grafting,
                        // matching the pruned Lean model.
                        // Do not truncate: subsequent ops observe the entire map.
                        let canonical: PathMap<u64> = result.iter().map(|(p, v)| (p, *v)).collect();
                        wz.graft_map(canonical);
                        "-"
                    } else {
                        R::SKIP
                    };
                    (name, ret.to_string())
                }
                65..=74 => {
                    use pathmap::experimental::path_sets::*;
                    let left = wz.make_map();
                    let result = match op {
                        65 => Some(basis(&left)),
                        66 => Some(hull(&left)),
                        69 => Some(branches(&left).iter().map(|(p, ())| (p, 1)).collect()),
                        70 | 71 => {
                            let mut out = PathMap::new();
                            if op == 70 {
                                zipper_basis(&mut left.read_zipper(), &mut out.write_zipper());
                            } else {
                                zipper_hull(&mut left.read_zipper(), &mut out.write_zipper());
                            }
                            Some(out)
                        }
                        74 => {
                            let mut out = PathMap::new();
                            zipper_branches(&mut left.read_zipper(), &mut out.write_zipper());
                            Some(out.iter().map(|(p, ())| (p, 1)).collect())
                        }
                        _ => rz.path_set(&left, op),
                    };
                    let ret = if let Some(result) = result {
                        // The pruned model observes valued paths only. Branch
                        // points carry 1 in this homogeneous u64 interpreter.
                        wz.graft_map(result.iter().map(|(p, v)| (p, *v)).collect());
                        "-"
                    } else { R::SKIP };
                    (PATH_SET_NAMES[op - 65], ret.to_string())
                }
                47 => {
                    let t = get!(d.modn(2));
                    // The blind-zipper addition: `descend_until` reporting the
                    // bytes it descended.  The observer's output is a blind
                    // zipper's only account of where it went, so it is compared
                    // byte for byte.
                    let mut obs: Vec<u8> = Vec::new();
                    let r = tgt!(t, *wz, *rz, z, z.descend_until_observed(&mut obs));
                    (
                        "descend_until_observed",
                        format!("{}:{}", show_bool(r), hex_path(&obs)),
                    )
                }
                _ => ("nop", "-".to_string()),
            };
            if check {
                check_zipper(&*wz, "write zipper", root0, true);
                check_zipper(rz, "read zipper", root1, R::VAL_COUNT);
            }
            let _ = writeln!(out, 
                "{step} {name} ret={ret} W={} R={}",
                fingerprint(&*wz, root0),
                fingerprint_with(rz, root1, R::VAL_COUNT)
            );
            step += 1;
        }
    }
    // The read source walked from its own root after the program: `reset` and a
    // full depth-first traversal, through the source itself.
    let _ = writeln!(out, "SRC {}", dump(rz));

}

#[cfg(test)]
mod input_format_tests {
    use super::*;
    use crate::{emit_repro, run_act};

    #[test]
    fn unversioned_inputs_keep_legacy_operation_decoding() {
        let bytes: Vec<u8> = (0..=255).collect();
        let mut d = Dec::new(&bytes).unwrap();
        for byte in 0..=255 {
            assert_eq!(d.op(), Some(byte % 56));
        }
    }

    #[test]
    fn input_header_count_controls_decoding_independently_of_current_operation_count() {
        for count in [1u16, 32, 56, 57, 58, 61, 65, 75, 256] {
            let mut bytes = WIRE_MAGIC.to_vec();
            bytes.extend_from_slice(&count.to_le_bytes());
            bytes.extend(0..=255);
            let mut d = Dec::new(&bytes).unwrap();
            for byte in 0..=255 {
                assert_eq!(d.op(), Some(byte % count as usize));
            }
        }
    }

    #[test]
    fn invalid_or_truncated_input_headers_are_rejected() {
        let mut bytes = WIRE_MAGIC.to_vec();
        assert!(Dec::new(&bytes).is_none());
        bytes.push(57);
        assert!(Dec::new(&bytes).is_none());
        for count in [0u16, 257, u16::MAX] {
            let mut bytes = WIRE_MAGIC.to_vec();
            bytes.extend_from_slice(&count.to_le_bytes());
            assert!(Dec::new(&bytes).is_none());
            assert_eq!(run(&bytes, true), "EMPTY\n");
            assert_eq!(run_act(&bytes, true), "EMPTY\n");
        }
    }

    #[test]
    fn header_count_56_preserves_legacy_replay_and_reproducer() {
        for legacy in [
            include_bytes!("../../lean/corpus/status-imprecise-join_map_into.bin").as_slice(),
            include_bytes!("../../lean/corpus/status-imprecise-restrict.bin").as_slice(),
        ] {
            let mut bytes = WIRE_MAGIC.to_vec();
            bytes.extend_from_slice(&56u16.to_le_bytes());
            bytes.extend_from_slice(legacy);
            assert_eq!(run(&bytes, false), run(legacy, false));
            assert_eq!(run_act(&bytes, false), run_act(legacy, false));
            assert_eq!(emit_repro(&bytes, 256), emit_repro(legacy, 256));
        }
    }

    #[test]
    fn convex_programs_prune_to_stability_and_preserve_left_payloads() {
        // A = {root, 0, 01}, B = {root, 0, 02}. A single pruning pass
        // wrongly keeps root instead of pruning the whole chain.
        let seeds = [
            3, 0, 10, 1, 0, 11, 2, 0, 1, 12, 3, 0, 20, 1, 0, 21, 2, 0, 2, 22, 0, 0,
        ];
        for (op, name) in [
            (61, "convex_meet"),
            (62, "convex_subtract"),
            (63, "zipper_convex_meet"),
            (64, "zipper_convex_subtract"),
        ] {
            let mut bytes = input_header();
            bytes.extend_from_slice(&seeds);
            bytes.extend_from_slice(&[op, op]);
            let trace = run(&bytes, true);
            let expected = if op % 2 == 0 {
                "MAP0 _:10,00:11,0001:12"
            } else {
                "MAP0 _:-"
            };
            assert!(trace.contains(expected), "{trace}");
            assert!(trace.contains(&format!("1 {name} ret=-")), "{trace}");
            let act = run_act(&bytes, false);
            assert!(act.contains(&format!("0 {name} ret=skip:act")), "{act}");
            assert!(act.contains("MAP0 _:10,00:11,0001:12"), "{act}");
            assert!(emit_repro(&bytes, 256).contains(&format!("::{name}(")));

            // Same domain, different payloads: both kernels retain the LHS
            // on meet and remove everything on subtract.
            let mut equal = input_header();
            equal.extend_from_slice(&[2, 0, 10, 1, 0, 11, 2, 0, 20, 1, 0, 21, 0, 0, op]);
            let trace = run(&equal, true);
            let expected = if op % 2 == 0 {
                "MAP0 _:-"
            } else {
                "MAP0 _:10,00:11"
            };
            assert!(trace.contains(expected), "{trace}");
        }
    }

    #[test]
    fn convex_programs_use_relative_focus_and_ignore_bare_extensions() {
        for op in 61..=64 {
            let mut bytes = input_header();
            bytes.extend_from_slice(&[
                3, 1, 3, 99, 1, 1, 7, 2, 1, 0, 8, // LHS: outside, root, tip.
                1, 2, 2, 0, 42, // RHS: matching tip, different value.
                1, 1, 1, 2, // Roots [1], [2].
                0, 0, 2, 0, 3, 29, 4, 0, // Create bare extension of LHS tip, reset.
                op, 60, 1, 1, 55, // Following write tests operand alignment and restored focus.
            ]);
            let trace = run(&bytes, true);
            let expected = if op % 2 == 0 {
                "MAP0 _:-,01:-,0101:55,03:99"
            } else {
                "MAP0 _:-,01:-,0100:8,0101:55,03:99"
            };
            assert!(trace.contains(expected), "{trace}");
            assert!(trace.contains("4 set_val_at ret=- W=_ o01"), "{trace}");
            assert!(trace.contains("R=_ o02"), "{trace}");
        }
    }

    #[test]
    fn path_set_programs_and_reproducers_preserve_the_wire_contract() {
        for op in 65u8..75 {
            let mut bytes = input_header();
            bytes.extend_from_slice(&[
                4, 0, 10, 1, 0, 11, 2, 0, 1, 12, 2, 0, 2, 13,
                3, 0, 20, 1, 0, 21, 2, 0, 3, 22, 0, 0,
                op,
            ]);
            let name = PATH_SET_NAMES[(op - 65) as usize];
            let expected = match (op - 65) % 5 {
                0 => "MAP0 _:10",
                1 => "MAP0 _:-,00:-,0001:12,0002:13",
                2 => "MAP0 _:10,00:11",
                _ => "MAP0 _:-,00:1",
            };
            let trace = run(&bytes, true);
            assert!(trace.lines().any(|line| line == expected), "{name}: {trace}");
            assert!(trace.contains(&format!("0 {name} ret=-")), "{trace}");
            let act = run_act(&bytes, false);
            if matches!((op - 65) % 5, 2 | 3) {
                assert!(act.contains(&format!("0 {name} ret=skip:act")), "{act}");
                assert!(act.contains("MAP0 _:10,00:11,0001:12,0002:13"), "{act}");
            } else {
                assert!(act.lines().any(|line| line == expected), "{act}");
            }
            let repro = emit_repro(&bytes, 256);
            assert!(repro.contains(&format!("::{name}(")), "{repro}");
        }
        // Previously recorded 65-selector programs still decode 65 as op 0.
        let mut old = WIRE_MAGIC.to_vec();
        old.extend_from_slice(&65u16.to_le_bytes());
        old.extend_from_slice(&[0, 0, 0, 0, 65, 0, 1, 2]);
        assert!(run(&old, true).contains("0 descend_to ret=02"));
    }

    #[test]
    fn old_selector_count_does_not_decode_convex_operations() {
        let mut bytes = WIRE_MAGIC.to_vec();
        bytes.extend_from_slice(&61u16.to_le_bytes());
        bytes.extend_from_slice(&[0, 0, 0, 0, 61, 0, 1, 2]);
        let trace = run(&bytes, true);
        assert!(trace.contains("0 descend_to"), "{trace}");
        assert!(!trace.contains("convex"), "{trace}");
        assert!(emit_repro(&bytes, 256).contains("wz.descend_to(&[2u8]);"));
    }

    #[test]
    fn trace_and_reproducer_decode_relative_writes() {
        let mut bytes = input_header();
        bytes.extend_from_slice(&[
            0, 0, 0, 0, // Empty maps and zipper roots.
            0, 0, 1, 1, // Descend the write zipper to [1].
            60, 2, 0, 1, 0, // [0,1] := 0.
            60, 2, 0, 2, 1, // [0,2] := 1.
            60, 2, 0, 1, 2, // [0,1] := 2, replacing 0 (issue #175).
            60, 0, 9, 60, 0, 10, // Empty path writes the focus, then replaces it.
            60, 2, 3, // Truncated path must not execute a write.
        ]);
        for trace in [run(&bytes, true), run_act(&bytes, false)] {
            for expected in [
                "1 set_val_at ret=- W=01",
                "2 set_val_at ret=- W=01",
                "3 set_val_at ret=0 W=01",
                "4 set_val_at ret=- W=01",
                "5 set_val_at ret=9 W=01",
                "MAP0 _:-,01:10,0100:-,010001:2,010002:1",
            ] {
                assert!(trace.contains(expected), "missing {expected}:\n{trace}");
            }
            assert!(!trace.contains("6 set_val_at"), "{trace}");
        }
        let repro = emit_repro(&bytes, 256);
        assert!(repro.contains("wz.set_val_at(&[0u8, 1], 2);"), "{repro}");
        assert!(repro.contains("wz.set_val_at(&[], 10);"), "{repro}");

        // With 60 selectors, byte 60 remains descend_to (op 0), not a write.
        let mut old = WIRE_MAGIC.to_vec();
        old.extend_from_slice(&60u16.to_le_bytes());
        old.extend_from_slice(&[0, 0, 0, 0, 60, 0, 1, 2]);
        let trace = run(&old, true);
        assert!(trace.contains("0 descend_to"), "{trace}");
        assert!(!trace.contains("set_val_at"), "{trace}");
    }

    #[test]
    fn trace_and_reproducer_decode_reverse_iteration() {
        let mut bytes = input_header();
        bytes.extend_from_slice(&[
            2, 1, 0, 10, 1, 2, 20, // map0: [0], [2].
            4, 0, 9, 1, 0, 11, 2, 0, 1, 12, 1, 2, 13, // map1: [], [0], [0,1], [2].
            0, 0, // Zipper roots.
            0, 0, 3, 3, 3, 3, // Missing write focus [3,3,3].
            58, 0, 58, 0, 58, 0, 58, 0, // Step backward, exhaust, wrap.
            57, 1, // Initialize reverse value iteration at [2].
            59, 1, 59, 1, 59, 1, 59, 1, // Iterate, exhaust at the valued root, wrap.
        ]);
        // ACT's known val_count defect prevents --check at a missing focus.
        for trace in [run(&bytes, true), run_act(&bytes, false)] {
            for expected in [
                "1 to_prev_step ret=1 W=02",
                "2 to_prev_step ret=1 W=00",
                "3 to_prev_step ret=0 W=_",
                "4 to_prev_step ret=1 W=02",
                "5 descend_last_val ret=1",
                "6 to_prev_val ret=1",
                "7 to_prev_val ret=1",
                "8 to_prev_val ret=0",
                "9 to_prev_val ret=1",
            ] {
                assert!(trace.contains(expected), "missing {expected}:\n{trace}");
            }
        }
        let repro = emit_repro(&bytes, 256);
        assert!(repro.contains("wz.to_prev_step();"));
        assert!(repro.contains("rz.to_prev_val();"));
        assert!(repro.contains("rz.descend_last_val();"));
    }

    #[test]
    fn trace_and_reproducer_decode_last_value_descent() {
        let mut bytes = input_header();
        bytes.extend_from_slice(&[
            0, // map0 empty.
            3, 0, 9, 1, 0, 10, 2, 0, 1, 11, // map1: [], [0], [0,1].
            0, 0, // Zipper roots.
            57, 1, 57, 1, // Find the last value; succeed again without movement.
            0, 1, 1, 3, // Descend to missing [0,1,3].
            57, 1, // Fail without leaving that subtree.
        ]);
        let trace = run(&bytes, true);
        assert!(trace.contains("0 descend_last_val ret=1"), "{trace}");
        assert!(trace.contains("1 descend_last_val ret=1"), "{trace}");
        assert!(trace.contains("3 descend_last_val ret=0"), "{trace}");
        assert!(trace.contains("R=000103 o000103 e0"), "{trace}");
        assert!(emit_repro(&bytes, 256).contains("rz.descend_last_val();"));
    }

    #[test]
    fn trace_and_reproducer_decode_headered_write_operations() {
        // Clear [0] and its descendant, prune the dangling focus, then write there again.
        let mut bytes = input_header();
        bytes.extend_from_slice(&[
            4, 0, 9, 1, 0, 10, 2, 0, 1, 12, 1, 1, 11, // map0 entries.
            1, 1, 2, 13, // map1 entry.
            0, 0, // Zipper roots.
            0, 0, 1, 0, // Descend to [0].
            56, 0, 56, 1, 27, 14, // Remove, prune, then reuse.
        ]);
        let trace = run(&bytes, true);
        assert!(
            trace.contains("1 remove_subtrie ret=1 W=00 o00 e1 v- c0 n0"),
            "{trace}"
        );
        assert!(
            trace.contains("2 remove_subtrie ret=0 W=00 o00 e0 v- c0 n0"),
            "{trace}"
        );
        assert!(trace.contains("MAP0 _:9,00:14,01:11"), "{trace}");
        assert!(trace.contains("MAP1 _:-,02:13"), "{trace}");
        let repro = emit_repro(&bytes, 256);
        assert!(repro.contains("wz.remove_subtrie(false);"));
        assert!(repro.contains("wz.remove_subtrie(true);"));
        assert!(repro.contains("wz.set_val(14);"));
    }
}
