//! A second op table for `pathmap`, with no model behind it: an input only has
//! to run to the end without a panic, a failed debug assertion, an abort or a
//! hang.
//!
//! [`crate::harness`] is differential, so it can only reach what the Lean model
//! specifies, and that leaves a lot of the crate alone.  This table covers that
//! surface.  It has no trace, no lockstep partner and nothing to agree with, so
//! it can grow freely:
//!
//! * **paths** outside the harness's 4-letter alphabet and 5-byte limit: bytes
//!   spread over all four `ByteMask` words, full bytes, and keys up to 67 bytes,
//!   longer than a list node holds inline;
//! * **value types** other than `u64`: `()`, `bool` and `u16`, whose lattice
//!   impls report identities differently;
//! * **`prune = true`** on every operation that takes it, and `prune_path` /
//!   `prune_ascend` off the map root;
//! * **`PathMap` methods** the harness never calls: `insert`/`remove`/`get_mut`,
//!   `remove_branches_at`, map-level `join`/`meet`/`subtract`/`restrict` and the
//!   `Lattice` impls, clones and copy-on-write, `iter`/`from_iter`, `merkleize`,
//!   `new_from_ana`;
//! * **zipper kinds**: owned read and write zippers, `read_zipper_at_borrowed_path`,
//!   forks, `TrieRef`, `ZipperHead` and `ZipperHeadOwned` with several zippers
//!   live at once, `ProductZipper`, `ProductZipperG`,
//!   `DependentProductZipperG`, `OverlayZipper`, `PrefixZipper`, `EmptyZipper`
//!   and the ACT zipper;
//! * **operations** absent from the harness: `join_into_take`, `drop_head`,
//!   `graft_map` on arbitrary maps, `meet_2` over two independent sources,
//!   `take_map` without restoring, `meet_k_path_into` on any focus, `k = 0`,
//!   witnesses, the `_observed` variants, `descend_indexed_branch`,
//!   `reserve_buffers`, `get_focus`, `try_borrow_focus`;
//! * **catamorphisms** in all four flavours, fallible ones stopping early, and
//!   `hash`;
//! * **`.paths` serialization**, round trips and decoding of corrupted streams.
//!
//! Calls with a *documented* panic are made to satisfy the documented
//! precondition (see [`KNOWN_PRECONDITIONS`]); anything else that panics is a
//! finding.
//!
//! # Wire format
//!
//! Byte-oriented like the harness's, so AFL mutations land on operands: every
//! operand is one or a few bytes reduced at the point of use, and a truncated
//! input is a shorter valid program.  The first byte picks the value type, then
//! come three seeded maps, then the op stream.

use std::io::Cursor;

use pathmap::PathMap;
use pathmap::arena_compact::ArenaCompactTree;
use pathmap::morphisms::Catamorphism;
use pathmap::paths_serialization::{deserialize_paths, for_each_deserialized_path, serialize_paths};
use pathmap::ring::{AlgebraicResult, DistributiveLattice, Lattice, SELF_IDENT};
use pathmap::utils::{BitMask, ByteMask};
use pathmap::zipper::*;

use crate::harness::{Dec, hex_path};

/// `CRASH_TRACE=1` prints every operation to stderr as it starts, so the last
/// line before a hang or a panic names the call that did it.
static TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();

macro_rules! note {
    ($($arg:tt)*) => {
        if *TRACE.get_or_init(|| std::env::var_os("CRASH_TRACE").is_some()) {
            eprintln!($($arg)*);
        }
    };
}

/// Total work per input, counted in operations including those inside episodes.
pub const MAX_STEPS: usize = 512;
/// How many steps one episode (one zipper's lifetime) may take.
const EPISODE_STEPS: usize = 48;
/// Maps in play.
const NMAPS: usize = 3;
/// Bound on any loop this file drives itself (iteration walks and the like).
const WALK: usize = 64;
/// A map that grows past this many values stops accepting growth ops, so a run
/// of `insert_prefix` and joins cannot turn one input into a memory benchmark.
const MAX_VALS: usize = 4096;

/// Known failures the table steers around unless [`set_include_known`] says
/// otherwise, so a survey reports what is new.  Each is either a documented
/// stub or a documented open issue.
pub const KNOWN_FAILURES: &[&str] = &[
    "val_count is todo!/unimplemented! on OverlayZipper, ProductZipperG and DependentProductZipperG",
    "TrieRef::fork_read_zipper panics on a TrieRef at a non-existent path (GOAT, issue #96)",
    "k == 0 is degenerate for k-path iteration, join_k_path_into and drop_head (the harness skips it as \
     skip:k0): it spins on several zipper kinds and trips `debug_assert!(byte_cnt > 0)` in drop_head",
    "to_next_k_path without a preceding descend_first_k_path continues state nothing set up; the harness \
     only runs whole walks, and alone it underflows path_len (and read_zipper_at_borrowed_path's)",
    "meet_k_path_into spins forever when the focus has no children, and escapes it when k == 0 \
     (see Zip.meetKPathUnspecified in the Lean model)",
];

static INCLUDE_KNOWN: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

/// Run the calls listed in [`KNOWN_FAILURES`] as well.
pub fn set_include_known(on: bool) {
    INCLUDE_KNOWN.store(on, std::sync::atomic::Ordering::Relaxed);
}

fn include_known() -> bool {
    INCLUDE_KNOWN.load(std::sync::atomic::Ordering::Relaxed)
}

thread_local! {
    /// Set while driving a zipper type whose `val_count` is a stub.
    static VAL_COUNT_STUB: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Marks the current episode as driving a `val_count` stub, until dropped.
struct ValCountStub;

impl ValCountStub {
    fn new() -> Self {
        VAL_COUNT_STUB.with(|c| c.set(true));
        ValCountStub
    }
}

impl Drop for ValCountStub {
    fn drop(&mut self) {
        VAL_COUNT_STUB.with(|c| c.set(false));
    }
}

fn val_count_ok() -> bool {
    include_known() || !VAL_COUNT_STUB.with(|c| c.get())
}

/// Preconditions this table deliberately satisfies, because the crate documents
/// a panic when they are broken.  Anything else that panics is a finding.
pub const KNOWN_PRECONDITIONS: &[&str] = &[
    "ProductZipper::new: secondary factors must be at node roots (factors are map-root zippers)",
    "TrieBuilder::push / push_byte / graft_at_byte: first bytes strictly increasing",
    "TrieBuilder::graft_at_byte: the source focus must hold a node (called only with children below)",
    "graft_child_maps: at least one map per set bit of the mask",
];

/// A value type the table can run over.
pub trait CrashValue:
    Clone + Send + Sync + Unpin + Lattice + DistributiveLattice + core::hash::Hash + core::fmt::Debug + Default + 'static
{
    fn from_byte(b: u8) -> Self;
    fn to_u64(&self) -> u64;
}

impl CrashValue for u64 {
    fn from_byte(b: u8) -> Self { b as u64 }
    fn to_u64(&self) -> u64 { *self }
}
impl CrashValue for u16 {
    fn from_byte(b: u8) -> Self { (b as u16) << (b % 9) }
    fn to_u64(&self) -> u64 { *self as u64 }
}
impl CrashValue for bool {
    fn from_byte(b: u8) -> Self { b & 1 == 1 }
    fn to_u64(&self) -> u64 { *self as u64 }
}
impl CrashValue for () {
    fn from_byte(_: u8) -> Self {}
    fn to_u64(&self) -> u64 { 0 }
}

// ---------------------------------------------------------------------------
// Operand decoding
// ---------------------------------------------------------------------------

/// A path over one of three alphabets, chosen by the low two bits of its header
/// byte: `0..4` (so paths share prefixes, as in the harness), sixteen bytes
/// spread over the whole range (so all four mask words are used), or any byte.
/// The rest of the header picks the length: mostly `0..7`, sometimes 7 to 67.
fn path(d: &mut Dec) -> Option<Vec<u8>> {
    let h = d.u8()?;
    let s = (h >> 2) as usize;
    let len = if s < 48 { s % 7 } else { 7 + (s - 48) * 4 };
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        let b = d.u8()?;
        v.push(match h & 3 {
            0 | 1 => b % 4,
            2 => (b % 16) * 17,
            _ => b,
        });
    }
    note!("  path {}", hex_path(&v));
    Some(v)
}

/// A short path, for places where a long one only costs time.
fn short_path(d: &mut Dec) -> Option<Vec<u8>> {
    let mut p = path(d)?;
    p.truncate(8);
    note!("  short_path {}", hex_path(&p));
    Some(p)
}

/// One byte, mostly from the small alphabet so it hits existing children.
fn byte(d: &mut Dec) -> Option<u8> {
    let b = d.u8()?;
    if b < 160 { Some(b % 4) } else { d.u8() }
}

fn mask(d: &mut Dec) -> Option<ByteMask> {
    let n = d.modn(6)?;
    let mut m = ByteMask::EMPTY;
    for _ in 0..n {
        m.set_bit(byte(d)?);
    }
    note!("  mask {:?}", m.iter().collect::<Vec<u8>>());
    Some(m)
}

fn val<V: CrashValue>(d: &mut Dec) -> Option<V> {
    let b = d.u8()?;
    note!("  val {b}");
    Some(V::from_byte(b))
}

/// Result of a map-level lattice operation, as a map.
fn resolve<V: CrashValue>(r: AlgebraicResult<PathMap<V>>, a: &PathMap<V>, b: &PathMap<V>) -> PathMap<V> {
    match r {
        AlgebraicResult::None => PathMap::new(),
        AlgebraicResult::Identity(m) => if m & SELF_IDENT != 0 { a.clone() } else { b.clone() },
        AlgebraicResult::Element(x) => x,
    }
}

/// Count one step against the input's budget; `None` ends the input.
fn tick(steps: &mut usize) -> Option<()> {
    *steps += 1;
    if *steps > MAX_STEPS { None } else { Some(()) }
}

/// The per-input state: the maps, and the step budget shared by everything.
pub struct State<V: CrashValue> {
    pub maps: [PathMap<V>; NMAPS],
    steps: usize,
}

impl<V: CrashValue> State<V> {
    fn small(&self, m: usize) -> bool {
        self.maps[m].val_count() < MAX_VALS
    }
}

// ---------------------------------------------------------------------------
// Steps shared by every zipper kind
// ---------------------------------------------------------------------------

// Observers are started from the zipper's current path: a `Vec<u8>` or `usize`
// observer mirrors the path, and an ascent above where it started would underflow it.

/// One movement or query.  Everything a `ZipperMoving + ZipperPath` offers.
fn move_step<Z: ZipperMoving + ZipperPath>(d: &mut Dec, z: &mut Z) -> Option<()> {
    let __op = d.modn(34)?;
    note!("move {__op} at {}", hex_path(z.path()));
    match __op {
        0 => { let p = path(d)?; note!("  p={}", hex_path(&p)); z.descend_to(&p); }
        1 => { let b = byte(d)?; z.descend_to_byte(b); }
        2 => { let p = path(d)?; let _ = z.descend_to_check(&p); }
        3 => { let p = path(d)?; let _ = z.descend_to_existing(&p); }
        4 => { let p = path(d)?; let _ = z.descend_to_val(&p); }
        5 => { let b = byte(d)?; let _ = z.descend_to_existing_byte(b); }
        6 => { let i = d.modn(8)?; let _ = z.descend_indexed_byte(i); }
        #[allow(deprecated)]
        7 => { let i = d.modn(8)?; let _ = z.descend_indexed_branch(i); }
        8 => { let _ = z.descend_first_byte(); }
        9 => { let _ = z.descend_last_byte(); }
        10 => { let _ = z.descend_until(); }
        11 => { let mut o = z.path().to_vec(); let _ = z.descend_until_observed(&mut o); }
        12 => { let n = d.modn(12)?; let _ = z.descend_until_max_bytes(n); }
        13 => { let n = d.modn(12)?; let mut o = z.path().len(); let _ = z.descend_until_max_bytes_observed(n, &mut o); }
        14 => { let n = d.modn(12)?; let _ = z.ascend(n); }
        15 => { let _ = z.ascend_byte(); }
        16 => { let _ = z.ascend_until(); }
        17 => { let _ = z.ascend_until_branch(); }
        18 => { let _ = z.to_next_sibling_byte(); }
        19 => { let _ = z.to_prev_sibling_byte(); }
        20 => { let _ = z.to_next_step(); }
        21 => { let mut o = z.path().to_vec(); let _ = z.to_next_step_observed(&mut o); }
        22 => { let p = path(d)?; let _ = z.move_to_path(&p); }
        23 => z.reset(),
        24 => { let _ = (z.path_exists(), z.is_val(), z.child_count(), z.child_mask()); }
        25 => { let _ = (z.depth(), z.at_root(), z.focus_byte(), z.path().len()); }
        26 => { if val_count_ok() { let _ = z.val_count(); } }
        27 => {
            // A sibling walk, the way callers enumerate children.
            if z.descend_first_byte().is_some() {
                let mut n = 0;
                while n < WALK && z.to_next_sibling_byte().is_some() { n += 1; }
                let _ = z.ascend_byte();
            }
        }
        28 => {
            if z.descend_last_byte().is_some() {
                let mut n = 0;
                while n < WALK && z.to_prev_sibling_byte().is_some() { n += 1; }
                let _ = z.ascend_byte();
            }
        }
        29 => { let mut n = 0; while n < WALK && z.to_next_step() { n += 1; } }
        #[allow(deprecated)]
        30 => { let _ = z.is_value(); }
        #[allow(deprecated)]
        31 => { let p = path(d)?; let _ = z.descend_to_value(&p); }
        _ => { let b = byte(d)?; z.descend_to_byte(b); let _ = z.ascend_byte(); }
    }
    Some(())
}

/// A k for k-path iteration: `0..n`, or `1..n` unless known failures are included.
fn kpath_k(d: &mut Dec, n: usize) -> Option<usize> {
    let k = d.modn(n)?;
    Some(if k == 0 && !include_known() { 1 } else { k })
}

/// One iteration step, or a movement.
fn iter_step<Z: ZipperMoving + ZipperPath + ZipperIteration>(d: &mut Dec, z: &mut Z) -> Option<()> {
    let __op = d.modn(14)?;
    note!("iter {__op} at {}", hex_path(z.path()));
    match __op {
        0 => { let _ = z.to_next_val(); }
        1 => { let mut o = z.path().to_vec(); let _ = z.to_next_val_observed(&mut o); }
        2 => { let _ = z.descend_last_path(); }
        3 => { let mut o = z.path().len(); let _ = z.descend_last_path_observed(&mut o); }
        4 => { let k = kpath_k(d, 6)?; note!("  k={k}"); let _ = z.descend_first_k_path(k); }
        5 => {
            let k = kpath_k(d, 6)?;
            note!("  k={k}");
            if include_known() { let _ = z.to_next_k_path(k); } else if z.descend_first_k_path(k) { let _ = z.to_next_k_path(k); }
        }
        6 => {
            // A whole k-path walk.
            let k = kpath_k(d, 5)?;
            note!("  k={k}");
            if z.descend_first_k_path(k) {
                let mut n = 0;
                while n < WALK && z.to_next_k_path(k) { n += 1; }
            }
        }
        7 => {
            let k = kpath_k(d, 5)?;
            note!("  k={k}");
            let mut o = z.path().to_vec();
            if z.descend_first_k_path_observed(k, &mut o) {
                let mut n = 0;
                while n < WALK && z.to_next_k_path_observed(k, &mut o) { n += 1; }
            }
        }
        8 => { let mut n = 0; while n < WALK && z.to_next_val() { n += 1; } }
        _ => move_step(d, z)?,
    }
    Some(())
}

/// A read program over a zipper with iteration and values.
fn read_program<V, Z>(d: &mut Dec, steps: &mut usize, z: &mut Z) -> Option<()>
where
    V: Clone,
    Z: ZipperMoving + ZipperPath + ZipperIteration + ZipperValues<V>,
{
    let n = d.modn(EPISODE_STEPS)?;
    for _ in 0..n {
        tick(steps)?;
        match d.modn(8)? {
            0 => { let _ = z.val().cloned(); }
            #[allow(deprecated)]
            1 => { let _ = z.value().cloned(); }
            _ => iter_step(d, z)?,
        }
    }
    Some(())
}

/// A read program over a zipper that moves and has values, but cannot iterate.
fn move_program<V, Z>(d: &mut Dec, steps: &mut usize, z: &mut Z) -> Option<()>
where
    V: Clone,
    Z: ZipperMoving + ZipperPath + ZipperValues<V>,
{
    let n = d.modn(EPISODE_STEPS)?;
    for _ in 0..n {
        tick(steps)?;
        match d.modn(8)? {
            0 => { let _ = z.val().cloned(); }
            _ => move_step(d, z)?,
        }
    }
    Some(())
}

/// The read-only value accessors: references that outlive the borrow of the
/// zipper, and iteration that hands them out.
macro_rules! ro_extras {
    ($d:expr, $z:expr) => {{
        let __e = $d.modn(4)?;
        note!("ro_extras {__e}");
        match __e {
            0 => { let _ = $z.get_val().cloned(); }
            1 => { let p = path($d)?; let _ = $z.get_val_at(&p).cloned(); }
            2 => { let mut n = 0; while n < WALK && $z.to_next_get_val().is_some() { n += 1; } }
            _ => { let mut o = $z.path().to_vec(); let _ = $z.to_next_get_val_observed(&mut o).cloned(); }
        }
    }};
}

/// Everything a subtrie-capable read zipper offers beyond moving: witnesses,
/// focus borrowing, forks, trie refs, buffer management.
macro_rules! sub_extras {
    ($d:expr, $steps:expr, $z:expr) => {{
        let __e = $d.modn(12)?;
        note!("sub_extras {__e}");
        match __e {
            0 => { let w = $z.witness(); let _ = $z.get_val_with_witness(&w).cloned(); }
            1 => {
                let w = $z.witness();
                let mut n = 0;
                while n < WALK && $z.to_next_get_val_with_witness(&w).is_some() { n += 1; }
            }
            2 => { let _ = $z.make_map().val_count(); }
            3 => { let _ = $z.try_make_map().map(|m| m.val_count()); }
            4 => { let p = path($d)?; let t = $z.trie_ref_at_path(&p); trie_ref_ops($d, $steps, &t)?; }
            5 => { let _ = ($z.is_shared(), $z.shared_node_id()); }
            6 => { let _ = $z.get_focus(); let p = path($d)?; let _ = $z.get_focus_at(&p); let _ = $z.try_borrow_focus().is_some(); }
            7 => { let (a, b) = ($d.modn(80)?, $d.modn(24)?); $z.reserve_buffers(a, b); $z.prepare_buffers(); }
            8 => { let mut f = $z.fork_read_zipper(); read_program($d, $steps, &mut f)?; }
            9 => { let _ = ($z.origin_path().len(), $z.root_prefix_path().len()); }
            10 => { let _ = $z.get_trie_ref().child_count(); }
            _ => { let _ = $z.native_subtries(); let _ = $z.trie_ref().is_some(); let p = path($d)?; let _ = $z.val_at(&p).cloned(); }
        }
    }};
}

/// Operations on a `TrieRef`, which is a zipper that cannot move.
fn trie_ref_ops<V, T>(d: &mut Dec, steps: &mut usize, t: &T) -> Option<()>
where
    V: Clone + Send + Sync + Unpin,
    T: ZipperValuesAt<V> + Zipper + ZipperInfallibleSubtries<V> + ZipperConcrete,
{
    let n = d.modn(8)?;
    for _ in 0..n {
        tick(steps)?;
        match d.modn(6)? {
            0 => { let _ = (t.val().cloned(), t.path_exists(), t.is_val(), t.child_count(), t.child_mask()); }
            1 => { let p = path(d)?; let _ = t.val_at(&p).cloned(); }
            2 => { let _ = t.make_map().val_count(); }
            3 => { let _ = (t.is_shared(), t.shared_node_id()); }
            4 => { let p = path(d)?; let _ = t.get_focus_at(&p); let _ = t.get_trie_ref().child_count(); }
            _ => { let _ = t.try_borrow_focus().is_some(); }
        }
    }
    Some(())
}

// ---------------------------------------------------------------------------
// Writing
// ---------------------------------------------------------------------------

/// One write, or a movement.  `srcs` are clones of the maps taken when the
/// episode began: sources that share nodes with the destination, which is what
/// most callers of the algebraic operations hand in.
fn write_step<V, W>(d: &mut Dec, z: &mut W, srcs: &[PathMap<V>; NMAPS]) -> Option<()>
where
    V: CrashValue,
    W: ZipperWriting<V> + ZipperMoving + ZipperPath + ZipperValues<V>,
{
    let src = |d: &mut Dec| -> Option<&PathMap<V>> { let i = d.modn(NMAPS)?; note!("  src map {i}"); Some(&srcs[i]) };
    let op = d.modn(40)?;
    note!("write {op} at {}", hex_path(z.path()));
    // Growth is refused below an oversized focus; everything else still runs.
    let grows = matches!(op, 9 | 10 | 11 | 12 | 13 | 19 | 20 | 21 | 23 | 26 | 28 | 29 | 30);
    if grows && z.val_count() > MAX_VALS {
        return Some(());
    }
    match op {
        0 => { let v = val(d)?; let _ = z.set_val(v); }
        1 => { let pr = d.boolean()?; note!("  pr={pr}"); let _ = z.remove_val(pr); }
        2 => { let v = val(d)?; if let Some(slot) = z.get_val_mut() { *slot = v; } }
        3 => { let v = val(d)?; let _ = z.get_val_or_set_mut(v).clone(); }
        4 => { let v = val(d)?; let _ = z.get_val_or_set_mut_with(|| v).clone(); }
        5 => { let _ = z.create_path(); }
        6 => { let _ = z.prune_path(); }
        7 => { let _ = z.prune_ascend(); }
        8 => { let pr = d.boolean()?; let _ = z.remove_branches(pr); }
        9 => { let s = src(d)?; let p = short_path(d)?; z.graft(&s.read_zipper_at_path(&p)); }
        10 => { let s = src(d)?; let p = short_path(d)?; z.graft_map(s.read_zipper_at_path(&p).make_map()); }
        11 => { let s = src(d)?; let p = short_path(d)?; let q = path(d)?; z.graft_src_at(&s.read_zipper_at_path(&p), &q); }
        12 => { let s = src(d)?; let p = short_path(d)?; let _ = z.join_into(&s.read_zipper_at_path(&p)); }
        13 => { let s = src(d)?; let p = short_path(d)?; let _ = z.join_map_into(s.read_zipper_at_path(&p).make_map()); }
        14 => { let s = src(d)?; let p = short_path(d)?; let pr = d.boolean()?; let _ = z.meet_into(&s.read_zipper_at_path(&p), pr); }
        15 => { let s = src(d)?; let p = short_path(d)?; let pr = d.boolean()?; let _ = z.subtract_into(&s.read_zipper_at_path(&p), pr); }
        16 => { let s = src(d)?; let p = short_path(d)?; let _ = z.restrict(&s.read_zipper_at_path(&p)); }
        17 => { let s = src(d)?; let p = short_path(d)?; let _ = z.restricting(&s.read_zipper_at_path(&p)); }
        18 => {
            // Two independent sources, possibly different maps.
            let (a, pa) = (src(d)?, short_path(d)?);
            let (b, pb) = (src(d)?, short_path(d)?);
            let _ = z.meet_2(&a.read_zipper_at_path(&pa), &b.read_zipper_at_path(&pb));
        }
        19 => {
            // The source is a write zipper on a private copy, emptied by the join.
            let s = src(d)?.clone();
            let p = short_path(d)?;
            let pr = d.boolean()?;
            note!("  pr={pr}");
            let mut sw = s.into_write_zipper(&p);
            let _ = z.join_into_take(&mut sw, pr);
            let _ = sw.into_map().val_count();
        }
        20 => { let k = kpath_k(d, 6)?; let pr = d.boolean()?; note!("  k={k} pr={pr}"); let _ = z.join_k_path_into(k, pr); }
        21 => {
            let k = d.modn(6)?;
            let pr = d.boolean()?;
            if include_known() || (k > 0 && z.child_count() > 0) {
                let _ = z.meet_k_path_into(k, pr);
            }
        }
        #[allow(deprecated)]
        22 => { let k = kpath_k(d, 6)?; let _ = z.drop_head(k); }
        23 => { let p = path(d)?; let _ = z.insert_prefix(&p); }
        24 => { let n = d.modn(10)?; let _ = z.remove_prefix(n); }
        25 => { let pr = d.boolean()?; let _ = z.take_map(pr).map(|m| m.val_count()); }
        26 => {
            let pr = d.boolean()?;
            if let Some(m) = z.take_map(pr) {
                let p = short_path(d)?;
                let _ = z.descend_to_existing(&p);
                z.graft_map(m);
            }
        }
        27 => { let m = mask(d)?; let pr = d.boolean()?; z.remove_unmasked_branches(m, pr); }
        28 => { let s = src(d)?; let p = short_path(d)?; let m = mask(d)?; let ru = d.boolean()?; note!("  ru={ru}"); z.graft_masked_branches(&s.read_zipper_at_path(&p), m, ru); }
        29 => {
            let s = src(d)?;
            let m = mask(d)?;
            let ru = d.boolean()?;
            let extra = d.modn(3)?;
            // One map per set bit, as documented, plus possibly a few spare ones.
            let maps: Vec<PathMap<V>> = m.iter().map(|b| s.read_zipper_at_path([b]).make_map())
                .chain((0..extra).map(|_| s.clone())).collect();
            z.graft_child_maps(m, maps, ru);
        }
        30 => {
            // `.paths` into the focus, from a serialized copy of a source.
            let s = src(d)?;
            let mut buf = Vec::new();
            if serialize_paths(s.read_zipper(), &mut buf).is_ok() {
                let v = val(d)?;
                let _ = deserialize_paths(&mut *z, Cursor::new(&buf[..]), v);
            }
        }
        _ => move_step(d, z)?,
    }
    Some(())
}

/// A write program over one write zipper.
fn write_program<V, W>(d: &mut Dec, steps: &mut usize, z: &mut W, srcs: &[PathMap<V>; NMAPS]) -> Option<()>
where
    V: CrashValue,
    W: ZipperWriting<V> + ZipperMoving + ZipperPath + ZipperValues<V>,
{
    let n = d.modn(EPISODE_STEPS)?;
    for _ in 0..n {
        tick(steps)?;
        write_step(d, z, srcs)?;
    }
    Some(())
}

fn snapshot<V: CrashValue>(maps: &[PathMap<V>; NMAPS]) -> [PathMap<V>; NMAPS] {
    [maps[0].clone(), maps[1].clone(), maps[2].clone()]
}

// ---------------------------------------------------------------------------
// Episodes: one zipper kind, created, driven, dropped
// ---------------------------------------------------------------------------

/// Traces the paths holding values in each map.
fn note_maps<V: CrashValue>(maps: &[PathMap<V>; NMAPS]) {
    if *TRACE.get_or_init(|| std::env::var_os("CRASH_TRACE").is_some()) {
        for (i, mp) in maps.iter().enumerate() {
            let mut rz = mp.read_zipper();
            let mut ps = vec![];
            if rz.is_val() { ps.push("_".to_string()); }
            //Values, and the ends of dangling paths marked `~`
            while ps.len() < 64 && rz.to_next_step() {
                if rz.is_val() { ps.push(hex_path(rz.path())) } else if rz.child_count() == 0 { ps.push(format!("{}~", hex_path(rz.path()))) }
            }
            note!("  map {i}: {}", ps.join(" "));
        }
    }
}

fn read_episode<V: CrashValue>(d: &mut Dec, st: &mut State<V>) -> Option<()> {
    let m = d.modn(NMAPS)?;
    let p = short_path(d)?;
    let map = st.maps[m].clone();
    let steps = &mut st.steps;
    let __kind = d.modn(12)?;
    note!("read episode {__kind} map {m} at {}", hex_path(&p));
    note_maps(&st.maps);
    match __kind {
        0 => {
            let mut z = map.read_zipper_at_path(&p);
            for _ in 0..d.modn(8)? {
                tick(steps)?;
                match d.modn(3)? { 0 => ro_extras!(d, z), 1 => sub_extras!(d, steps, z), _ => iter_step(d, &mut z)? }
            }
            read_program(d, steps, &mut z)?;
        }
        1 => {
            let mut z = map.read_zipper_at_borrowed_path(&p);
            for _ in 0..d.modn(8)? {
                tick(steps)?;
                match d.modn(3)? { 0 => ro_extras!(d, z), 1 => sub_extras!(d, steps, z), _ => iter_step(d, &mut z)? }
            }
            read_program(d, steps, &mut z)?;
        }
        2 => {
            let mut z = map.into_read_zipper(&p);
            for _ in 0..d.modn(8)? {
                tick(steps)?;
                if d.boolean()? { sub_extras!(d, steps, z) } else { iter_step(d, &mut z)? }
            }
            read_program(d, steps, &mut z)?;
            let mut c = z.clone();
            read_program(d, steps, &mut c)?;
        }
        3 => {
            let t = map.trie_ref_at_path(&p);
            trie_ref_ops(d, steps, &t)?;
            let q = path(d)?;
            let t2 = t.trie_ref_at_path(&q);
            trie_ref_ops(d, steps, &t2)?;
            if include_known() || t2.path_exists() {
                let mut f = t2.fork_read_zipper();
                read_program(d, steps, &mut f)?;
            }
        }
        4 => {
            // A prefix in front of a zipper, possibly rooted part way into it.
            let prefix = path(d)?;
            let mut z = PrefixZipper::new(&prefix[..], map.read_zipper_at_path(&p));
            if d.boolean()? {
                let cut = d.modn(prefix.len() + 1)?;
                note!("  prefix={} cut={cut}", hex_path(&prefix));
                let _ = z.set_root_prefix_path(&prefix[..cut]);
            }
            for _ in 0..d.modn(8)? {
                tick(steps)?;
                match d.modn(3)? { 0 => ro_extras!(d, z), 1 => sub_extras!(d, steps, z), _ => iter_step(d, &mut z)? }
            }
            read_program(d, steps, &mut z)?;
        }
        5 => {
            let other = st.maps[d.modn(NMAPS)?].clone();
            let q = short_path(d)?;
            let _stub = ValCountStub::new();
            let mut z = OverlayZipper::new(map.read_zipper_at_path(&p), other.read_zipper_at_path(&q));
            move_program(d, &mut st.steps, &mut z)?;
        }
        6 => {
            // Secondary factors are map-root zippers: see KNOWN_PRECONDITIONS.
            let pick: Vec<usize> = (0..d.modn(4)?).map(|_| d.modn(NMAPS)).collect::<Option<_>>()?;
            let others: Vec<PathMap<V>> = pick.iter().map(|&i| st.maps[i].clone()).collect();
            let more_i = d.modn(NMAPS)?;
            note!("  product factors {pick:?}, more {more_i}");
            let more = st.maps[more_i].clone();
            let steps = &mut st.steps;
            let mut z = ProductZipper::new(map.read_zipper_at_path(&p), others.iter().map(|o| o.read_zipper()));
            if d.boolean()? {
                note!("  new_factors");
                z.new_factors([more.read_zipper()]);
            }
            for _ in 0..d.modn(8)? {
                tick(steps)?;
                let __c = d.modn(4)?;
                note!("  product op {__c} at {}", hex_path(z.path()));
                match __c {
                    0 => { let _ = (z.focus_factor(), z.factor_count(), z.path_indices().len()); }
                    1 => { let w = z.witness(); let _ = z.get_val_with_witness(&w).cloned(); }
                    2 => { let _ = (z.is_shared(), z.shared_node_id(), z.origin_path().len()); }
                    _ => iter_step(d, &mut z)?,
                }
            }
            read_program(d, steps, &mut z)?;
        }
        7 => {
            let others: Vec<PathMap<V>> = (0..d.modn(4)?).map(|_| d.modn(NMAPS).map(|i| st.maps[i].clone())).collect::<Option<_>>()?;
            let steps = &mut st.steps;
            let _stub = ValCountStub::new();
            let mut z = ProductZipperG::new(map.read_zipper_at_path(&p), others.iter().map(|o| o.read_zipper_at_path(&[])));
            for _ in 0..d.modn(8)? {
                tick(steps)?;
                match d.modn(3)? {
                    0 => { let _ = (z.focus_factor(), z.factor_count(), z.path_indices().len()); }
                    _ => iter_step(d, &mut z)?,
                }
            }
            read_program(d, steps, &mut z)?;
        }
        8 => {
            // Factors enrolled as the zipper walks: a map-root zipper on one of
            // the maps, chosen from the path and the depth, a bounded number of times.
            let pool = snapshot(&st.maps);
            let steps = &mut st.steps;
            let sel = d.u8()?;
            let budget = d.modn(4)?;
            let _stub = ValCountStub::new();
            let mut z = DependentProductZipperG::new_enroll(
                map.read_zipper_at_path(&p),
                budget,
                move |left: usize, path: &[u8], depth: usize| {
                    let pick = (path.iter().fold(sel as usize, |a, &b| a.wrapping_mul(31).wrapping_add(b as usize)) + depth) % (NMAPS + 1);
                    if left == 0 || pick == NMAPS {
                        (left, None)
                    } else {
                        (left - 1, Some(pool[pick].clone().into_read_zipper(&[])))
                    }
                },
            );
            for _ in 0..d.modn(8)? {
                tick(steps)?;
                match d.modn(3)? {
                    0 => { let _ = (z.focus_factor(), z.path_indices().len()); }
                    _ => iter_step(d, &mut z)?,
                }
            }
            read_program(d, steps, &mut z)?;
        }
        9 => {
            let mut z = EmptyZipper::new_at_path(&p);
            for _ in 0..d.modn(8)? {
                tick(steps)?;
                match d.modn(3)? { 0 => { let _: Option<&V> = z.get_val(); } _ => iter_step(d, &mut z)? }
            }
            read_program::<V, _>(d, steps, &mut z)?;
        }
        10 => {
            // A fork taken part way through a walk, driven while the parent lives.
            let mut z = map.read_zipper_at_path(&p);
            move_program(d, steps, &mut z)?;
            let mut f = z.fork_read_zipper();
            read_program(d, steps, &mut f)?;
            drop(f);
            read_program(d, steps, &mut z)?;
        }
        _ => {
            // The arena-compact form of the map.
            let act = ArenaCompactTree::from_zipper(map.read_zipper(), |v: &V| v.to_u64());
            let mut z = act.read_zipper_at_path_u64(&p);
            for _ in 0..d.modn(8)? {
                tick(steps)?;
                match d.modn(4)? {
                    0 => { let _ = act.get_val_at(&p); }
                    1 => { let mut n = 0; for _ in act.iter() { n += 1; if n > WALK { break } } }
                    2 => { let mut f = z.fork_read_zipper(); read_program(d, steps, &mut f)?; }
                    _ => iter_step(d, &mut z)?,
                }
            }
            read_program(d, steps, &mut z)?;
            let mut u = act.read_zipper_at_path(&p);
            read_program(d, steps, &mut u)?;
        }
    }
    Some(())
}

fn write_episode<V: CrashValue>(d: &mut Dec, st: &mut State<V>) -> Option<()> {
    let m = d.modn(NMAPS)?;
    let p = path(d)?;
    let srcs = snapshot(&st.maps);
    let State { maps, steps } = st;
    let __kind = d.modn(7)?;
    note!("write episode {__kind} map {m} at {}", hex_path(&p));
    note_maps(maps);
    match __kind {
        0 => {
            let mut z = maps[m].write_zipper_at_path(&p);
            write_program(d, steps, &mut z, &srcs)?;
        }
        1 => {
            let mut z = maps[m].write_zipper();
            z.descend_to(&p);
            write_program(d, steps, &mut z, &srcs)?;
            // A fork of the write zipper, read while the writer is still live.
            {
                let mut f = z.fork_read_zipper();
                read_program(d, steps, &mut f)?;
            }
            write_program(d, steps, &mut z, &srcs)?;
        }
        2 => {
            // An owned write zipper, turned back into the map afterwards.
            let map = std::mem::take(&mut maps[m]);
            let mut z = map.into_write_zipper(&p);
            let r = write_program(d, steps, &mut z, &srcs);
            maps[m] = z.into_map();
            r?;
        }
        3 => {
            let zh = maps[m].zipper_head();
            zh_program(d, steps, &zh, &srcs)?;
        }
        4 => {
            // A ZipperHead handed out by a write zipper at its focus.
            let mut z = maps[m].write_zipper_at_path(&p);
            write_program(d, steps, &mut z, &srcs)?;
            {
                let zh = z.zipper_head();
                zh_program(d, steps, &zh, &srcs)?;
            }
            write_program(d, steps, &mut z, &srcs)?;
        }
        5 => {
            let map = std::mem::take(&mut maps[m]);
            let zh = map.into_zipper_head(&p);
            let r = zh_program(d, steps, &zh, &srcs);
            maps[m] = zh.into_map();
            r?;
        }
        _ => {
            // A write zipper and a read zipper on the same map at once, through a head.
            let zh = maps[m].zipper_head();
            let q = short_path(d)?;
            if let (Ok(mut w), Ok(mut r)) = (zh.write_zipper_at_exclusive_path(&p), zh.read_zipper_at_path(&q)) {
                for _ in 0..d.modn(EPISODE_STEPS)? {
                    tick(steps)?;
                    if d.boolean()? { write_step(d, &mut w, &srcs)? } else { iter_step(d, &mut r)? }
                }
            }
        }
    }
    Some(())
}

/// Several zippers from one head, live at once and driven in turn.  Requests
/// that conflict are refused with `Err`, which is the documented outcome.
fn zh_program<'t, V, H>(d: &mut Dec, steps: &mut usize, zh: &H, srcs: &[PathMap<V>; NMAPS]) -> Option<()>
where
    V: CrashValue,
    H: ZipperCreation<'t, V>,
{
    let paths: Vec<Vec<u8>> = (0..3).map(|_| short_path(d)).collect::<Option<_>>()?;
    let mut w0 = zh.write_zipper_at_exclusive_path(&paths[0]).ok();
    let mut w1 = zh.write_zipper_at_exclusive_path(&paths[1]).ok();
    let mut r0 = zh.read_zipper_at_path(&paths[2]).ok();
    let mut r1 = zh.read_zipper_at_borrowed_path(&paths[2]).ok();
    note!("  head zippers: w0 {} {}, w1 {} {}, r0/r1 {} {} {}", hex_path(&paths[0]), w0.is_some(), hex_path(&paths[1]), w1.is_some(), hex_path(&paths[2]), r0.is_some(), r1.is_some());
    let n = d.modn(EPISODE_STEPS)?;
    for _ in 0..n {
        tick(steps)?;
        let __which = d.modn(7)?;
        note!("  head step {__which}");
        match __which {
            0 => if let Some(z) = w0.as_mut() { write_step(d, z, srcs)? },
            1 => if let Some(z) = w1.as_mut() { write_step(d, z, srcs)? },
            2 => if let Some(z) = r0.as_mut() { iter_step(d, z)? },
            3 => if let Some(z) = r1.as_mut() { if d.boolean()? { sub_extras!(d, steps, z) } else { iter_step(d, z)? } },
            4 => { drop(w0.take()); let q = short_path(d)?; w0 = zh.write_zipper_at_exclusive_path(&q).ok(); note!("  w0 = {} {}", hex_path(&q), w0.is_some()); }
            5 => { drop(r0.take()); let q = short_path(d)?; r0 = zh.read_zipper_at_path(&q).ok(); note!("  r0 = {} {}", hex_path(&q), r0.is_some()); }
            _ => { w1 = None; r1 = None; }
        }
    }
    Some(())
}

// ---------------------------------------------------------------------------
// Whole-map operations
// ---------------------------------------------------------------------------

fn map_op<V: CrashValue>(d: &mut Dec, st: &mut State<V>) -> Option<()> {
    let m = d.modn(NMAPS)?;
    let __op = d.modn(20)?;
    note!("map {__op}");
    match __op {
        0 => { let p = path(d)?; let v = val(d)?; if st.small(m) { let _ = st.maps[m].set_val_at(&p, v); } }
        1 => { let p = path(d)?; let v = val(d)?; if st.small(m) { let _ = st.maps[m].insert(&p, v); } }
        2 => { let p = path(d)?; let pr = d.boolean()?; let _ = st.maps[m].remove_val_at(&p, pr); }
        3 => { let p = path(d)?; let _ = st.maps[m].remove(&p); }
        4 => {
            let p = path(d)?;
            let v = val(d)?;
            match d.modn(3)? {
                0 => { if let Some(slot) = st.maps[m].get_val_mut_at(&p) { *slot = v; } }
                1 => { let _ = st.maps[m].get_val_or_set_mut_at(&p, v).clone(); }
                _ => { let _ = st.maps[m].get_val_or_set_mut_with_at(&p, || v).clone(); }
            }
        }
        5 => {
            let p = path(d)?;
            let map = &st.maps[m];
            let _ = (map.get(&p).cloned(), map.contains(&p), map.path_exists_at(&p), map.is_empty());
            #[allow(deprecated)]
            let _ = map.contains_path(&p);
        }
        6 => { let p = path(d)?; let _ = st.maps[m].create_path(&p); }
        7 => { let p = path(d)?; let _ = st.maps[m].prune_path(&p); }
        8 => { let p = path(d)?; let pr = d.boolean()?; let _ = st.maps[m].remove_branches_at(&p, pr); }
        9 => { let to = d.modn(NMAPS)?; st.maps[to] = st.maps[m].clone(); }
        10 => {
            let (b, to) = (d.modn(NMAPS)?, d.modn(NMAPS)?);
            let (x, y) = (&st.maps[m], &st.maps[b]);
            let r = match d.modn(8)? {
                0 => x.join(y),
                1 => x.meet(y),
                2 => x.subtract(y),
                3 => x.restrict(y),
                4 => resolve(x.pjoin(y), x, y),
                5 => resolve(x.pmeet(y), x, y),
                6 => resolve(x.psubtract(y), x, y),
                _ => y.restrict(x),
            };
            if r.val_count() <= MAX_VALS { st.maps[to] = r; }
        }
        11 => {
            // A comb: many children under one prefix, over a chosen alphabet, so
            // list nodes split and dense nodes form.
            let prefix = path(d)?;
            let n = d.modn(40)?;
            let v: V = val(d)?;
            if st.small(m) {
                for _ in 0..n {
                    let mut k = prefix.clone();
                    k.push(byte(d)?);
                    k.extend(short_path(d)?);
                    let _ = st.maps[m].set_val_at(&k, v.clone());
                }
            }
        }
        12 => {
            let to = d.modn(NMAPS)?;
            let rebuilt: PathMap<V> = st.maps[m].iter().take(MAX_VALS).map(|(k, v)| (k, v.clone())).collect();
            let _ = st.maps[m].clone().into_iter().take(WALK).count();
            st.maps[to] = rebuilt;
        }
        13 => { let _ = st.maps[m].merkleize(); }
        14 => { let to = d.modn(NMAPS)?; st.maps[to] = ana(d, &st.maps)?; }
        15 => cata(d, &st.maps[m])?,
        16 => {
            // `.paths` round trip, then decoding a damaged copy, which must fail
            // cleanly or decode something, not panic.
            let p = short_path(d)?;
            let mut buf = Vec::new();
            let _ = serialize_paths(st.maps[m].read_zipper_at_path(&p), &mut buf);
            let to = d.modn(NMAPS)?;
            let q = short_path(d)?;
            let v = val(d)?;
            if st.small(to) {
                let _ = deserialize_paths(st.maps[to].write_zipper_at_path(&q), Cursor::new(&buf[..]), v);
            }
            let flips = d.modn(4)?;
            let cut = d.u8()? as usize;
            let mut bad = buf.clone();
            for _ in 0..flips {
                if bad.is_empty() { break }
                let i = d.u8()? as usize * 7 % bad.len();
                bad[i] ^= d.u8()? | 1;
            }
            if cut & 1 == 1 { bad.truncate(cut % (bad.len() + 1)); }
            decode_bounded(&bad);
        }
        17 => {
            // Decoding arbitrary bytes from the input.
            let len = d.modn(64)?;
            let raw: Vec<u8> = (0..len).map(|_| d.u8()).collect::<Option<_>>()?;
            decode_bounded(&raw);
        }
        18 => {
            let p = path(d)?;
            let map = &st.maps[m];
            let _ = (map.is_shared(), map.shared_node_id(), map.val().cloned(), map.val_at(&p).cloned(), map.goat_val_count());
        }
        _ => {
            // A clone mutated while the original is read: copy-on-write.
            let mut c = st.maps[m].clone();
            let p = path(d)?;
            let v = val(d)?;
            if st.small(m) {
                let _ = c.set_val_at(&p, v);
                let q = path(d)?;
                let _ = c.remove_branches_at(&q, d.boolean()?);
            }
            let _ = (st.maps[m].val_count(), c.val_count());
        }
    }
    Some(())
}

fn decode_bounded(bytes: &[u8]) {
    let mut n = 0usize;
    let _ = for_each_deserialized_path(Cursor::new(bytes), |_, _| {
        n += 1;
        if n > MAX_VALS { Err(std::io::Error::other("enough")) } else { Ok(()) }
    });
}

/// A trie built by an anamorphism.  `W` is the remaining depth; the children
/// pushed at each step come from the input, sorted and de-duplicated by first
/// byte as `TrieBuilder` requires, and sometimes grafted from one of the maps.
fn ana<V: CrashValue>(d: &mut Dec, maps: &[PathMap<V>; NMAPS]) -> Option<PathMap<V>> {
    let depth = d.modn(5)?;
    let spec: Vec<u8> = (0..32).map(|_| d.u8()).collect::<Option<_>>()?;
    let graft_from = maps[d.modn(NMAPS)?].clone();
    let mut calls = 0usize;
    Some(PathMap::<V>::new_from_ana(depth, |left: usize, v: &mut Option<V>, children, path: &[u8]| {
        calls += 1;
        let h = spec[(calls + path.len()) % spec.len()];
        if h & 1 == 1 {
            *v = Some(V::from_byte(h));
        }
        if left == 0 || calls > 256 {
            return;
        }
        let fan = (h >> 1) as usize % 4;
        let mut firsts: Vec<(u8, Vec<u8>)> = (0..fan)
            .map(|i| {
                let s = spec[(calls * 7 + i * 3) % spec.len()];
                let first = if s & 0x80 == 0 { s % 4 } else { s };
                let tail = (0..(s as usize % 3)).map(|j| spec[(i + j + calls) % spec.len()] % 4).collect();
                (first, tail)
            })
            .collect();
        firsts.sort_by_key(|(b, _)| *b);
        firsts.dedup_by_key(|(b, _)| *b);
        for (i, (first, tail)) in firsts.into_iter().enumerate() {
            let rz = graft_from.read_zipper_at_path([first]);
            if (h >> 4) as usize % 4 == i && rz.child_count() > 0 {
                children.graft_at_byte(first, &rz);
            } else {
                let mut sub = vec![first];
                sub.extend(tail);
                children.push(&sub, left - 1);
            }
        }
    }))
}

/// The four catamorphism flavours, some stopping early with an error, and `hash`.
fn cata<V: CrashValue>(d: &mut Dec, map: &PathMap<V>) -> Option<()> {
    let p = short_path(d)?;
    let stop = d.modn(32)?;
    let z = map.read_zipper_at_path(&p);
    match d.modn(9)? {
        0 => { let _: usize = z.into_cata_side_effect(|_m, ch: &mut [usize], v: Option<&V>, path: &[u8]| ch.iter().sum::<usize>() + v.is_some() as usize + path.len()); }
        1 => { let _: usize = z.into_cata_jumping_side_effect(|_m, ch: &mut [usize], jump, v: Option<&V>, _p: &[u8]| ch.iter().sum::<usize>() + jump + v.is_some() as usize); }
        2 => { let _: usize = z.into_cata_cached(|_m, ch: &mut [usize], v: Option<&V>| ch.iter().sum::<usize>() + v.map_or(0, |v| v.to_u64() as usize)); }
        3 => { let _: usize = z.into_cata_jumping_cached(|_m, ch: &mut [usize], v: Option<&V>, sub: &[u8]| ch.iter().sum::<usize>() + sub.len() + v.is_some() as usize); }
        4 => {
            let mut n = 0;
            let _: Result<usize, ()> = z.into_cata_side_effect_fallible(|_m, ch: &mut [usize], _v: Option<&V>, _p: &[u8]| { n += 1; if n > stop { Err(()) } else { Ok(ch.len()) } });
        }
        5 => {
            let mut n = 0;
            let _: Result<usize, ()> = z.into_cata_jumping_side_effect_fallible(|_m, ch: &mut [usize], j, _v: Option<&V>, _p: &[u8]| { n += 1; if n > stop { Err(()) } else { Ok(ch.len() + j) } });
        }
        6 => { let _: Result<usize, ()> = z.into_cata_cached_fallible(|m: &ByteMask, ch: &mut [usize], _v: Option<&V>| if m.count_bits() > stop % 4 { Err(()) } else { Ok(ch.len()) }); }
        7 => { let _: Result<usize, ()> = z.into_cata_jumping_cached_fallible(|_m, ch: &mut [usize], _v: Option<&V>, sub: &[u8]| if sub.len() > stop { Err(()) } else { Ok(ch.len()) }); }
        _ => { let _ = z.hash(); }
    }
    Some(())
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

fn seed<V: CrashValue>(d: &mut Dec) -> Option<State<V>> {
    let mut st = State { maps: Default::default(), steps: 0 };
    for m in 0..NMAPS {
        for _ in 0..d.modn(12)? {
            let p = path(d)?;
            let v = val(d)?;
            note!("seed map {m}: {} = {v:?}", hex_path(&p));
            st.maps[m].set_val_at(&p, v);
        }
    }
    Some(st)
}

fn run_typed<V: CrashValue>(d: &mut Dec) {
    let Some(mut st) = seed::<V>(d) else { return };
    let _ = (|| -> Option<()> {
        loop {
            tick(&mut st.steps)?;
            match d.modn(8)? {
                0 | 1 | 2 => map_op(d, &mut st)?,
                3 | 4 => read_episode(d, &mut st)?,
                _ => write_episode(d, &mut st)?,
            }
        }
    })();
    // Tear down in a varied order: dropping shared nodes is part of the surface.
    let order = d.u8().unwrap_or(0) as usize;
    for i in 0..NMAPS {
        let m = (order + i) % NMAPS;
        let _ = st.maps[m].val_count();
        st.maps[m] = PathMap::new();
    }
}

/// Run one input.  Returns normally unless the crate panics, aborts or hangs.
///
/// Anything this reaches with `debug_assertions` off is also reachable with
/// them on; build with them on to turn internal invariant checks into failures.
pub fn run(bytes: &[u8]) {
    let mut d = Dec { bytes, pos: 0 };
    match d.u8().map(|b| b % 4) {
        None => {}
        Some(0) | Some(1) => run_typed::<u64>(&mut d),
        Some(2) => run_typed::<()>(&mut d),
        Some(_) => {
            if d.boolean().unwrap_or(false) { run_typed::<bool>(&mut d) } else { run_typed::<u16>(&mut d) }
        }
    }
}
