//! Grafting when the source has nothing to give.
//!
//! `graft_masked_branches` and `graft_child_maps` replace each masked branch of the destination
//! with the source's.  `benches/graft_masked_branches.rs` covers sources that have every masked
//! branch.  This covers the rest: masked branches the source lacks or holds only as dangling
//! paths, a source with no node at all, a destination focus that does not exist, and empty maps.
//! Those are where grafting nothing has to empty a branch while keeping its location, so they
//! are where the cost of doing that shows.
//!
//! ```sh
//! cargo bench --bench graft_nothing
//! ```

use divan::{Bencher, Divan};
use rand::seq::SliceRandom;
use rand::{SeedableRng, rngs::StdRng};

use pathmap::PathMap;
use pathmap::utils::ByteMask;
use pathmap::zipper::*;

fn main() {
    Divan::from_args().sample_count(1000).main();
}

/// Masked branch counts.  1 and 2 take the per-branch path in `graft_masked_branches`, 3 and up
/// the byte-node merge; `graft_child_maps` switches to its fast path above 2 with `remove_unset`.
const BITS: [usize; 7] = [1, 2, 3, 8, 30, 100, 200];

/// Branches the destination holds besides the masked ones
const DST_EXTRA: usize = 50;

/// The first `n` bytes of a fixed shuffle, so masks are spread out and runs are reproducible
fn bytes(n: usize) -> Vec<u8> {
    let mut all: Vec<u8> = (0u8..=255).collect();
    all.shuffle(&mut StdRng::seed_from_u64(0x9a4f_7_u64));
    all.truncate(n);
    all
}

fn masked(bits: usize) -> Vec<u8> {
    bytes(bits)
}

/// The masked bytes, then `DST_EXTRA` more that are not masked
fn dst_bytes(bits: usize) -> Vec<u8> {
    bytes((bits + DST_EXTRA).min(256))
}

/// A destination with a small subtrie and a value at each of `branches`
fn dst_with(branches: &[u8]) -> PathMap<u32> {
    let mut m = PathMap::new();
    m.set_val_at(b"", 1);
    for (i, b) in branches.iter().copied().enumerate() {
        let i = i as u32;
        m.set_val_at([b], 10_000 + i);
        m.set_val_at([b, 1], 10_001 + i);
        m.set_val_at([b, 2, 3], 10_002 + i);
    }
    m
}

/// What the source holds at each masked byte
#[derive(Clone, Copy)]
enum Src {
    /// A value and a subtrie at every masked byte: nothing is empty
    Full,
    /// Every other masked byte; the rest are absent
    Half,
    /// No masked byte, but branches elsewhere, so the source still has a node to merge from
    NoneMasked,
    /// A dangling path at every masked byte
    Dangling,
    /// Only a root value: no node at all
    BareValue,
}

fn src(kind: Src, masked: &[u8]) -> PathMap<u32> {
    let mut m = PathMap::new();
    m.set_val_at(b"", 0);
    let put = |m: &mut PathMap<u32>, b: u8, i: u32| {
        m.set_val_at([b], 20_000 + i);
        m.set_val_at([b, 4], 20_001 + i);
        m.set_val_at([b, 5, 6], 20_002 + i);
    };
    match kind {
        Src::Full => for (i, b) in masked.iter().copied().enumerate() { put(&mut m, b, i as u32) },
        Src::Half => for (i, b) in masked.iter().copied().enumerate().step_by(2) { put(&mut m, b, i as u32) },
        Src::NoneMasked => {
            let unmasked: Vec<u8> = (0u8..=255).filter(|b| !masked.contains(b)).take(3).collect();
            for (i, b) in unmasked.into_iter().enumerate() { put(&mut m, b, i as u32) }
        }
        Src::Dangling => for b in masked.iter().copied() { m.create_path([b]); },
        Src::BareValue => {}
    }
    m
}

fn run_masked(bencher: Bencher, src: PathMap<u32>, dst: PathMap<u32>, focus: &[u8], mask: ByteMask, remove_unset: bool) {
    let focus = focus.to_vec();
    bencher
        .with_inputs(|| dst.clone())
        .bench_local_values(|mut dst| {
            {
                let mut wz = dst.write_zipper_at_path(&focus);
                wz.graft_masked_branches(&src.read_zipper(), mask, remove_unset);
            }
            dst
        });
}

fn masked_case(bencher: Bencher, bits: usize, kind: Src, remove_unset: bool) {
    let m = masked(bits);
    run_masked(bencher, src(kind, &m), dst_with(&dst_bytes(bits)), b"", ByteMask::from_iter(m.iter().copied()), remove_unset);
}

// ------------------------------------------------------------ graft_masked_branches

/// Baseline: the source has every masked branch, so nothing is grafted from nothing
#[divan::bench(args = BITS)]
fn masked_src_full(bencher: Bencher, bits: usize) {
    masked_case(bencher, bits, Src::Full, false);
}

/// Half the masked branches are absent from the source and are emptied in the destination
#[divan::bench(args = BITS)]
fn masked_src_half(bencher: Bencher, bits: usize) {
    masked_case(bencher, bits, Src::Half, false);
}

/// Every masked branch is absent from the source, which still has a node
#[divan::bench(args = BITS)]
fn masked_src_none_masked(bencher: Bencher, bits: usize) {
    masked_case(bencher, bits, Src::NoneMasked, false);
}

/// Every masked branch is a dangling path in the source, which counts as nothing
#[divan::bench(args = BITS)]
fn masked_src_dangling(bencher: Bencher, bits: usize) {
    masked_case(bencher, bits, Src::Dangling, false);
}

/// The source has no node at all, so every masked branch of the destination is emptied
#[divan::bench(args = BITS)]
fn masked_src_bare_value(bencher: Bencher, bits: usize) {
    masked_case(bencher, bits, Src::BareValue, false);
}

/// As [masked_src_half], with `remove_unset`: the unmasked branches go outright
#[divan::bench(args = BITS)]
fn masked_src_half_remove_unset(bencher: Bencher, bits: usize) {
    masked_case(bencher, bits, Src::Half, true);
}

/// The destination focus does not exist and the source lacks every masked branch: nothing to do,
/// and nothing may be created
#[divan::bench(args = BITS)]
fn masked_missing_focus_src_none_masked(bencher: Bencher, bits: usize) {
    let m = masked(bits);
    run_masked(bencher, src(Src::NoneMasked, &m), dst_with(&dst_bytes(bits)), &[255, 254, 253], ByteMask::from_iter(m.iter().copied()), false);
}

/// The destination focus does not exist and the source has every masked branch: the focus is created
#[divan::bench(args = BITS)]
fn masked_missing_focus_src_full(bencher: Bencher, bits: usize) {
    let m = masked(bits);
    run_masked(bencher, src(Src::Full, &m), dst_with(&dst_bytes(bits)), &[255, 254, 253], ByteMask::from_iter(m.iter().copied()), false);
}

// ------------------------------------------------------------------ graft_child_maps

/// One map per masked byte: full, or empty for every other byte when `half_empty`
fn child_maps(masked: &[u8], half_empty: bool) -> Vec<PathMap<u32>> {
    masked.iter().enumerate().map(|(i, _)| {
        let mut m = PathMap::new();
        if !(half_empty && i % 2 == 1) {
            m.set_val_at(b"", 20_000 + i as u32);
            m.set_val_at([4u8], 20_001 + i as u32);
            m.set_val_at([5u8, 6], 20_002 + i as u32);
        }
        m
    }).collect()
}

fn run_child_maps(bencher: Bencher, bits: usize, half_empty: bool, remove_unset: bool) {
    let m = masked(bits);
    let maps = child_maps(&m, half_empty);
    let mask = ByteMask::from_iter(m.iter().copied());
    let dst = dst_with(&dst_bytes(bits));
    bencher
        .with_inputs(|| (dst.clone(), maps.clone()))
        .bench_local_values(|(mut dst, maps)| {
            dst.write_zipper().graft_child_maps(mask, maps, remove_unset);
            dst
        });
}

/// Slow path, every map non-empty: each branch is emptied before its map goes in
#[divan::bench(args = BITS)]
fn child_maps_keep_full(bencher: Bencher, bits: usize) {
    run_child_maps(bencher, bits, false, false);
}

/// Slow path, every other map empty: those branches are emptied and kept as dangling paths
#[divan::bench(args = BITS)]
fn child_maps_keep_half_empty(bencher: Bencher, bits: usize) {
    run_child_maps(bencher, bits, true, false);
}

/// Fast path (`remove_unset`, more than two maps), every map non-empty
#[divan::bench(args = BITS)]
fn child_maps_remove_unset_full(bencher: Bencher, bits: usize) {
    run_child_maps(bencher, bits, false, true);
}

/// Fast path, every other map empty: the empty ones are left out of the new node
#[divan::bench(args = BITS)]
fn child_maps_remove_unset_half_empty(bencher: Bencher, bits: usize) {
    run_child_maps(bencher, bits, true, true);
}
