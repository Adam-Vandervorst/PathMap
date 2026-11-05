//! Benchmarks for `graft_masked_branches` and `graft_child_maps`.
//!
//! Cases vary mask size and distribution, source contents, destination density,
//! and whether the destination focus exists.
//!
//! Run with `cargo bench --bench graft_masked_branches`.

use divan::{Bencher, Divan};
use rand::seq::SliceRandom;
use rand::{SeedableRng, rngs::StdRng};

use pathmap::PathMap;
use pathmap::utils::ByteMask;
use pathmap::zipper::*;

fn main() {
    let divan = Divan::from_args().sample_count(1000);

    divan.main();
}

const BRANCH_COUNTS: [usize; 11] = [1, 2, 3, 4, 6, 8, 15, 30, 60, 100, 200];
const LOW_DENSITY_DST_BRANCHES: usize = 3;
const HIGH_DENSITY_DST_BRANCHES: usize = 150;

#[derive(Clone, Copy, Debug)]
enum MaskDistribution {
    Contiguous,
    PseudoRandom,
}

fn default_extra_branch_count(masked_branch_count: usize) -> usize {
    ((masked_branch_count / 2).max(2)).min(256 - masked_branch_count)
}

fn deterministic_permuted_bytes(seed: u64) -> Vec<u8> {
    let mut bytes: Vec<u8> = (0u8..=255).collect();
    let mut rng = StdRng::seed_from_u64(seed);
    bytes.shuffle(&mut rng);
    bytes
}

fn make_children(masked_branch_count: usize, extra_branch_count: usize, distribution: MaskDistribution) -> (Vec<u8>, Vec<u8>) {
    debug_assert!(masked_branch_count <= 256);
    debug_assert!(extra_branch_count <= 256 - masked_branch_count);

    match distribution {
        MaskDistribution::Contiguous => {
            let masked_children: Vec<u8> = (0..masked_branch_count).map(|idx| idx as u8).collect();
            let extra_children: Vec<u8> = (masked_branch_count..(masked_branch_count + extra_branch_count))
                .map(|idx| idx as u8)
                .collect();
            (masked_children, extra_children)
        }
        MaskDistribution::PseudoRandom => {
            // Deterministic shuffle so benchmark inputs are reproducible without the regular
            // spacing artifacts of a linear permutation prefix.
            let permuted_bytes = deterministic_permuted_bytes(0x5eed_cafe_u64 ^ masked_branch_count as u64);
            let masked_children = permuted_bytes[..masked_branch_count].to_vec();
            let extra_children = permuted_bytes[masked_branch_count..masked_branch_count + extra_branch_count].to_vec();
            (masked_children, extra_children)
        }
    }
}

fn debug_print_mask(_label: &str, _distribution: MaskDistribution, _child_mask: ByteMask) {
    //NOTE: Uncomment this function body to inspect the masks
    // let ranges: Vec<(u8, u8)> = _child_mask
    //     .range_iter()
    //     .map(|range| (*range.start(), *range.end()))
    //     .collect();
    // let ranges_cnt = ranges.len();
    // println!(
    //     "[graft_masked_branches bench] case={_label} distribution={_distribution:?} bits={} ranges={ranges_cnt} mask={}",
    //     pathmap::utils::BitMask::count_bits(&_child_mask),
    //     _child_mask.fmt_binary(),
    // );
}

fn make_case(masked_branch_count: usize, distribution: MaskDistribution) -> (PathMap<u32>, PathMap<u32>, ByteMask) {
    let extra_branch_count = default_extra_branch_count(masked_branch_count);
    let (masked_children, extra_children) = make_children(masked_branch_count, extra_branch_count, distribution);

    let mut src = PathMap::new();
    let mut dst = PathMap::new();

    src.set_val_at(b"", 0);
    dst.set_val_at(b"", 1);

    for (idx, child) in masked_children.iter().copied().enumerate() {
        let idx = idx as u32;

        dst.set_val_at(&[child], 10_000 + idx);
        dst.set_val_at(&[child, 1], 10_001 + idx);
        dst.set_val_at(&[child, 2, 3], 10_002 + idx);

        src.set_val_at(&[child], 20_000 + idx);
        src.set_val_at(&[child, 4], 20_001 + idx);
        src.set_val_at(&[child, 5, 6], 20_002 + idx);
        src.set_val_at(&[child, 7, 8, 9], 20_003 + idx);
    }

    for (idx, child) in extra_children.iter().copied().enumerate() {
        let idx = idx as u32;
        dst.set_val_at(&[child], 30_000 + idx);
        dst.set_val_at(&[child, 11], 30_001 + idx);
        dst.set_val_at(&[child, 12, 13], 30_002 + idx);

        src.set_val_at(&[child], 40_000 + idx);
        src.set_val_at(&[child, 14], 40_001 + idx);
    }

    let child_mask = ByteMask::from_iter(masked_children);
    debug_print_mask("full_src", distribution, child_mask);
    (src, dst, child_mask)
}

fn make_partial_source_case(masked_branch_count: usize, distribution: MaskDistribution) -> (PathMap<u32>, PathMap<u32>, ByteMask) {
    let extra_branch_count = default_extra_branch_count(masked_branch_count);
    let (masked_children, extra_children) = make_children(masked_branch_count, extra_branch_count, distribution);

    let mut src = PathMap::new();
    let mut dst = PathMap::new();

    src.set_val_at(b"", 0);
    dst.set_val_at(b"", 1);

    for (idx, child) in masked_children.iter().copied().enumerate() {
        let idx = idx as u32;

        dst.set_val_at(&[child], 10_000 + idx);
        dst.set_val_at(&[child, 1], 10_001 + idx);
        dst.set_val_at(&[child, 2, 3], 10_002 + idx);

        //Having both a value and onward branch forces an early upgrade from the PairNode to a ByteNode
        // src.set_val_at(&[child], 20_000 + idx);
        src.set_val_at(&[child, 4], 20_001 + idx);
        src.set_val_at(&[child, 5, 6], 20_002 + idx);
        src.set_val_at(&[child, 7, 8, 9], 20_003 + idx);
    }

    for (idx, child) in extra_children.iter().copied().enumerate() {
        let idx = idx as u32;
        dst.set_val_at(&[child], 30_000 + idx);
        dst.set_val_at(&[child, 11], 30_001 + idx);
        dst.set_val_at(&[child, 12, 13], 30_002 + idx);
    }

    let child_mask = ByteMask::from_iter(masked_children);
    debug_print_mask("part_src", distribution, child_mask);
    (src, dst, child_mask)
}

fn make_keep_case_with_dst_branch_count(
    masked_branch_count: usize,
    distribution: MaskDistribution,
    dst_branch_count: usize,
    full_src: bool,
) -> (PathMap<u32>, PathMap<u32>, ByteMask) {
    let src_extra_branch_count = if full_src {
        default_extra_branch_count(masked_branch_count)
    } else {
        0
    };
    let dst_branch_count = dst_branch_count.min(256);
    let src_extra_branch_count = src_extra_branch_count.min(256 - masked_branch_count);
    let (masked_children, src_extra_children) = make_children(masked_branch_count, src_extra_branch_count, distribution);
    let dst_existing_children = deterministic_permuted_bytes(0xd57_d157_u64)[..dst_branch_count].to_vec();

    let mut src = PathMap::new();
    let mut dst = PathMap::new();

    src.set_val_at(b"", 0);
    dst.set_val_at(b"", 1);

    for (idx, child) in dst_existing_children.iter().copied().enumerate() {
        let idx = idx as u32;

        dst.set_val_at(&[child], 10_000 + idx);
        dst.set_val_at(&[child, 1], 10_001 + idx);
        dst.set_val_at(&[child, 2, 3], 10_002 + idx);
    }

    for (idx, child) in masked_children.iter().copied().enumerate() {
        let idx = idx as u32;
        if full_src {
            src.set_val_at(&[child], 20_000 + idx);
        }
        src.set_val_at(&[child, 4], 20_001 + idx);
        src.set_val_at(&[child, 5, 6], 20_002 + idx);
        src.set_val_at(&[child, 7, 8, 9], 20_003 + idx);
    }

    for (idx, child) in src_extra_children.iter().copied().enumerate() {
        let idx = idx as u32;
        src.set_val_at(&[child], 40_000 + idx);
        src.set_val_at(&[child, 14], 40_001 + idx);
    }

    let child_mask = ByteMask::from_iter(masked_children);
    debug_print_mask("keep_dst_branch_count", distribution, child_mask);
    (src, dst, child_mask)
}

fn run_graft_bench(bencher: Bencher, src_template: PathMap<u32>, dst_template: PathMap<u32>, child_mask: ByteMask, remove_unset: bool) {
    let out = bencher
        .with_inputs(|| (src_template.clone(), dst_template.clone()))
        .bench_local_values(|(src, mut dst)| {
            let mut wz = dst.write_zipper_at_path(b"");
            let rz = src.read_zipper_at_path(b"");
            wz.graft_masked_branches(&rz, child_mask, remove_unset);
            drop(wz);
            dst
        });

    divan::black_box_drop(out);
}

// Source-content and missing-focus fixtures.

/// Branch counts for source-content, missing-focus, and child-map cases.
/// Counts 1 and 2 exercise per-branch grafts; 3 and above exercise bulk grafts.
const SOURCE_BRANCH_COUNTS: [usize; 7] = [1, 2, 3, 8, 30, 100, 200];

/// At least two branches are needed to include both populated and empty sources.
const MIXED_BRANCH_COUNTS: [usize; 6] = [2, 3, 8, 30, 100, 200];

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

/// - `remove_unset = true`
/// - `src` contains hundreds of branches, regardless of mask
/// - the mask bits are a contiguous range
#[divan::bench(args = BRANCH_COUNTS)]
fn graft_masked_branches_remove_full_src_contiguous(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_case(masked_branch_count, MaskDistribution::Contiguous);
    run_graft_bench(bencher, src_template, dst_template, child_mask, true);
}

/// - `remove_unset = true`
/// - `src` contains hundreds of branches, regardless of mask
/// - mask bits are distributed pseudorandomly
#[divan::bench(args = BRANCH_COUNTS)]
fn graft_masked_branches_remove_full_src_pseudorandom(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_case(masked_branch_count, MaskDistribution::PseudoRandom);
    run_graft_bench(bencher, src_template, dst_template, child_mask, true);
}

/// - `remove_unset = true`
/// - `src` contains only the branches we're grafting,
/// - the mask bits are a contiguous range
#[divan::bench(args = BRANCH_COUNTS)]
fn graft_masked_branches_remove_part_src_contiguous(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_partial_source_case(masked_branch_count, MaskDistribution::Contiguous);
    run_graft_bench(bencher, src_template, dst_template, child_mask, true);
}

/// - `remove_unset = true`
/// - `src` contains only the branches we're grafting
/// - mask bits are distributed pseudorandomly
#[divan::bench(args = BRANCH_COUNTS)]
fn graft_masked_branches_remove_part_src_pseudorandom(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_partial_source_case(masked_branch_count, MaskDistribution::PseudoRandom);
    run_graft_bench(bencher, src_template, dst_template, child_mask, true);
}

/// - `remove_unset = false`
/// - `src` contains hundreds of branches, regardless of mask
/// - the mask bits are a contiguous range
/// - destination contains a LOW density of pre-existing branches before the graft operation
#[divan::bench(args = BRANCH_COUNTS)]
fn graft_masked_branches_keep_full_src_contiguous_low(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_keep_case_with_dst_branch_count(
        masked_branch_count,
        MaskDistribution::Contiguous,
        LOW_DENSITY_DST_BRANCHES,
        true,
    );
    run_graft_bench(bencher, src_template, dst_template, child_mask, false);
}

/// - `remove_unset = false`
/// - `src` contains hundreds of branches, regardless of mask
/// - the mask bits are a contiguous range
/// - destination contains a HIGH density of pre-existing branches before the graft operation
#[divan::bench(args = BRANCH_COUNTS)]
fn graft_masked_branches_keep_full_src_contiguous_high(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_keep_case_with_dst_branch_count(
        masked_branch_count,
        MaskDistribution::Contiguous,
        HIGH_DENSITY_DST_BRANCHES,
        true,
    );
    run_graft_bench(bencher, src_template, dst_template, child_mask, false);
}

/// - `remove_unset = false`
/// - `src` contains hundreds of branches, regardless of mask
/// - mask bits are distributed pseudorandomly
/// - destination contains a LOW density of pre-existing branches before the graft operation
#[divan::bench(args = BRANCH_COUNTS)]
fn graft_masked_branches_keep_full_src_pseudorandom_low(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_keep_case_with_dst_branch_count(
        masked_branch_count,
        MaskDistribution::PseudoRandom,
        LOW_DENSITY_DST_BRANCHES,
        true,
    );
    run_graft_bench(bencher, src_template, dst_template, child_mask, false);
}

/// - `remove_unset = false`
/// - `src` contains hundreds of branches, regardless of mask
/// - mask bits are distributed pseudorandomly
/// - destination contains a HIGH density of pre-existing branches before the graft operation
#[divan::bench(args = BRANCH_COUNTS)]
fn graft_masked_branches_keep_full_src_pseudorandom_high(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_keep_case_with_dst_branch_count(
        masked_branch_count,
        MaskDistribution::PseudoRandom,
        HIGH_DENSITY_DST_BRANCHES,
        true,
    );
    run_graft_bench(bencher, src_template, dst_template, child_mask, false);
}

/// - `remove_unset = false`
/// - `src` contains only the branches we're grafting
/// - the mask bits are a contiguous range
/// - destination contains a LOW density of pre-existing branches before the graft operation
#[divan::bench(args = BRANCH_COUNTS)]
fn graft_masked_branches_keep_part_src_contiguous_low(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_keep_case_with_dst_branch_count(
        masked_branch_count,
        MaskDistribution::Contiguous,
        LOW_DENSITY_DST_BRANCHES,
        false,
    );
    run_graft_bench(bencher, src_template, dst_template, child_mask, false);
}

/// - `remove_unset = false`
/// - `src` contains only the branches we're grafting
/// - the mask bits are a contiguous range
/// - destination contains a HIGH density of pre-existing branches before the graft operation
#[divan::bench(args = BRANCH_COUNTS)]
fn graft_masked_branches_keep_part_src_contiguous_high(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_keep_case_with_dst_branch_count(
        masked_branch_count,
        MaskDistribution::Contiguous,
        HIGH_DENSITY_DST_BRANCHES,
        false,
    );
    run_graft_bench(bencher, src_template, dst_template, child_mask, false);
}

/// - `remove_unset = false`
/// - `src` contains only the branches we're grafting
/// - mask bits are distributed pseudorandomly
/// - destination contains a LOW density of pre-existing branches before the graft operation
#[divan::bench(args = BRANCH_COUNTS)]
fn graft_masked_branches_keep_part_src_pseudorandom_low(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_keep_case_with_dst_branch_count(
        masked_branch_count,
        MaskDistribution::PseudoRandom,
        LOW_DENSITY_DST_BRANCHES,
        false,
    );
    run_graft_bench(bencher, src_template, dst_template, child_mask, false);
}

/// - `remove_unset = false`
/// - `src` contains only the branches we're grafting
/// - mask bits are distributed pseudorandomly
/// - destination contains a HIGH density of pre-existing branches before the graft operation
#[divan::bench(args = BRANCH_COUNTS)]
fn graft_masked_branches_keep_part_src_pseudorandom_high(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_keep_case_with_dst_branch_count(
        masked_branch_count,
        MaskDistribution::PseudoRandom,
        HIGH_DENSITY_DST_BRANCHES,
        false,
    );
    run_graft_bench(bencher, src_template, dst_template, child_mask, false);
}

/// Half the masked branches are absent from the source and are emptied in the destination
#[divan::bench(args = MIXED_BRANCH_COUNTS)]
fn masked_src_half(bencher: Bencher, bits: usize) {
    masked_case(bencher, bits, Src::Half, false);
}

/// Every masked branch is absent from the source, which still has a node
#[divan::bench(args = SOURCE_BRANCH_COUNTS)]
fn masked_src_none_masked(bencher: Bencher, bits: usize) {
    masked_case(bencher, bits, Src::NoneMasked, false);
}

/// Every masked branch is a dangling path in the source, which counts as nothing
#[divan::bench(args = SOURCE_BRANCH_COUNTS)]
fn masked_src_dangling(bencher: Bencher, bits: usize) {
    masked_case(bencher, bits, Src::Dangling, false);
}

/// The source has no node at all, so every masked branch of the destination is emptied
#[divan::bench(args = SOURCE_BRANCH_COUNTS)]
fn masked_src_bare_value(bencher: Bencher, bits: usize) {
    masked_case(bencher, bits, Src::BareValue, false);
}

/// As [masked_src_half], with `remove_unset`: the unmasked branches go outright
#[divan::bench(args = MIXED_BRANCH_COUNTS)]
fn masked_src_half_remove_unset(bencher: Bencher, bits: usize) {
    masked_case(bencher, bits, Src::Half, true);
}

/// The destination focus does not exist and the source lacks every masked branch: nothing to do,
/// and nothing may be created
#[divan::bench(args = SOURCE_BRANCH_COUNTS)]
fn masked_missing_focus_src_none_masked(bencher: Bencher, bits: usize) {
    let m = masked(bits);
    run_masked(bencher, src(Src::NoneMasked, &m), dst_with(&dst_bytes(bits)), &[255, 254, 253], ByteMask::from_iter(m.iter().copied()), false);
}

/// The destination focus does not exist and the source has every masked branch: the focus is created
#[divan::bench(args = SOURCE_BRANCH_COUNTS)]
fn masked_missing_focus_src_full(bencher: Bencher, bits: usize) {
    let m = masked(bits);
    run_masked(bencher, src(Src::Full, &m), dst_with(&dst_bytes(bits)), &[255, 254, 253], ByteMask::from_iter(m.iter().copied()), false);
}

// Child-map grafts.

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

/// Replace masked branches with nonempty maps, preserving unmasked branches
#[divan::bench(args = SOURCE_BRANCH_COUNTS)]
fn child_maps_keep_full(bencher: Bencher, bits: usize) {
    run_child_maps(bencher, bits, false, false);
}

/// Alternate nonempty and empty maps, preserving unmasked branches
#[divan::bench(args = MIXED_BRANCH_COUNTS)]
fn child_maps_keep_half_empty(bencher: Bencher, bits: usize) {
    run_child_maps(bencher, bits, true, false);
}

/// Replace all children with nonempty maps at the masked bytes
#[divan::bench(args = SOURCE_BRANCH_COUNTS)]
fn child_maps_remove_unset_full(bencher: Bencher, bits: usize) {
    run_child_maps(bencher, bits, false, true);
}

/// Replace all children with alternating nonempty and empty maps
#[divan::bench(args = MIXED_BRANCH_COUNTS)]
fn child_maps_remove_unset_half_empty(bencher: Bencher, bits: usize) {
    run_child_maps(bencher, bits, true, true);
}
