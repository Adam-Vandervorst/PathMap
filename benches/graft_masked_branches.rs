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

/// - `remove_unset = true`
/// - `src` contains hundreds of branches, regardless of mask
/// - the mask bits are a contiguous range
#[divan::bench(sample_size = 1, args = BRANCH_COUNTS)]
fn graft_masked_branches_remove_full_src_contiguous(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_case(masked_branch_count, MaskDistribution::Contiguous);
    run_graft_bench(bencher, src_template, dst_template, child_mask, true);
}

/// - `remove_unset = true`
/// - `src` contains hundreds of branches, regardless of mask
/// - mask bits are distributed pseudorandomly
#[divan::bench(sample_size = 1, args = BRANCH_COUNTS)]
fn graft_masked_branches_remove_full_src_pseudorandom(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_case(masked_branch_count, MaskDistribution::PseudoRandom);
    run_graft_bench(bencher, src_template, dst_template, child_mask, true);
}

/// - `remove_unset = true`
/// - `src` contains only the branches we're grafting,
/// - the mask bits are a contiguous range
#[divan::bench(sample_size = 1, args = BRANCH_COUNTS)]
fn graft_masked_branches_remove_part_src_contiguous(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_partial_source_case(masked_branch_count, MaskDistribution::Contiguous);
    run_graft_bench(bencher, src_template, dst_template, child_mask, true);
}

/// - `remove_unset = true`
/// - `src` contains only the branches we're grafting
/// - mask bits are distributed pseudorandomly
#[divan::bench(sample_size = 1, args = BRANCH_COUNTS)]
fn graft_masked_branches_remove_part_src_pseudorandom(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_partial_source_case(masked_branch_count, MaskDistribution::PseudoRandom);
    run_graft_bench(bencher, src_template, dst_template, child_mask, true);
}

/// - `remove_unset = false`
/// - `src` contains hundreds of branches, regardless of mask
/// - the mask bits are a contiguous range
/// - destination contains a LOW density of pre-existing branches before the graft operation
#[divan::bench(sample_size = 1, args = BRANCH_COUNTS)]
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
#[divan::bench(sample_size = 1, args = BRANCH_COUNTS)]
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
#[divan::bench(sample_size = 1, args = BRANCH_COUNTS)]
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
#[divan::bench(sample_size = 1, args = BRANCH_COUNTS)]
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
#[divan::bench(sample_size = 1, args = BRANCH_COUNTS)]
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
#[divan::bench(sample_size = 1, args = BRANCH_COUNTS)]
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
#[divan::bench(sample_size = 1, args = BRANCH_COUNTS)]
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
#[divan::bench(sample_size = 1, args = BRANCH_COUNTS)]
fn graft_masked_branches_keep_part_src_pseudorandom_high(bencher: Bencher, masked_branch_count: usize) {
    let (src_template, dst_template, child_mask) = make_keep_case_with_dst_branch_count(
        masked_branch_count,
        MaskDistribution::PseudoRandom,
        HIGH_DENSITY_DST_BRANCHES,
        false,
    );
    run_graft_bench(bencher, src_template, dst_template, child_mask, false);
}
