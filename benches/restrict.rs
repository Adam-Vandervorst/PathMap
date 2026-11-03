//! Asymptotic scaling of `restrict`
//!
//! `restrict(L, R)` keeps every path of `L` that has a prefix leading to a value in `R`.  It only
//! needs to walk the structure `L` and `R` have in common, and it can stop at each of `R`'s values
//! because everything in `L` below that point is kept as-is.  So the cost should be governed by `R`
//! and by the overlap, not by how big, deep or wide `L` is.
//!
//! Each benchmark sweeps a single parameter with the others held fixed.
//!
//! "Spine" tries are built from `SPINES` pseudo-random paths that start with distinct bytes.  An
//! `R` is made by putting values on the spines at the cut-off depth.  `L` gets `branching - 1`
//! sibling leaves at every node along each spine, which makes the nodes a restriction has to pass
//! through as wide as we want without changing which paths the restriction follows.
//!
//! "Random" tries are uniform random keys, where `R` is half prefixes of `L`'s keys and half fresh
//! keys that diverge from `L` after the first few bytes.

use divan::{Bencher, Divan, black_box};
use pathmap::PathMap;
use pathmap::zipper::*;
use rand::{Rng, SeedableRng, rngs::StdRng};

fn main() {
    Divan::from_args().main();
}

const SPINES: usize = 64;

/// The `i`th spine, `len` bytes long
fn spine(i: usize, len: usize) -> Vec<u8> {
    let mut rng = StdRng::seed_from_u64(i as u64);
    let mut path = Vec::with_capacity(len);
    path.push((i * (256 / SPINES)) as u8);
    path.extend((1..len).map(|_| rng.random::<u8>()));
    path
}

/// Puts a value at the end of each path, plus `branching - 1` sibling leaves next to each step of
/// each path, from depth 1 to `sibling_depth`.  Sibling bytes are the step byte plus `1..branching`,
/// so paths can diverge from the spines with `step ^ 0x80` without landing on a sibling if
/// `branching <= 128`
fn bushy_trie(paths: &[Vec<u8>], sibling_depth: usize, branching: usize) -> PathMap<u64> {
    let mut map = PathMap::new();
    for path in paths {
        map.set_val_at(path, 0);
        for depth in 1..sibling_depth.min(path.len()) {
            let mut sibling = path[..=depth].to_vec();
            for t in 1..branching {
                sibling[depth] = path[depth].wrapping_add(t as u8);
                map.set_val_at(&sibling, 0);
            }
        }
    }
    map
}

fn spines(len: usize) -> Vec<Vec<u8>> {
    (0..SPINES).map(|i| spine(i, len)).collect()
}

/// Width of `L`'s nodes along the restricted paths.  Ideally flat
///
/// `L`: spines of depth 32, siblings at every step.  `R`: values on the spines at depth 16
#[divan::bench(args = [1, 2, 4, 16, 64, 256])]
fn lhs_branching(bencher: Bencher, branching: usize) {
    let l = bushy_trie(&spines(32), 32, branching);
    let r = bushy_trie(&spines(16), 0, 1);
    bencher.bench_local(|| black_box(&l).restrict(black_box(&r)));
}

/// How much of `L` hangs below `R`'s values.  Ideally flat
///
/// `L`: spines of the given depth, 16 wide at every step.  `R`: values on the spines at depth 8
#[divan::bench(args = [8, 32, 128, 512])]
fn lhs_depth_below_cutoff(bencher: Bencher, depth: usize) {
    let l = bushy_trie(&spines(depth), depth, 16);
    let r = bushy_trie(&spines(8), 0, 1);
    bencher.bench_local(|| black_box(&l).restrict(black_box(&r)));
}

/// Depth of `R`'s values, i.e. how far the restriction descends.  Ideally linear
///
/// `L`: spines of depth 128, 16 wide at every step.  `R`: values on the spines at the given depth
#[divan::bench(args = [1, 4, 16, 64, 128])]
fn cutoff_depth(bencher: Bencher, cutoff: usize) {
    let l = bushy_trie(&spines(128), 128, 16);
    let r = bushy_trie(&spines(cutoff), 0, 1);
    bencher.bench_local(|| black_box(&l).restrict(black_box(&r)));
}

/// Width of `R`'s nodes, none of whose siblings exist in `L`.  Ideally flat
///
/// `L`: bare spines of depth 32.  `R`: values on the spines at depth 16, siblings at every step
#[divan::bench(args = [1, 2, 4, 16, 64, 256])]
fn rhs_branching(bencher: Bencher, branching: usize) {
    let l = bushy_trie(&spines(32), 0, 1);
    let r = bushy_trie(&spines(16), 16, branching);
    bencher.bench_local(|| black_box(&l).restrict(black_box(&r)));
}

/// How far `R` continues below its first value on each path.  Ideally flat
///
/// `L`: spines of depth 32, 16 wide at every step.  `R`: values on the spines at depth 8 and at
/// the given depth
#[divan::bench(args = [8, 32, 128, 512])]
fn rhs_depth_below_cutoff(bencher: Bencher, depth: usize) {
    let l = bushy_trie(&spines(32), 32, 16);
    let mut r = bushy_trie(&spines(depth), 0, 1);
    for path in spines(8) {
        r.set_val_at(&path, 0);
    }
    bencher.bench_local(|| black_box(&l).restrict(black_box(&r)));
}

/// Percentage of `R`'s paths that are in `L`; the others leave `L` half way down.  Ideally linear
///
/// `L`: spines of depth 32, 16 wide at every step.  `R`: values at depth 16
#[divan::bench(args = [0, 25, 50, 75, 100])]
fn overlap_percent(bencher: Bencher, percent: usize) {
    let l = bushy_trie(&spines(32), 32, 16);
    let r_paths: Vec<Vec<u8>> = spines(16).into_iter().enumerate().map(|(i, mut path)| {
        if i * 100 >= percent * SPINES {
            path[8] ^= 0x80;
        }
        path
    }).collect();
    let r = bushy_trie(&r_paths, 0, 1);
    bencher.bench_local(|| black_box(&l).restrict(black_box(&r)));
}

fn random_keys(rng: &mut StdRng, n: usize, len: usize) -> Vec<Vec<u8>> {
    (0..n).map(|_| (0..len).map(|_| rng.random::<u8>()).collect()).collect()
}

/// Half of the `R` keys cut off `L` keys after 4 bytes, the other half are fresh 8 byte keys
fn random_pair(lhs_size: usize, rhs_size: usize) -> (PathMap<u64>, PathMap<u64>) {
    let mut rng = StdRng::seed_from_u64(1);
    let l_keys = random_keys(&mut rng, lhs_size, 8);
    let mut r_keys = random_keys(&mut rng, rhs_size / 2, 8);
    r_keys.extend((0..rhs_size - rhs_size / 2).map(|_| l_keys[rng.random_range(0..lhs_size)][..4].to_vec()));
    (l_keys.iter().map(|k| (k, 0)).collect(), r_keys.iter().map(|k| (k, 0)).collect())
}

/// Size of a random `L` restricted by 64 keys.  Ideally ~flat (only the trie depth grows)
#[divan::bench(args = [1_000, 10_000, 100_000, 1_000_000])]
fn random_lhs_size(bencher: Bencher, lhs_size: usize) {
    let (l, r) = random_pair(lhs_size, 64);
    bencher.bench_local(|| black_box(&l).restrict(black_box(&r)));
}

/// Size of a random `R` restricting 100k keys.  Ideally ~linear
#[divan::bench(args = [16, 256, 4_096, 65_536])]
fn random_rhs_size(bencher: Bencher, rhs_size: usize) {
    let (l, r) = random_pair(100_000, rhs_size);
    bencher.bench_local(|| black_box(&l).restrict(black_box(&r)));
}

/// [lhs_branching], through [WriteZipper::restrict] at a focus below the root
#[divan::bench(args = [1, 2, 4, 16, 64, 256])]
fn zipper_restrict_lhs_branching(bencher: Bencher, branching: usize) {
    let mut l = PathMap::new();
    l.write_zipper_at_path(b"focus").graft_map(bushy_trie(&spines(32), 32, branching));
    let r = bushy_trie(&spines(16), 0, 1);
    bencher.with_inputs(|| l.clone()).bench_local_refs(|l| {
        let mut wz = l.write_zipper_at_path(b"focus");
        black_box(wz.restrict(&black_box(&r).read_zipper()))
    });
}

/// [lhs_branching] with the roles swapped through [WriteZipper::restricting]: the zipper holds the
/// stems and the (wide) source is restricted by them
#[divan::bench(args = [1, 2, 4, 16, 64, 256])]
fn zipper_restricting_src_branching(bencher: Bencher, branching: usize) {
    let src = bushy_trie(&spines(32), 32, branching);
    let stems = bushy_trie(&spines(16), 0, 1);
    bencher.with_inputs(|| stems.clone()).bench_local_refs(|stems| {
        black_box(stems.write_zipper().restricting(&black_box(&src).read_zipper()))
    });
}
