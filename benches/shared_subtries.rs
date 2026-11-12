//! Algebraic operations on tries that share subtries
//!
//! A subtrie that both operands hold as the same node is its own join, meet and restriction, and
//! subtracting it leaves nothing, so an operation should settle it by pointer equality without
//! descending into it, and without copying it.  Every benchmark here gives both operands a shared
//! subtrie of `n` random keys, so a cost that grows with `n` means the shared part is walked or
//! copied.  Ideally all of them are flat.
//!
//! "Slot" benchmarks put the shared subtrie `M` at `P` in two otherwise small maps: `a` has values
//! at three sibling bytes, so `P` is a slot of a byte node, and `b` holds `M` alone or with fewer
//! siblings.  "Edited copy" benchmarks pair a map with a clone of itself that has had `EDITS` keys
//! added, so all but the edited paths are shared; their cost should follow `EDITS`, not `n`.

use divan::{Bencher, Divan, black_box};
use pathmap::PathMap;
use pathmap::ring::Lattice;
use pathmap::zipper::*;
use rand::{Rng, SeedableRng, rngs::StdRng};

fn main() {
    Divan::from_args().main();
}

const SIZES: &[usize] = &[1_000, 10_000, 100_000];

/// Where the shared subtrie sits in the slot benchmarks
const P: &[u8] = b"p";

/// Keys added to the edited copy
const EDITS: usize = 16;

fn random_keys(rng: &mut StdRng, n: usize) -> Vec<Vec<u8>> {
    (0..n).map(|_| (0..8).map(|_| rng.random::<u8>()).collect()).collect()
}

/// `n` random 8 byte keys
fn subtrie(n: usize) -> PathMap<u64> {
    random_keys(&mut StdRng::seed_from_u64(1), n).iter().map(|k| (k, 0)).collect()
}

/// A map holding `m` at `P`, with a value at each of `siblings`
fn holding(m: &PathMap<u64>, siblings: &[&[u8]]) -> PathMap<u64> {
    let mut map = PathMap::new();
    for key in siblings {
        map.set_val_at(key, 0);
    }
    map.write_zipper_at_path(P).graft_map(m.clone());
    map
}

/// `a` with `M` in a byte node's slot at `P`, and `b` with `M` in the same slot of a smaller byte node
fn slot_pair(n: usize) -> (PathMap<u64>, PathMap<u64>) {
    let m = subtrie(n);
    (holding(&m, &[b"a", b"b", b"c"]), holding(&m, &[b"a", b"b"]))
}

/// A map of `n` random keys and a clone of it with `EDITS` more
fn edited_pair(n: usize) -> (PathMap<u64>, PathMap<u64>) {
    let x = subtrie(n);
    let mut y = x.clone();
    for key in random_keys(&mut StdRng::seed_from_u64(2), EDITS) {
        y.set_val_at(&key, 1);
    }
    (x, y)
}

/// [PathMap::join_into] where both maps hold `M` in a byte node's slot
#[divan::bench(args = SIZES)]
fn join_into_shared_slot(bencher: Bencher, n: usize) {
    let (a, b) = slot_pair(n);
    bencher.with_inputs(|| (a.clone(), b.clone())).bench_local_values(|(mut a, b)| {
        black_box(a.join_into(b));
        a
    });
}

/// [PathMap::join_into] where the other map's root is a list node holding `M`, so the join merges
/// it into a byte node child by child
#[divan::bench(args = SIZES)]
fn join_into_shared_list_child(bencher: Bencher, n: usize) {
    let m = subtrie(n);
    let a = holding(&m, &[b"a", b"b", b"c"]);
    let b = holding(&m, &[]);
    bencher.with_inputs(|| (a.clone(), b.clone())).bench_local_values(|(mut a, b)| {
        black_box(a.join_into(b));
        a
    });
}

/// [PathMap::join_into] of a map and its own clone, which share the root
#[divan::bench(args = SIZES)]
fn join_into_own_clone(bencher: Bencher, n: usize) {
    let x = subtrie(n);
    bencher.with_inputs(|| (x.clone(), x.clone())).bench_local_values(|(mut a, b)| {
        black_box(a.join_into(b));
        a
    });
}

/// [PathMap::join_into] of a map and an edited copy of it
#[divan::bench(args = SIZES)]
fn join_into_edited_copy(bencher: Bencher, n: usize) {
    let (x, y) = edited_pair(n);
    bencher.with_inputs(|| (x.clone(), y.clone())).bench_local_values(|(mut a, b)| {
        black_box(a.join_into(b));
        a
    });
}

/// [ZipperWriting::join_into_take] with both foci at `M`
#[divan::bench(args = SIZES)]
fn join_into_take_shared_focus(bencher: Bencher, n: usize) {
    let (a, b) = slot_pair(n);
    bencher.with_inputs(|| (a.clone(), b.clone())).bench_local_values(|(mut a, mut b)| {
        black_box(a.write_zipper_at_path(P).join_into_take(&mut b.write_zipper_at_path(P), false));
        (a, b)
    });
}

/// [PathMap::restrict] of a map by itself
#[divan::bench(args = SIZES)]
fn restrict_by_itself(bencher: Bencher, n: usize) {
    let x = subtrie(n);
    bencher.bench_local(|| black_box(&x).restrict(black_box(&x)));
}

/// [PathMap::restrict] of a map by an edited copy of it
#[divan::bench(args = SIZES)]
fn restrict_by_edited_copy(bencher: Bencher, n: usize) {
    let (x, y) = edited_pair(n);
    bencher.bench_local(|| black_box(&x).restrict(black_box(&y)));
}

/// [PathMap::meet] of a map and an edited copy of it
#[divan::bench(args = SIZES)]
fn meet_edited_copy(bencher: Bencher, n: usize) {
    let (x, y) = edited_pair(n);
    bencher.bench_local(|| black_box(&x).meet(black_box(&y)));
}

/// [PathMap::subtract] of a map from an edited copy of it
#[divan::bench(args = SIZES)]
fn subtract_from_edited_copy(bencher: Bencher, n: usize) {
    let (x, y) = edited_pair(n);
    bencher.bench_local(|| black_box(&y).subtract(black_box(&x)));
}

/// [ZipperWriting::join_into] with both foci at `M`
#[divan::bench(args = SIZES)]
fn zipper_join_into_shared_focus(bencher: Bencher, n: usize) {
    let (a, b) = slot_pair(n);
    bencher.with_inputs(|| a.clone()).bench_local_refs(|a| {
        black_box(a.write_zipper_at_path(P).join_into(&b.read_zipper_at_path(P)))
    });
}

/// [ZipperWriting::meet_into] with both foci at `M`
#[divan::bench(args = SIZES)]
fn zipper_meet_into_shared_focus(bencher: Bencher, n: usize) {
    let (a, b) = slot_pair(n);
    bencher.with_inputs(|| a.clone()).bench_local_refs(|a| {
        black_box(a.write_zipper_at_path(P).meet_into(&b.read_zipper_at_path(P), false))
    });
}

/// [ZipperWriting::subtract_into] with both foci at `M`
#[divan::bench(args = SIZES)]
fn zipper_subtract_into_shared_focus(bencher: Bencher, n: usize) {
    let (a, b) = slot_pair(n);
    bencher.with_inputs(|| a.clone()).bench_local_refs(|a| {
        black_box(a.write_zipper_at_path(P).subtract_into(&b.read_zipper_at_path(P), false))
    });
}

/// [ZipperWriting::restrict] with both foci at `M`
#[divan::bench(args = SIZES)]
fn zipper_restrict_shared_focus(bencher: Bencher, n: usize) {
    let (a, b) = slot_pair(n);
    bencher.with_inputs(|| a.clone()).bench_local_refs(|a| {
        black_box(a.write_zipper_at_path(P).restrict(&b.read_zipper_at_path(P)))
    });
}
