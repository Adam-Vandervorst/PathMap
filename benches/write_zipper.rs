//! WriteZipper benchmarks
//!
//! # Movement over nodes the zipper doesn't own (`shared_descend_to_*`)
//!
//! Moving a zipper doesn't change the trie, so a WriteZipper that only moves should cost about what a
//! ReadZipper does.  Over shared nodes it costs far more: the WriteZipper holds a stack of mutable
//! node references and takes each one with `make_mut`, which clones a node that has another owner.
//! Descending into a cloned map or a grafted subtrie therefore copies every node on the way down,
//! before anything is written and even if nothing ever is.  See "Scouting write zipper" in the book.
//!
//! The same descents are run three ways:
//! - `rz`: a ReadZipper, the baseline
//! - `wz_owned`: a WriteZipper over nodes it owns, which is what its movement costs without clones
//! - `wz_shared`: a WriteZipper over the same trie when every node has another owner
//!
//! The argument is the width of the nodes the zipper passes through.  A ReadZipper doesn't care how
//! wide a node is, and neither does a WriteZipper that owns it, but a clone costs the node's width.
//! So `wz_shared` ought to match `wz_owned` and stay flat; the gap between them is the cost of the
//! clones.  Nothing writes to the trie in any of the three.
//!
//! Descents are the movement that shows this.  A walk over a whole shared trie copies all of it, but
//! it visits every child of a node it cloned, which hides the cost of the clone.
//!
//! # Writes below nodes the zipper doesn't own (`shared_set_val_*`)
//!
//! The same descents, each followed by setting the value at the end of the path.  Here the clones
//! are needed: `wz_shared` copies every node on each path, and `wz_owned` copies none.  This is the
//! cost that `shared_descend_to_wz_shared` shouldn't have.  It is here so that a change to how a
//! WriteZipper moves over shared nodes also shows what it does to the write that follows.

use divan::{Bencher, Divan, black_box};
use pathmap::PathMap;
use pathmap::zipper::*;
use rand::{Rng, SeedableRng, rngs::StdRng};

fn main() {
    Divan::from_args().main();
}

const BRANCHING: [usize; 5] = [1, 4, 16, 64, 256];
const SPINES: usize = 16;
const DEPTH: usize = 16;

/// `SPINES` random paths of `DEPTH` bytes that start with distinct bytes and end in a value.  Each
/// step of a path after the first has `branching - 1` siblings, and each sibling leads to a node of
/// its own, like the children in the upper levels of a big trie do.  From a `branching` of 4 up,
/// each path crosses `DEPTH - 1` nodes below the root
fn spine_trie(branching: usize) -> (PathMap<u64>, Vec<Vec<u8>>) {
    let mut rng = StdRng::seed_from_u64(1);
    let mut map = PathMap::new();
    let mut paths = Vec::with_capacity(SPINES);
    for i in 0..SPINES {
        let mut path = vec![(i * (256 / SPINES)) as u8];
        path.extend((1..DEPTH).map(|_| rng.random::<u8>()));
        map.set_val_at(&path, 0);
        for depth in 1..DEPTH {
            let mut sibling = path[..=depth].to_vec();
            sibling.extend([0, 0]);
            for t in 1..branching {
                sibling[depth] = path[depth].wrapping_add(t as u8);
                map.set_val_at(&sibling, 0);
            }
        }
        paths.push(path);
    }
    (map, paths)
}

/// Descends from the root to the end of each path
fn descend_to_each<Z: ZipperMoving>(z: &mut Z, paths: &[Vec<u8>]) -> usize {
    let mut found = 0;
    for path in paths {
        z.descend_to(path);
        found += z.is_val() as usize;
        z.reset();
    }
    assert_eq!(found, paths.len());
    found
}

#[divan::bench(args = BRANCHING)]
fn shared_descend_to_rz(bencher: Bencher, branching: usize) {
    let (map, paths) = spine_trie(branching);
    bencher.bench_local(|| descend_to_each(&mut black_box(&map).read_zipper(), &paths));
}

#[divan::bench(args = BRANCHING)]
fn shared_descend_to_wz_owned(bencher: Bencher, branching: usize) {
    let (mut map, paths) = spine_trie(branching);
    bencher.bench_local(|| descend_to_each(&mut black_box(&mut map).write_zipper(), &paths));
}

/// The first descent through shared nodes leaves the map it went through owning a private copy of
/// them, so every run gets a fresh handle to the shared trie, which is a refcount bump on the root
/// made outside the timing.  The run returns its handle so that freeing the copies isn't timed
/// either: what is measured is the movement plus allocating and filling the clones.
#[divan::bench(args = BRANCHING)]
fn shared_descend_to_wz_shared(bencher: Bencher, branching: usize) {
    let (map, paths) = spine_trie(branching);
    bencher.with_inputs(|| map.clone()).bench_local_values(|mut map| {
        black_box(descend_to_each(&mut map.write_zipper(), &paths));
        map
    });
}

/// Descends from the root to the end of each path, and sets the value there
fn set_val_at_each<Z: ZipperMoving + ZipperWriting<u64>>(z: &mut Z, paths: &[Vec<u8>]) -> usize {
    let mut replaced = 0;
    for path in paths {
        z.descend_to(path);
        replaced += z.set_val(1).is_some() as usize;
        z.reset();
    }
    assert_eq!(replaced, paths.len());
    replaced
}

#[divan::bench(args = BRANCHING)]
fn shared_set_val_wz_owned(bencher: Bencher, branching: usize) {
    let (mut map, paths) = spine_trie(branching);
    bencher.bench_local(|| set_val_at_each(&mut black_box(&mut map).write_zipper(), &paths));
}

/// As in [shared_descend_to_wz_shared], every run gets a fresh handle to the shared trie and hands
/// it back, so the timing covers the movement, the clones and the writes, but not freeing the clones
#[divan::bench(args = BRANCHING)]
fn shared_set_val_wz_shared(bencher: Bencher, branching: usize) {
    let (map, paths) = spine_trie(branching);
    bencher.with_inputs(|| map.clone()).bench_local_values(|mut map| {
        black_box(set_val_at_each(&mut map.write_zipper(), &paths));
        map
    });
}
