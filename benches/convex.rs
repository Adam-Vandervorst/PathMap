//! Scaling of stable convex meet and subtraction, through both native nodes and zippers.
//!
//! Valued interiors exercise stable pruning; the fringe cases isolate descendant-witness searches.
//! Each sweep varies one parameter. Independent operands
//! have no shared nodes; the `shared_*` sweeps measure identity with and without a root value,
//! and sparse edits.
//!
//! Setup and a check against the hull/retain specification run outside the timing. Each timed
//! call returns a fresh map; Divan defers its destruction. The zipper measurements include opening
//! the input/output zippers, making their allocation and output lifetime comparable to the map API.
//!
//! Run with `cargo bench --bench convex`; `-- --test` checks every fixture without sampling.

use divan::{Bencher, Divan, black_box};
use pathmap::{
    PathMap,
    experimental::{
        convex::{convex_meet, convex_subtract, zipper_convex_meet, zipper_convex_subtract},
        path_sets::{hull, retain},
    },
};

type Map = PathMap<u64>;
type Pair = (Map, Map);

fn main() {
    Divan::from_args().main();
}

trait Operation {
    const SUBTRACT: bool;
    fn apply(left: &Map, right: &Map) -> Map;
}

struct NativeMeet;
struct NativeSubtract;
struct ZipperMeet;
struct ZipperSubtract;

impl Operation for NativeMeet {
    const SUBTRACT: bool = false;
    fn apply(left: &Map, right: &Map) -> Map {
        convex_meet(left, right)
    }
}

impl Operation for NativeSubtract {
    const SUBTRACT: bool = true;
    fn apply(left: &Map, right: &Map) -> Map {
        convex_subtract(left, right)
    }
}

impl Operation for ZipperMeet {
    const SUBTRACT: bool = false;
    fn apply(left: &Map, right: &Map) -> Map {
        let mut out = Map::new();
        zipper_convex_meet(
            &mut left.read_zipper(),
            &mut right.read_zipper(),
            &mut out.write_zipper(),
        );
        out
    }
}

impl Operation for ZipperSubtract {
    const SUBTRACT: bool = true;
    fn apply(left: &Map, right: &Map) -> Map {
        let mut out = Map::new();
        zipper_convex_subtract(
            &mut left.read_zipper(),
            &mut right.read_zipper(),
            &mut out.write_zipper(),
        );
        out
    }
}

fn measure<O: Operation>(bencher: Bencher, (left, right): Pair) {
    // Mask algebra observes only domains, even when the input payloads differ.
    let left_keys: PathMap<()> = left.iter().map(|(p, _)| (p, ())).collect();
    let right_keys: PathMap<()> = right.iter().map(|(p, _)| (p, ())).collect();
    let expected = if O::SUBTRACT {
        retain(&left, &hull(&left_keys).subtract(&right_keys))
    } else {
        // Ordinary meet may combine payloads; convex meet keeps the left payload unchanged.
        let common: Map = left
            .iter()
            .filter(|(p, _)| right.get(p).is_some())
            .map(|(p, v)| (p, *v))
            .collect();
        retain(&common, &hull(&left_keys).meet(&hull(&right_keys)))
    };
    let actual = O::apply(&left, &right);
    for (p, v) in expected.iter() {
        assert_eq!(actual.get(&p), Some(v), "path {p:?}");
    }
    assert_eq!(actual.val_count(), expected.val_count());
    drop((actual, expected));
    bencher.bench_local(|| O::apply(black_box(&left), black_box(&right)));
}

/// Deterministic, distinct keys spread across the root's children, without random setup state.
fn key(i: usize) -> [u8; 8] {
    (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15).to_be_bytes()
}

/// Common interior marks precede each leaf. Nonmatching leaves diverge only at the last byte,
/// forcing meet to discard their common interiors and subtraction to preserve those interiors.
fn independent(tips: usize, overlap: usize, stem_len: usize) -> Pair {
    let mut left = Map::new();
    let mut right = Map::new();
    let stem = vec![0x55; stem_len];
    left.set_val_at(&stem, 1);
    right.set_val_at(&stem, 2);
    for i in 0..tips {
        let mut p = stem.clone();
        p.extend(key(i));
        for end in [stem_len + 4, p.len()] {
            left.set_val_at(&p[..end], i as u64 + 1);
            right.set_val_at(&p[..end], i as u64 + 2);
        }
        p.push(0);
        left.set_val_at(&p, i as u64 + 1);
        *p.last_mut().unwrap() = u8::from(i >= tips * overlap / 100);
        right.set_val_at(&p, i as u64 + 2);
    }
    (left, right)
}

fn population(tips: usize) -> Pair {
    independent(tips, 50, 0)
}

fn overlap(percent: usize) -> Pair {
    independent(4096, percent, 0)
}

fn compressed_depth(bytes: usize) -> Pair {
    independent(64, 50, bytes)
}

/// All common marks are interiors; differing tips make meet empty after stable pruning.
/// Subtraction keeps every left mark, even though the mask contains every interior.
fn valued_depth(depth: usize) -> Pair {
    let mut left = Map::new();
    let mut right = Map::new();
    let mut p = Vec::with_capacity(depth + 1);
    for _ in 0..=depth {
        left.set_val_at(&p, 1);
        right.set_val_at(&p, 2);
        p.push(0);
    }
    *p.last_mut().unwrap() = 1;
    left.set_val_at(&p, 1);
    *p.last_mut().unwrap() = 2;
    right.set_val_at(&p, 2);
    (left, right)
}

/// Fixed common spines, with increasing left-only sibling branches. Subtraction can share them;
/// meet needs their liveness to avoid treating common interior marks as original tips.
fn branching(width: usize) -> Pair {
    let mut left = Map::new();
    let mut right = Map::new();
    for head in 0..8 {
        let mut p = vec![head];
        for _ in 0..16 {
            left.set_val_at(&p, 1);
            right.set_val_at(&p, 2);
            p.push(0);
            for sibling in 1..width {
                *p.last_mut().unwrap() = sibling as u8;
                left.set_val_at(&p, 1);
            }
            *p.last_mut().unwrap() = 0;
        }
        left.set_val_at(&p, 1);
        right.set_val_at(&p, 2);
    }
    (left, right)
}

/// Left tips coincide with right marks. Right-only descendants require one valued witness,
/// or a full scan when the entire fringe is bare. A subtree cardinality scan would make the
/// valued-fringe sweep unnecessarily linear in the number of descendants.
fn fringe(descendants: usize, valued: bool) -> Pair {
    let mut left = Map::new();
    let mut right = Map::new();
    for head in 0..4 {
        left.set_val_at([head], 1);
        right.set_val_at([head], 2);
        for i in 0..descendants {
            let mut p = vec![head];
            p.extend(key(i));
            if valued {
                right.set_val_at(&p, 2);
            } else {
                right.create_path(&p);
            }
        }
    }
    (left, right)
}

fn rhs_fringe(descendants: usize) -> Pair {
    fringe(descendants, true)
}

fn rhs_bare_fringe(descendants: usize) -> Pair {
    fringe(descendants, false)
}

// A value at the focus suppresses ZipperConcrete::shared_node_id. Keep this case
// separate from the unvalued root so both the traversal and sharing fast path are visible.
fn shared_identity(tips: usize) -> Pair {
    let (left, _) = population(tips);
    let right = left.clone();
    (left, right)
}

fn shared_unvalued_root(tips: usize) -> Pair {
    let (mut left, _) = population(tips);
    left.remove_val_at([], false);
    let right = left.clone();
    (left, right)
}

fn shared_edit(tips: usize) -> Pair {
    let (left, mut right) = shared_identity(tips);
    let mut p = key(0).to_vec();
    p.push(0);
    right.remove_val_at(&p, true);
    *p.last_mut().unwrap() = 1;
    right.set_val_at(&p, 2);
    (left, right)
}

// Keep operation and fixture in each function name: the CI table parser records
// one group plus its argument, so nested generic groups would overwrite cases.
macro_rules! sweep {
    ($name:ident, $args:expr) => {
        paste::paste! {
            #[divan::bench(args = $args)]
            fn [<native_meet_ $name>](bencher: Bencher, n: usize) {
                measure::<NativeMeet>(bencher, $name(n));
            }
            #[divan::bench(args = $args)]
            fn [<native_subtract_ $name>](bencher: Bencher, n: usize) {
                measure::<NativeSubtract>(bencher, $name(n));
            }
            #[divan::bench(args = $args)]
            fn [<zipper_meet_ $name>](bencher: Bencher, n: usize) {
                measure::<ZipperMeet>(bencher, $name(n));
            }
            #[divan::bench(args = $args)]
            fn [<zipper_subtract_ $name>](bencher: Bencher, n: usize) {
                measure::<ZipperSubtract>(bencher, $name(n));
            }
        }
    };
}

sweep!(population, [64, 256, 1024, 4096, 16384]);
sweep!(overlap, [0, 25, 50, 75, 100]);
sweep!(compressed_depth, [0, 16, 256, 4096, 16384]);
sweep!(valued_depth, [8, 32, 128, 512, 2048]);
sweep!(branching, [2, 4, 16, 64, 256]);
sweep!(rhs_fringe, [0, 16, 256, 4096, 16384]);
sweep!(rhs_bare_fringe, [0, 16, 256, 4096]);
sweep!(shared_identity, [64, 256, 1024, 4096, 16384]);
sweep!(shared_unvalued_root, [64, 256, 1024, 4096, 16384]);
sweep!(shared_edit, [64, 256, 1024, 4096, 16384]);
