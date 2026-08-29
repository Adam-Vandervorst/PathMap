use divan::{Divan, Bencher, black_box};
use core::convert::Infallible;
use pathmap::morphisms::{Catamorphism, Summarization};
use pathmap::utils::ByteMask;
use pathmap::utils::ints::gen_int_range;
use pathmap::PathMap;

fn main() {
    // Run registered benchmarks.
    let divan = Divan::from_args()
        .sample_count(4000);

    divan.main();
}

fn build_map(count: u64) -> PathMap<()> {
    // Dense range of u64 keys encoded as paths; sized to keep benches fast and stable.
    gen_int_range::<(), 8, u64>(0, count, 1, ())
}

const MAP_COUNT: u64 = 20_000_000;

// A complete binary trie keeps every internal node as a two-entry LineListNode.
const BINARY_TREE_DEPTH: usize = 18;
const BINARY_TREE_LEAF_COUNT: usize = 1 << BINARY_TREE_DEPTH;

fn build_binary_tree_map() -> PathMap<()> {
    let mut map = PathMap::new();
    for leaf in 0..BINARY_TREE_LEAF_COUNT {
        let mut path = [0u8; BINARY_TREE_DEPTH];
        for (level, byte) in path.iter_mut().enumerate() {
            *byte = ((leaf >> (BINARY_TREE_DEPTH - level - 1)) & 1) as u8;
        }
        map.insert(path, ());
    }
    map
}

#[divan::bench()]
fn recursive_cata_jumping_val_count(bencher: Bencher) {
    let map = build_map(MAP_COUNT);
    let mut sink = 0usize;
    bencher.bench_local(|| {
        let rz = map.read_zipper();
        *black_box(&mut sink) = rz.recursive_cata::<_, _, Infallible, _, _, _, false>(
            |_| Ok(0usize),
            |_mask, w: usize, total| { *total += w; Ok(()) },
            |_mask, v, total, _| Ok((v.is_some() as usize) + total.unwrap_or(0)),
        ).unwrap();
    });
    assert_eq!(sink, MAP_COUNT as usize);
}

#[divan::bench()]
fn recursive_cata_binary_tree_leaf_count(bencher: Bencher) {
    let map = build_binary_tree_map();
    let mut sink = 0usize;
    bencher.bench_local(|| {
        let rz = map.read_zipper();
        *black_box(&mut sink) = rz
            .recursive_cata::<_, _, Infallible, _, _, _, false>(
                |_| Ok(0usize),
                |_mask, child_count: usize, total| {
                    *total += child_count;
                    Ok(())
                },
                |_mask, value, total, _| Ok((value.is_some() as usize) + total.unwrap_or(0)),
            )
            .unwrap();
    });
    assert_eq!(sink, BINARY_TREE_LEAF_COUNT);
}

#[divan::bench()]
fn cached_jumping_cata_val_count(bencher: Bencher) {
    let map = build_map(MAP_COUNT);
    let mut sink = 0usize;
    bencher.bench_local(|| {
        let rz = map.read_zipper();
        *black_box(&mut sink) = rz.into_cata_jumping_cached(|_mask: &ByteMask, children: &mut [usize], val, _sub_path| {
            let mut sum: usize = children.iter().sum();
            if val.is_some() {
                sum += 1;
            }
            sum
        });
    });
    assert_eq!(sink, MAP_COUNT as usize);
}

#[divan::bench()]
fn recursive_cata_jumping_total_len(bencher: Bencher) {
    let map = build_map(MAP_COUNT);
    let mut sink = (0usize, 0usize);
    bencher.bench_local(|| {
        let rz = map.read_zipper();
        *black_box(&mut sink) = rz.recursive_cata::<_, _, Infallible, _, _, _, true>(
            |_| Ok((0usize, 0usize)),
            |_mask: &ByteMask, w: (usize, usize), acc: &mut (usize, usize)| {
                acc.0 += w.0;
                acc.1 += w.1;
                Ok(())
            },
            |_mask: &ByteMask, val, acc, prefix| {
                let (count, total_len) = acc.unwrap_or((0, 0));
                let count = count + val.is_some() as usize;
                Ok((count, total_len + count * prefix.len()))
            },
        ).unwrap();
    });
    assert_eq!(sink.0, MAP_COUNT as usize);
}

#[divan::bench()]
fn cached_jumping_cata_total_len(bencher: Bencher) {
    let map = build_map(MAP_COUNT);
    let mut sink = (0usize, 0usize);
    bencher.bench_local(|| {
        let rz = map.read_zipper();
        *black_box(&mut sink) = rz.into_cata_jumping_cached(|mask: &ByteMask, children: &mut [(usize, usize)], val, sub_path| {
            let mut count = 0usize;
            let mut total_len = 0usize;
            let prefix_len = sub_path.len();
            if val.is_some() {
                count += 1;
                total_len += prefix_len;
            }
            for (_byte, child) in mask.iter().zip(children.iter_mut()) {
                count += child.0;
                total_len += child.1 + child.0 * prefix_len;
            }
            (count, total_len)
        });
    });
    assert_eq!(sink.0, MAP_COUNT as usize);
}
