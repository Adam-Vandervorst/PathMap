
use rand::{Rng, SeedableRng, rngs::StdRng};
use divan::{Divan, Bencher, black_box};

use pathmap::PathMap;
use pathmap::zipper::*;

fn main() {
    // Run registered benchmarks.
    let divan = Divan::from_args()
        .sample_count(4000);

    divan.main();
}

const KEY_LENGTH: usize = 96;

/// Makes `count` pseudorandom keys of `KEY_LENGTH` bytes, where each key takes the form:
/// "0--1--1--0--1--0--0--0--1--0--0--1--1", etc. where the 0 or 1 is random
fn make_keys(count: usize, rand_seed: u64) -> Vec<Vec<u8>> {
    let mut rng = StdRng::seed_from_u64(rand_seed);
    (0..count).map(|_| {
        (0..KEY_LENGTH).map(|byte_idx| {
            if byte_idx % 3 == 0 {
                if rng.random_bool(0.5) { b'0' } else { b'1' }
            } else {
                b'-'
            }
        }).collect()
    }).collect()
}

#[divan::bench(sample_size = 1, args = [50, 100, 200, 400, 800, 1600])]
fn binary_insert(bencher: Bencher, n: u64) {

    let keys = make_keys(n as usize, 1);

    //Benchmark the insert operation
    let out = bencher.with_inputs(|| {
        PathMap::new()
    }).bench_local_values(|mut map| {
        for i in 0..n { black_box(&mut map).set_val_at(&keys[i as usize], i); }
        map //Return the map so we don't drop it inside the timing loop
    });
    divan::black_box_drop(out)
}

#[divan::bench(args = [250, 500, 1000, 2000, 4000, 8000])]
fn binary_get(bencher: Bencher, n: u64) {

    let keys = make_keys(n as usize, 1);

    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.set_val_at(&keys[i as usize], i); }

    //Benchmark the get operation
    bencher.bench_local(|| {
        for i in 0..n {
            assert_eq!(map.get_val_at(&keys[i as usize]), Some(&i));
        }
    });
}

#[divan::bench(args = [250, 500, 1000, 2000, 4000, 8000])]
fn binary_descend_until(bencher: Bencher, n: u64) {
    let keys = make_keys(n as usize, 1);

    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.set_val_at(&keys[i as usize], i); }

    let mut sink = 0usize;
    bencher.bench_local(|| {
        let mut zipper = map.read_zipper();
        let keys_len = keys.len().max(1);
        for i in 0..n {
            zipper.reset();
            let key = &keys[(i as usize) % keys_len];
            let start = (i as usize) % key.len().max(1);
            if start > 0 {
                zipper.descend_to(&key[..start]);
            }
            if zipper.descend_until() {
                sink += 1;
            }
        }
        black_box(sink);
    });
}

const DESCEND_UNTIL_MAX_BYTES: usize = 2;

#[divan::bench(args = [250, 500, 1000, 2000, 4000, 8000])]
fn binary_descend_until_max_bytes(bencher: Bencher, n: u64) {
    let keys = make_keys(n as usize, 1);

    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.set_val_at(&keys[i as usize], i); }

    let mut sink = 0usize;
    bencher.bench_local(|| {
        let mut zipper = map.read_zipper();
        let keys_len = keys.len().max(1);
        for i in 0..n {
            zipper.reset();
            let key = &keys[(i as usize) % keys_len];
            let start = (i as usize) % key.len().max(1);
            if start > 0 {
                zipper.descend_to(&key[..start]);
            }
            if zipper.descend_until_max_bytes(DESCEND_UNTIL_MAX_BYTES) {
                sink += 1;
            }
        }
        black_box(sink);
    });
}

#[divan::bench(args = [125, 250, 500, 1000, 2000, 4000])]
fn binary_val_count_bench(bencher: Bencher, n: u64) {

    let keys = make_keys(n as usize, 1);

    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.set_val_at(&keys[i as usize], i); }

    //Benchmark the time taken to count the number of values in the map
    let mut sink = 0;
    bencher.bench_local(|| {
        *black_box(&mut sink) = map.val_count()
    });
    assert_eq!(sink, n as usize);
}

#[divan::bench(args = [50, 100, 200, 400, 800, 1600])]
fn binary_drop_head(bencher: Bencher, n: u64) {

    let keys = make_keys(n as usize, 1);

    bencher.with_inputs(|| {
        let mut map: PathMap<u64> = PathMap::new();
        for i in 0..n { map.set_val_at(&keys[i as usize], i); }
        map
    }).bench_local_values(|mut map| {
        let mut wz = map.write_zipper();
        wz.join_k_path_into(5, true);
    });
}

#[divan::bench(args = [50, 100, 200, 400, 800, 1600])]
fn binary_meet(bencher: Bencher, n: u64) {
    let overlap = 0.5;
    let o = ((1. - overlap) * n as f64) as u64;

    let keys = make_keys((n+o) as usize, 1);

    let mut l: PathMap<u64> = PathMap::new();
    for i in 0..n { l.set_val_at(&keys[i as usize], i); }
    let mut r: PathMap<u64> = PathMap::new();
    for i in o..(n+o) { r.set_val_at(&keys[i as usize], i); }

    let mut intersection: PathMap<u64> = PathMap::new();
    bencher.bench_local(|| {
        *black_box(&mut intersection) = l.meet(black_box(&r));
    });
}

#[divan::bench(args = [50, 100, 200, 400, 800, 1600])]
fn binary_k_path_iter(bencher: Bencher, n: u64) {

    let keys = make_keys(n as usize, 1);
    let map: PathMap<usize> = keys.iter().enumerate().map(|(n, s)| (s, n)).collect();

    //Benchmark the zipper's iterator
    bencher.bench_local(|| {
        let mut zipper = map.read_zipper();
        let mut count = 1;

        //NOTE: 30 was found empirically and has no special meaning.  It's just a number that is deep enough
        // that there happens not to be any non-unique paths at that depth, given the RNG I tested.  If this
        // test fails, make that number smaller.
        zipper.descend_first_k_path(KEY_LENGTH-30);
        while zipper.to_next_k_path(KEY_LENGTH-30) {
            count += 1;
        }
        assert_eq!(count, n);
    });
}

#[divan::bench(args = [50, 100, 200, 400, 800, 1600])]
fn binary_zipper_iter(bencher: Bencher, n: u64) {

    let keys = make_keys(n as usize, 1);
    let map: PathMap<usize> = keys.iter().enumerate().map(|(n, s)| (s, n)).collect();

    //Benchmark the zipper's iterator
    bencher.bench_local(|| {
        let mut count = 0;
        let mut zipper = map.read_zipper();
        while zipper.to_next_val() {
            count += 1;
        }
        assert_eq!(count, n);
    });
}

#[divan::bench(sample_size = 1, args = [50, 100, 200, 400, 800, 1600])]
fn binary_join(bencher: Bencher, n: u64) {

    let overlap = 0.5;
    let o = ((1. - overlap) * n as f64) as u64;

    let keys = make_keys((n+o) as usize, 1);

    let mut vnl = PathMap::new();
    let mut vnr = PathMap::new();
    for i in 0..n { vnl.set_val_at(&keys[i as usize], i); }
    for i in o..(n+o) { vnr.set_val_at(&keys[i as usize], i); }

    //Benchmark the join operation
    let mut j: PathMap<u64> = PathMap::new();
    bencher.bench_local(|| {
        *black_box(&mut j) = vnl.join(black_box(&vnr));
    });
}
