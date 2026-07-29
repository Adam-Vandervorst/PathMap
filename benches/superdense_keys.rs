
use divan::{Divan, Bencher, black_box};
use pathmap::PathMap;
use pathmap::zipper::*;

fn main() {
    // Run registered benchmarks.
    let divan = Divan::from_args()
        .sample_count(5000);

    divan.main();
}

#[divan::bench(args = [1000, 2000, 4000, 8000, 16000, 32000])]
fn superdense_join(bencher: Bencher, n: u64) {
    let overlap = 0.5;
    let o = ((1. - overlap) * n as f64) as u64;

    let mut vnl = PathMap::new();
    let mut vnr = PathMap::new();
    for i in 0..n { vnl.set_val_at(prefix_key(&i), i); }
    // println!("{:?}", vnl.root);
    for i in 0..n { assert_eq!(vnl.get_val_at(prefix_key(&i)), Some(i).as_ref()); }
    for i in n..2*n { assert_eq!(vnl.get_val_at(prefix_key(&i)), None); }
    let mut c: Vec<u64> = Vec::with_capacity(n as usize);
    vnl.iter().for_each(|(k, v)| {
        assert!(*v < n);
        assert_eq!(k, prefix_key(&v));
        c.push(from_prefix_key(k.clone()));
    });
    c.sort();
    assert_eq!(c, (0..n).collect::<Vec<u64>>());
    for i in o..(n+o) { vnr.set_val_at(prefix_key(&i), i); }

    //Benchmark the join operation
    let mut j: PathMap<u64> = PathMap::new();
    bencher.bench_local(|| {
        *black_box(&mut j) = vnl.join(black_box(&vnr));
    });
}

#[divan::bench(args = [100, 200, 400, 800, 1600, 3200])]
fn superdense_insert(bencher: Bencher, n: u64) {

    //Benchmark the insert operation
    let out = bencher.with_inputs(|| {
        PathMap::new()
    }).bench_local_values(|mut map| {
        for i in 0..n { black_box(&mut map).set_val_at(prefix_key(&i), i); }
        map //Return the map so we don't drop it inside the timing loop
    });
    divan::black_box_drop(out)
}

#[divan::bench(sample_size = 1, args = [100, 200, 400, 800, 1600, 3200])]
fn superdense_drop_bench(bencher: Bencher, n: u64) {

    //Benchmark the time taken to drop the map
    bencher.with_inputs(|| {
        let mut map = PathMap::new();
        for i in 0..n { map.set_val_at(prefix_key(&i), i); }
        map
    }).bench_local_values(|map| {
        drop(map);
    });
}

#[divan::bench(args = [1000, 2000, 4000, 8000, 16000, 32000])]
fn superdense_get(bencher: Bencher, n: u64) {

    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.set_val_at(prefix_key(&i), i); }

    //Benchmark the get operation
    bencher.bench_local(|| {
        for i in 0..n {
            assert_eq!(map.get_val_at(prefix_key(&i)), Some(&i));
        }
    });
}

#[divan::bench(args = [1000, 2000, 4000, 8000, 16000, 32000])]
fn superdense_descend_until(bencher: Bencher, n: u64) {
    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.set_val_at(prefix_key(&i), i); }
    let keys: Vec<Vec<u8>> = (0..n).map(|i| prefix_key(&i).to_vec()).collect();

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
            if zipper.descend_until(&mut ()) {
                sink += 1;
            }
        }
        black_box(sink);
    });
}

const DESCEND_UNTIL_MAX_BYTES: usize = 2;

#[divan::bench(args = [1000, 2000, 4000, 8000, 16000, 32000])]
fn superdense_descend_until_max_bytes(bencher: Bencher, n: u64) {
    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.set_val_at(prefix_key(&i), i); }
    let keys: Vec<Vec<u8>> = (0..n).map(|i| prefix_key(&i).to_vec()).collect();

    let mut sink = 0usize;
    bencher.bench_local(|| {
        let mut zipper = map.read_zipper();
        let keys_len = keys.len().max(1);
        for i in 0..n {
            zipper.reset();
            let key = &keys[(i as usize) % keys_len];
            let start = (i as usize) % key.len().max(1);
            if start > 0 {
                zipper.descend_to_existing(&key[..start]);
            }
            if zipper.descend_until_max_bytes(DESCEND_UNTIL_MAX_BYTES, &mut ()) {
                sink += 1;
            }
        }
        black_box(sink);
    });
}

#[divan::bench(args = [1000, 2000, 4000, 8000, 16000, 32000])]
fn superdense_drop_head(bencher: Bencher, n: u64) {

    bencher.with_inputs(|| {
        let mut map = PathMap::new();
        for i in 0..n { map.set_val_at(prefix_key(&i), i); }
        map
    }).bench_local_values(|mut map| {
        let mut wz = map.write_zipper();
        wz.join_k_path_into(1, true);
    });
}

#[divan::bench(args = [1000, 2000, 4000, 8000, 16000, 32000])]
fn superdense_meet(bencher: Bencher, n: u64) {
    let overlap = 0.5;
    let o = ((1. - overlap) * n as f64) as u64;

    let mut l: PathMap<u64> = PathMap::new();
    for i in 0..n { l.set_val_at(prefix_key(&i), i); }
    let mut r: PathMap<u64> = PathMap::new();
    for i in o..(n+o) { r.set_val_at(prefix_key(&i), i); }

    let mut intersection: PathMap<u64> = PathMap::new();
    bencher.bench_local(|| {
        *black_box(&mut intersection) = l.meet(black_box(&r));
    });
}

/// This is the success case for dense meet's intersection-mask walk: both
/// nodes have many children, but only a small fraction of those children are
/// present in both nodes.
#[divan::bench(args = [1000, 2000, 4000, 8000, 16000, 32000])]
fn superdense_meet_low_overlap(bencher: Bencher, n: u64) {
    let overlap = n / 16;
    let offset = n - overlap;

    let mut l: PathMap<u64> = PathMap::new();
    for i in 0..n { l.set_val_at(prefix_key(&i), i); }
    let mut r: PathMap<u64> = PathMap::new();
    for i in offset..(offset + n) { r.set_val_at(prefix_key(&i), i); }

    let mut intersection: PathMap<u64> = PathMap::new();
    bencher.bench_local(|| {
        *black_box(&mut intersection) = l.meet(black_box(&r));
    });
    assert_eq!(intersection.val_count(), overlap as usize);
}

/// This tests the performance of the meet op when there are already some shared nodes between the maps
#[divan::bench(args = [1000, 2000, 4000, 8000, 16000, 32000])]
fn superdense_meet_after_join(bencher: Bencher, n: u64) {

    let mut l: PathMap<u64> = PathMap::new();
    for i in 0..(n/2) { l.set_val_at(prefix_key(&i), i); }
    let mut r: PathMap<u64> = PathMap::new();
    for i in (n/2)..n { r.set_val_at(prefix_key(&i), i); }

    let joined = l.join(&r);
    let mut intersection: PathMap<u64> = PathMap::new();
    bencher.bench_local(|| {
        *black_box(&mut intersection) = joined.meet(black_box(&l));
    });
}

/// This tests the performance of the meet op when there are already some shared nodes between the maps
#[divan::bench(args = [1000, 2000, 4000, 8000, 16000, 32000])]
fn superdense_subtract_after_join(bencher: Bencher, n: u64) {

    let mut l: PathMap<u64> = PathMap::new();
    for i in 0..(n/2) { l.set_val_at(prefix_key(&i), i); }
    let mut r: PathMap<u64> = PathMap::new();
    for i in (n/2)..n { r.set_val_at(prefix_key(&i), i); }

    let joined = l.join(&r);
    let mut remaining: PathMap<u64> = PathMap::new();
    bencher.bench_local(|| {
        *black_box(&mut remaining) = joined.subtract(black_box(&r));
    });
    assert_eq!(remaining.val_count(), l.val_count())
}

#[divan::bench(args = [100, 200, 400, 800, 1600, 3200])]
fn superdense_iter(bencher: Bencher, n: u64) {

    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.set_val_at(prefix_key(&i), i); }

    //Benchmark the iterator
    let mut sink = 0;
    bencher.bench_local(|| {
        map.iter().for_each(|(_key, val)| *black_box(&mut sink) = *val);
    });
}

#[cfg(feature = "old_cursor")]
#[divan::bench(args = [100, 200, 400, 800, 1600, 3200])]
fn superdense_cursor(bencher: Bencher, n: u64) {

    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.set_val_at(prefix_key(&i), i); }

    //Benchmark the cursor
    let mut sink = 0;
    bencher.bench_local(|| {
        let mut cursor = map.cursor();
        while let Some((_key, val)) = cursor.next() {
            *black_box(&mut sink) = *val
        }
    });
}

#[divan::bench(args = [500, 1000, 2000, 4000, 8000, 16000])]
fn superdense_k_path_iter(bencher: Bencher, n: u64) {

    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n {
        map.set_val_at(&i.to_be_bytes()[..][6..], i);
    }

    //Benchmark the zipper's iterator
    bencher.bench_local(|| {
        let mut zipper = map.read_zipper();
        let mut count = 1;

        zipper.descend_first_k_path(2, &mut ());
        while zipper.to_next_k_path(2, &mut ()) {
            count += 1;
        }
        assert_eq!(count, n);
    });
}

#[cfg(all(feature = "all_dense_nodes", feature = "old_cursor"))]
#[divan::bench(args = [100, 200, 400, 800, 1600, 3200])]
fn superdense_all_dense_cursor(bencher: Bencher, n: u64) {

    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.insert(prefix_key(&i), i); }

    //Benchmark the cursor
    let mut sink = 0;
    bencher.bench_local(|| {
        let mut cursor = map.all_dense_cursor();
        while let Some((_key, val)) = cursor.next() {
            *black_box(&mut sink) = *val
        }
    });
}

#[divan::bench(args = [100, 200, 400, 800, 1600, 3200])]
fn superdense_zipper_cursor(bencher: Bencher, n: u64) {

    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.set_val_at(prefix_key(&i), i); }

    //Benchmark using the the zipper as a cursor
    bencher.bench_local(|| {
        let mut count = 0;
        let mut zipper = map.read_zipper();
        while zipper.to_next_val(&mut ()) {
            count += 1;
        }
        assert_eq!(count, n);
    });
}

fn prefix_key(k: &u64) -> &[u8] {
    let bs = (8 - k.leading_zeros()/8) as u8;
    let kp: *const u64 = k;
    unsafe { std::slice::from_raw_parts(kp as *const _, (bs as usize).max(1)) }
}

fn from_prefix_key(k: Vec<u8>) -> u64 {
    let mut buf = [0u8; 8];
    unsafe { core::ptr::copy_nonoverlapping(k.as_ptr(), buf.as_mut_ptr(), k.len()); }
    let shift = 64usize.saturating_sub(k.len()*8);
    u64::from_le_bytes(buf) & (!0u64 >> shift)
}

#[divan::bench(sample_size = 1, args = [100, 200, 400, 800, 1600, 3200, 20_000])]
fn superdense_val_count_bench(bencher: Bencher, n: u64) {

    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.set_val_at(prefix_key(&i), i); }

    //Benchmark the time taken to count the number of values in the map
    let mut sink = 0;
    bencher.bench_local(|| {
        *black_box(&mut sink) = map.val_count()
    });
    assert_eq!(sink, n as usize);
}

#[cfg(feature="arena_compact")]
#[divan::bench(sample_size = 1, args = [100, 200, 400, 800, 1600, 3200, 20_000])]
fn superdense_val_count_bench_act(bencher: Bencher, n: u64) {
    use pathmap::{
        arena_compact::ArenaCompactTree,
        zipper::ZipperMoving,
    };
    let mut map: PathMap<u64> = PathMap::new();
    for i in 0..n { map.set_val_at(prefix_key(&i), i); }
    let act = ArenaCompactTree::from_zipper(map.read_zipper(), |&v| v);
    let zipper = act.read_zipper();
    //Benchmark the time taken to count the number of values in the map
    let mut sink = 0;
    bencher.bench_local(|| {
        *black_box(&mut sink) = zipper.val_count();
    });
    assert_eq!(sink, n as usize);
}
