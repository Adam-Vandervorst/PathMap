#![cfg(all(feature = "counters", feature = "serialization"))]

use std::time::Instant;
use pathmap::PathMap;
use pathmap::counters::memory_profile;
use pathmap::zipper::{ZipperMoving, ZipperIteration};

fn xorshift_keys(seed: u64, n: u32) -> Vec<[u8; 8]> {
    let mut x = seed;
    (0..n).map(|_| { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x.to_be_bytes() }).collect()
}
fn timeit(reps: usize, mut f: impl FnMut() -> f64) -> f64 {
    let mut b = f64::MAX; for _ in 0..reps { let t = f(); if t < b { b = t } } b
}
fn survey(label: &str, paths: &[Vec<u8>]) {
    let build_ms = timeit(3, || {
        let t = Instant::now();
        let mut m: PathMap<()> = PathMap::new();
        for p in paths { m.set_val_at(&p[..], ()); }
        let e = t.elapsed().as_secs_f64()*1e3; drop(m); e
    });
    let mut m: PathMap<()> = PathMap::new();
    for p in paths { m.set_val_at(&p[..], ()); }
    let iter_ms = timeit(3, || {
        let t = Instant::now();
        let mut z = m.read_zipper(); let mut n = 0u64;
        while z.to_next_val() { n += 1 }
        let e = t.elapsed().as_secs_f64()*1e3; assert!(n > 0); e
    });
    let get_ms = timeit(3, || {
        let t = Instant::now();
        let mut hits = 0u64;
        for p in paths { if m.get_val_at(&p[..]).is_some() { hits += 1 } }
        let e = t.elapsed().as_secs_f64()*1e3; assert!(hits > 0); e
    });
    let prof = memory_profile(&m);
    prof.report(label, m.val_count());
    println!("SWEEP\t{}\tK={}\tnodesz={}\tbytes={}\tlist_nodes={}\tdense_nodes={}\tbuild={:.1}\titer={:.1}\tget={:.1}",
        label, pathmap::counters::LIST_NODE_KEY_BYTES, pathmap::counters::LIST_NODE_SIZE,
        prof.total_bytes(), prof.list_nodes, prof.dense_nodes, build_ms, iter_ms, get_ms);
}

/// Dangling paths: paths that exist but carry no value. `remove_val(prune=false)` is how they are
/// made, and a `LineListNode` records one by pointing the slot at the empty-node sentinel.
#[test]
fn dangling_path_survey() {
    use pathmap::zipper::ZipperWriting;
    let words: Vec<Vec<u8>> = std::fs::read_to_string("benches/shakespeare.txt").unwrap()
        .split_ascii_whitespace().map(|w| w.as_bytes().to_vec()).collect::<std::collections::BTreeSet<_>>()
        .into_iter().collect();

    let mut m: PathMap<()> = PathMap::new();
    for w in &words { m.set_val_at(&w[..], ()); }
    let before = memory_profile(&m);
    before.report("shakespeare, no dangling paths", m.val_count());

    // strip every other value without pruning -- the maximal dangling-path case
    for (i, w) in words.iter().enumerate() {
        if i % 2 == 0 {
            let mut wz = m.write_zipper_at_path(&w[..]);
            wz.remove_val(false);
        }
    }
    let after = memory_profile(&m);
    after.report("shakespeare, half the values removed with prune=false", m.val_count());
    println!("DANGLING  bytes {} -> {}   empty nodes {} -> {}   sentinel slots {} -> {}",
        before.total_bytes(), after.total_bytes(),
        before.empty_nodes, after.empty_nodes, before.dangling_slots, after.dangling_slots);

    //A dangling path costs nothing over the value it replaced.  The empty-node sentinel is a bogus
    //address rather than an allocation, and the payload word it sits in is part of a fixed-size
    //`LineListNode` whether it is used or not -- so turning 14k values into dangling paths moves
    //the byte count not at all.  A `DenseByteNode` does not use the sentinel in the first place: it
    //represents a dangling path as a CoFree holding neither a child nor a value.
    assert!(after.dangling_slots > 10_000, "the fixture should have produced plenty of dangling paths");
    assert_eq!(after.total_bytes(), before.total_bytes(),
        "dangling paths must cost nothing over the values they replaced");
    assert_eq!(after.empty_nodes, 0, "the sentinel must never become an allocated node");
    assert_eq!(before.empty_nodes, 0);
}

#[test]
fn memory_profile_survey() {
    // MORK-representative
    let mut m: PathMap<()> = PathMap::new();
    let f = std::fs::File::open("benches/big_logic.metta.paths").unwrap();
    pathmap::paths_serialization::deserialize_paths(m.write_zipper(), f, ()).unwrap();
    let mork: Vec<Vec<u8>> = { let mut v = vec![]; let mut z = m.read_zipper();
        while z.to_next_val() { v.push(z.path().to_vec()) } v };
    survey("mork_big_logic", &mork);

    let rnd: Vec<Vec<u8>> = xorshift_keys(0x243F6A8885A308D3, 1_000_000).iter().map(|k| k.to_vec()).collect();
    survey("random_8byte", &rnd);

    let text = std::fs::read_to_string("benches/shakespeare.txt").unwrap();
    let words: Vec<Vec<u8>> = { let mut v: Vec<Vec<u8>> = text.split_ascii_whitespace().map(|w| w.as_bytes().to_vec()).collect();
        v.sort(); v.dedup(); v };
    survey("shakespeare", &words);
}
