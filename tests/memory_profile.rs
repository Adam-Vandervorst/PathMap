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
