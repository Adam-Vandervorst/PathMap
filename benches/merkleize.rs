use divan::{Divan, Bencher};
use pathmap::PathMap;
use pathmap::zipper::*;

fn main() {
    Divan::from_args().sample_count(50).main();
}

struct XorShift(u64);
impl XorShift {
    fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 }
    fn shuffle<T>(&mut self, items: &mut [T]) {
        for i in (1..items.len()).rev() { let j = (self.next() % (i as u64 + 1)) as usize; items.swap(i, j); }
    }
}

fn random_suffixes(count: usize, len: usize, seed: u64) -> Vec<Vec<u8>> {
    let mut rng = XorShift(seed);
    (0..count).map(|_| (0..len).map(|_| (rng.next() >> 32) as u8).collect()).collect()
}

/// `copies` one-byte prefixes over the same suffixes, each copy inserted in the same or its own order
fn build(suffixes: &[Vec<u8>], copies: usize, shuffle: bool) -> PathMap<()> {
    let mut map = PathMap::<()>::new();
    let mut rng = XorShift(0x2545F4914F6CDD1D);
    for copy in 0..copies {
        let mut order: Vec<&Vec<u8>> = suffixes.iter().collect();
        if shuffle { rng.shuffle(&mut order); }
        let prefix = [copy as u8];
        let mut wz = map.write_zipper_at_path(&prefix);
        for suffix in order { wz.descend_to(suffix); wz.set_val(()); wz.reset(); }
    }
    map
}

fn bench_merkleize(bencher: Bencher, map: PathMap<()>) {
    bencher
        .with_inputs(|| map.clone())
        .bench_local_values(|mut map| map.merkleize());
}

#[divan::bench]
fn same_order_16x2000(bencher: Bencher) {
    bench_merkleize(bencher, build(&random_suffixes(2000, 6, 0x9E3779B97F4A7C15), 16, false));
}

#[divan::bench]
fn shuffled_order_16x2000(bencher: Bencher) {
    bench_merkleize(bencher, build(&random_suffixes(2000, 6, 0x9E3779B97F4A7C15), 16, true));
}

#[divan::bench]
fn no_sharing_random_50k(bencher: Bencher) {
    let mut map = PathMap::<()>::new();
    for key in random_suffixes(50_000, 8, 0x1234_5678_9ABC_DEF1) { map.insert(&key, ()); }
    bench_merkleize(bencher, map);
}

#[divan::bench]
fn already_merkleized_16x2000(bencher: Bencher) {
    let mut map = build(&random_suffixes(2000, 6, 0x9E3779B97F4A7C15), 16, true);
    map.merkleize();
    bench_merkleize(bencher, map);
}
