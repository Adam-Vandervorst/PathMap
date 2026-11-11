//! Measures how much merkleization shares between logically equal subtries that were built with
//! different physical layouts.  Run with `--features viz`.
use std::time::Instant;
use pathmap::PathMap;
use pathmap::morphisms::CatamorphismCached;
use pathmap::viz::{viz_maps, DrawConfig, VizMode};
use pathmap::zipper::*;

fn physical_nodes(map: &PathMap<()>) -> usize {
    let dc = DrawConfig { mode: VizMode::Mermaid, ascii_path: false, hide_value_paths: true, minimize_values: true, logical: false, color: false };
    let mut out = Vec::new();
    viz_maps(std::slice::from_ref(map), &dc, &mut out).unwrap();
    String::from_utf8(out).unwrap().lines().filter(|l| l.contains("shape: rect")).count()
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

fn cities() -> Vec<Vec<u8>> {
    let text = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/benches/cities5000.txt")).expect("benches/cities5000.txt");
    text.lines().filter_map(|line| line.split('\t').nth(1)).map(|name| name.as_bytes().to_vec()).collect()
}

/// Inserts `suffixes` under each of `copies` one-byte prefixes.  `shuffle` inserts every copy in
/// its own random order.  With `assemble_at > 0`, every odd copy is assembled from parts instead of
/// inserted path by path: the suffixes are grouped by their first `assemble_at` bytes and each group
/// is built as its own map and grafted under that stem, which leaves a node boundary at the stem
/// that direct insertion would not have.
fn build(suffixes: &[Vec<u8>], copies: usize, shuffle: bool, assemble_at: usize) -> PathMap<()> {
    let mut map = PathMap::<()>::new();
    let mut rng = XorShift(0x2545F4914F6CDD1D);
    for copy in 0..copies {
        let mut order: Vec<&Vec<u8>> = suffixes.iter().collect();
        if shuffle { rng.shuffle(&mut order); }
        let prefix = [copy as u8];
        let mut wz = map.write_zipper_at_path(&prefix);
        if assemble_at > 0 && copy % 2 == 1 {
            let mut groups = std::collections::BTreeMap::<&[u8], Vec<&[u8]>>::new();
            for suffix in order {
                let split = assemble_at.min(suffix.len());
                groups.entry(&suffix[..split]).or_default().push(&suffix[split..]);
            }
            for (stem, rests) in groups {
                let sub: PathMap<()> = rests.into_iter().map(|rest| (rest, ())).collect();
                wz.descend_to(stem);
                wz.graft_map(sub);
                wz.reset();
            }
        } else {
            for suffix in order { wz.descend_to(suffix); wz.set_val(()); wz.reset(); }
        }
    }
    map
}

fn report(name: &str, mut map: PathMap<()>, single_copy: &PathMap<()>) {
    let paths = map.val_count();
    let before = physical_nodes(&map);
    let hash = CatamorphismCached::hash(&map);
    let one_copy = physical_nodes(single_copy);
    let t = Instant::now();
    let result = map.merkleize();
    let elapsed = t.elapsed();
    let after = physical_nodes(&map);
    assert_eq!(map.val_count(), paths);
    println!("{name:<24} paths {paths:>7}  nodes before {before:>7}  after {after:>7}  one copy {one_copy:>6}  reused {:>6}  replaced {:>6}  cloned {:>6}  hash matches cata: {}  {:.2?}",
        result.reused, result.replaced, result.cloned, if result.hash == hash { "yes" } else { "NO" }, elapsed);
}

fn main() {
    let suffixes = random_suffixes(2000, 6, 0x9E3779B97F4A7C15);
    let copies = 16;
    let one = build(&suffixes, 1, false, 0);
    report("same order", build(&suffixes, copies, false, 0), &one);
    report("shuffled order", build(&suffixes, copies, true, 0), &one);
    report("half assembled at 3", build(&suffixes, copies, false, 3), &one);
    report("shuffled + assembled", build(&suffixes, copies, true, 3), &one);

    let names = cities();
    let one = build(&names, 1, false, 0);
    report("cities same order", build(&names, 8, false, 0), &one);
    report("cities shuffled", build(&names, 8, true, 0), &one);
    report("cities half assembled", build(&names, 8, false, 4), &one);
    report("cities shuffled+assembled", build(&names, 8, true, 4), &one);
}
