//! Catamorphisms over a trie holding every prefix of every English Wikipedia article title.
//!
//! The trie maps every non-empty prefix of every title to `()`, so every path in it holds a value.
//! Each operation is timed on two maps built from the same titles:
//!
//! - `built`: the map as built, in which no node is shared;
//! - `merkleized`: a second, separately built map after `merkleize`, in which identical subtries
//!   (common endings such as `_(disambiguation)`) are a single shared node. Every shared node hangs
//!   below a path that holds a value.
//!
//! The data is not in the repository (~110 MB download, ~400 MB unpacked):
//!
//! ```sh
//! curl -L https://dumps.wikimedia.org/enwiki/latest/enwiki-latest-all-titles-in-ns0.gz \
//!   | gunzip > benches/enwiki-latest-all-titles-in-ns0
//! ```
//!
//! The file is read from `BENCH_DATA_DIR` (default `benches/`). The full dump has ~19M titles and
//! gives ~173M values. Each map takes 12-17 s to build, outside the timings, and a full run peaks at
//! ~38 GB and takes ~10 minutes. `WIKI_TITLES=<n>` keeps an evenly spaced sample of about `n` titles for a quicker run.
//! Without the file, the bench prints these instructions and runs nothing.

use std::path::PathBuf;
use std::sync::OnceLock;
use std::time::Instant;

use divan::{Divan, Bencher};
use pathmap::PathMap;
use pathmap::morphisms::Catamorphism;
use pathmap::zipper::*;

const FILE: &str = "enwiki-latest-all-titles-in-ns0";
const MAPS: &[&str] = &["built", "merkleized"];

fn main() {
    let path = titles_path();
    if !path.exists() {
        eprintln!("wiki_prefixes: {} not found, skipping. Fetch it with\n  curl -L https://dumps.wikimedia.org/enwiki/latest/{FILE}.gz | gunzip > {}",
            path.display(), path.display());
        return;
    }
    Divan::from_args()
        .sample_count(5)
        .main();
}

fn titles_path() -> PathBuf {
    let dir = match std::env::var("BENCH_DATA_DIR") {
        Ok(val) => PathBuf::from(val),
        Err(_) => PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benches"),
    };
    dir.join(FILE)
}

/// The titles, sorted and deduplicated, read once per process
fn titles() -> &'static [&'static [u8]] {
    static TITLES: OnceLock<Vec<&'static [u8]>> = OnceLock::new();
    TITLES.get_or_init(|| {
        let buf: &'static [u8] = Box::leak(std::fs::read(titles_path()).unwrap().into_boxed_slice());
        let mut titles: Vec<&[u8]> = buf.split(|&b| b == b'\n')
            .enumerate()
            .filter(|&(i, line)| !line.is_empty() && !(i == 0 && line == b"page_title"))
            .map(|(_, line)| line)
            .collect();
        if let Some(n) = std::env::var("WIKI_TITLES").ok().and_then(|s| s.parse::<usize>().ok()) {
            let step = titles.len().div_ceil(n.max(1)).max(1);
            titles = titles.into_iter().step_by(step).collect();
        }
        titles.sort_unstable();
        titles.dedup();
        titles
    })
}

/// Every non-empty prefix of every title gets a value
fn build_prefix_closed() -> PathMap<()> {
    let mut map = PathMap::new();
    let mut wz = map.write_zipper();
    let mut prev: &[u8] = &[];
    for &title in titles() {
        let common = title.iter().zip(prev).take_while(|(a, b)| a == b).count();
        wz.ascend(prev.len() - common);
        for &byte in &title[common..] {
            wz.descend_to_byte(byte);
            wz.set_val(());
        }
        prev = title;
    }
    drop(wz);
    map
}

fn built() -> &'static PathMap<()> {
    static BUILT: OnceLock<PathMap<()>> = OnceLock::new();
    BUILT.get_or_init(|| {
        let t = Instant::now();
        let map = build_prefix_closed();
        eprintln!("wiki_prefixes: {} titles, {} values, built in {:.1} s",
            titles().len(), map.val_count(), t.elapsed().as_secs_f64());
        map
    })
}

fn merkleized() -> &'static PathMap<()> {
    static MERKLEIZED: OnceLock<PathMap<()>> = OnceLock::new();
    MERKLEIZED.get_or_init(|| {
        let mut map = build_prefix_closed();
        let t = Instant::now();
        let result = map.merkleize();
        eprintln!("wiki_prefixes: merkleize reused {} and cloned {} nodes in {:.1} s",
            result.reused, result.cloned, t.elapsed().as_secs_f64());
        map
    })
}

fn map(name: &str) -> &'static PathMap<()> {
    match name {
        "built" => built(),
        "merkleized" => merkleized(),
        _ => unreachable!(),
    }
}

#[divan::bench(args = MAPS)]
fn val_count(bencher: Bencher, name: &str) {
    let map = map(name);
    bencher.bench_local(|| map.val_count());
}

/// Counts the values: each step returns its children's counts plus one if it holds a value
#[divan::bench(args = MAPS)]
fn into_cata_cached(bencher: Bencher, name: &str) {
    let map = map(name);
    bencher.bench_local(|| {
        map.read_zipper().into_cata_cached(|_mask, children: &mut [usize], val| {
            children.iter().sum::<usize>() + val.is_some() as usize
        })
    });
}

/// Counts the values with the same algebra, called only where a path forks or holds a value
#[divan::bench(args = MAPS)]
fn into_cata_jumping_cached(bencher: Bencher, name: &str) {
    let map = map(name);
    bencher.bench_local(|| {
        map.read_zipper().into_cata_jumping_cached(|_mask, children: &mut [usize], val, _sub_path| {
            children.iter().sum::<usize>() + val.is_some() as usize
        })
    });
}

#[divan::bench(args = MAPS)]
fn hash(bencher: Bencher, name: &str) {
    let map = map(name);
    bencher.bench_local(|| map.read_zipper().hash());
}

/// `merkleize` in place on a freshly built map; building it and dropping it are not timed
#[divan::bench]
fn merkleize(bencher: Bencher) {
    bencher
        .with_inputs(build_prefix_closed)
        .bench_local_values(|mut map| {
            map.merkleize();
            map
        });
}
