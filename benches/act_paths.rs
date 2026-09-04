//! `PathMap` -> `.paths` -> `.act`.
//!
//! The pipeline of the `test_act_paths_round_trip` unit test, sized up:
//! serialize a `PathMap` to `.paths`, then replay the paths into an
//! [ACTOutputStream] to build an `.act` file without ever holding the trie in
//! memory. `*_map_to_act_cata` builds the same file through the catamorphism
//! instead, as a baseline for the streaming path; both write a `0` value per
//! path so the two measure the same output.
//!
//! Three axes:
//! - `size_*` holds the shape fixed and varies the number of paths, to see
//!   whether any stage is worse than linear.
//! - `shape_*` holds the number of paths fixed and varies the structure, from
//!   a complete 4-ary trie to uniform random 16-byte paths. `inflate_only`
//!   replays `.paths` without building anything, so the ACT build cost can be
//!   separated from the cost of decompressing its input.
//! - `round_trip` and `big_logic_paths_to_act` run the whole pipeline, the
//!   latter on real data.
//!
//! Correctness is checked once per benchmark, outside the timed closure:
//! `val_count` walks the whole trie, so it would swamp what is measured.
//! Setting `ACT_BENCH_TABLE=1` prints path/`.paths`/`.act` sizes per shape
//! before the run.

use divan::{Bencher, Divan, counter::ItemsCount};
use pathmap::PathMap;
use pathmap::arena_compact::{ACTOutputStream, ArenaCompactTree};
use pathmap::paths_serialization::{for_each_deserialized_path, serialize_paths};
use pathmap::morphisms::CatamorphismCachedIterative;
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::path::Path;

const SIZES: &[usize] = &[25_000, 50_000, 100_000, 200_000, 400_000, 800_000];
const SHAPES: &[Shape] = &[
  Shape::DenseNarrow, Shape::DenseWide, Shape::Clustered,
  Shape::SmallAlphabet, Shape::RandomLong,
];
const SHAPE_SIZE: usize = 200_000;
/// The shape the `size_*` sweep uses, unless the bench name says otherwise
const SIZE_SHAPE: Shape = Shape::RandomLong;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Shape {
  /// Complete 4-ary trie: every branch node is full and the trie is as deep
  /// as it can be for this path count
  DenseNarrow,
  /// 3-byte counters in lex order, i.e. fanout 256 at the top two levels
  DenseWide,
  /// Piecewise dense: random 8-byte prefixes, each carrying a dense block of
  /// 2-byte suffixes
  Clustered,
  /// Random over 5 letters, length 1..12 (the round-trip test's shape) —
  /// heavy prefix sharing, short paths. Only ~half the draws are distinct.
  SmallAlphabet,
  /// Uniform random 16-byte paths — almost no sharing below the first couple
  /// of bytes, so nearly every path ends in a line node
  RandomLong,
}

impl std::fmt::Display for Shape {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    f.pad(match self { // `pad`, not `write_str`: the size table aligns columns
      Shape::DenseNarrow => "dense_narrow",
      Shape::DenseWide => "dense_wide",
      Shape::Clustered => "clustered",
      Shape::SmallAlphabet => "small_alphabet",
      Shape::RandomLong => "random_long",
    })
  }
}

/// Generates `n` paths of the requested shape, lazily: at the top sizes
/// materializing them would cost more memory than the trie they build
fn paths(shape: Shape, n: usize) -> Box<dyn Iterator<Item = Vec<u8>>> {
  let mut rng = StdRng::seed_from_u64(0xAC7_0003);
  match shape {
    Shape::DenseNarrow => {
      let depth = (n as f64).log(4.0).ceil() as u32;
      Box::new((0..n).map(move |i| (0..depth).rev().map(|d| b"abcd"[(i >> (2 * d)) & 3]).collect()))
    }
    Shape::DenseWide =>
      Box::new((0..n).map(|i| vec![(i >> 16) as u8, (i >> 8) as u8, i as u8])),
    Shape::Clustered => {
      let cluster = 100;
      Box::new((0..n.div_ceil(cluster)).flat_map(move |_| {
        let prefix: [u8; 8] = rng.random();
        (0..cluster).map(move |j| {
          let mut p = prefix.to_vec();
          p.extend_from_slice(&[(j >> 8) as u8, j as u8]);
          p
        })
      }).take(n))
    }
    Shape::SmallAlphabet => Box::new((0..n).map(move |_| {
      let len = rng.random_range(1..12);
      (0..len).map(|_| b"abcde"[rng.random_range(0..5)]).collect()
    })),
    Shape::RandomLong => Box::new((0..n).map(move |_| rng.random::<[u8; 16]>().to_vec())),
  }
}

fn make_map(shape: Shape, n: usize) -> PathMap<u64> {
  let mut map = PathMap::new();
  for (idx, path) in paths(shape, n).enumerate() {
    map.set_val_at(&path[..], idx as u64);
  }
  map
}

fn to_paths(map: &PathMap<u64>) -> Vec<u8> {
  let mut data = Vec::new();
  serialize_paths(map.read_zipper(), &mut data).expect("serialization error");
  data
}

/// Replays `.paths` data into the `.act` file at `dst`, returning the number
/// of paths written. The tree is dropped and the file rewritten on the next
/// call, so only the write side is measured.
fn paths_to_act(data: &[u8], dst: &Path) -> usize {
  let mut out = ACTOutputStream::new(dst).expect("open error");
  let stats = for_each_deserialized_path(data, |_idx, p| out.push(p))
    .expect("deserialization error");
  out.finish().expect("act write error");
  stats.path_count
}

fn act_val_count(dst: &Path) -> usize {
  ArenaCompactTree::open_mmap(dst).unwrap().read_zipper_u64().val_count()
}

fn big_logic_paths() -> Vec<u8> {
  let data_dir = match std::env::var("BENCH_DATA_DIR") {
    Ok(val) => std::path::PathBuf::from(val),
    Err(_) => std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benches"),
  };
  std::fs::read(data_dir.join("big_logic.metta.paths")).unwrap()
}

// ---- shared bench bodies --------------------------------------------------

fn bench_map_to_paths(bencher: Bencher, map: PathMap<u64>) {
  let expected = map.val_count();
  let mut buf = Vec::with_capacity(1 << 22);
  bencher.counter(ItemsCount::new(expected)).bench_local(|| {
    buf.clear();
    serialize_paths(map.read_zipper(), &mut buf).expect("serialization error").path_count
  });
}

fn bench_paths_to_act(bencher: Bencher, map: PathMap<u64>) {
  let expected = map.val_count();
  let data = to_paths(&map);
  let dir = tempfile::tempdir().unwrap();
  let file = dir.path().join("bench.act");

  assert_eq!(paths_to_act(&data, &file), expected);
  assert_eq!(act_val_count(&file), expected);

  bencher.counter(ItemsCount::new(expected)).bench_local(|| paths_to_act(&data, &file));
}

fn bench_map_to_act_cata(bencher: Bencher, map: PathMap<u64>) {
  let expected = map.val_count();
  let dir = tempfile::tempdir().unwrap();
  let file = dir.path().join("bench_cata.act");

  ArenaCompactTree::dump_from_zipper(map.read_zipper(), |_| 0, &file).expect("act write error");
  assert_eq!(act_val_count(&file), expected);

  bencher.counter(ItemsCount::new(expected)).bench_local(|| {
    ArenaCompactTree::dump_from_zipper(map.read_zipper(), |_| 0, &file).expect("act write error")
  });
}

// ---- number of paths, shape held fixed ------------------------------------

#[divan::bench(args = SIZES)]
fn size_map_to_paths(bencher: Bencher, n: usize) {
  bench_map_to_paths(bencher, make_map(SIZE_SHAPE, n))
}

#[divan::bench(args = SIZES)]
fn size_paths_to_act(bencher: Bencher, n: usize) {
  bench_paths_to_act(bencher, make_map(SIZE_SHAPE, n))
}

#[divan::bench(args = SIZES)]
fn size_map_to_act_cata(bencher: Bencher, n: usize) {
  bench_map_to_act_cata(bencher, make_map(SIZE_SHAPE, n))
}

/// The dense counterpart of `size_paths_to_act`: whether the sweep stays
/// linear should not depend on the shape
#[divan::bench(args = SIZES)]
fn size_dense_paths_to_act(bencher: Bencher, n: usize) {
  bench_paths_to_act(bencher, make_map(Shape::DenseWide, n))
}

// ---- shape, number of paths held fixed ------------------------------------

#[divan::bench(args = SHAPES)]
fn shape_map_to_paths(bencher: Bencher, shape: Shape) {
  bench_map_to_paths(bencher, make_map(shape, SHAPE_SIZE))
}

#[divan::bench(args = SHAPES)]
fn shape_paths_to_act(bencher: Bencher, shape: Shape) {
  bench_paths_to_act(bencher, make_map(shape, SHAPE_SIZE))
}

#[divan::bench(args = SHAPES)]
fn shape_map_to_act_cata(bencher: Bencher, shape: Shape) {
  bench_map_to_act_cata(bencher, make_map(shape, SHAPE_SIZE))
}

#[divan::bench(args = SHAPES)]
fn shape_inflate_only(bencher: Bencher, shape: Shape) {
  let map = make_map(shape, SHAPE_SIZE);
  let data = to_paths(&map);
  bencher.counter(ItemsCount::new(map.val_count())).bench_local(|| {
    for_each_deserialized_path(&data[..], |_idx, p| { divan::black_box(p); Ok(()) })
      .expect("deserialization error").path_count
  });
}

// ---- the whole pipeline ---------------------------------------------------

#[divan::bench]
fn round_trip(bencher: Bencher) {
  let map = make_map(Shape::SmallAlphabet, SHAPE_SIZE);
  let expected = map.val_count();
  let dir = tempfile::tempdir().unwrap();
  let file = dir.path().join("round_trip.act");
  bencher.counter(ItemsCount::new(expected)).bench_local(|| {
    paths_to_act(&to_paths(&map), &file)
  });
  assert_eq!(act_val_count(&file), expected);
}

#[divan::bench]
fn big_logic_paths_to_act(bencher: Bencher) {
  let data = big_logic_paths();
  let dir = tempfile::tempdir().unwrap();
  let file = dir.path().join("big_logic.act");

  let expected = paths_to_act(&data, &file);
  assert_eq!(act_val_count(&file), expected);

  bencher.counter(ItemsCount::new(expected)).bench_local(|| paths_to_act(&data, &file));
}

/// Path bytes in, `.paths` bytes and `.act` bytes out, per shape — context for
/// the `shape_*` numbers. Skipped unless asked for: it costs a second of setup
/// that a filtered run should not pay.
fn print_size_table() {
  println!("{:<15} {:>8} {:>12} {:>12} {:>12} {:>10}",
    "shape", "paths", "path bytes", ".paths", ".act", "act/path");
  let dir = tempfile::tempdir().unwrap();
  for &shape in SHAPES {
    let mut map = PathMap::new();
    let mut path_bytes = 0;
    for (idx, path) in paths(shape, SHAPE_SIZE).enumerate() {
      path_bytes += path.len();
      map.set_val_at(&path[..], idx as u64);
    }
    let data = to_paths(&map);
    let file = dir.path().join(format!("{shape}.act"));
    let count = paths_to_act(&data, &file);
    let act_bytes = std::fs::metadata(&file).unwrap().len() as usize;
    println!("{:<15} {:>8} {:>12} {:>12} {:>12} {:>10.2}",
      shape, count, path_bytes, data.len(), act_bytes, act_bytes as f64 / count as f64);
  }
  println!();
}

fn main() {
  if std::env::var_os("ACT_BENCH_TABLE").is_some() {
    print_size_table();
  }
  Divan::from_args().sample_count(5).main();
}
