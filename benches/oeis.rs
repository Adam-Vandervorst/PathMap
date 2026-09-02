use std::io::Read;
use std::usize;
use pathmap::PathMap;
use pathmap::zipper::{Zipper, ZipperValues, ZipperMoving, ZipperPath, ZipperWriting, ZipperCreation};
use num::BigInt;
use divan::{Divan, Bencher, black_box};

const MAX_OFFSET: u8 = 10;

fn drop_symbol_head_byte<Z: ZipperWriting<usize> + Zipper + ZipperMoving + ZipperPath>(loc: &mut Z) {
  let mut it = loc.child_mask().iter();

  let p = loc.path().to_vec();
  while let Some(b) = it.next() {
    if b == 0 { continue }
    loc.descend_to_existing_byte(b);
    loc.join_k_path_into(b as usize, true);
    assert_eq!(loc.ascend(1), 1);
  }
  loc.reset();
  loc.descend_to(&p[..]);
  loc.join_k_path_into(1, true);
}

fn encode_seq<F : Iterator<Item=BigInt>>(iter: F) -> Vec<u8> {
  let mut v = vec![];
  for n in iter {
    let bs = n.to_signed_bytes_be();
    let bsl = bs.len();
    v.push(bsl as u8);
    v.extend(bs);
  }
  v
}

#[allow(unused)]
fn decode_seq(s: &[u8]) -> Vec<BigInt> {
  let mut v = vec![];
  let mut i = 0;
  while i < s.len() {
    let j = s[i] as usize;
    i += 1;
    v.push(BigInt::from_signed_bytes_be(&s[i..i + j]));
    i += j;
  }
  v
}

fn load_sequences() -> Vec<Vec<u8>> {
  let data_dir = match std::env::var("BENCH_DATA_DIR") {
      Ok(val) => std::path::PathBuf::from(val),
      Err(_) => std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benches"),
  };
  let file_path = data_dir.join("oeis_stripped.txt");
  let mut file = std::fs::File::open(file_path)
    .expect("Should have been able to read the file");
  let mut s = String::new();
  file.read_to_string(&mut s).unwrap();
  let mut sequences = vec![vec![]];
  let mut i = 0;
  for l in s.lines() {
    if l.starts_with("#") { continue }
    let mut cs = l.split(",").map(|c| {
      let mut cs = c.to_string();
      cs.retain(|c| !c.is_whitespace());
      cs
    });
    let first = cs.next().unwrap();
    let a_number = first.strip_prefix("A").expect("First not A").parse::<usize>().expect("A not followed by a number");
    let numbers = cs.filter(|n| !n.is_empty()).map(|n| n.parse::<BigInt>().expect(format!("not a number {}", n).as_str()));
    let seq = encode_seq(numbers);
    if a_number > sequences.len() { sequences.resize(a_number + 1, vec![]) }
    sequences.insert(a_number, seq);
    i += 1;
  }
  assert_eq!(i, 375842);
  sequences
}

fn build_map(sequences: &Vec<Vec<u8>>) -> PathMap<usize> {
  let mut m = PathMap::new();
  let mut buildz = m.write_zipper_at_path(&[0]);
  for (i, s) in sequences.iter().enumerate() {
    if s.len() == 0 { continue }
    buildz.descend_to(&s[..]);
    match buildz.val() {
      None => { buildz.set_val(i); }
      Some(_v) => { /* keep the smallest integer sequence */ }
    }
    buildz.ascend(s.len());
  }
  drop(buildz);
  black_box(m)
}

fn drophead(m: &mut PathMap<usize>) {
  const MAX_OFFSET: u8 = 10;
  let map_head = m.zipper_head();
  for i in 1..(MAX_OFFSET + 1) {
    let k = &[i];
    let mut z1 = unsafe{ map_head.write_zipper_at_exclusive_path_unchecked(k) };

    z1.graft(&unsafe { map_head.read_zipper_at_path_unchecked(&[i - 1]) });
    drop_symbol_head_byte(&mut z1);
  }
  drop(map_head);
}

fn count_contents(m: &PathMap<usize>) {
  for i in 0..(MAX_OFFSET + 1) {
    black_box(m.read_zipper_at_path(&[i]).val_count());
  }
}

fn query(m: &PathMap<usize>) {
  const QSEQ: [u64; 6] = [1, 2, 3, 5, 8, 13];
  let mut qseq = encode_seq(QSEQ.into_iter().map(BigInt::from));
  qseq.insert(0, 0);
  let mut q = PathMap::new();
  for i in 0..(MAX_OFFSET + 1) {
    qseq[0] = i;
    q.set_val_at(&qseq[..], 0usize);
  }

  let qresult = m.restrict(&q);
  black_box(qresult.val_count());
  black_box(qresult);
}

#[divan::bench(args = ["build_map", "drophead", "query"])]
fn run(bencher: Bencher, stage: &str) {
  let sequences = load_sequences();
  if stage == "build_map" { return bencher.bench_local(|| build_map(&sequences)) }
  let mut m = build_map(&sequences);
  if stage == "drophead" { return bencher.bench_local(|| drophead(&mut m)) }
  drophead(&mut m);
  if stage == "count_contents" { return bencher.bench_local(|| count_contents(&m)) }
  count_contents(&m);
  if stage == "query" { return bencher.bench_local(|| query(&m)) }
  unreachable!()
}

fn main() {
  // Run registered benchmarks.
  let divan = Divan::from_args()
    .sample_count(3);

  divan.main();
}
/*
RESULTS ON BadBad with sample_count(30); (I think)

normal
oeis             fastest       │ slowest       │ median        │ mean          │ samples │ iters
╰─ run                         │               │               │               │         │
   ├─ build_map  299 ms        │ 357 ms        │ 347.9 ms      │ 334.6 ms      │ 30      │ 30
   ├─ drophead   1.357 s       │ 2.524 s       │ 2.108 s       │ 1.997 s       │ 30      │ 30
   ╰─ query      123.2 µs      │ 269.9 µs      │ 126 µs        │ 173 µs        │ 30      │ 30

racy cow (commit 982a8fd)
oeis             fastest       │ slowest       │ median        │ mean          │ samples │ iters
╰─ run                         │               │               │               │         │
   ├─ build_map  168.6 ms      │ 219.4 ms      │ 179.2 ms      │ 182.4 ms      │ 30      │ 30
   ├─ drophead   1.31 s        │ 1.448 s       │ 1.335 s       │ 1.349 s       │ 30      │ 30
   ╰─ query      91.25 µs      │ 204.6 µs      │ 93.3 µs       │ 97.85 µs      │ 30      │ 30
*/

/*
RESULTS ON M4 MacBook Air with sample_count(30);
I have noticed quite a lot of sensitivity to `sample_count` with more samples hurting drop_head
time.  This is probably due to `drop_head` iterations causing useful cache contents from
`build_map` to be evicted.

normal
oeis             fastest       │ slowest       │ median        │ mean          │ samples │ iters
╰─ run                         │               │               │               │         │
   ├─ build_map  184.2 ms      │ 217.4 ms      │ 188.3 ms      │ 190.6 ms      │ 30      │ 30
   ├─ drophead   1.272 s       │ 2.233 s       │ 1.789 s       │ 1.762 s       │ 30      │ 30
   ╰─ query      59.41 µs      │ 140.7 µs      │ 63.7 µs       │ 66.83 µs      │ 30      │ 30

*/