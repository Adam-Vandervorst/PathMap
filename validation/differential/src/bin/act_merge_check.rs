//! Checks `ArenaCompactTree::merge_zipper_into_file` against its specification.
//!
//!     cargo run -p differential --bin act_merge_check
//!
//! ACT has no write zipper, but it can be *merged into*: given an ACT on disk
//! and a zipper over some other trie, `merge_zipper_into_file` writes a new ACT
//! holding the union.  The documented rule (see the method's doc example) is a
//! join in which the zipper's value wins on a collision -- in the model's terms,
//! `Trie.join` with the source preferred:
//!
//!     paths(merge(base, src)) = paths(base) ∪ paths(src)
//!     val(merge(base, src), p) = val(src, p)  when src has one, else val(base, p)
//!
//! Both halves are checked here, over randomly generated prefix-sharing tries of
//! the same shape the differential harness produces.

use pathmap::PathMap;
use pathmap::arena_compact::ArenaCompactTree;
use pathmap::zipper::*;
use std::collections::BTreeMap;

/// Every existing location, with its value if any.
fn locations(m: &PathMap<u64>) -> BTreeMap<Vec<u8>, Option<u64>> {
    let mut rz = m.read_zipper();
    let mut out = BTreeMap::new();
    out.insert(Vec::new(), rz.val().copied());
    while rz.to_next_step() {
        out.insert(rz.path().to_vec(), rz.val().copied());
    }
    out
}

fn locations_act<S: AsRef<[u8]>>(t: &ArenaCompactTree<S>) -> BTreeMap<Vec<u8>, Option<u64>> {
    let mut rz = t.read_zipper_u64();
    let mut out = BTreeMap::new();
    out.insert(Vec::new(), rz.val().copied());
    while rz.to_next_step() {
        out.insert(rz.path().to_vec(), rz.val().copied());
    }
    out
}

/// The specified result of merging `src` into `base`.
fn expected(
    base: &BTreeMap<Vec<u8>, Option<u64>>,
    src: &BTreeMap<Vec<u8>, Option<u64>>,
) -> BTreeMap<Vec<u8>, Option<u64>> {
    let mut out = base.clone();
    for (p, v) in src {
        let slot = out.entry(p.clone()).or_insert(None);
        if v.is_some() {
            *slot = *v;
        }
    }
    out
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        (self.next() >> 32) % n
    }
}

/// A small trie over a 4-byte alphabet, so paths share prefixes and branch.
fn gen_map(rng: &mut Rng) -> PathMap<u64> {
    let mut m = PathMap::<u64>::new();
    if rng.below(4) == 0 {
        let mut w = m.write_zipper();
        w.set_val(rng.below(256));
    }
    for _ in 0..rng.below(7) {
        let len = rng.below(5) as usize;
        let key: Vec<u8> = (0..len).map(|_| rng.below(4) as u8).collect();
        if key.is_empty() {
            let mut w = m.write_zipper();
            w.set_val(rng.below(256));
        } else {
            m.insert(&key, rng.below(256));
        }
    }
    // a dangling path now and then, since merge has to carry those too
    if rng.below(3) == 0 {
        let len = 1 + rng.below(3) as usize;
        let key: Vec<u8> = (0..len).map(|_| rng.below(4) as u8).collect();
        m.create_path(&key);
    }
    m
}

fn main() {
    let dir = std::env::temp_dir().join("pathmap-act-merge-check");
    std::fs::create_dir_all(&dir).unwrap();
    let mut rng = Rng(0x5eed);
    let (mut ok, mut bad) = (0usize, 0usize);

    for i in 0..300u32 {
        let base = gen_map(&mut rng);
        let src = gen_map(&mut rng);

        let file = dir.join(format!("base{i}.act"));
        let _ = std::fs::remove_file(&file);
        ArenaCompactTree::dump_from_zipper(base.read_zipper(), |&v| v, &file).unwrap();

        let merged =
            match ArenaCompactTree::merge_zipper_into_file(&file, src.read_zipper(), |&v| v) {
                Ok(t) => t,
                Err(e) => {
                    bad += 1;
                    println!("case {i}: merge failed: {e}");
                    continue;
                }
            };

        let got = locations_act(&merged);
        let want = expected(&locations(&base), &locations(&src));
        if got == want {
            ok += 1;
        } else {
            bad += 1;
            if bad <= 5 {
                println!("case {i}: MISMATCH");
                println!("   base    {:?}", locations(&base));
                println!("   src     {:?}", locations(&src));
                println!("   want    {want:?}");
                println!("   got     {got:?}");
                let only_want: Vec<_> = want.iter().filter(|(k, _)| !got.contains_key(*k)).collect();
                let only_got: Vec<_> = got.iter().filter(|(k, _)| !want.contains_key(*k)).collect();
                let differing: Vec<_> = want
                    .iter()
                    .filter(|(k, v)| got.get(*k).map(|g| g != *v).unwrap_or(false))
                    .collect();
                if !only_want.is_empty() { println!("   missing from result: {only_want:?}"); }
                if !only_got.is_empty()  { println!("   extra in result:     {only_got:?}"); }
                if !differing.is_empty() { println!("   wrong value:         {differing:?}"); }
            }
        }
        let _ = std::fs::remove_file(&file);
    }
    println!("merge_zipper_into_file: {ok} of {} cases match the specification", ok + bad);
}
