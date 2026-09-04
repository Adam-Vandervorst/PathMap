//! Checks the properties structural sharing must preserve.
//!
//!     cargo run -p differential --bin sharing_check
//!
//! The Lean model has no notion of nodes, so sharing is invisible to it: a
//! `Trie` is a flat map from paths to entries, and grafting the same subtrie
//! into two places yields two independent copies *by construction*.  That is
//! deliberate -- sharing is an implementation strategy, not part of the meaning
//! -- and it is exactly what makes the model able to detect sharing bugs rather
//! than what hides them.  If a mutation through one reference leaked to another
//! path, the model would say the two are independent and the differential would
//! flag it.
//!
//! Two properties are not reachable through the differential harness, though,
//! so they are checked directly here:
//!
//!   1. **Copy-on-write.**  Graft one source into several places, mutate one,
//!      and the others must be untouched.  The harness can stumble into this by
//!      chance; this does it on purpose.
//!   2. **`merkleize()` preserves meaning.**  It exists to *increase* sharing,
//!      replacing identical subtries with references to one copy, so it is the
//!      one operation that deliberately changes the thing the model cannot see.
//!      The observable trie must come through unchanged, and the hash it
//!      reports must be a function of content -- equal content, equal hash,
//!      however the trie was built.

use pathmap::PathMap;
use pathmap::zipper::*;
use std::collections::BTreeMap;

fn contents(m: &PathMap<u64>) -> BTreeMap<Vec<u8>, Option<u64>> {
    let mut rz = m.read_zipper();
    let mut out = BTreeMap::new();
    out.insert(Vec::new(), rz.val().copied());
    while rz.to_next_step() {
        out.insert(rz.path().to_vec(), rz.val().copied());
    }
    out
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
    fn below(&mut self, n: u64) -> u64 { (self.next() >> 32) % n }
}

fn gen_map(rng: &mut Rng) -> PathMap<u64> {
    let mut m = PathMap::<u64>::new();
    for _ in 0..rng.below(8) {
        let len = 1 + rng.below(5) as usize;
        let key: Vec<u8> = (0..len).map(|_| rng.below(4) as u8).collect();
        m.insert(&key, rng.below(256));
    }
    if rng.below(3) == 0 {
        let len = 1 + rng.below(3) as usize;
        let key: Vec<u8> = (0..len).map(|_| rng.below(4) as u8).collect();
        m.create_path(&key);
    }
    m
}

/// Graft `src` under each of `spots`, producing deliberate sharing.
fn fan_out(src: &PathMap<u64>, spots: &[&[u8]]) -> PathMap<u64> {
    let mut m = PathMap::<u64>::new();
    for spot in spots {
        let mut wz = m.write_zipper_at_path(spot);
        wz.graft(&src.read_zipper());
    }
    m
}

/// Run `f`, turning a panic into an `Err` carrying its message, so one bad case
/// reports instead of ending the run.
fn guard<T>(f: impl FnOnce() -> T) -> Result<T, String> {
    use std::sync::{Arc, Mutex};
    let msg = Arc::new(Mutex::new(String::new()));
    let sink = msg.clone();
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        *sink.lock().unwrap() = info.to_string().lines().take(2).collect::<Vec<_>>().join(" | ");
    }));
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(f));
    std::panic::set_hook(prev);
    r.map_err(|_| msg.lock().unwrap().clone())
}

fn main() {
    let mut rng = Rng(0xC0FFEE);
    let spots: [&[u8]; 3] = [&[0], &[1], &[2, 2]];
    let mut cow = (0usize, 0usize, 0usize);   // ok, violated, panicked
    let mut mk = (0usize, 0usize, 0usize);
    let mut hash = (0usize, 0usize, 0usize);
    let mut total_reused = 0usize;
    let mut panics: std::collections::BTreeMap<String, usize> = Default::default();
    // Print the trie behind the first panic of each kind, so a failure is
    // reproducible rather than just counted.
    let mut shown: std::collections::BTreeSet<String> = Default::default();
    let note = |panics: &mut std::collections::BTreeMap<String, usize>,
                    shown: &mut std::collections::BTreeSet<String>,
                    phase: &str, e: String, ctx: &BTreeMap<Vec<u8>, Option<u64>>| {
        let key = format!("{phase}: {e}");
        if shown.insert(key.clone()) {
            println!("first {phase} panic ({e})");
            println!("   on: {ctx:?}");
        }
        *panics.entry(key).or_default() += 1;
    };

    for _case in 0..300u32 {
        let src = gen_map(&mut rng);
        if src.val_count() == 0 { continue }

        // --- 1. copy-on-write ---------------------------------------------
        // Graft one source into three places, then write under the first.  The
        // other two must be untouched: the model calls them independent copies.
        match guard(|| {
            let mut m = fan_out(&src, &spots);
            let before: Vec<_> = spots[1..].iter()
                .map(|s| contents(&m.read_zipper_at_path(s).make_map())).collect();
            {
                let mut wz = m.write_zipper_at_path(spots[0]);
                wz.descend_to(&[3u8, 3]);
                wz.set_val(999);
            }
            let after: Vec<_> = spots[1..].iter()
                .map(|s| contents(&m.read_zipper_at_path(s).make_map())).collect();
            before == after
        }) {
            Ok(true) => cow.0 += 1,
            Ok(false) => cow.1 += 1,
            Err(e) => { cow.2 += 1; note(&mut panics, &mut shown, "copy-on-write", e, &contents(&src)) }
        }

        // --- 2. merkleize preserves the observable trie --------------------
        let merk = guard(|| {
            let mut m = fan_out(&src, &spots);
            let want = contents(&m);
            let res = m.merkleize();
            (want.clone(), contents(&m), res.hash, res.reused)
        });
        let want_hash = match merk {
            Ok((want, got, h, reused)) => {
                total_reused += reused;
                if want == got { mk.0 += 1 } else { mk.1 += 1 }
                Some((want, h))
            }
            Err(e) => { mk.2 += 1; note(&mut panics, &mut shown, "merkleize", e, &contents(&src)); None }
        };

        // --- 3. the hash is a function of content --------------------------
        // The same content built by inserting key by key rather than grafting,
        // so the node structure going in is different.
        if let Some((want, h1)) = want_hash {
            match guard(|| {
                let mut m = PathMap::<u64>::new();
                for (k, v) in want.iter() {
                    match v {
                        Some(v) => { m.insert(k, *v); }
                        None => if !k.is_empty() { m.create_path(k); },
                    }
                }
                (contents(&m) == want, m.merkleize().hash)
            }) {
                Ok((same_content, h2)) if same_content => {
                    if h1 == h2 { hash.0 += 1 } else { hash.1 += 1 }
                }
                Ok(_) => {}
                Err(e) => { hash.2 += 1; note(&mut panics, &mut shown, "rebuild+hash", e, &want) }
            }
        }
    }

    // A panic is not a disagreement -- the property never got to be tested --
    // so the three outcomes are counted separately.
    println!("copy-on-write:        {} preserved, {} violated, {} panicked", cow.0, cow.1, cow.2);
    println!("merkleize preserves:  {} preserved, {} violated, {} panicked  ({total_reused} node refs reused)",
             mk.0, mk.1, mk.2);
    println!("hash follows content: {} agreed,   {} differed, {} panicked", hash.0, hash.1, hash.2);
    if !panics.is_empty() {
        println!("\npanics:");
        for (k, n) in &panics { println!("  x{n:<4} {k}"); }
    }
}
