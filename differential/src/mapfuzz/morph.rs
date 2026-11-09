//! Map fuzzer, ops 50–59: catamorphisms, anamorphisms.  Mirrors `MapFuzz/Morph.lean`,
//! which documents the operands, the closures and the visiting rules.
//!
//! Every closure returns a *faithful* string encoding of what it was shown
//! (path, jump length, value, child mask, the children's results, and for the
//! side-effecting flavours the call's sequence number), so the model can predict
//! the result exactly and any difference in what was visited, in which order or
//! with which arguments is a textual diff.

use pathmap::alloc::{global_alloc, GlobalAlloc};
use pathmap::morphisms::{Catamorphism, TrieBuilder};
use pathmap::utils::{BitMask, ByteMask};
use pathmap::zipper::*;

use super::*;

/// The trie a catamorphism folds: `m[i]` (a clone), optionally with a dangling
/// path `q` created in it, presented as the map itself (`kind 0`), a
/// `read_zipper_at_path(p)` (`kind 1`) or a `ReadZipperOwned` at `p` (`kind 2`).
/// The zippers are first moved to `f`, which the catamorphism must ignore.
struct CSrc {
    i: usize,
    kind: usize,
    p: Vec<u8>,
    f: Vec<u8>,
    q: Vec<u8>,
}

fn csrc(d: &mut Dec) -> Option<CSrc> {
    Some(CSrc { i: map_ix(d)?, kind: d.modn(3)?, p: d.path(4)?, f: d.path(4)?, q: d.path(6)? })
}

/// Something to run on any `Catamorphism` (the source types differ per `kind`).
trait CataRun {
    fn run<C: Catamorphism<u64>>(self, c: C) -> String;
}

fn dispatch<R: CataRun>(st: &MapState, c: &CSrc, r: R) -> String {
    let mut t = st.maps[c.i].clone();
    if !c.q.is_empty() {
        t.create_path(&c.q);
    }
    match c.kind {
        0 => r.run(t),
        1 => {
            let mut z = t.read_zipper_at_path(&c.p);
            z.descend_to(&c.f);
            r.run(z)
        }
        _ => {
            let mut z = t.into_read_zipper(&c.p);
            z.descend_to(&c.f);
            r.run(z)
        }
    }
}

fn hex_mask(m: &ByteMask) -> String {
    hex_path(&m.iter().collect::<Vec<u8>>())
}

fn show_jump(j: Option<usize>) -> String {
    match j {
        Some(j) => format!(":{j}"),
        None => String::new(),
    }
}

/// One side-effecting call: `(<idx>:<path>[:<jump>]:<val>:<mask><children>)`.
fn enc_side(i: usize, path: &[u8], jump: Option<usize>, v: Option<&u64>, m: &ByteMask, ch: &mut [String]) -> String {
    format!("({i}:{}{}:{}:{}{})", hex_path(path), show_jump(jump), show_val(v), hex_mask(m), ch.concat())
}

/// The error a side-effecting call returns when it is the `k`-th one.
fn err_side(i: usize, path: &[u8], jump: Option<usize>, v: Option<&u64>, m: &ByteMask, ch: &[String]) -> String {
    format!("E{i}:{}{}:{}:{}:{}", hex_path(path), show_jump(jump), show_val(v), hex_mask(m), ch.len())
}

/// Ops 50/51: `into_cata_side_effect` / `into_cata_jumping_side_effect`, or their
/// `_fallible` versions failing at call number `err_at`.
struct Side {
    jumping: bool,
    err_at: Option<usize>,
}

impl CataRun for Side {
    fn run<C: Catamorphism<u64>>(self, c: C) -> String {
        let mut idx = 0usize;
        let err_at = self.err_at;
        let r: Result<String, String> = match (self.jumping, err_at) {
            (false, None) => Ok(c.into_cata_side_effect(|m, ch: &mut [String], v, path| {
                let i = idx;
                idx += 1;
                enc_side(i, path, None, v, m, ch)
            })),
            (false, Some(k)) => c.into_cata_side_effect_fallible(|m, ch: &mut [String], v, path| {
                let i = idx;
                idx += 1;
                if i == k { Err(err_side(i, path, None, v, m, ch)) } else { Ok(enc_side(i, path, None, v, m, ch)) }
            }),
            (true, None) => Ok(c.into_cata_jumping_side_effect(|m, ch: &mut [String], j, v, path| {
                let i = idx;
                idx += 1;
                enc_side(i, path, Some(j), v, m, ch)
            })),
            (true, Some(k)) => c.into_cata_jumping_side_effect_fallible(|m, ch: &mut [String], j, v, path| {
                let i = idx;
                idx += 1;
                if i == k { Err(err_side(i, path, Some(j), v, m, ch)) } else { Ok(enc_side(i, path, Some(j), v, m, ch)) }
            }),
        };
        match r {
            Ok(w) => format!("{w} calls={idx}"),
            Err(e) => format!("Err:{e} calls={idx}"),
        }
    }
}

/// Ops 52/53: `into_cata_cached` / `into_cata_jumping_cached`, or their
/// `_fallible` versions with an order-independent failure predicate.
struct Cached {
    jumping: bool,
    pred: u8,
    v: u64,
}

impl Cached {
    /// `pred % 4`: 0 never (the infallible API), 1 the value is `v`, 2 the child
    /// count is `(pred >> 2) % 4`, 3 a location with one child and no value.
    fn fails(&self, m: &ByteMask, val: Option<&u64>) -> bool {
        match self.pred % 4 {
            1 => val == Some(&self.v),
            2 => m.count_bits() == ((self.pred >> 2) % 4) as usize,
            3 => m.count_bits() == 1 && val.is_none(),
            _ => false,
        }
    }
}

/// One cached call: `([<sub_path>:]<val>:<mask><children>)`.
fn enc_cached(sub: Option<&[u8]>, v: Option<&u64>, m: &ByteMask, ch: &mut [String]) -> String {
    let sub = match sub {
        Some(s) => format!("{}:", hex_path(s)),
        None => String::new(),
    };
    format!("({sub}{}:{}{})", show_val(v), hex_mask(m), ch.concat())
}

impl CataRun for Cached {
    fn run<C: Catamorphism<u64>>(self, c: C) -> String {
        let r: Result<String, String> = match (self.jumping, self.pred % 4 == 0) {
            (false, true) => Ok(c.into_cata_cached(|m, ch: &mut [String], v| enc_cached(None, v, m, ch))),
            (false, false) => c.into_cata_cached_fallible(|m, ch: &mut [String], v| {
                if self.fails(m, v) { Err("E".to_string()) } else { Ok(enc_cached(None, v, m, ch)) }
            }),
            (true, true) => Ok(c.into_cata_jumping_cached(|m, ch: &mut [String], v, sub| enc_cached(Some(sub), v, m, ch))),
            (true, false) => c.into_cata_jumping_cached_fallible(|m, ch: &mut [String], v, sub| {
                if self.fails(m, v) { Err("E".to_string()) } else { Ok(enc_cached(Some(sub), v, m, ch)) }
            }),
        };
        match r {
            Ok(w) => w,
            Err(e) => format!("Err:{e}"),
        }
    }
}

/// Op 54: `hash` (`with = false`) or `hash_with(|v| v % 3)`.
struct Hash {
    with: bool,
}

impl CataRun for Hash {
    fn run<C: Catamorphism<u64>>(self, c: C) -> String {
        if self.with { format!("{}", c.hash_with(|v| (*v % 3) as u128)) } else { format!("{}", c.hash()) }
    }
}

/// Skip token: `ana_replicate` would build a map larger than `REP_CAP` locations.
pub const SKIP_TOO_BIG: &str = "skip:too-big";
/// `repCap` in `MapFuzz/Morph.lean`.
pub const REP_CAP: usize = 256;

/// The bytes after `loc` along its single-child chain: extend while the location
/// has exactly one child and no value.
fn follow(src: &PathMap<u64>, loc: &[u8]) -> Vec<u8> {
    let mut z = src.read_zipper_at_path(loc);
    let mut chain = vec![];
    while z.child_count() == 1 && !z.is_val() {
        let b = z.child_mask().iter().next().unwrap();
        chain.push(b);
        z.descend_to_byte(b);
    }
    chain
}

/// Op 55's closure: rebuild `src` below `w`, transformed by `s` (see `copyAlg`).
fn copy_alg(src: &PathMap<u64>, s: u8, w: Vec<u8>, val: &mut Option<u64>, b: &mut TrieBuilder<u64, Vec<u8>, GlobalAlloc>, depth: usize) {
    if let Some(v) = src.get(&w) {
        if (v.wrapping_add(depth as u64)) % 4 != ((s >> 2) % 4) as u64 {
            *val = Some(v.wrapping_add((s >> 6) as u64));
        }
    }
    let rz = src.read_zipper_at_path(&w);
    let mask = rz.child_mask();
    let bytes: Vec<u8> = mask.iter().collect();
    let set_mask_mode = ((s >> 1) as usize + depth) % 3 == 0;
    if set_mask_mode {
        if !bytes.is_empty() {
            let ws: Vec<Vec<u8>> = bytes.iter().map(|&x| [&w[..], &[x]].concat()).collect();
            b.set_child_mask(mask.0, ws);
        }
        return;
    }
    for &x in &bytes {
        let wc = [&w[..], &[x]].concat();
        match (((s >> 4) % 4) as usize + x as usize + depth) % 4 {
            0 => b.push_byte(x, wc),
            1 => {
                let chain = follow(src, &wc);
                let sub = [&[x][..], &chain[..]].concat();
                let w2 = [&wc[..], &chain[..]].concat();
                b.push(&sub, w2)
            }
            2 => {
                let crz = src.read_zipper_at_path(&wc);
                if crz.child_count() > 0 { b.graft_at_byte(x, &crz) } else { b.push_byte(x, wc) }
            }
            _ => {}
        }
    }
}

pub fn step(op: usize, d: &mut Dec, st: &mut MapState) -> StepResult {
    Some(match op {
        50 | 51 => {
            let c = csrc(d)?;
            let e = d.u8()?;
            let err_at = if e % 2 == 0 { None } else { Some(((e >> 1) % 32) as usize) };
            let name = if op == 50 { "cata_side" } else { "cata_jump_side" };
            (name, dispatch(st, &c, Side { jumping: op == 51, err_at }))
        }
        52 | 53 => {
            let c = csrc(d)?;
            let pred = d.u8()?;
            let v = val(d)?;
            let name = if op == 52 { "cata_cached" } else { "cata_jump_cached" };
            (name, dispatch(st, &c, Cached { jumping: op == 53, pred, v }))
        }
        54 => {
            let a = csrc(d)?;
            let b = csrc(d)?;
            let ha = dispatch(st, &a, Hash { with: false });
            let hb = dispatch(st, &b, Hash { with: false });
            let wa = dispatch(st, &a, Hash { with: true });
            let wb = dispatch(st, &b, Hash { with: true });
            ("hash", format!("eq={} eqw={}", show_bool(ha == hb), show_bool(wa == wb)))
        }
        55 => {
            let (i, p, dst, s, use_in) = (map_ix(d)?, d.path(4)?, map_ix(d)?, d.u8()?, d.boolean()?);
            let src = st.maps[i].clone();
            let mut calls: Vec<String> = vec![];
            // Each call is reported with what the builder then holds:
            // `<path>#<len>.<child_mask>` (`TrieBuilder::len`, `child_mask`).
            let alg = |w: Vec<u8>, val: &mut Option<u64>, b: &mut TrieBuilder<u64, Vec<u8>, GlobalAlloc>, path: &[u8]| {
                copy_alg(&src, s, w, val, b, path.len());
                calls.push(format!("{}#{}.{}", hex_path(path), b.len(), hex_mask(&ByteMask(b.child_mask()))));
            };
            let m = if use_in { PathMap::new_from_ana_in(p, alg, global_alloc()) } else { PathMap::new_from_ana(p, alg) };
            st.maps[dst] = m;
            ("ana_copy", format!("calls={}", calls.join(",")))
        }
        56 => {
            let (i, p, dst, lv, mb) = (map_ix(d)?, d.path(4)?, map_ix(d)?, d.modn(3)?, d.u8()?);
            let src = st.maps[i].clone();
            let rz = src.read_zipper_at_path(&p);
            let has = rz.child_count() > 0;
            let mut bytes: Vec<u8> = (0..4u8).filter(|x| (mb >> x) & 1 == 1).collect();
            if bytes.is_empty() {
                bytes.push(0);
            }
            let set_vals = (mb >> 4) & 1 == 1;
            // Bounded so repeated replication cannot grow a map past what the
            // list-based model handles quickly (same rule as `repTooBig`).
            let mut node_locs = 1usize;
            let mut walk = src.read_zipper_at_path(&p);
            while walk.to_next_step() { node_locs += 1; }
            drop(walk);
            if node_locs * bytes.len().pow(lv as u32 + 1) > REP_CAP {
                return Some(("ana_replicate", SKIP_TOO_BIG.to_string()));
            }
            let mut calls = 0usize;
            let m = PathMap::new_from_ana(lv, |lvl: usize, val: &mut Option<u64>, b: &mut TrieBuilder<u64, usize, GlobalAlloc>, path: &[u8]| {
                calls += 1;
                if set_vals {
                    *val = Some(path.len() as u64);
                }
                if lvl == 0 {
                    if has {
                        for &x in &bytes {
                            b.graft_at_byte(x, &rz);
                        }
                    }
                } else {
                    for &x in &bytes {
                        b.push_byte(x, lvl - 1);
                    }
                }
            });
            drop(rz);
            st.maps[dst] = m;
            ("ana_replicate", format!("calls={calls}"))
        }
        _ => ("nop", "-".to_string()),
    })
}
