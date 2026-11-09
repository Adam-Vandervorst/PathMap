//! Map fuzzer, ops 50–59: catamorphisms, anamorphisms.  Mirrors `MapFuzz/Morph.lean`,
//! which documents the operands, the closures and the visiting rules.  Ops 57/58
//! serialize a trie into a prefix tree with a catamorphism and deserialize it back
//! with an anamorphism; `lean/PathMapModel/PrefixTree.lean` proves the round trip.
//!
//! Every closure returns a *faithful* string encoding of what it was shown
//! (path, jump length, value, child mask, the children's results, and for the
//! side-effecting flavours the call's sequence number), so the model can predict
//! the result exactly and any difference in what was visited, in which order or
//! with which arguments is a textual diff.

use pathmap::alloc::{global_alloc, GlobalAlloc};
#[allow(deprecated)]
use pathmap::morphisms::{Catamorphism, SplitCata, SplitCataJumping, TrieBuilder};
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

/// One node of a rendered prefix tree: `(<val>,<edge hex><child>,...)`
/// (`PTree.render` in `PrefixTree.lean`).
fn tree_node<I: Iterator<Item = Vec<u8>>>(v: Option<&u64>, edges: I, ch: &[String]) -> String {
    let mut out = format!("({}", show_val(v));
    for (e, c) in edges.zip(ch.iter()) {
        out.push(',');
        out.push_str(&hex_path(&e));
        out.push_str(c);
    }
    out.push(')');
    out
}

/// A jumping fold's node: the bytes it jumped over, and its rendering with
/// each child's edge = mask byte ++ the child's jumped bytes.
fn line_node(sub: &[u8], v: Option<&u64>, m: &ByteMask, ch: &[(Vec<u8>, String)]) -> (Vec<u8>, String) {
    let edges = m.iter().zip(ch.iter()).map(|(b, c)| [&[b][..], &c.0[..]].concat());
    let strs: Vec<String> = ch.iter().map(|c| c.1.clone()).collect();
    (sub.to_vec(), tree_node(v, edges, &strs))
}

/// `PathMap.rootLine`: a non-empty jump at the root is a leading edge.
fn root_line(r: (Vec<u8>, String)) -> String {
    if r.0.is_empty() { r.1 } else { format!("(-,{}{})", hex_path(&r.0), r.1) }
}

/// Op 57: a byte tree from a stepping fold.  `fl % 4`: side-effect,
/// side-effect fallible (never failing), cached, cached fallible (never failing).
struct TreeBytes {
    fl: u8,
}

impl CataRun for TreeBytes {
    fn run<C: Catamorphism<u64>>(self, c: C) -> String {
        let bytes = |m: &ByteMask| m.iter().map(|b| vec![b]).collect::<Vec<_>>().into_iter();
        match self.fl % 4 {
            0 => c.into_cata_side_effect(|m, ch: &mut [String], v, _path| tree_node(v, bytes(m), ch)),
            1 => c
                .into_cata_side_effect_fallible(|m, ch: &mut [String], v, _path| Ok::<_, ()>(tree_node(v, bytes(m), ch)))
                .unwrap_or_else(|_| "Err".to_string()),
            2 => c.into_cata_cached(|m, ch: &mut [String], v| tree_node(v, bytes(m), ch)),
            _ => c
                .into_cata_cached_fallible(|m, ch: &mut [String], v| Ok::<_, ()>(tree_node(v, bytes(m), ch)))
                .unwrap_or_else(|_| "Err".to_string()),
        }
    }
}

/// Op 58: a line tree from a jumping fold, flavours as in [TreeBytes].  The
/// side-effecting closure reads its jumped bytes off the end of its path.
struct TreeLines {
    fl: u8,
}

impl CataRun for TreeLines {
    fn run<C: Catamorphism<u64>>(self, c: C) -> String {
        let r = match self.fl % 4 {
            0 => c.into_cata_jumping_side_effect(|m, ch: &mut [(Vec<u8>, String)], j, v, path| {
                line_node(&path[path.len() - j..], v, m, ch)
            }),
            1 => match c.into_cata_jumping_side_effect_fallible(|m, ch: &mut [(Vec<u8>, String)], j, v, path| {
                Ok::<_, ()>(line_node(&path[path.len() - j..], v, m, ch))
            }) {
                Ok(r) => r,
                Err(_) => return "Err".to_string(),
            },
            2 => c.into_cata_jumping_cached(|m, ch: &mut [(Vec<u8>, String)], v, sub| line_node(sub, v, m, ch)),
            _ => match c.into_cata_jumping_cached_fallible(|m, ch: &mut [(Vec<u8>, String)], v, sub| {
                Ok::<_, ()>(line_node(sub, v, m, ch))
            }) {
                Ok(r) => r,
                Err(_) => return "Err".to_string(),
            },
        };
        root_line(r)
    }
}

/// Op 59: the deprecated 3/4-function shims.  `mode % 2 = 0`: `SplitCata`
/// building the byte tree (`map_f` a valued leaf, `alg_f` a node from its
/// children, `collapse_f` puts a value into it); `1`: `SplitCataJumping`
/// counting and summing the values (`jump_f` the identity).
struct Split {
    mode: u8,
}

impl CataRun for Split {
    #[allow(deprecated)]
    fn run<C: Catamorphism<u64>>(self, c: C) -> String {
        if self.mode % 2 == 0 {
            let alg = |m: &ByteMask, ch: &mut [String], _path: &[u8]| {
                tree_node(None, m.iter().map(|b| vec![b]).collect::<Vec<_>>().into_iter(), ch)
            };
            let map = |v: &u64, _path: &[u8]| format!("({v})");
            let collapse = |v: &u64, w: String, _path: &[u8]| format!("({v}{}", &w[2..]);
            c.into_cata_side_effect(SplitCata::new(map, collapse, alg))
        } else {
            let alg = |_m: &ByteMask, ch: &mut [(u64, u64)], _path: &[u8]| {
                ch.iter().fold((0u64, 0u64), |a, w| (a.0 + w.0, a.1.wrapping_add(w.1)))
            };
            let map = |v: &u64, _path: &[u8]| (1u64, *v);
            let collapse = |v: &u64, w: (u64, u64), _path: &[u8]| (w.0 + 1, w.1.wrapping_add(*v));
            let jump = |_stem: &[u8], w: (u64, u64), _path: &[u8]| w;
            let (n, sum) = c.into_cata_jumping_side_effect(SplitCataJumping::new(map, collapse, alg, jump));
            format!("n={n} s={sum}")
        }
    }
}

/// A parsed prefix tree (`PTree`).
#[derive(Clone, Default)]
struct PTree {
    v: Option<u64>,
    kids: Vec<(Vec<u8>, PTree)>,
}

/// Parse a rendering made by [tree_node]; `None` on anything else.
fn parse_tree(s: &[u8], i: &mut usize) -> Option<PTree> {
    if s.get(*i) != Some(&b'(') {
        return None;
    }
    *i += 1;
    let start = *i;
    while *i < s.len() && s[*i] != b',' && s[*i] != b')' {
        *i += 1;
    }
    let vs = std::str::from_utf8(&s[start..*i]).ok()?;
    let v = if vs == "-" { None } else { Some(vs.parse().ok()?) };
    let mut kids = vec![];
    while s.get(*i) == Some(&b',') {
        *i += 1;
        let start = *i;
        while *i < s.len() && s[*i] != b'(' {
            *i += 1;
        }
        let hex = std::str::from_utf8(&s[start..*i]).ok()?;
        if hex.len() % 2 != 0 || hex.is_empty() {
            return None;
        }
        let e: Vec<u8> = (0..hex.len() / 2).map(|k| u8::from_str_radix(&hex[2 * k..2 * k + 2], 16)).collect::<Result<_, _>>().ok()?;
        kids.push((e, parse_tree(s, i)?));
    }
    if s.get(*i) != Some(&b')') {
        return None;
    }
    *i += 1;
    Some(PTree { v, kids })
}

/// Whether the deserializer grafts edge `e` at `path` from the source instead
/// of pushing it (`grafts` in `Morph.lean`): one-byte edges only, with `g` odd;
/// the caller also asks for something below the source location.
fn grafts(g: u8, path: &[u8], e: &[u8]) -> bool {
    e.len() == 1 && g % 2 == 1 && ((g >> 1) as usize + path.len() + e[0] as usize) % 3 == 0
}

/// Ops 57/58, second half: deserialize `tree` with `new_from_ana(_in)`, pushing
/// each edge (`push_byte` for one byte, unless `g & 8` asks for `push`), or
/// grafting it from `src` at `root ++ path ++ e` (see [grafts]).  Returns the
/// map and the number of closure calls.
fn deserialize(tree: PTree, src: &PathMap<u64>, root: &[u8], g: u8, use_in: bool) -> (PathMap<u64>, usize) {
    let mut calls = 0usize;
    let alg = |w: PTree, val: &mut Option<u64>, b: &mut TrieBuilder<u64, PTree, GlobalAlloc>, path: &[u8]| {
        calls += 1;
        *val = w.v;
        for (e, c) in w.kids {
            let at = [root, path, &e[..]].concat();
            let rz = src.read_zipper_at_path(&at);
            // Only where the source has something below: `graft_at_byte`
            // panics on a leaf (finding PT1 in lean/findings/ptree.md).
            if grafts(g, path, &e) && rz.child_count() > 0 {
                b.graft_at_byte(e[0], &rz);
            } else if e.len() == 1 && (g >> 3) & 1 == 0 {
                b.push_byte(e[0], c);
            } else {
                b.push(&e, c);
            }
        }
    };
    let m = if use_in { PathMap::new_from_ana_in(tree, alg, global_alloc()) } else { PathMap::new_from_ana(tree, alg) };
    (m, calls)
}

/// Every location below a zipper's root with its value, depth-first, uncapped.
fn walk<Z: ZipperMoving + ZipperPath + ZipperValues<u64>>(mut z: Z) -> Vec<(Vec<u8>, Option<u64>)> {
    z.reset();
    let mut out = vec![(z.path().to_vec(), z.val().copied())];
    while z.to_next_step() {
        out.push((z.path().to_vec(), z.val().copied()));
    }
    out
}

/// The trie a csrc presents, as a map and the root inside it.
fn source_map(st: &MapState, c: &CSrc) -> (PathMap<u64>, Vec<u8>) {
    let mut t = st.maps[c.i].clone();
    if !c.q.is_empty() {
        t.create_path(&c.q);
    }
    let root = if c.kind == 0 { vec![] } else { c.p.clone() };
    (t, root)
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
        57 | 58 => {
            let (c, fl, dst, g, use_in) = (csrc(d)?, d.u8()?, map_ix(d)?, d.u8()?, d.boolean()?);
            let name = if op == 57 { "tree_bytes" } else { "tree_lines" };
            let s = if op == 57 { dispatch(st, &c, TreeBytes { fl }) } else { dispatch(st, &c, TreeLines { fl }) };
            let Some(tree) = parse_tree(s.as_bytes(), &mut 0) else {
                return Some((name, format!("{s} unparsed")));
            };
            let (src, root) = source_map(st, &c);
            let (m, calls) = deserialize(tree, &src, &root, g, use_in);
            // Compare with the source view, crate against crate: the model
            // predicts `same=1` exactly when nothing dangling was lost.
            let same = walk(m.read_zipper()) == walk(src.read_zipper_at_path(&root));
            st.maps[dst] = m;
            (name, format!("{s} calls={calls} same={}", show_bool(same)))
        }
        59 => {
            let (c, mode) = (csrc(d)?, d.u8()?);
            ("split_cata", dispatch(st, &c, Split { mode }))
        }
        _ => ("nop", "-".to_string()),
    })
}
