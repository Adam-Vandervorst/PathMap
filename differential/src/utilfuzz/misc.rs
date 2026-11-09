//! Util fuzzer, ops 80–99: the external path sorters (`sort_paths`,
//! `sort_paths_par`) and the feature-gated modules.  Mirrors
//! `UtilFuzz/Misc.lean`, which states the model.
//!
//! ## Sorting (ops 80–84)
//!
//! Both sorters take an unordered `.paths` stream and write the sorted,
//! deduplicated paths as a `.paths` stream.  Each call gets its own fresh
//! scratch directory (`<tmp>/pathmap-utilfuzz-<pid>-<n>`, created with
//! `create_dir`, so never shared); the answer reports how many files the sorter
//! left in it (`t=`), and the harness then removes them and the directory.
//!
//! | op | name | operands | answer |
//! |---|---|---|---|
//! | 80 | `sort_paths` | `mem`, path list (below) | `sorted(ser)` |
//! | 81 | `sort_paths_par` | `mem`, path list | `sorted(par)` |
//! | 82 | `sort_big` | generated list (below) | `S<digest(ser)>|P<digest(par)>` |
//! | 83 | `sort_cut` | path list, cut (below) | `S<sorted(ser)>|P<sorted(par)>` of a truncated stored-block stream |
//! | 84 | `sort_long` | `δ := u8 % 3`, path list, `at := u8 % (n + 1)` | one path of `65535 + δ` `a5` bytes inserted at `at` (the 1 MiB budget's limit is 65536): `S<digest>|P<digest>` |
//!
//! `mem := u8`: when `mem % 16 == 0` the budget is `1 MiB - 1 - mem / 16`
//! (refused, `InvalidInput`), else `(1 + mem % 4)` MiB.
//!
//! Path list: `alpha := [2, 4, 256][u8 % 3]`, `n := u8 % 24`, then `n` paths of
//! `len := u8 % 20` bytes, each `u8 % alpha`.  The input stream is written by
//! `serialize_paths_from_funcs` in list order.
//!
//! `sorted(..)`: `err:<ErrorKind>,t=<left>` on error, else
//! `n=<path_count>,u=<bytes_in>,o=<bytes_out == bytes written>,t=<left>;[<paths>]`
//! with the output decoded by `for_each_deserialized_path`.  `digest(..)`
//! renders the paths as `h=<FNV-1a 64 of the decoded records>,f=<first>,l=<last>`
//! (`-` when there is none; a path over 64 bytes as `#<len>`)
//! instead of listing them.
//!
//! Generated list (op 82): `g := u8`; `n := 200 * (1 + u8 % 8)`, or when
//! `g % 4 == 0`, `n := 2000 * (1 + u8 % 20)` (enough to make both sorters spill
//! runs to disk at 1 MiB); `maxlen := [8, 24, 64][u8 % 3]`,
//! `alpha := [2, 4, 256][u8 % 3]`, `distinct := [n / 4, n, 2^32][u8 % 3]`,
//! `seed := 4 × u8` (little-endian), `mem := (1 + u8 % 2)` MiB.  Path `j` is
//! `pathOf(seed + (idx_j))` where `idx_j := (x_j >> 16) % distinct` and
//! `x_{j+1} := lcg(x_j)`, `x_0 := lcg(seed)`; `pathOf(z)`: `z := lcg(z)`,
//! `len := (z >> 40) % maxlen`, then each byte `z := lcg(z)`,
//! `(z >> 56) % alpha`.  `lcg(x) := x * 6364136223846793005 + 1442695040888963407`
//! (mod 2^64).
//!
//! Cut stream (op 83): the records `[u32 len LE][path]` of the path list are put
//! in one stored deflate block in a zlib wrapper (`78 01`, `01 LEN NLEN`, data,
//! Adler-32): byte `7 + i` of the stream is data byte `i`.  `mode := u8 % 4`:
//! 0 keeps the whole stream; 1 cuts it at `7 + u16le % (data + 1)`; 2 drops
//! `1 + u8 % 4` bytes of the trailer; 3 keeps `u8 % 7` bytes (inside the
//! headers).  `mem` is 1 MiB.

use super::*;
use pathmap::PathMap;
use pathmap::zipper::*;
use pathmap::paths_serialization::{
    for_each_deserialized_path, serialize_paths_from_funcs, sort_paths, sort_paths_par,
};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

const MIB: usize = 1 << 20;

/// A fresh scratch directory, exclusive to one sort call.
fn scratch() -> PathBuf {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let base = std::env::temp_dir();
    loop {
        let n = NEXT.fetch_add(1, Ordering::Relaxed);
        let p = base.join(format!("pathmap-utilfuzz-{}-{n}", std::process::id()));
        if std::fs::create_dir(&p).is_ok() {
            return p;
        }
    }
}

/// Count the files a sort left behind, remove them and the directory.
fn cleanup(dir: &Path) -> usize {
    let mut left = 0;
    if let Ok(rd) = std::fs::read_dir(dir) {
        for e in rd.flatten() {
            left += 1;
            let _ = std::fs::remove_file(e.path());
        }
    }
    let _ = std::fs::remove_dir(dir);
    left
}

type ListSrc<'a> = (&'a [Vec<u8>], usize);

fn list_advance(s: &mut ListSrc) -> std::io::Result<bool> {
    s.1 += 1;
    Ok(s.1 <= s.0.len())
}

fn list_path<'s>(s: &'s ListSrc) -> Option<&'s [u8]> {
    Some(&s.0[s.1 - 1][..])
}

/// Serialize `paths` in list order with the crate's own writer.
fn serialize(paths: &[Vec<u8>]) -> Vec<u8> {
    let mut buf = Vec::new();
    let mut src: ListSrc = (paths, 0);
    serialize_paths_from_funcs(&mut buf, &mut src, list_advance, list_path).expect("serialize into a Vec");
    buf
}

fn fnv(paths: &[Vec<u8>]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    let mut eat = |b: u8| {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    };
    for p in paths {
        for b in (p.len() as u32).to_le_bytes() {
            eat(b);
        }
        for &b in p {
            eat(b);
        }
    }
    h
}

/// Run one sorter on `input` and render its answer (see the module docs).
fn run_sort(par: bool, input: &[u8], mem: usize, digest: bool) -> String {
    let dir = scratch();
    let mut out = Vec::new();
    let r = if par {
        sort_paths_par(input, &mut out, mem, &dir)
    } else {
        sort_paths(input, &mut out, mem, &dir)
    };
    let left = cleanup(&dir);
    let stats = match r {
        Err(e) => return format!("err:{:?},t={left}", e.kind()),
        Ok(s) => s,
    };
    let mut paths = Vec::new();
    let dec = for_each_deserialized_path(&out[..], |_, p| {
        paths.push(p.to_vec());
        Ok(())
    });
    let mut s = format!(
        "n={},u={},o={},t={left}",
        stats.path_count,
        stats.bytes_in,
        show_bool(stats.bytes_out == out.len())
    );
    if let Err(e) = dec {
        let _ = write!(s, ",dec:{:?}", e.kind());
    }
    if digest {
        let first = paths.first().map_or("-".to_string(), |p| show_short(p));
        let last = paths.last().map_or("-".to_string(), |p| show_short(p));
        let _ = write!(s, ";h={:016x},f={first},l={last}", fnv(&paths));
    } else {
        let v: Vec<String> = paths.iter().map(|p| hex_path(p)).collect();
        let _ = write!(s, ";[{}]", v.join(","));
    }
    s
}

/// A path in a digest: hex, or `#<len>` when longer than 64 bytes.
fn show_short(p: &[u8]) -> String {
    if p.len() > 64 { format!("#{}", p.len()) } else { hex_path(p) }
}

fn read_mem(d: &mut Dec) -> Option<usize> {
    let m = d.u8()? as usize;
    Some(if m % 16 == 0 { MIB - 1 - m / 16 } else { (1 + m % 4) * MIB })
}

const ALPHA: [usize; 3] = [2, 4, 256];

fn read_list(d: &mut Dec) -> Option<Vec<Vec<u8>>> {
    let alpha = ALPHA[d.modn(3)?];
    let n = d.modn(24)?;
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let len = d.modn(20)?;
        let mut p = Vec::with_capacity(len);
        for _ in 0..len {
            p.push((d.u8()? as usize % alpha) as u8);
        }
        v.push(p);
    }
    Some(v)
}

fn lcg(x: u64) -> u64 {
    x.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407)
}

fn path_of(mut z: u64, maxlen: u64, alpha: u64) -> Vec<u8> {
    z = lcg(z);
    let len = (z >> 40) % maxlen;
    let mut p = Vec::with_capacity(len as usize);
    for _ in 0..len {
        z = lcg(z);
        p.push(((z >> 56) % alpha) as u8);
    }
    p
}

fn read_generated(d: &mut Dec) -> Option<(Vec<Vec<u8>>, usize)> {
    let g = d.u8()?;
    let n = if g % 4 == 0 { 2000 * (1 + d.modn(20)?) } else { 200 * (1 + d.modn(8)?) };
    let maxlen = [8u64, 24, 64][d.modn(3)?];
    let alpha = ALPHA[d.modn(3)?] as u64;
    let distinct = [(n / 4) as u64, n as u64, 1u64 << 32][d.modn(3)?];
    let mut seed = 0u64;
    for i in 0..4 {
        seed |= (d.u8()? as u64) << (8 * i);
    }
    let mem = (1 + d.modn(2)?) * MIB;
    let mut x = lcg(seed);
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let idx = (x >> 16) % distinct;
        v.push(path_of(seed.wrapping_add(idx), maxlen, alpha));
        x = lcg(x);
    }
    Some((v, mem))
}

/// Adler-32 of `data`.
fn adler32(data: &[u8]) -> u32 {
    let (mut a, mut b) = (1u32, 0u32);
    for &x in data {
        a = (a + x as u32) % 65521;
        b = (b + a) % 65521;
    }
    (b << 16) | a
}

/// `data` as a zlib stream holding one final stored deflate block.
fn stored_zlib(data: &[u8]) -> Vec<u8> {
    let len = data.len() as u16;
    let mut z = vec![0x78, 0x01, 0x01];
    z.extend_from_slice(&len.to_le_bytes());
    z.extend_from_slice(&(!len).to_le_bytes());
    z.extend_from_slice(data);
    z.extend_from_slice(&adler32(data).to_be_bytes());
    z
}

fn both(input: &[u8], mem: usize, digest: bool) -> String {
    format!("S{}|P{}", run_sort(false, input, mem, digest), run_sort(true, input, mem, digest))
}

// ---------------------------------------------------------------- viz (85–87)

/// Path bytes of the maps the feature-module ops build: `a`, `b`, and the two
/// bytes of `é` (`c3 a9`), so labels are valid UTF-8 or not by chance.
pub const VIZ_ALPHA: [u8; 4] = [0x61, 0x62, 0xc3, 0xa9];

/// A small map: `rv := u8` (root value `rv / 2` when `rv` is odd),
/// `n := 1 + u8 % 8` entries of `len := u8 % 5` bytes `VIZ_ALPHA[u8 % 4]` and
/// value `u8`, set in order (a later entry overwrites).
fn read_small_map(d: &mut Dec) -> Option<PathMap<u64>> {
    let mut m = PathMap::new();
    let rv = d.u8()?;
    if rv % 2 == 1 {
        m.set_val_at([], (rv / 2) as u64);
    }
    let n = 1 + d.modn(8)?;
    for _ in 0..n {
        let len = d.modn(5)?;
        let mut p = Vec::with_capacity(len);
        for _ in 0..len {
            p.push(VIZ_ALPHA[d.modn(4)?]);
        }
        let v = d.u8()? as u64;
        m.set_val_at(&p, v);
    }
    Some(m)
}

/// `k := 1 + u8 % 3` independently built small maps.
fn read_maps(d: &mut Dec) -> Option<Vec<PathMap<u64>>> {
    let k = 1 + d.modn(3)?;
    let mut v = Vec::with_capacity(k);
    for _ in 0..k {
        v.push(read_small_map(d)?);
    }
    Some(v)
}

/// Escape a rendering onto one trace line: `\n`, `\\`, and every char outside
/// printable ASCII as `\u{hex}`.
fn esc(s: &str) -> String {
    let mut o = String::new();
    for c in s.chars() {
        match c {
            '\n' => o.push_str("\\n"),
            '\\' => o.push_str("\\\\"),
            ' '..='~' => o.push(c),
            _ => { let _ = write!(o, "\\u{{{:x}}}", c as u32); }
        }
    }
    o
}

/// `f := u8`: `ascii_path` = bit 0, `hide_value_paths` = bits 1–2 both 0,
/// `minimize_values` = bit 3, `color` = bit 4.
fn read_config(d: &mut Dec, mode: pathmap::viz::VizMode, logical: bool) -> Option<pathmap::viz::DrawConfig> {
    let f = d.u8()?;
    Some(pathmap::viz::DrawConfig {
        mode,
        ascii_path: f & 1 == 1,
        hide_value_paths: (f >> 1) & 3 == 0,
        minimize_values: (f >> 3) & 1 == 1,
        logical,
        color: (f >> 4) & 1 == 1,
    })
}

/// `viz_maps` panics on a map without a root node (`viz_no_root_node`): a map
/// with nothing below its root.  Skipped, same token in `Misc.lean`.
fn viz_skip(maps: &[PathMap<u64>]) -> bool {
    maps.iter().any(|m| m.read_zipper().child_count() == 0)
}

fn viz_render(maps: &[PathMap<u64>], dc: &pathmap::viz::DrawConfig) -> String {
    let mut out = Vec::new();
    match pathmap::viz::viz_maps(maps, dc, &mut out) {
        Ok(()) => String::from_utf8_lossy(&out).into_owned(),
        Err(e) => format!("err:{:?}", e.kind()),
    }
}

/// A mermaid edge label, `{jump:?}` of the rendered label, back to bytes.
fn mermaid_label(dbg: &str, ascii: bool) -> Option<Vec<u8>> {
    let s = dbg.strip_prefix('"')?.strip_suffix('"')?;
    if s.contains('\\') {
        return None; // never produced for this alphabet
    }
    if ascii && !s.starts_with('[') {
        return Some(s.as_bytes().to_vec());
    }
    let inner = s.strip_prefix('[')?.strip_suffix(']')?;
    if inner.is_empty() {
        return Some(vec![]);
    }
    inner.split(", ").map(|x| x.parse::<u8>().ok()).collect()
}

enum Target { Node(String), Val(String) }

/// The graph of a mermaid rendering: map roots in order, labelled out-edges,
/// value labels.  `None` on a line it does not recognise.
struct Mermaid {
    roots: Vec<String>,
    edges: std::collections::HashMap<String, Vec<(Vec<u8>, Target)>>,
    vals: std::collections::HashMap<String, String>,
}

fn parse_mermaid(text: &str, ascii: bool, logical: bool) -> Result<Mermaid, String> {
    let mut g = Mermaid { roots: vec![], edges: Default::default(), vals: Default::default() };
    let mut lines = text.lines();
    if lines.next() != Some("flowchart LR") {
        return Err("header".into());
    }
    for l in lines {
        if l.starts_with("style ") {
            continue;
        }
        if let Some((id, rest)) = l.split_once("@{ shape: ") {
            if rest.starts_with("cylinder, label: \"PathMap[") {
                if logical { g.roots.push(id.to_string()); }
            } else if let Some(lab) = rest.strip_prefix("rounded, label: \"").and_then(|r| r.strip_suffix("\" }")) {
                g.vals.insert(id.to_string(), lab.to_string());
            } else if rest == "circle, label: \".\"}" {
                if id.starts_with('v') { g.vals.insert(id.to_string(), ".".to_string()); }
            } else if !rest.starts_with("rect, label: \"") {
                return Err(l.to_string());
            }
            continue;
        }
        let (src, label, dst) = if let Some((src, rest)) = l.split_once(" --\"") {
            let (lab, dst) = rest.rsplit_once("\"--> ").ok_or_else(|| l.to_string())?;
            (src, mermaid_label(lab, ascii).ok_or_else(|| l.to_string())?, dst)
        } else if let Some((src, dst)) = l.split_once(" --> ") {
            (src, vec![], dst)
        } else {
            return Err(l.to_string());
        };
        if src.starts_with('m') && !logical {
            g.roots.push(dst.to_string());
            continue;
        }
        let t = if dst.starts_with('v') { Target::Val(dst.to_string()) } else { Target::Node(dst.to_string()) };
        g.edges.entry(src.to_string()).or_default().push((label, t));
    }
    Ok(g)
}

/// Canonical form of a logical rendering: per map `M{node}`, where a node is
/// `{edge,…}` sorted by label bytes, an edge `hex(label)` followed by its
/// target node or `=value`.
fn mermaid_canon(g: &Mermaid) -> String {
    fn node(g: &Mermaid, id: &str, depth: usize, out: &mut String) {
        out.push('{');
        if depth < 64 {
            let mut es: Vec<&(Vec<u8>, Target)> = g.edges.get(id).map(|v| v.iter().collect()).unwrap_or_default();
            es.sort_by(|a, b| a.0.cmp(&b.0));
            for (i, (lab, t)) in es.into_iter().enumerate() {
                if i > 0 { out.push(','); }
                out.push_str(&hex_path(lab));
                match t {
                    Target::Val(v) => { out.push('='); out.push_str(g.vals.get(v).map_or("?", |s| s.as_str())); }
                    Target::Node(n) => node(g, n, depth + 1, out),
                }
            }
        }
        out.push('}');
    }
    let mut out = String::new();
    for (i, r) in g.roots.iter().enumerate() {
        if i > 0 { out.push(';'); }
        out.push('M');
        node(g, r, 0, &mut out);
    }
    out
}

/// The values a physical rendering shows: per map the sorted `hex(path)=value`
/// list, the path being the concatenated edge labels from the root node.
fn mermaid_values(g: &Mermaid) -> String {
    fn walk(g: &Mermaid, id: &str, path: &mut Vec<u8>, depth: usize, acc: &mut Vec<(Vec<u8>, String)>) {
        if depth > 64 { return; }
        for (lab, t) in g.edges.get(id).map(|v| v.as_slice()).unwrap_or(&[]) {
            let n = path.len();
            path.extend_from_slice(lab);
            match t {
                Target::Val(v) => acc.push((path.clone(), g.vals.get(v).cloned().unwrap_or("?".into()))),
                Target::Node(c) => walk(g, c, path, depth + 1, acc),
            }
            path.truncate(n);
        }
    }
    let mut out = String::new();
    for (i, r) in g.roots.iter().enumerate() {
        let mut acc = vec![];
        walk(g, r, &mut vec![], 0, &mut acc);
        acc.sort();
        if i > 0 { out.push(';'); }
        let v: Vec<String> = acc.iter().map(|(p, v)| format!("{}={v}", hex_path(p))).collect();
        let _ = write!(out, "M[{}]", v.join(","));
    }
    out
}

fn viz_op(op: usize, d: &mut Dec) -> Option<(&'static str, String)> {
    use pathmap::viz::VizMode;
    let maps = read_maps(d)?;
    let (mode, logical) = match op { 85 => (VizMode::Ascii, true), 86 => (VizMode::Mermaid, true), _ => (VizMode::Mermaid, false) };
    let dc = read_config(d, mode, logical)?;
    // A root value is never drawn by the mermaid renderers
    // (`viz_mermaid_drops_root_value`).  Those ops get their own names and
    // `;skip:viz-mermaid-root-value`: the model leaves the root value out and
    // the rest of the graph is still compared (as a KNOWN entry the bug ended
    // the comparison of ~15% of inputs).
    let rv = !dc.hide_value_paths && maps.iter().any(|m| m.val_at([]).is_some());
    let name = match (op, rv) {
        (85, _) => "viz_ascii",
        (86, false) => "viz_mermaid",
        (86, true) => "viz_mermaid_rv",
        (_, false) => "viz_phys",
        (_, true) => "viz_phys_rv",
    };
    if viz_skip(&maps) {
        return Some((name, "skip:viz-no-root-node".to_string()));
    }
    let text = viz_render(&maps, &dc);
    let ret = match op {
        85 => esc(&text),
        _ => match parse_mermaid(&text, dc.ascii_path, logical) {
            Err(l) => format!("unparsed:{}", esc(&l)),
            Ok(g) => if logical { mermaid_canon(&g) } else { mermaid_values(&g) },
        },
    };
    let ret = if rv && op != 85 { ret + ";skip:viz-mermaid-root-value" } else { ret };
    Some((name, ret))
}

pub fn step(op: usize, d: &mut Dec) -> StepResult {
    let r = match op {
        80 | 81 => {
            let mem = read_mem(d)?;
            let list = read_list(d)?;
            let input = serialize(&list);
            let par = op == 81;
            (if par { "sort_paths_par" } else { "sort_paths" }, run_sort(par, &input, mem, false))
        }
        82 => {
            let (list, mem) = read_generated(d)?;
            ("sort_big", both(&serialize(&list), mem, true))
        }
        83 => {
            let list = read_list(d)?;
            let mut data = Vec::new();
            for p in &list {
                data.extend_from_slice(&(p.len() as u32).to_le_bytes());
                data.extend_from_slice(p);
            }
            let z = stored_zlib(&data);
            let keep = match d.modn(4)? {
                0 => z.len(),
                1 => 7 + (d.u8()? as usize | (d.u8()? as usize) << 8) % (data.len() + 1),
                2 => z.len() - 1 - d.modn(4)?,
                _ => d.modn(7)?,
            };
            ("sort_cut", both(&z[..keep], MIB, false))
        }
        84 => {
            let delta = d.modn(3)?;
            let mut list = read_list(d)?;
            let at = d.modn(list.len() + 1)?;
            list.insert(at, vec![0xa5; 65535 + delta]);
            ("sort_long", both(&serialize(&list), MIB, true))
        }
        85..=87 => viz_op(op, d)?,
        _ => ("nop", "-".to_string()),
    };
    Some(r)
}
