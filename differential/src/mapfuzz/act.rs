//! Map fuzzer, ops 40–49: ArenaCompactTree files, merge, stream.  Mirrors
//! `MapFuzz/Act.lean`, which states what each one must produce.
//!
//! Every op renders the trie read back from the ACT it built, so the answer is
//! checked against the model's dump.  Files live in a per-op [`TmpDir`].

use super::serial::TmpDir;
use super::*;
use pathmap::arena_compact::{ACTOutputStream, ArenaCompactTree};
use pathmap::zipper::*;

/// The value mapping selected by an op's `mode` operand.  `Act.fmap`.
fn fmap(mode: usize, v: u64) -> u64 {
    match mode {
        0 => v,
        1 => v.wrapping_mul(0x0101010101010101),
        _ => !v,
    }
}

/// An `ACTOutputStream` with the line cache selected by `cache`: the default,
/// or a limit of 0 (disabled), 1 or 2 entries.
fn stream(file: &std::path::Path, cache: usize) -> ACTOutputStream {
    match cache {
        0 => ACTOutputStream::new(file),
        n => ACTOutputStream::with_cache_limit(file, n - 1),
    }
    .expect("create ACT stream")
}

/// Every location below `z`'s root, relative to it, depth-first, capped like `dump`.
fn walk_paths<Z: ZipperMoving + ZipperPath>(z: &mut Z) -> String {
    z.reset();
    let mut ps = vec![z.path().to_vec()];
    while ps.len() < DUMP_CAP && z.to_next_step() {
        if z.path().is_empty() {
            ps.push(b"ESCAPED-ROOT".to_vec());
            break;
        }
        ps.push(z.path().to_vec());
    }
    show_paths(ps)
}

/// Every location of a unit-valued `ACTZipper` below its root, depth-first,
/// relative to it, capped like `dump`: `<path>` + `v` (a value) or `-`, and `!`
/// where `get_val` (`ZipperReadOnlyValues<()>`) disagrees with `val`.  Joined
/// with `/`.  `Act.unitWalk`.
fn unit_walk<'t, S: AsRef<[u8]>>(z: &mut pathmap::arena_compact::ACTZipper<'t, S, ()>) -> String {
    let one = |z: &pathmap::arena_compact::ACTZipper<'t, S, ()>| {
        let v = ZipperValues::<()>::val(z).is_some();
        let g = ZipperReadOnlyValues::<()>::get_val(z).is_some();
        format!("{}{}{}", hex_path(z.path()), if v { "v" } else { "-" }, if v == g { "" } else { "!" })
    };
    z.reset();
    let mut ps = vec![one(z)];
    while ps.len() < DUMP_CAP && z.to_next_step() {
        if z.path().is_empty() {
            ps.push("ESCAPED-ROOT".to_string());
            break;
        }
        ps.push(one(z));
    }
    ps.join("/")
}

pub fn step(op: usize, d: &mut Dec, st: &mut MapState) -> StepResult {
    Some(match op {
        40 => {
            let (i, p, mode) = (map_ix(d)?, d.path(6)?, d.modn(3)?);
            let mut td = TmpDir::new("act_dump");
            let file = td.file("t.act");
            let f = |v: &u64| fmap(mode, *v);
            let a = ArenaCompactTree::dump_from_zipper(st.maps[i].read_zipper_at_path(&p), f, &file)
                .expect("dump_from_zipper");
            let b = ArenaCompactTree::from_zipper(st.maps[i].read_zipper_at_path(&p), f);
            let same = a.get_data() == b.get_data();
            ("act_dump", format!("{};same={}", dump(&mut a.read_zipper_u64()), show_bool(same)))
        }
        41 => {
            let (i, p, mode, k) = (map_ix(d)?, d.path(6)?, d.modn(3)?, d.modn(20)?);
            let mut td = TmpDir::new("act_open");
            let file = td.file("t.act");
            let short = td.file("short.act");
            let b = ArenaCompactTree::from_zipper(st.maps[i].read_zipper_at_path(&p), |v: &u64| fmap(mode, *v));
            std::fs::write(&file, b.get_data()).expect("write ACT");
            let o = ArenaCompactTree::open_mmap(&file).expect("open_mmap");
            let same = o.get_data() == b.get_data();
            let k = k.min(b.get_data().len());
            std::fs::write(&short, &b.get_data()[..k]).expect("write ACT prefix");
            // `skip:act_open_short`: a file shorter than the magic (empty
            // included) makes `open_mmap` panic slicing it
            // (`lean/findings/map-serial.md`); see `MapFuzz/Act.lean`.
            let trunc = if k < 8 {
                "skip:act_open_short"
            } else if ArenaCompactTree::open_mmap(&short).is_ok() { "ok" } else { "err" };
            ("act_open", format!("{};same={};trunc={}",
                dump(&mut o.read_zipper_u64()), show_bool(same), trunc))
        }
        42 | 43 => {
            let (i, p, j, q) = (map_ix(d)?, d.path(6)?, map_ix(d)?, d.path(6)?);
            let second = if op == 43 { Some((map_ix(d)?, d.path(6)?)) } else { None };
            let mode = d.modn(3)?;
            let f = |v: &u64| fmap(mode, *v);
            let mut td = TmpDir::new("act_merge");
            let file = td.file("t.act");
            let base = ArenaCompactTree::from_zipper(st.maps[i].read_zipper_at_path(&p), f);
            std::fs::write(&file, base.get_data()).expect("write ACT");
            drop(base);
            let mut m = ArenaCompactTree::merge_zipper_into_file(&file, st.maps[j].read_zipper_at_path(&q), f)
                .expect("merge_zipper_into_file");
            if let Some((k, r)) = second {
                drop(m);
                m = ArenaCompactTree::merge_zipper_into_file(&file, st.maps[k].read_zipper_at_path(&r), f)
                    .expect("merge_zipper_into_file");
            }
            let name = if op == 42 { "act_merge" } else { "act_merge2" };
            (name, format!("{};h={}", dump(&mut m.read_zipper_u64()), m.root_history().len()))
        }
        44 => {
            let (i, p, mode, cache) = (map_ix(d)?, d.path(6)?, d.modn(3)?, d.modn(4)?);
            let mut td = TmpDir::new("act_stream");
            let file = td.file("t.act");
            let mut s = stream(&file, cache);
            let mut rz = st.maps[i].read_zipper_at_path(&p);
            if let Some(v) = rz.val() {
                s.push_val(b"", fmap(mode, *v)).expect("push root");
            }
            while rz.to_next_val() {
                let v = fmap(mode, *rz.val().unwrap());
                s.push_val(rz.path(), v).expect("push in order");
            }
            let t = s.finish().expect("finish");
            ("act_stream", dump(&mut t.read_zipper_u64()))
        }
        45 => {
            let (cache, n) = (d.modn(4)?, d.modn(6)?);
            let mut xs = Vec::with_capacity(n);
            for _ in 0..n {
                xs.push((d.path(6)?, val(d)?));
            }
            let mut td = TmpDir::new("act_stream_raw");
            let file = td.file("t.act");
            let mut s = stream(&file, cache);
            let mut bits = String::new();
            for (path, v) in &xs {
                let r = if v % 4 == 0 { s.push(path) } else { s.push_val(path, *v) };
                bits.push(match r {
                    Ok(()) => '1',
                    Err(e) if e.kind() == std::io::ErrorKind::InvalidInput => '0',
                    Err(_) => '!',
                });
            }
            if bits.is_empty() { bits.push('-'); }
            let t = s.finish().expect("finish");
            ("act_stream_raw", format!("{};{}", bits, dump(&mut t.read_zipper_u64())))
        }
        46 => {
            let (i, p, j) = (map_ix(d)?, d.path(6)?, map_ix(d)?);
            let n = d.modn(3)? + 1;
            let mut pres = Vec::with_capacity(n);
            for _ in 0..n {
                pres.push(d.path(4)?);
            }
            let mode = d.modn(3)?;
            let mut tmp = st.maps[i].clone();
            for a in &pres {
                tmp.write_zipper_at_path(a).graft(&st.maps[j].read_zipper());
            }
            let t = ArenaCompactTree::from_zipper_cached(tmp.read_zipper_at_path(&p), |v: &u64| fmap(mode, *v));
            ("act_cached", dump(&mut t.read_zipper_u64()))
        }
        47 => {
            let (i, p, mode, n) = (map_ix(d)?, d.path(6)?, d.modn(3)?, d.modn(4)?);
            let mut qs = Vec::with_capacity(n);
            for _ in 0..n {
                qs.push(d.path(6)?);
            }
            let t = ArenaCompactTree::from_zipper(st.maps[i].read_zipper_at_path(&p), |v: &u64| fmap(mode, *v));
            #[allow(deprecated)]
            let gets: Vec<String> = qs.iter()
                .map(|q| format!("{}/{}", show_val(t.get_val_at(q).as_ref()), show_val(t.get(q).as_ref())))
                .collect();
            let g = if gets.is_empty() { "-".to_string() } else { gets.join(",") };
            ("act_get", format!("{};{}", g, show_pairs(t.iter())))
        }
        48 => {
            let (i, p, q, mode) = (map_ix(d)?, d.path(6)?, d.path(6)?, d.modn(3)?);
            let t = ArenaCompactTree::from_zipper(st.maps[i].read_zipper_at_path(&p), |v: &u64| fmap(mode, *v));
            let mut z = t.read_zipper_at_borrowed_path_u64(&q);
            let mut u = t.read_zipper_at_borrowed_path(&q);
            // The unit-valued zipper over the whole tree (`read_zipper`): its
            // walk, `val_at(q)` / `get_val_at(q)` from the root, and the walk of
            // its `fork_read_zipper` at `q` (`_` when there is none).
            let mut r = t.read_zipper();
            let whole = unit_walk(&mut r);
            r.reset();
            let a = ZipperValuesAt::<()>::val_at(&r, &q).is_some();
            let ga = ZipperReadOnlyValues::<()>::get_val_at(&r, &q).is_some();
            r.descend_to(&q);
            let fork = match ZipperForking::<()>::fork_read_zipper(&r) {
                Some(mut f) => unit_walk(&mut f),
                None => "_".to_string(),
            };
            ("act_zipper_at", format!("{};{};U{};a{}{};F{}", dump(&mut z), walk_paths(&mut u), whole,
                show_bool(a), if a == ga { "" } else { "!" }, fork))
        }
        _ => ("nop", "-".to_string()),
    })
}
