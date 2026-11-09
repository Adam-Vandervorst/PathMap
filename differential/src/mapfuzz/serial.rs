//! Map fuzzer, ops 30–39: serialization round trips.  Mirrors `MapFuzz/Serial.lean`,
//! which states what each format preserves.

use super::*;
use pathmap::experimental::serialization::{
    deserialize_file, write_trie, ValueSlice, META_DATA_FILENAME, RAW_HEX_DATA_FILENAME,
    ZERO_COMPRESSED_HEX_DATA_FILENAME,
};
use pathmap::paths_serialization::*;
use pathmap::zipper::*;
use std::cell::{Cell, RefCell};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

/// A scratch directory for one operation's files, removed (file by file, then
/// the directory) when dropped -- also while unwinding from a panic, since the
/// server catches panics and keeps running.  Unique per process and per call:
/// the server runs many inputs per process, on several threads.
pub(crate) struct TmpDir {
    pub dir: PathBuf,
    files: Vec<PathBuf>,
}

static TMP_SEQ: AtomicU64 = AtomicU64::new(0);

impl TmpDir {
    pub fn new(tag: &str) -> TmpDir {
        let n = TMP_SEQ.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir()
            .join(format!("pathmap-mapfuzz-{}-{}-{}", std::process::id(), n, tag));
        std::fs::create_dir(&dir).expect("create scratch dir");
        TmpDir { dir, files: Vec::new() }
    }

    /// A file in this directory that is removed on drop.
    pub fn file(&mut self, name: &str) -> PathBuf {
        let f = self.dir.join(name);
        self.files.push(f.clone());
        f
    }
}

impl Drop for TmpDir {
    fn drop(&mut self) {
        for f in &self.files {
            let _ = std::fs::remove_file(f);
        }
        let _ = std::fs::remove_dir(&self.dir);
    }
}

/// `write_trie` value encoders: minimal little-endian (`0` is the empty
/// slice), or the eight raw bytes borrowed from the value.
fn enc_min<'r, 'e>(v: &'r u64, buf: &'e mut Vec<u8>) -> ValueSlice<'r, 'e> {
    let b = v.to_le_bytes();
    let n = 8 - (v.leading_zeros() as usize / 8);
    buf.extend_from_slice(&b[..n]);
    ValueSlice::Encode(buf)
}

fn enc_raw<'r, 'e>(v: &'r u64, _buf: &'e mut Vec<u8>) -> ValueSlice<'r, 'e> {
    // SAFETY: a u64 is eight initialised bytes, borrowed for `'r`.
    ValueSlice::Read(unsafe { std::slice::from_raw_parts(v as *const u64 as *const u8, 8) })
}

fn dec_le(b: &[u8]) -> u64 {
    let mut a = [0u8; 8];
    let n = b.len().min(8);
    a[..n].copy_from_slice(&b[..n]);
    u64::from_le_bytes(a)
}

/// `"KEY" : 123` from `write_trie`'s `meta.json`.
fn meta_field(meta: &str, key: &str) -> String {
    let Some(at) = meta.find(&format!("\"{key}\"")) else { return "?".to_string() };
    let rest = &meta[at + key.len() + 2..];
    let rest = rest.trim_start().trim_start_matches(':').trim_start();
    rest.chars().take_while(|c| c.is_ascii_digit()).collect()
}

/// `;r=1` when the `.paths` stream holds a zero-length record (the focus
/// value), `;r=0` when not.  `Serial.rootRec`.
fn root_rec(buf: &[u8]) -> &'static str {
    let mut root = false;
    let _ = for_each_deserialized_path(buf, |_, path| { root |= path.is_empty(); Ok(()) });
    if root { ";r=1" } else { ";r=0" }
}

fn ser(m: &PathMap<u64>, p: &[u8]) -> (Vec<u8>, SerializationStats) {
    let mut buf = Vec::new();
    let s = serialize_paths(m.read_zipper_at_path(p), &mut buf).expect("serialize to a Vec");
    (buf, s)
}

pub fn step(op: usize, d: &mut Dec, st: &mut MapState) -> StepResult {
    Some(match op {
        30 => {
            let (i, p, j, q, v) = (map_ix(d)?, d.path(6)?, map_ix(d)?, d.path(4)?, val(d)?);
            let (buf, s) = ser(&st.maps[i], &p);
            let r = deserialize_paths(st.maps[j].write_zipper_at_path(&q), buf.as_slice(), v)
                .expect("deserialize");
            ("ser_paths", format!("{},{}{}", s.path_count, r.path_count, root_rec(&buf)))
        }
        31 => {
            let (i, p, j, q) = (map_ix(d)?, d.path(6)?, map_ix(d)?, d.path(4)?);
            let mut buf = Vec::new();
            let mut side: Vec<(Vec<u8>, u64)> = Vec::new();
            let mut bad = String::new();
            let s = serialize_paths_with_auxdata(
                st.maps[i].read_zipper_at_path(&p), &mut buf,
                |k, path, v| {
                    if k != side.len() { bad.push_str("!sidx"); }
                    side.push((path.to_vec(), *v));
                },
            ).expect("serialize to a Vec");
            let mismatch = Cell::new(false);
            let r = deserialize_paths_with_auxdata(
                st.maps[j].write_zipper_at_path(&q), buf.as_slice(),
                |k, path| match side.get(k) {
                    Some((sp, v)) => {
                        if sp.as_slice() != path { mismatch.set(true); }
                        *v
                    }
                    None => { mismatch.set(true); 0 }
                },
            ).expect("deserialize");
            if mismatch.get() { bad.push_str("!didx"); }
            ("ser_paths_aux", format!("{},{}{}{}", s.path_count, r.path_count, bad, root_rec(&buf)))
        }
        32 => {
            let (i, p) = (map_ix(d)?, d.path(6)?);
            let (buf, s) = ser(&st.maps[i], &p);
            let paths = RefCell::new(Vec::new());
            let r = for_each_deserialized_path(buf.as_slice(), |k, path| {
                let mut ps = paths.borrow_mut();
                if k != ps.len() { ps.push(b"!idx".to_vec()); }
                ps.push(path.to_vec());
                Ok(())
            }).expect("deserialize");
            let c = if s.bytes_out == buf.len() && r.bytes_in == buf.len() { "ok" } else { "bad" };
            let paths = paths.into_inner();
            let root = if paths.iter().any(|p| p.is_empty()) { ";r=1" } else { ";r=0" };
            ("for_each_path", format!("{};u={},{};c={}{}",
                show_paths(paths), s.bytes_in, r.bytes_out, c, root))
        }
        33 => {
            let (i, p, j, q) = (map_ix(d)?, d.path(6)?, map_ix(d)?, d.path(4)?);
            let (enc, file) = (d.modn(2)?, d.modn(2)?);
            let mut td = TmpDir::new("write_trie");
            let dir = td.dir.clone();
            let raw = td.file(RAW_HEX_DATA_FILENAME);
            let meta = td.file(META_DATA_FILENAME);
            let zc = td.file(ZERO_COMPRESSED_HEX_DATA_FILENAME);
            let rz = st.maps[i].read_zipper_at_path(&p);
            if enc == 0 {
                write_trie("mapfuzz", rz, enc_min, &dir)
            } else {
                write_trie("mapfuzz", rz, enc_raw, &dir)
            }.expect("write_trie");
            let src: &Path = if file == 0 { &zc } else { &raw };
            let m = match deserialize_file(src, dec_le) {
                Ok(m) => m,
                // The model never fails.  Rendered rather than unwrapped so the
                // divergence names itself (`write_trie_stale_tail_after_rollback`
                // is the known one) and leaves the maps alone.
                Err(e) => {
                    let why = if e.to_string().contains("<tag byte><space>") { "tag" } else { "other" };
                    let name = if p.is_empty() { "write_trie" } else { "write_trie_at" };
                    return Some((name, format!("err:{why}")));
                }
            };
            let meta = std::fs::read_to_string(&meta).unwrap_or_default();
            let v = format!("v{}", meta_field(&meta, "VAL_COUNT"));
            if p.is_empty() {
                st.maps[j].write_zipper_at_path(&q).graft_map(m);
                ("write_trie", format!("{},l{}", v, meta_field(&meta, "MAX_PATH_LEN")))
            } else {
                // Below the map root the result is only rendered, under its own
                // name: see `MapFuzz/Serial.lean` and
                // `write_trie_below_root_drops_prefix_bytes`.
                ("write_trie_at", format!("{};{}", v, dump(&mut m.read_zipper())))
            }
        }
        _ => ("nop", "-".to_string()),
    })
}
