//! Map fuzzer, ops 60–69: ZipperHead sessions.  Mirrors `MapFuzz/Head.lean`,
//! which documents the session language, the conflict rules and the trace.
//!
//! A session runs on a clone of `m[i]` and is committed back only when it was
//! decoded to the end, so an input that runs out mid-session leaves the maps as
//! they were on both sides.

use core::cell::RefCell;
use pathmap::zipper::*;

use super::*;

/// Skip token: the open would conflict with a live `_unchecked` zipper.  Those
/// are untracked in release builds, so the crate cannot see the conflict, and
/// the caller promised there would be none; making it would be undefined
/// behaviour, not a test.
pub const SKIP_UNCHECKED_CONFLICT: &str = "skip:unchecked-conflict";
/// Skip token: `into_read_zipper` on an `_unchecked` writer, which unwraps the
/// writer's (absent in release) tracker and panics.  See lean/findings/map-morph.md.
pub const SKIP_UNCHECKED_INTO_READ: &str = "skip:unchecked-into-read";

/// Skip token: a reader opened from a head whose root path does not exist
/// creates that path (it should create nothing; `zipper_headf` says so for the
/// map root).  The stray dangling path would contaminate everything after, so
/// such opens are skipped.  See lean/findings/map-morph.md.
pub const SKIP_HEAD_ROOT_ABSENT: &str = "skip:head-root-absent";

/// Skip token: `cleanup_write_zipper` on a head made from a write zipper whose
/// focus is below its root.  It resolves the child's path against the parent's
/// *root* rather than its focus (where the child was created), prunes or panics
/// there, and resets the parent.  See lean/findings/map-morph.md.
pub const SKIP_CLEANUP_OFF_ROOT: &str = "skip:cleanup-off-root";

/// Skip token: `remove_val` / `remove_branches` with `prune` at a writer focus
/// that does not exist.  The model makes that a no-op; a stump left by a dropped
/// writer (H4 in lean/findings/map-morph.md) is pruned from below instead.
pub const SKIP_PRUNE_ABSENT_FOCUS: &str = "skip:prune-absent-focus";

/// Slots per session; `slotCap` in `Head.lean`.
const SLOTS: usize = 8;

/// Owns the paths that `read_zipper_at_borrowed_path` readers borrow, for the
/// length of a session.  Boxed slices never move, so a reference handed out
/// stays valid while later paths are pushed.
struct Arena(RefCell<Vec<Box<[u8]>>>);

impl Arena {
    fn alloc(&self, p: Vec<u8>) -> &[u8] {
        let b = p.into_boxed_slice();
        let ptr: *const [u8] = &*b;
        self.0.borrow_mut().push(b);
        // SAFETY: the box is owned by the arena until the arena drops, and is
        // never mutated or removed before then.
        unsafe { &*ptr }
    }
}

enum Zp<'a, 'p> {
    R(ReadZipperTracked<'a, 'p, u64>),
    W(WriteZipperTracked<'a, 'static, u64>),
}

struct Slot<'a, 'p> {
    z: Zp<'a, 'p>,
    /// Path relative to the head.
    path: Vec<u8>,
    unchecked: bool,
}

fn is_prefix(a: &[u8], b: &[u8]) -> bool {
    b.starts_with(a)
}

/// The harness's own rule for `_unchecked` zippers (`uncheckedClash`).
fn unchecked_clash(slots: &[Option<Slot>], p: &[u8], writer: bool, unchecked: bool) -> bool {
    slots.iter().flatten().any(|s| {
        (unchecked || s.unchecked)
            && (writer || matches!(s.z, Zp::W(_)))
            && (is_prefix(&s.path, p) || is_prefix(p, &s.path))
    })
}

/// `Conflict` is not nameable without the `zipper_tracking` feature, so it is
/// rendered from its `Display` text and its `path()`.
fn show_conflict(msg: &str, path: &[u8]) -> String {
    let with = if msg.contains("write zipper") {
        "W".to_string()
    } else if let Some(i) = msg.find("arity: ") {
        let n: String = msg[i + 7..].chars().take_while(|c| c.is_ascii_digit()).collect();
        format!("R{n}")
    } else {
        format!("?{msg}")
    };
    format!("C:{with}@{}", hex_path(path))
}

/// The slot a step names: byte `k` picks among the live slots (live writers,
/// for a writer-only step) in slot order; with none, slot 0, which the step then
/// finds empty or of the wrong kind.  `pick` in `Head.lean`.
fn pick(slots: &[Option<Slot>], k: u8, writers: bool) -> usize {
    let live: Vec<usize> = (0..slots.len())
        .filter(|&i| matches!(&slots[i], Some(s) if !writers || matches!(s.z, Zp::W(_))))
        .collect();
    if live.is_empty() { 0 } else { live[k as usize % live.len()] }
}

fn free_slot(slots: &[Option<Slot>]) -> Option<usize> {
    slots.iter().position(|s| s.is_none())
}

/// Run one session's steps on `head`.  `depth` 0 may nest one more session
/// in a writer's `zipper_head`.
///
/// `base_exists`: whether the head's root path exists in the map.  It starts as
/// the caller found it and becomes true when a writer is opened (which creates
/// its path, and so the root's); nothing in a session can remove the root.
///
/// `cleanup_ok`: false for a head taken from a write zipper whose focus is not
/// its root, where `cleanup_write_zipper` is skipped (`SKIP_CLEANUP_OFF_ROOT`).
fn session<'t, H: ZipperCreation<'t, u64>>(head: &H, d: &mut Dec, depth: usize, mut base_exists: bool, cleanup_ok: bool) -> Option<String> {
    let n = d.modn(if depth == 0 { 10 } else { 6 })?;
    let arena = Arena(RefCell::new(vec![]));
    let mut slots: Vec<Option<Slot>> = (0..SLOTS).map(|_| None).collect();
    let mut buffer: Option<WriteZipperBuffer<u64>> = None;
    let mut out: Vec<String> = vec![];
    for _ in 0..n {
        let kind = d.modn(12)?;
        let r: String = match kind {
            0..=4 => {
                let (writer, unchecked) = match kind {
                    0 | 1 => (false, false),
                    2 | 3 => (true, false),
                    _ => (d.boolean()?, true),
                };
                let p = d.path(5)?;
                if !writer && !base_exists {
                    SKIP_HEAD_ROOT_ABSENT.to_string()
                } else if unchecked_clash(&slots, &p, writer, unchecked) {
                    SKIP_UNCHECKED_CONFLICT.to_string()
                } else if let Some(ix) = free_slot(&slots) {
                    let z: Result<Zp, _> = match kind {
                        0 => head.read_zipper_at_path(&p).map(Zp::R),
                        1 => head.read_zipper_at_borrowed_path(arena.alloc(p.clone())).map(Zp::R),
                        2 => head.write_zipper_at_exclusive_path(&p).map(Zp::W),
                        3 => match buffer.take() {
                            Some(b) => head.write_zipper_at_exclusive_path_with_buffer(&p, b).map(Zp::W),
                            None => head.write_zipper_at_exclusive_path(&p).map(Zp::W),
                        },
                        // SAFETY: `unchecked_clash` ruled out every conflict with a live
                        // zipper, and checked opens that would conflict with this one are
                        // skipped the same way while it lives.
                        _ => Ok(if writer {
                            Zp::W(unsafe { head.write_zipper_at_exclusive_path_unchecked(&p) })
                        } else {
                            Zp::R(unsafe { head.read_zipper_at_path_unchecked(&p) })
                        }),
                    };
                    match z {
                        Ok(z) => {
                            base_exists |= writer;
                            slots[ix] = Some(Slot { z, path: p, unchecked });
                            format!("o{ix}")
                        }
                        Err(c) => show_conflict(&format!("{c}"), c.path()),
                    }
                } else {
                    "full".to_string()
                }
            }
            5 => {
                let k = pick(&slots, d.u8()?, false);
                if slots[k].take().is_some() { "d".to_string() } else { "-".to_string() }
            }
            6 => {
                let (k, sub, rel, v) = (pick(&slots, d.u8()?, true), d.modn(4)?, d.path(3)?, val(d)?);
                match &mut slots[k] {
                    Some(Slot { z: Zp::W(w), .. }) => {
                        w.reset();
                        w.descend_to(&rel);
                        let prune = v % 2 == 1;
                        match sub {
                            1 | 2 if prune && !w.path_exists() => SKIP_PRUNE_ABSENT_FOCUS.to_string(),
                            0 => format!("s{}", show_val(w.set_val(v).as_ref())),
                            1 => format!("r{}", show_val(w.remove_val(prune).as_ref())),
                            2 => format!("b{}", show_bool(w.remove_branches(prune))),
                            _ => format!("c{}", show_bool(w.create_path())),
                        }
                    }
                    _ => "-".to_string(),
                }
            }
            7 => {
                let k = pick(&slots, d.u8()?, false);
                match &mut slots[k] {
                    Some(Slot { z: Zp::R(z), .. }) => {
                        z.reset();
                        format!("e{}[{}]", show_bool(z.path_exists()), dump(z))
                    }
                    Some(Slot { z: Zp::W(z), .. }) => {
                        z.reset();
                        format!("e{}[{}]", show_bool(z.path_exists()), dump(z))
                    }
                    None => "-".to_string(),
                }
            }
            8 => {
                let k = pick(&slots, d.u8()?, true);
                match slots[k].take() {
                    Some(s @ Slot { z: Zp::W(_), .. }) if !cleanup_ok => {
                        slots[k] = Some(s);
                        SKIP_CLEANUP_OFF_ROOT.to_string()
                    }
                    Some(Slot { z: Zp::W(w), .. }) => {
                        head.cleanup_write_zipper(w);
                        "cl".to_string()
                    }
                    other => {
                        slots[k] = other;
                        "-".to_string()
                    }
                }
            }
            9 => {
                let k = pick(&slots, d.u8()?, false);
                match slots[k].take() {
                    Some(Slot { z: Zp::W(w), path, unchecked: false }) => {
                        slots[k] = Some(Slot { z: Zp::R(w.into_read_zipper()), path, unchecked: false });
                        "cv".to_string()
                    }
                    Some(s @ Slot { z: Zp::W(_), unchecked: true, .. }) => {
                        slots[k] = Some(s);
                        SKIP_UNCHECKED_INTO_READ.to_string()
                    }
                    Some(Slot { z: Zp::R(rz), path, unchecked }) => {
                        let copy = rz.clone();
                        slots[k] = Some(Slot { z: Zp::R(rz), path: path.clone(), unchecked });
                        match free_slot(&slots) {
                            Some(ix) => {
                                slots[ix] = Some(Slot { z: Zp::R(copy), path, unchecked });
                                format!("k{ix}")
                            }
                            None => "full".to_string(),
                        }
                    }
                    None => "-".to_string(),
                }
            }
            10 => {
                let k = pick(&slots, d.u8()?, true);
                match &mut slots[k] {
                    Some(Slot { z: Zp::W(w), .. }) if depth == 0 => {
                        let exists = w.path_exists();
                        let at_root = w.path().is_empty();
                        let sub = w.zipper_head();
                        let r = session(&sub, d, depth + 1, exists, at_root)?;
                        drop(sub);
                        format!("[{r}]")
                    }
                    _ => "-".to_string(),
                }
            }
            _ => {
                let k = pick(&slots, d.u8()?, true);
                match slots[k].take() {
                    Some(Slot { z: Zp::W(w), .. }) => {
                        buffer = Some(w.into_zipper_buffer());
                        "buf".to_string()
                    }
                    other => {
                        slots[k] = other;
                        "-".to_string()
                    }
                }
            }
        };
        out.push(r);
    }
    for s in slots.iter_mut() {
        drop(s.take());
    }
    Some(out.join(" "))
}

/// Rebuild `t` from scratch, location by location (`set_val_at` for a value,
/// `create_path` for a dangling leaf).  The identity on the trie's meaning, so
/// the model does nothing here.  A session leaves representation behind that
/// later ops mishandle, each a separate finding in lean/findings/map-morph.md:
/// a writer dropped without `cleanup_write_zipper` leaves an empty
/// `CellByteNode` stump that `remove` *below* it prunes
/// (`head_stump_pruned_by_remove_below`), and a reader opened from a head whose
/// root is a leaf leaves an empty node there that keeps `remove(root)` from
/// pruning (`head_reader_empty_node_blocks_prune`).  Left in place, they would
/// surface in every later op that touches the map.
fn rebuild(t: &mut PathMap<u64>) {
    let mut fresh = PathMap::<u64>::new();
    {
        let mut z = t.read_zipper();
        if let Some(v) = z.val() {
            fresh.set_val_at([], *v);
        }
        while z.to_next_step() {
            match z.val() {
                Some(v) => {
                    fresh.set_val_at(z.path(), *v);
                }
                None if z.child_count() == 0 => {
                    fresh.create_path(z.path());
                }
                None => {}
            }
        }
    }
    *t = fresh;
}

pub fn step(op: usize, d: &mut Dec, st: &mut MapState) -> StepResult {
    Some(match op {
        60 => {
            let (i, mode) = (map_ix(d)?, d.modn(3)?);
            let mut t = st.maps[i].clone();
            let ret = match mode {
                0 => {
                    let zh = t.zipper_head();
                    format!("m0 {}", session(&zh, d, 0, true, true)?)
                }
                1 => {
                    let base = d.path(4)?;
                    let exists = t.read_zipper_at_path(&base).path_exists();
                    let zh = t.into_zipper_head(&base);
                    let r = session(&zh, d, 0, exists, true);
                    t = zh.into_map();
                    format!("m1 {}", r?)
                }
                _ => {
                    let (r, f, post) = (d.path(3)?, d.path(3)?, d.u8()?);
                    let mut wz = t.write_zipper_at_path(&r);
                    wz.descend_to(&f);
                    let exists = wz.path_exists();
                    let zh = wz.zipper_head();
                    let res = session(&zh, d, 0, exists, f.is_empty())?;
                    drop(zh);
                    let post_r = if post % 2 == 1 {
                        wz.descend_to_byte((post >> 1) % 4);
                        show_val(wz.set_val((post >> 3) as u64).as_ref())
                    } else {
                        "-".to_string()
                    };
                    format!("m2 {res} post={post_r}")
                }
            };
            rebuild(&mut t);
            st.maps[i] = t;
            ("head", ret)
        }
        _ => ("nop", "-".to_string()),
    })
}
