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

fn free_slot(slots: &[Option<Slot>]) -> Option<usize> {
    slots.iter().position(|s| s.is_none())
}

/// Run one session's steps on `head`.  `depth` 0 may nest one more session
/// in a writer's `zipper_head`.
fn session<'t, H: ZipperCreation<'t, u64>>(head: &H, d: &mut Dec, depth: usize) -> Option<String> {
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
                if unchecked_clash(&slots, &p, writer, unchecked) {
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
                let k = d.modn(SLOTS)?;
                if slots[k].take().is_some() { "d".to_string() } else { "-".to_string() }
            }
            6 => {
                let (k, sub, rel, v) = (d.modn(SLOTS)?, d.modn(4)?, d.path(3)?, val(d)?);
                match &mut slots[k] {
                    Some(Slot { z: Zp::W(w), .. }) => {
                        w.reset();
                        w.descend_to(&rel);
                        let prune = v % 2 == 1;
                        match sub {
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
                let k = d.modn(SLOTS)?;
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
                let k = d.modn(SLOTS)?;
                match slots[k].take() {
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
                let k = d.modn(SLOTS)?;
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
                let k = d.modn(SLOTS)?;
                match &mut slots[k] {
                    Some(Slot { z: Zp::W(w), .. }) if depth == 0 => {
                        let sub = w.zipper_head();
                        let r = session(&sub, d, depth + 1)?;
                        drop(sub);
                        format!("[{r}]")
                    }
                    _ => "-".to_string(),
                }
            }
            _ => {
                let k = d.modn(SLOTS)?;
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

pub fn step(op: usize, d: &mut Dec, st: &mut MapState) -> StepResult {
    Some(match op {
        60 => {
            let (i, mode) = (map_ix(d)?, d.modn(3)?);
            let mut t = st.maps[i].clone();
            let ret = match mode {
                0 => {
                    let zh = t.zipper_head();
                    format!("m0 {}", session(&zh, d, 0)?)
                }
                1 => {
                    let base = d.path(4)?;
                    let zh = t.into_zipper_head(&base);
                    let r = session(&zh, d, 0);
                    t = zh.into_map();
                    format!("m1 {}", r?)
                }
                _ => {
                    let (r, f, post) = (d.path(3)?, d.path(3)?, d.u8()?);
                    let mut wz = t.write_zipper_at_path(&r);
                    wz.descend_to(&f);
                    let zh = wz.zipper_head();
                    let res = session(&zh, d, 0)?;
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
            st.maps[i] = t;
            ("head", ret)
        }
        _ => ("nop", "-".to_string()),
    })
}
