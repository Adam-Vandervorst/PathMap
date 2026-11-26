//! Util fuzzer, ops 0–29: `ByteMask`, `BitMask` for `ByteMask` and `[u64; 4]`,
//! and the other public items of `src/utils/mod.rs`.  Mirrors
//! `lean/PathMapModel/UtilFuzz/Mask.lean`, which documents each op's operands
//! and answer; the two must decode the same bytes the same way.
//!
//! Masks are built and rendered here with plain word arithmetic, never with
//! the crate's own methods, so a rendering cannot share a bug with the method
//! under test.  A mask renders as `{` + its member bytes in ascending order as
//! two hex digits each + `}`; the raw words as `w0.w1.w2.w3` in lowercase hex.

#![allow(deprecated)]

use core::ops::Bound;

use pathmap::ring::{AlgebraicResult, DistributiveLattice, Lattice};
use pathmap::utils::{
    empty_mask, find_prefix_overlap, BitMask, ByteMask, ByteMaskIter, ByteMaskRangeIter, IntoByteMaskIter,
};

use super::*;

type W = [u64; 4];

const EMPTY_W: W = [0; 4];

fn has(w: &W, b: u8) -> bool {
    (w[(b >> 6) as usize] >> (b & 63)) & 1 == 1
}

fn put(w: &mut W, b: u8) {
    w[(b >> 6) as usize] |= 1u64 << (b & 63);
}

fn of_bytes(bs: &[u8]) -> W {
    let mut w = EMPTY_W;
    for &b in bs {
        put(&mut w, b);
    }
    w
}

fn w_or(a: &W, b: &W) -> W {
    [a[0] | b[0], a[1] | b[1], a[2] | b[2], a[3] | b[3]]
}

fn w_and(a: &W, b: &W) -> W {
    [a[0] & b[0], a[1] & b[1], a[2] & b[2], a[3] & b[3]]
}

/// `{` + the member bytes, ascending, two hex digits each + `}`.  `showMask`.
fn show_w(w: &W) -> String {
    let mut s = String::from("{");
    for b in 0..=255u8 {
        if has(w, b) {
            let _ = write!(s, "{b:02x}");
        }
    }
    s.push('}');
    s
}

fn show(m: &ByteMask) -> String {
    show_w(&m.0)
}

/// The raw words, `w0.w1.w2.w3`, lowercase hex.  `showWords`.
fn show_words(w: &W) -> String {
    format!("{:x}.{:x}.{:x}.{:x}", w[0], w[1], w[2], w[3])
}

fn show_res(r: &AlgebraicResult<ByteMask>) -> String {
    show_alg_result(r, show)
}

fn show_res_w(r: &AlgebraicResult<W>) -> String {
    show_alg_result(r, show_w)
}

/// A mask operand.  `maskOperand` in `Mask.lean`:
/// `k := u8 % 4`;
/// * `0`: the bytes of a `maskBytes` operand;
/// * `1`: `n := u8 % 4` inclusive ranges, each two bytes `a b` (either order);
/// * `2`: the complement of a `maskBytes` operand;
/// * `3`: four words, low first, each `s := u8 % 4`: `0` zero, `1` all ones,
///   `2` a byte `b` repeated in all eight lanes, `3` `!0 << (b % 64)` for a byte `b`.
fn dec_mask(d: &mut Dec) -> Option<W> {
    match d.modn(4)? {
        0 => Some(of_bytes(&mask_bytes(d)?)),
        1 => {
            let n = d.modn(4)?;
            let mut w = EMPTY_W;
            for _ in 0..n {
                let a = d.u8()?;
                let b = d.u8()?;
                for x in a.min(b)..=a.max(b) {
                    put(&mut w, x);
                }
            }
            Some(w)
        }
        2 => {
            let w = of_bytes(&mask_bytes(d)?);
            Some([!w[0], !w[1], !w[2], !w[3]])
        }
        _ => {
            let mut w = EMPTY_W;
            for word in w.iter_mut() {
                *word = match d.modn(4)? {
                    0 => 0,
                    1 => !0,
                    2 => (d.u8()? as u64) * 0x0101_0101_0101_0101,
                    _ => !0u64 << (d.u8()? % 64),
                };
            }
            Some(w)
        }
    }
}

/// Two related mask operands, so that identities and subsets come up often.
/// `maskPair`: `a := mask`, `s := u8 % 5`, then `b` is
/// `0`: `a`; `1`: a fresh mask `c`; `2`: `a ∪ c`; `3`: `a ∩ c`; `4`: empty.
fn dec_pair(d: &mut Dec) -> Option<(W, W)> {
    let a = dec_mask(d)?;
    let b = match d.modn(5)? {
        0 => a,
        1 => dec_mask(d)?,
        2 => w_or(&a, &dec_mask(d)?),
        3 => w_and(&a, &dec_mask(d)?),
        _ => EMPTY_W,
    };
    Some((a, b))
}

/// Drain a byte iterator: `<hex,hex,...>;<one more next>` (`-` once fused).
/// Stops after 300 items, which no correct iterator reaches.
fn drain_bytes(mut it: impl Iterator<Item = u8>) -> String {
    let mut parts = Vec::new();
    for b in it.by_ref() {
        parts.push(format!("{b:02x}"));
        if parts.len() > 300 {
            break;
        }
    }
    format!("{};{}", parts.join(","), show_byte_opt(it.next()))
}

/// Drain a range iterator: `<aa-bb,...>;<one more next>`.
fn drain_ranges(mut it: ByteMaskRangeIter) -> String {
    let show_r = |r: core::ops::RangeInclusive<u8>| format!("{:02x}-{:02x}", r.start(), r.end());
    let mut parts = Vec::new();
    for r in it.by_ref() {
        parts.push(show_r(r));
        if parts.len() > 300 {
            break;
        }
    }
    format!("{};{}", parts.join(","), it.next().map_or("-".to_string(), show_r))
}

/// `skip:join-all-empty`, documented in `Mask.lean`: when every operand of
/// `join_all` is empty, `AlgebraicResult`'s contract allows both `None` (which
/// "should take precedence") and an `Identity` naming any of the (equal, empty)
/// arguments, and the crate's choice depends on the argument count's parity
/// (`lean/findings/u-mask.md`, M1).  Either allowed answer renders as the skip
/// token; anything else (an `Element`, an out-of-range identity bit) renders as
/// itself and diverges.
const SKIP_JOIN_ALL_EMPTY: &str = "skip:join-all-empty";

fn join_all_shown<V>(r: &AlgebraicResult<V>, n: usize, empty_union: bool, show: impl Fn(&V) -> String) -> String {
    let allowed = match r {
        AlgebraicResult::None => true,
        AlgebraicResult::Identity(m) => *m != 0 && *m >> n == 0,
        AlgebraicResult::Element(_) => false,
    };
    if empty_union && allowed { SKIP_JOIN_ALL_EMPTY.to_string() } else { show_alg_result(r, show) }
}

/// A `ByteMask::join_all` operand: `AsRef<ByteMask>` has no impl in the crate.
struct Wrap(ByteMask);

impl AsRef<ByteMask> for Wrap {
    fn as_ref(&self) -> &ByteMask {
        &self.0
    }
}

pub fn step(op: usize, d: &mut Dec) -> StepResult {
    let r: (&'static str, String) = match op {
        // `FromIterator<u8>`.
        0 => {
            let bs = mask_bytes(d)?;
            let m: ByteMask = bs.iter().copied().collect();
            ("bm_from_iter", show(&m))
        }
        // `From<u8>`, `ByteMask::subset`.
        1 => {
            let b = d.u8()?;
            ("bm_from_u8", format!("{} {}", show(&ByteMask::from(b)), show(&ByteMask::subset(b))))
        }
        // `ByteMask::from_range` at every `RangeBounds<u8>` shape, and
        // `From<Range<u8>>` / `From<RangeInclusive<u8>>`; `11`/`12` take
        // `a..=b` after iterating it to the end (empty).
        2 => {
            let k = d.modn(13)?;
            let a = d.u8()?;
            let b = d.u8()?;
            let exhausted = || {
                let mut r = a..=b;
                for _ in r.by_ref() {}
                r
            };
            let m = match k {
                0 => ByteMask::from_range(a..b),
                1 => ByteMask::from_range(a..=b),
                2 => ByteMask::from_range(a..),
                3 => ByteMask::from_range(..b),
                4 => ByteMask::from_range(..=b),
                5 => ByteMask::from_range(..),
                6 => ByteMask::from_range((Bound::Excluded(a), Bound::Included(b))),
                7 => ByteMask::from_range((Bound::Excluded(a), Bound::Excluded(b))),
                8 => ByteMask::from_range((Bound::Excluded(a), Bound::Unbounded)),
                9 => ByteMask::from(a..b),
                10 => ByteMask::from(a..=b),
                11 => ByteMask::from_range(exhausted()),
                _ => ByteMask::from(exhausted()),
            };
            ("bm_from_range", show(&m))
        }
        // The raw words through every conversion, and the equalities.
        3 => {
            let a = dec_mask(d)?;
            let b = if d.boolean()? { a } else { dec_mask(d)? };
            let m = ByteMask(a);
            let m2 = ByteMask::from(b);
            let w1 = m.into_inner();
            let w2: W = m.into();
            let w3: &W = m.as_ref();
            let w4: &W = core::borrow::Borrow::borrow(&m);
            let d0 = ByteMask::default();
            let ret = format!(
                "{} {} {} {} {} eq={}{}{}{} d={}",
                show_words(&w1),
                show_words(&w2),
                show_words(w3),
                show_words(w4),
                show(&m2),
                show_bool(m == m2),
                show_bool(m == m2.0),
                show_bool(m.0 == m2),
                show_bool(m.clone() == m),
                show(&d0),
            );
            ("bm_words", ret)
        }
        // `count_bits`, `is_empty_mask`.
        4 => {
            let w = dec_mask(d)?;
            let m = ByteMask(w);
            let ret = format!(
                "{} {} {} {}",
                m.count_bits(),
                show_bool(m.is_empty_mask()),
                w.count_bits(),
                show_bool(w.is_empty_mask())
            );
            ("bm_count", ret)
        }
        // `test_bit`.
        5 => {
            let w = dec_mask(d)?;
            let k = d.u8()?;
            ("bm_test_bit", format!("{}{}", show_bool(ByteMask(w).test_bit(k)), show_bool(w.test_bit(k))))
        }
        // `set_bit`, `clear_bit`, `toggle_bit`.
        6..=8 => {
            let w = dec_mask(d)?;
            let k = d.u8()?;
            let mut m = ByteMask(w);
            let mut v = w;
            let name = match op {
                6 => {
                    m.set_bit(k);
                    v.set_bit(k);
                    "bm_set_bit"
                }
                7 => {
                    m.clear_bit(k);
                    v.clear_bit(k);
                    "bm_clear_bit"
                }
                _ => {
                    m.toggle_bit(k);
                    v.toggle_bit(k);
                    "bm_toggle_bit"
                }
            };
            (name, format!("{} {}", show(&m), show_w(&v)))
        }
        // `make_empty`.
        9 => {
            let w = dec_mask(d)?;
            let mut m = ByteMask(w);
            let mut v = w;
            m.make_empty();
            v.make_empty();
            ("bm_make_empty", format!("{} {}", show(&m), show_w(&v)))
        }
        // `or`, `|` (owned and by reference), `|=`.
        10 => {
            let (a, b) = dec_pair(d)?;
            let (x, y) = (ByteMask(a), ByteMask(b));
            let mut z = x;
            z |= y;
            let ret = format!(
                "{} {} {} {} {}",
                show(&x.or(&y)),
                show_w(&a.or(&b)),
                show(&(x | y)),
                show(&(&x | &y)),
                show(&z)
            );
            ("bm_or", ret)
        }
        // `and`, `&` (owned and by reference), `&=`.
        11 => {
            let (a, b) = dec_pair(d)?;
            let (x, y) = (ByteMask(a), ByteMask(b));
            let mut z = x;
            z &= y;
            let ret = format!(
                "{} {} {} {} {}",
                show(&x.and(&y)),
                show_w(&a.and(&b)),
                show(&(x & y)),
                show(&(&x & &y)),
                show(&z)
            );
            ("bm_and", ret)
        }
        // `xor`, `^`, `^=`.
        12 => {
            let (a, b) = dec_pair(d)?;
            let (x, y) = (ByteMask(a), ByteMask(b));
            let mut z = x;
            z ^= y;
            let ret = format!("{} {} {} {}", show(&x.xor(&y)), show_w(&a.xor(&b)), show(&(x ^ y)), show(&z));
            ("bm_xor", ret)
        }
        // `andn`.
        13 => {
            let (a, b) = dec_pair(d)?;
            ("bm_andn", format!("{} {}", show(&ByteMask(a).andn(&ByteMask(b))), show_w(&a.andn(&b))))
        }
        // `BitMask::not`, `!`.
        14 => {
            let w = dec_mask(d)?;
            let m = ByteMask(w);
            ("bm_not", format!("{} {} {}", show(&BitMask::not(&m)), show_w(&BitMask::not(&w)), show(&!m)))
        }
        // `index_of`.
        15 => {
            let w = dec_mask(d)?;
            let b = d.u8()?;
            ("bm_index_of", ByteMask(w).index_of(b).to_string())
        }
        // `indexed_bit::<true>`, `indexed_bit::<false>`.  Index `i := u8`:
        // `i % 16` below 128 (sparse masks), else `2 * (i - 128)`.
        16 => {
            let w = dec_mask(d)?;
            let i = d.u8()? as usize;
            let i = if i < 128 { i % 16 } else { 2 * (i - 128) };
            let m = ByteMask(w);
            let ret = format!(
                "{} {}",
                show_byte_opt(m.indexed_bit::<true>(i)),
                show_byte_opt(m.indexed_bit::<false>(i))
            );
            ("bm_indexed_bit", ret)
        }
        // `next_bit`, `prev_bit`.
        17 => {
            let w = dec_mask(d)?;
            let b = d.u8()?;
            let m = ByteMask(w);
            ("bm_next_prev", format!("{} {}", show_byte_opt(m.next_bit(b)), show_byte_opt(m.prev_bit(b))))
        }
        // Every way to get a `ByteMaskIter`.
        18 => {
            let w = dec_mask(d)?;
            let m = ByteMask(w);
            let it: ByteMaskIter = match d.modn(7)? {
                0 => m.iter(),
                1 => ByteMaskIter::new(m),
                2 => ByteMaskIter::from(m),
                3 => ByteMaskIter::from(w),
                4 => m.byte_mask_iter(),
                5 => w.byte_mask_iter(),
                _ => (&w).byte_mask_iter(),
            };
            ("bm_iter", drain_bytes(it))
        }
        // Every way to get a `ByteMaskRangeIter`.
        19 => {
            let w = dec_mask(d)?;
            let m = ByteMask(w);
            let it: ByteMaskRangeIter = match d.modn(4)? {
                0 => m.range_iter(),
                1 => ByteMaskRangeIter::new(m),
                2 => ByteMaskRangeIter::from(m),
                _ => ByteMaskRangeIter::from(w),
            };
            ("bm_range_iter", drain_ranges(it))
        }
        // `set_` / `clear_` / `toggle_inclusive_bit_range`.  `k := u8 % 9`:
        // the op is `k % 3`; the range (`a b`), by `k / 3`: `0` put in order,
        // `1` `a..=b` as given (empty when `a > b`; a `debug_assert` in debug
        // builds, see the findings), `2` `a..=b` after iterating it to the end
        // (an exhausted, so empty, range).  The answer is tagged with the range
        // shape (`o`, `g`, `x`) so a KNOWN entry can name the exhausted one.
        20 => {
            let w = dec_mask(d)?;
            let k = d.modn(9)?;
            let a = d.u8()?;
            let b = d.u8()?;
            let r = match k / 3 {
                0 => a.min(b)..=a.max(b),
                1 => a..=b,
                _ => {
                    let mut r = a..=b;
                    for _ in r.by_ref() {}
                    r
                }
            };
            let mut m = ByteMask(w);
            match k % 3 {
                0 => m.set_inclusive_bit_range(r),
                1 => m.clear_inclusive_bit_range(r),
                _ => m.toggle_inclusive_bit_range(r),
            }
            ("bm_incl_range", format!("{} {}", ["o", "g", "x"][k / 3], show(&m)))
        }
        // `Debug for ByteMask`, plain or alternate (`{:#?}`); newlines as `\n`.
        21 => {
            let w = dec_mask(d)?;
            let m = ByteMask(w);
            let s = if d.boolean()? { format!("{m:#?}") } else { format!("{m:?}") };
            ("bm_debug", s.replace('\n', "\\n"))
        }
        // `fmt_binary`: `Debug` then `Display`.
        22 => {
            let w = dec_mask(d)?;
            let f = ByteMask(w).fmt_binary();
            ("bm_binary", format!("{f:?}|{f}"))
        }
        // `pjoin`, `pmeet`, `psubtract` on `ByteMask` and on `[u64; 4]`.
        23 => {
            let (a, b) = dec_pair(d)?;
            let (x, y) = (ByteMask(a), ByteMask(b));
            let ret = format!(
                "j={} m={} s={} J={} M={} S={}",
                show_res(&x.pjoin(&y)),
                show_res(&x.pmeet(&y)),
                show_res(&x.psubtract(&y)),
                show_res_w(&a.pjoin(&b)),
                show_res_w(&a.pmeet(&b)),
                show_res_w(&a.psubtract(&b)),
            );
            ("bm_lattice", ret)
        }
        // `Lattice::join_into` (the trait default) on `ByteMask` and `[u64; 4]`.
        24 => {
            let (a, b) = dec_pair(d)?;
            let mut x = ByteMask(a);
            let sx = x.join_into(ByteMask(b));
            let mut v = a;
            let sv = v.join_into(b);
            ("bm_join_into", format!("{} {} {} {}", show_status(sx), show(&x), show_status(sv), show_w(&v)))
        }
        // `Lattice::join_all` (the trait default): `[u64; 4]` over a slice of
        // `ByteMask` (through `AsRef<[u64; 4]>`), and `ByteMask` over `Wrap`s.
        // Operands: `n := u8 % 5`, then each `s := u8 % 5` relative to the
        // previous one `p` (empty for the first): `0` `p`, `1` a fresh mask,
        // `2` `p ∪ mask`, `3` empty, `4` `p ∩ mask`.
        25 => {
            let n = d.modn(5)?;
            let mut xs: Vec<W> = Vec::with_capacity(n);
            for _ in 0..n {
                let prev = xs.last().copied().unwrap_or(EMPTY_W);
                let x = match d.modn(5)? {
                    0 => prev,
                    1 => dec_mask(d)?,
                    2 => w_or(&prev, &dec_mask(d)?),
                    3 => EMPTY_W,
                    _ => w_and(&prev, &dec_mask(d)?),
                };
                xs.push(x);
            }
            let ms: Vec<ByteMask> = xs.iter().map(|&w| ByteMask(w)).collect();
            let ws: Vec<Wrap> = ms.iter().map(|&m| Wrap(m)).collect();
            let r1 = <W as Lattice>::join_all(&ms);
            let r2 = <ByteMask as Lattice>::join_all(&ws);
            let empty_union = n > 0 && xs.iter().all(|w| *w == EMPTY_W);
            let ret = format!(
                "{} {}",
                join_all_shown(&r1, n, empty_union, show_w),
                join_all_shown(&r2, n, empty_union, show)
            );
            ("bm_join_all", ret)
        }
        // The constants, `new`, `Default`, `empty_mask`, the iterators' `Debug`.
        26 => {
            let ret = format!(
                "E={} F={} n={} d={} e={} i={:?} r={:?}",
                show(&ByteMask::EMPTY),
                show(&ByteMask::FULL),
                show(&ByteMask::new()),
                show(&ByteMask::default()),
                show_words(&empty_mask()),
                ByteMask::FULL.iter(),
                ByteMask::FULL.range_iter(),
            );
            ("bm_consts", ret)
        }
        // `utils::find_prefix_overlap` (deprecated re-export of
        // `fast_slice_utils::find_prefix_overlap`).  `a` is `u8 % 72` path
        // bytes; `b` is `a`'s first `u8 % (|a| + 1)` bytes then `u8 % 40` more.
        27 => {
            let la = d.modn(72)?;
            let a = d.path_n(la)?;
            let k = d.modn(la + 1)?;
            let lt = d.modn(40)?;
            let mut b = a[..k].to_vec();
            b.extend(d.path_n(lt)?);
            ("prefix_overlap", find_prefix_overlap(&a, &b).to_string())
        }
        // A short program of in-place edits on one `ByteMask`: `n := u8 % 8`
        // steps, each `t := u8 % 10`: `0`/`1`/`2` set/clear/toggle bit `u8`;
        // `3`/`4`/`5` set/clear/toggle inclusive range `u8 u8` (put in order);
        // `6`/`7`/`8` `|=`/`&=`/`^=` a mask; `9` `m = !m`.
        28 => {
            let w = dec_mask(d)?;
            let n = d.modn(8)?;
            let mut m = ByteMask(w);
            for _ in 0..n {
                match d.modn(10)? {
                    0 => m.set_bit(d.u8()?),
                    1 => m.clear_bit(d.u8()?),
                    2 => m.toggle_bit(d.u8()?),
                    t @ 3..=5 => {
                        let a = d.u8()?;
                        let b = d.u8()?;
                        let r = a.min(b)..=a.max(b);
                        match t {
                            3 => m.set_inclusive_bit_range(r),
                            4 => m.clear_inclusive_bit_range(r),
                            _ => m.toggle_inclusive_bit_range(r),
                        }
                    }
                    6 => m |= ByteMask(dec_mask(d)?),
                    7 => m &= ByteMask(dec_mask(d)?),
                    8 => m ^= ByteMask(dec_mask(d)?),
                    _ => m = !m,
                }
            }
            ("bm_program", format!("{} {}", show(&m), m.count_bits()))
        }
        _ => ("nop", "-".to_string()),
    };
    Some(r)
}
