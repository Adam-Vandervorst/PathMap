//! Util fuzzer, ops 60–79: `utils/ints.rs` (`PathInteger` and the encodings /
//! range generator built on it).  Mirrors `UtilFuzz/Ints.lean`, which states
//! what each encoding means.
//!
//! Every op is instantiated for each `PathInteger` impl: `u8`, `u16`, `u32`,
//! `u64`, `usize`, `u128` (type index `t` in that order).
//!
//! | op | name | operands | answer |
//! |---|---|---|---|
//! | 60–65 | `bob_<ty>` | prefix `path(3)`, `cnt := u8 % 9`, `cnt` × `int` | `indices_to_bob` appended to the prefix: `steps;bytes;bob_to_indices(bytes)` |
//! | 66–71 | `weave_<ty>` | prefix `path(3)`, `cnt := u8 % 9`, `cnt` × `int(8)` (usize) | `indices_to_weave` appended to the prefix: `bytes;weave_to_indices(bytes)`; for `u128` only `prefix|<lower 8 byte positions>;skip:weave-u128-shift` |
//! | 72–77 | `unbob_<ty>` / `unweave_<ty>` | `bool` (1 = weave), then the encoded bytes (below) | the decoded integers |
//! | 78 | `range_<ty>` | `t := u8 % 6`, small range (below), `alloc := bool`, `v := u8` | the whole map: `[path:val,…];n=<locations>` |
//! | 79 | `range_big_<ty>` | `t := u8 % 6`, big range (below), `v := u8`, 3 × probe (below) | `c=<val_count>;f=[first 4];p=<val at each probe>` |
//!
//! `int` (`int(N)` for an `N`-byte type) reads `k := u8 % (N + 1)` and then `k`
//! bytes, big-endian: the value has at most `k` significant bytes.
//!
//! `unbob`: `cnt := u8 % 9`, `len := u8 % (8N + 1)`, `len` raw bytes.
//! `unweave`: `cnt := 1 + u8 % 8`, `steps := u8 % (N + 1)`, `cnt * steps` raw bytes.
//! (Both stay inside the decoders' domain: `bob_to_indices` asserts
//! `len <= 8N`; `weave_to_indices` has no such check, see the findings file.)
//!
//! Small range: `start := int`, `step := int` (0 read as 1), `k := u8 % 40`,
//! `r := u8 % step`, `stop := min(MAX, start + k*step + r)`; then `e := u8`, and
//! when `e % 8 == 0`, `stop := start - (e / 8 % 3)` (saturating at 0): an empty
//! range.  `alloc` picks `gen_int_range_in(.., global_alloc())`.
//!
//! Big range: `start := int`, `mode := u8 % 2`; mode 0: `step := 2^(u8 % 8N)`,
//! `cnt := int`; mode 1: `step := int` (0 read as 1), `cnt := int(2) % 4097`.
//! Then `r := int % step` and `stop := min(MAX, start + cnt*step + r)`: about
//! `cnt` elements.
//! (`gen_int_range` builds a range in time proportional to the distinct
//! sub-ranges it caches; a power-of-two step has O(levels) of them, an
//! arbitrary one can have millions.)  `val_count` is rendered only when the
//! element count is below 2^63 (`-` otherwise: it would overflow `usize`).
//! Probes: start, start + step, the last element, one step past it, stop - 1,
//! stop, then 3 read as `m := int % (count + 2)` (saturating), `δ := u8 % 3`:
//! `start + m*step` plus 0,
//! +1 or -1 by `δ` (saturating; every probe clamped to MAX).  Each renders the
//! value there or `-`.
//!
//! `step = 0` is never generated: `gen_int_range` loops forever on it for `u8`
//! and divides by zero for the wider types (an undocumented precondition).

use super::*;
use pathmap::utils::ints::*;
use pathmap::PathMap;
use pathmap::zipper::*;

const BOB: [&str; 6] = ["bob_u8", "bob_u16", "bob_u32", "bob_u64", "bob_usize", "bob_u128"];
const WEAVE: [&str; 6] = ["weave_u8", "weave_u16", "weave_u32", "weave_u64", "weave_usize", "weave_u128"];
const UNBOB: [&str; 6] = ["unbob_u8", "unbob_u16", "unbob_u32", "unbob_u64", "unbob_usize", "unbob_u128"];
const UNWEAVE: [&str; 6] = ["unweave_u8", "unweave_u16", "unweave_u32", "unweave_u64", "unweave_usize", "unweave_u128"];
const RANGE: [&str; 6] = ["range_u8", "range_u16", "range_u32", "range_u64", "range_usize", "range_u128"];
const RANGE_BIG: [&str; 6] = ["range_big_u8", "range_big_u16", "range_big_u32", "range_big_u64", "range_big_usize", "range_big_u128"];

/// Conversions the harness needs, without a `num-traits` dependency.
trait Conv: Copy {
    fn to_u128(self) -> u128;
    fn of_u128(x: u128) -> Self;
    fn zero() -> Self { Self::of_u128(0) }
    fn be(self) -> Vec<u8>;
}
macro_rules! conv {
    ($($t:ty),*) => {$(
        impl Conv for $t {
            fn to_u128(self) -> u128 { self as u128 }
            fn of_u128(x: u128) -> Self { x as $t }
            fn be(self) -> Vec<u8> { self.to_be_bytes().to_vec() }
        }
    )*};
}
conv!(u8, u16, u32, u64, usize, u128);

/// Instantiate the generic `$f::<N, T>(args)` for type index `$t`.
macro_rules! by_type {
    ($t:expr, $f:ident ( $($a:expr),* )) => {
        match $t {
            0 => $f::<1, u8>($($a),*),
            1 => $f::<2, u16>($($a),*),
            2 => $f::<4, u32>($($a),*),
            3 => $f::<8, u64>($($a),*),
            4 => $f::<8, usize>($($a),*),
            _ => $f::<16, u128>($($a),*),
        }
    };
}

fn max_of(n: usize) -> u128 {
    if n >= 16 { u128::MAX } else { (1u128 << (8 * n)) - 1 }
}

/// `int(N)`: `k := u8 % (N + 1)`, then `k` big-endian bytes.
fn int_n(d: &mut Dec, n: usize) -> Option<u128> {
    let k = d.modn(n + 1)?;
    let mut x: u128 = 0;
    for _ in 0..k {
        x = (x << 8) | d.u8()? as u128;
    }
    Some(x)
}

fn show_ints<T: Conv>(xs: &[T]) -> String {
    let v: Vec<String> = xs.iter().map(|x| x.to_u128().to_string()).collect();
    format!("[{}]", v.join(","))
}

fn bob_op<const N: usize, T: PathInteger<N> + Conv>(d: &mut Dec) -> Option<String> {
    let pre = d.path(3)?;
    let cnt = d.modn(9)?;
    let mut xs = Vec::with_capacity(cnt);
    for _ in 0..cnt {
        xs.push(T::of_u128(int_n(d, N)?));
    }
    let mut bob = pre.clone();
    let steps = indices_to_bob::<N, T>(&xs, &mut bob);
    let mut back = vec![<T as Conv>::zero(); cnt];
    bob_to_indices::<N, T>(&bob[pre.len()..], &mut back);
    Some(format!("{steps};{};{}", hex_path(&bob), show_ints(&back)))
}

fn weave_op<const N: usize, T: PathInteger<N> + Conv>(d: &mut Dec) -> Option<String> {
    let pre = d.path(3)?;
    let cnt = d.modn(9)?;
    let mut xs = Vec::with_capacity(cnt);
    for _ in 0..cnt {
        xs.push(int_n(d, 8)? as usize);
    }
    let mut weave = pre.clone();
    indices_to_weave::<N, T>(&xs, &mut weave);
    if N == 16 {
        // `skip:weave-u128-shift` (finding `weave_u128_shift_overflow`): the
        // upper 8 bytes of each integer are garbage, which would end the
        // comparison of every input at its first `weave_u128`.  The lower 8
        // byte positions (the second half) are still compared.
        let enc = &weave[pre.len()..];
        return Some(format!("{}|{};skip:weave-u128-shift", hex_path(&pre), hex_path(&enc[enc.len() / 2..])));
    }
    let mut back = vec![<T as Conv>::zero(); cnt];
    weave_to_indices::<N, T>(&weave[pre.len()..], &mut back);
    Some(format!("{};{}", hex_path(&weave), show_ints(&back)))
}

fn unbob_op<const N: usize, T: PathInteger<N> + Conv>(d: &mut Dec) -> Option<String> {
    let cnt = d.modn(9)?;
    let len = d.modn(8 * N + 1)?;
    let mut bob = Vec::with_capacity(len);
    for _ in 0..len {
        bob.push(d.u8()?);
    }
    let mut back = vec![<T as Conv>::zero(); cnt];
    bob_to_indices::<N, T>(&bob, &mut back);
    Some(show_ints(&back))
}

fn unweave_op<const N: usize, T: PathInteger<N> + Conv>(d: &mut Dec) -> Option<String> {
    let cnt = 1 + d.modn(8)?;
    let steps = d.modn(N + 1)?;
    let mut weave = Vec::with_capacity(cnt * steps);
    for _ in 0..cnt * steps {
        weave.push(d.u8()?);
    }
    let mut back = vec![<T as Conv>::zero(); cnt];
    weave_to_indices::<N, T>(&weave, &mut back);
    Some(show_ints(&back))
}

/// The element count of `start..stop` by `step` (`step >= 1`).
fn range_count(start: u128, stop: u128, step: u128) -> u128 {
    if start >= stop { 0 } else { (stop - start - 1) / step + 1 }
}

fn gen_range<const N: usize, T: PathInteger<N> + Conv>(start: u128, stop: u128, step: u128, v: u64, alloc: bool) -> PathMap<u64> {
    let (a, b, c) = (T::of_u128(start), T::of_u128(stop), T::of_u128(step));
    if alloc {
        gen_int_range_in(a, b, c, v, pathmap::alloc::global_alloc())
    } else {
        gen_int_range(a, b, c, v)
    }
}

fn range_op<const N: usize, T: PathInteger<N> + Conv>(d: &mut Dec) -> Option<String> {
    let max = max_of(N);
    let start = int_n(d, N)?;
    let step = int_n(d, N)?.max(1);
    let k = d.modn(40)? as u128;
    let r = d.u8()? as u128 % step;
    let mut stop = start.saturating_add(k.saturating_mul(step)).saturating_add(r).min(max);
    let e = d.u8()?;
    if e % 8 == 0 {
        stop = start.saturating_sub((e / 8 % 3) as u128);
    }
    let alloc = d.boolean()?;
    let v = d.u8()? as u64;
    let map = gen_range::<N, T>(start, stop, step, v, alloc);
    let mut out = String::new();
    for (i, (p, val)) in map.iter().enumerate() {
        if i > 0 { out.push(','); }
        let _ = write!(out, "{}:{val}", hex_path(&p));
    }
    let mut rz = map.read_zipper();
    let mut n = 0usize;
    while rz.to_next_step() { n += 1; }
    Some(format!("[{out}];n={n}"))
}

fn range_big_op<const N: usize, T: PathInteger<N> + Conv>(d: &mut Dec) -> Option<String> {
    let max = max_of(N);
    let start = int_n(d, N)?;
    let (step, cnt) = if d.modn(2)? == 0 {
        (1u128 << d.modn(8 * N)?, int_n(d, N)?)
    } else {
        (int_n(d, N)?.max(1), int_n(d, 2)? % 4097)
    };
    let r = int_n(d, N)? % step;
    let stop = start.saturating_add(cnt.saturating_mul(step)).saturating_add(r).min(max);
    let v = d.u8()? as u64;
    let count = range_count(start, stop, step);
    let mut probes = Vec::new();
    for _ in 0..3 {
        let m = int_n(d, N)? % count.saturating_add(2);
        let q = start.saturating_add(m.saturating_mul(step));
        probes.push(match d.modn(3)? { 0 => q, 1 => q.saturating_add(1), _ => q.saturating_sub(1) });
    }
    let map = gen_range::<N, T>(start, stop, step, v, false);
    let c = if count < (1u128 << 63) { map.val_count().to_string() } else { "-".to_string() };
    let first: Vec<String> = map.iter().take(4).map(|(p, val)| format!("{}:{val}", hex_path(&p))).collect();
    let mut qs = vec![start, start.saturating_add(step)];
    let last = if count > 0 { start + (count - 1) * step } else { start };
    qs.push(last);
    qs.push(last.saturating_add(step));
    qs.push(stop.saturating_sub(1));
    qs.push(stop);
    qs.extend(probes);
    let hits: Vec<String> = qs.into_iter().map(|q| show_val(map.val_at(T::of_u128(q.min(max)).be()))).collect();
    Some(format!("c={c};f=[{}];p={}", first.join(","), hits.join(",")))
}

pub fn step(op: usize, d: &mut Dec) -> StepResult {
    let r = match op {
        60..=65 => {
            let t = op - 60;
            (BOB[t], by_type!(t, bob_op(d))?)
        }
        66..=71 => {
            let t = op - 66;
            (WEAVE[t], by_type!(t, weave_op(d))?)
        }
        72..=77 => {
            let t = op - 72;
            if d.boolean()? {
                (UNWEAVE[t], by_type!(t, unweave_op(d))?)
            } else {
                (UNBOB[t], by_type!(t, unbob_op(d))?)
            }
        }
        78 => {
            let t = d.modn(6)?;
            (RANGE[t], by_type!(t, range_op(d))?)
        }
        79 => {
            let t = d.modn(6)?;
            (RANGE_BIG[t], by_type!(t, range_big_op(d))?)
        }
        _ => ("nop", "-".to_string()),
    };
    Some(r)
}
