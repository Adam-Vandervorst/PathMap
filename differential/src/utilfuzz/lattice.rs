//! Util fuzzer, ops 30–59: `ring.rs`: the `Lattice` / `DistributiveLattice`
//! impls, `LatticeRef` / `DistributiveLatticeRef`, `AlgebraicResult`,
//! `AlgebraicStatus`, `SetLattice`.  Mirrors `UtilFuzz/Lattice.lean`, which
//! states what every answer means; this file only decodes, calls the crate and
//! renders.
//!
//! Value operands come from a fixed table of concrete types (`lty!`, and
//! `dty!` for the ones that are also a `DistributiveLattice`); the index is the
//! first operand byte.  Each type implements [`Val`]: its decoder, its
//! rendering, and two facts the meet-swap skip needs (see [`SKIP_MEET_SWAP`]).
//!
//! Op lines: `<i> <op> ret=<type> <operands...> <answer>`.

use super::*;
use pathmap::ring::*;
use std::collections::{HashMap, HashSet};

/// `SetLattice`'s `pmeet` (the `set_lattice!` macro, so `HashMap`/`HashSet`)
/// hands each shared key's values to the value type's `pmeet` with the
/// operands **swapped** whenever `self` is not the smaller set
/// (`smaller.pmeet(larger)`).  For a value type whose `pmeet` is not symmetric
/// (the integers' left projection, `bool`'s single identity bit, ...) the
/// answer then comes from the wrong operand.  A crate bug
/// (`lean/findings/u-lattice.md`, L1); it fires on most map meets, so the
/// meet ops render this token instead when it could (`Val::hazard`), unless
/// the op's `full` byte is 255.  Same token and condition in `Lattice.lean`.
pub const SKIP_MEET_SWAP: &str = "skip:setlattice-meet-swap";

/// `skip:join-all-empty`: the token and rule of `utilfuzz/mask.rs` (u-mask's
/// M1, `lean/findings/u-mask.md`), applied to every type's default
/// `join_all`: over all-bottom arguments the answer depends on the
/// argument count's parity, and both answers are allowed.
pub const SKIP_JOIN_ALL_EMPTY: &str = "skip:join-all-empty";

/// An integer operand: small (`b % 4`, so operands collide) below 224, else a
/// spread value.  `intOfByte` in `Lattice.lean`; callers truncate (`as uN`).
fn int_byte(b: u8) -> u64 {
    if b < 224 { (b % 4) as u64 } else { (b as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) }
}

/// A value-table type: decoder, rendering, and the meet-swap facts.
pub trait Val: Lattice + Clone + Sized {
    fn name() -> String;
    /// `pmeet(b, a)` is always `pmeet(a, b).invert_identity()`.
    const MEET_SYM: bool;
    fn dec(d: &mut Dec) -> Option<Self>;
    fn show(&self) -> String;
    /// Could `SetLattice`'s operand swap (see [`SKIP_MEET_SWAP`]) change the
    /// answer of `self.pmeet(other)`?
    fn hazard(_a: &Self, _b: &Self) -> bool { false }
}

impl Val for () {
    fn name() -> String { "unit".into() }
    const MEET_SYM: bool = true;
    fn dec(_d: &mut Dec) -> Option<Self> { Some(()) }
    fn show(&self) -> String { "()".into() }
}

impl Val for bool {
    fn name() -> String { "bool".into() }
    const MEET_SYM: bool = false;
    fn dec(d: &mut Dec) -> Option<Self> { Some(d.u8()? % 2 == 1) }
    fn show(&self) -> String { if *self { "true".into() } else { "false".into() } }
}

macro_rules! int_val {
    ($t:ty, $n:expr) => {
        impl Val for $t {
            fn name() -> String { $n.into() }
            const MEET_SYM: bool = false;
            fn dec(d: &mut Dec) -> Option<Self> { Some(int_byte(d.u8()?) as $t) }
            fn show(&self) -> String { format!("{self}") }
        }
    };
}
int_val!(u8, "u8");
int_val!(u16, "u16");
int_val!(u32, "u32");
int_val!(u64, "u64");
int_val!(usize, "usize");

impl<T: Val> Val for Option<T> {
    fn name() -> String { format!("opt<{}>", T::name()) }
    const MEET_SYM: bool = T::MEET_SYM;
    fn dec(d: &mut Dec) -> Option<Self> {
        if d.u8()? % 4 == 0 { Some(None) } else { Some(Some(T::dec(d)?)) }
    }
    fn show(&self) -> String {
        match self { None => "None".into(), Some(v) => format!("Some({})", v.show()) }
    }
    fn hazard(a: &Self, b: &Self) -> bool {
        match (a, b) { (Some(a), Some(b)) => T::hazard(a, b), _ => false }
    }
}

impl<T: Val> Val for Box<T> {
    fn name() -> String { format!("box<{}>", T::name()) }
    const MEET_SYM: bool = T::MEET_SYM;
    fn dec(d: &mut Dec) -> Option<Self> { Some(Box::new(T::dec(d)?)) }
    fn show(&self) -> String { self.as_ref().show() }
    fn hazard(a: &Self, b: &Self) -> bool { T::hazard(a, b) }
}

impl Val for HashSet<u8> {
    fn name() -> String { "set".into() }
    const MEET_SYM: bool = true;
    fn dec(d: &mut Dec) -> Option<Self> {
        let n = d.modn(6)?;
        let mut s = HashSet::new();
        for _ in 0..n { s.insert(d.u8()? % 8); }
        Some(s)
    }
    fn show(&self) -> String {
        let mut v: Vec<u8> = self.iter().copied().collect();
        v.sort();
        let v: Vec<String> = v.iter().map(|b| b.to_string()).collect();
        format!("{{{}}}", v.join(","))
    }
}

impl<T: Val> Val for HashMap<u8, T> {
    fn name() -> String { format!("map<{}>", T::name()) }
    const MEET_SYM: bool = T::MEET_SYM;
    fn dec(d: &mut Dec) -> Option<Self> {
        let n = d.modn(5)?;
        let mut m = HashMap::new();
        for _ in 0..n {
            let k = d.u8()? % 6;
            let v = T::dec(d)?;
            m.insert(k, v);
        }
        Some(m)
    }
    fn show(&self) -> String {
        let mut ks: Vec<&u8> = self.keys().collect();
        ks.sort();
        let v: Vec<String> = ks.iter().map(|k| format!("{}:{}", k, self[*k].show())).collect();
        format!("{{{}}}", v.join(","))
    }
    fn hazard(a: &Self, b: &Self) -> bool {
        let shared: Vec<&u8> = a.keys().filter(|k| b.contains_key(*k)).collect();
        !T::MEET_SYM
            && !shared.is_empty()
            && (a.len() >= b.len()
                || shared.iter().any(|k| T::hazard(&a[*k], &b[*k]) || T::hazard(&b[*k], &a[*k])))
    }
}

/// The `Lattice` value table.  `ltys` in `Lattice.lean`, same order.
pub const N_LTY: usize = 24;
macro_rules! lty {
    ($i:expr, $f:ident ( $($arg:expr),* )) => {
        match $i {
            0 => $f::<()>($($arg),*),
            1 => $f::<bool>($($arg),*),
            2 => $f::<u8>($($arg),*),
            3 => $f::<u16>($($arg),*),
            4 => $f::<u32>($($arg),*),
            5 => $f::<u64>($($arg),*),
            6 => $f::<usize>($($arg),*),
            7 => $f::<Option<()>>($($arg),*),
            8 => $f::<Option<bool>>($($arg),*),
            9 => $f::<Option<u64>>($($arg),*),
            10 => $f::<Option<Option<bool>>>($($arg),*),
            11 => $f::<Option<Option<u64>>>($($arg),*),
            12 => $f::<Box<u64>>($($arg),*),
            13 => $f::<Box<Option<bool>>>($($arg),*),
            14 => $f::<HashSet<u8>>($($arg),*),
            15 => $f::<HashMap<u8, ()>>($($arg),*),
            16 => $f::<HashMap<u8, bool>>($($arg),*),
            17 => $f::<HashMap<u8, u64>>($($arg),*),
            18 => $f::<HashMap<u8, HashSet<u8>>>($($arg),*),
            19 => $f::<HashMap<u8, Option<u64>>>($($arg),*),
            20 => $f::<Option<HashSet<u8>>>($($arg),*),
            21 => $f::<Box<HashMap<u8, u16>>>($($arg),*),
            22 => $f::<HashMap<u8, HashMap<u8, bool>>>($($arg),*),
            _ => $f::<HashMap<u8, u8>>($($arg),*),
        }
    };
}

/// The `DistributiveLattice` value table.  `dtys` in `Lattice.lean`.
pub const N_DTY: usize = 20;
macro_rules! dty {
    ($i:expr, $f:ident ( $($arg:expr),* )) => {
        match $i {
            0 => $f::<()>($($arg),*),
            1 => $f::<bool>($($arg),*),
            2 => $f::<u16>($($arg),*),
            3 => $f::<u64>($($arg),*),
            4 => $f::<Option<()>>($($arg),*),
            5 => $f::<Option<bool>>($($arg),*),
            6 => $f::<Option<u64>>($($arg),*),
            7 => $f::<Option<Option<bool>>>($($arg),*),
            8 => $f::<Option<Option<u64>>>($($arg),*),
            9 => $f::<Box<u64>>($($arg),*),
            10 => $f::<Box<Option<bool>>>($($arg),*),
            11 => $f::<HashSet<u8>>($($arg),*),
            12 => $f::<HashMap<u8, ()>>($($arg),*),
            13 => $f::<HashMap<u8, bool>>($($arg),*),
            14 => $f::<HashMap<u8, u64>>($($arg),*),
            15 => $f::<HashMap<u8, HashSet<u8>>>($($arg),*),
            16 => $f::<HashMap<u8, Option<u64>>>($($arg),*),
            17 => $f::<Option<HashSet<u8>>>($($arg),*),
            18 => $f::<Box<HashMap<u8, u16>>>($($arg),*),
            _ => $f::<HashMap<u8, HashMap<u8, bool>>>($($arg),*),
        }
    };
}

fn show_opt_val<T: Val>(o: &Option<T>) -> String { o.show() }

// ---- value-level lattice ops -------------------------------------------------

fn op_pjoin<T: Val>(d: &mut Dec) -> Option<String> {
    let a = T::dec(d)?;
    let b = T::dec(d)?;
    let r = a.pjoin(&b);
    Some(format!("{} {} {} {}", T::name(), a.show(), b.show(), show_alg_result(&r, T::show)))
}

/// `pmeet`; `full` = no meet-swap skip.
fn op_pmeet<T: Val>(d: &mut Dec, full: bool) -> Option<String> {
    let a = T::dec(d)?;
    let b = T::dec(d)?;
    let r = if !full && T::hazard(&a, &b) {
        SKIP_MEET_SWAP.to_string()
    } else {
        show_alg_result(&a.pmeet(&b), T::show)
    };
    Some(format!("{} {} {} {}", T::name(), a.show(), b.show(), r))
}

fn op_psub<T: Val + DistributiveLattice>(d: &mut Dec) -> Option<String> {
    let a = T::dec(d)?;
    let b = T::dec(d)?;
    let r = a.psubtract(&b);
    Some(format!("{} {} {} {}", T::name(), a.show(), b.show(), show_alg_result(&r, T::show)))
}

fn op_join_into<T: Val>(d: &mut Dec) -> Option<String> {
    let a = T::dec(d)?;
    let b = T::dec(d)?;
    let mut x = a.clone();
    let st = x.join_into(b.clone());
    Some(format!("{} {} {} {:?} {}", T::name(), a.show(), b.show(), st, x.show()))
}

fn op_join_all<T: Val>(d: &mut Dec) -> Option<String> {
    let n = d.modn(5)?;
    let mut xs: Vec<Box<T>> = Vec::with_capacity(n);
    for _ in 0..n { xs.push(Box::new(T::dec(d)?)); }
    let r = <T as Lattice>::join_all(&xs[..]);
    let shown: Vec<String> = xs.iter().map(|x| x.show()).collect();
    // `skip:join-all-empty` (u-mask's M1, same token and rule): every
    // argument is a bottom (its self-join annihilates) and the answer is one
    // the contract allows, `None` or an identity of in-range arguments.
    let all_bot = n > 0 && xs.iter().all(|x| x.pjoin(x).is_none());
    let allowed = match &r {
        AlgebraicResult::None => true,
        AlgebraicResult::Identity(m) => *m != 0 && *m >> n == 0,
        AlgebraicResult::Element(_) => false,
    };
    let rs = if all_bot && allowed { SKIP_JOIN_ALL_EMPTY.to_string() } else { show_alg_result(&r, T::show) };
    Some(format!("{} [{}] {}", T::name(), shown.join(","), rs))
}

/// `LatticeRef` on `&V` (mode 0 join, 1 meet) and `Option<&V>` (2, 3).
fn op_lref<T: Val>(d: &mut Dec, mode: usize) -> Option<String> {
    let r = match mode {
        0 | 1 => {
            let a = T::dec(d)?;
            let b = T::dec(d)?;
            let (ra, rb) = (&a, &b);
            let r = if mode == 0 {
                show_alg_result(&LatticeRef::pjoin(&ra, &rb), T::show)
            } else if T::hazard(&a, &b) {
                SKIP_MEET_SWAP.to_string()
            } else {
                show_alg_result(&LatticeRef::pmeet(&ra, &rb), T::show)
            };
            format!("{} {} {} {}", T::name(), a.show(), b.show(), r)
        }
        _ => {
            let a = <Option<T>>::dec(d)?;
            let b = <Option<T>>::dec(d)?;
            let (ra, rb) = (a.as_ref(), b.as_ref());
            let r = if mode == 2 {
                show_alg_result(&LatticeRef::pjoin(&ra, &rb), show_opt_val)
            } else if <Option<T>>::hazard(&a, &b) {
                SKIP_MEET_SWAP.to_string()
            } else {
                show_alg_result(&LatticeRef::pmeet(&ra, &rb), show_opt_val)
            };
            format!("{} {} {} {}", <Option<T>>::name(), a.show(), b.show(), r)
        }
    };
    Some(r)
}

/// `DistributiveLatticeRef` on `&V` (`opt` false) and `Option<&V>`.
fn op_dref<T: Val + DistributiveLattice>(d: &mut Dec, opt: bool) -> Option<String> {
    if !opt {
        let a = T::dec(d)?;
        let b = T::dec(d)?;
        let r = DistributiveLatticeRef::psubtract(&&a, &&b);
        Some(format!("{} {} {} {}", T::name(), a.show(), b.show(), show_alg_result(&r, T::show)))
    } else {
        let a = <Option<T>>::dec(d)?;
        let b = <Option<T>>::dec(d)?;
        let r = DistributiveLatticeRef::psubtract(&a.as_ref(), &b.as_ref());
        Some(format!("{} {} {} {}", <Option<T>>::name(), a.show(), b.show(), show_alg_result(&r, show_opt_val)))
    }
}

fn didem<U: Val + DistributiveLattice>() -> String {
    format!("{}:{}", U::name(), <U as DistributiveLattice>::IDEMPOTENT as u8)
}

fn op_consts<T: Val>(d: &mut Dec) -> Option<String> {
    let di = d.modn(N_DTY)?;
    let ds = dty!(di, didem());
    Some(format!(
        "{}:{} {} self{} counter{} {:?} {:?}",
        T::name(),
        <T as Lattice>::IDEMPOTENT as u8,
        ds,
        SELF_IDENT,
        COUNTER_IDENT,
        AlgebraicResult::<u64>::default(),
        AlgebraicStatus::default()
    ))
}

// ---- AlgebraicResult / AlgebraicStatus ------------------------------------

/// A mask: `b % 4` below 128 (the valid arity-2 masks, and 0), `b - 128`
/// below 192, else one high bit.  `maskOfByte` in `Lattice.lean`.
fn mask_byte(b: u8) -> u64 {
    if b < 128 { (b % 4) as u64 } else if b < 192 { (b - 128) as u64 } else { 1u64 << (b % 64) }
}

fn dec_ar(d: &mut Dec) -> Option<AlgebraicResult<u64>> {
    Some(match d.modn(3)? {
        0 => AlgebraicResult::None,
        1 => AlgebraicResult::Identity(mask_byte(d.u8()?)),
        _ => AlgebraicResult::Element(int_byte(d.u8()?)),
    })
}

fn dec_opt_u64(d: &mut Dec) -> Option<Option<u64>> {
    let b = d.u8()?;
    if b % 4 == 0 { Some(None) } else { Some(Some(int_byte(d.u8()?))) }
}

fn dec_status(d: &mut Dec) -> Option<AlgebraicStatus> {
    Some(match d.modn(3)? {
        0 => AlgebraicStatus::Element,
        1 => AlgebraicStatus::Identity,
        _ => AlgebraicStatus::None,
    })
}

fn show_u64(v: &u64) -> String { v.to_string() }
fn show_opt_u64(v: &Option<u64>) -> String {
    match v { None => "None".into(), Some(v) => format!("Some({v})") }
}
fn show_opt_bool(v: &Option<bool>) -> String {
    match v { None => "None".into(), Some(v) => format!("Some({v})") }
}

/// Catch a documented panic (slice index, `unwrap` of `None`) as `panic`.
fn guarded(f: impl FnOnce() -> String) -> String {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(f)).unwrap_or_else(|_| "panic".to_string())
}

fn op_ar_query(d: &mut Dec) -> Option<String> {
    let r = dec_ar(d)?;
    let m = match r.identity_mask() { Some(m) => m.to_string(), None => "-".into() };
    Some(format!(
        "{} n{}i{}e{} m{} {:?} {:?} eq{}",
        show_alg_result(&r, show_u64),
        r.is_none() as u8,
        r.is_identity() as u8,
        r.is_element() as u8,
        m,
        r.status(),
        r,
        (r.clone() == r) as u8
    ))
}

fn op_ar_invert(d: &mut Dec) -> Option<String> {
    let r = dec_ar(d)?;
    Some(format!("{} {}", show_alg_result(&r, show_u64), show_alg_result(&r.invert_identity(), show_u64)))
}

fn op_ar_map(d: &mut Dec) -> Option<String> {
    let r = dec_ar(d)?;
    let m = r.map(|v| v.wrapping_mul(3).wrapping_add(1));
    let a = r.as_ref().map(|v| *v ^ 0xff);
    let s = r.map(|v| format!("s{v}"));
    Some(format!(
        "{} {} {} {}",
        show_alg_result(&r, show_u64),
        show_alg_result(&m, show_u64),
        show_alg_result(&a, show_u64),
        show_alg_result(&s, |s: &String| s.clone())
    ))
}

fn dec_table(d: &mut Dec) -> Option<Vec<u64>> {
    let k = d.modn(4)?;
    let mut t = Vec::with_capacity(k);
    for _ in 0..k { t.push(int_byte(d.u8()?)); }
    Some(t)
}

fn show_table(t: &[u64]) -> String {
    let v: Vec<String> = t.iter().map(|x| x.to_string()).collect();
    format!("[{}]", v.join(","))
}

fn op_ar_unwrap(d: &mut Dec) -> Option<String> {
    let r = dec_ar(d)?;
    let t = dec_table(d)?;
    let nv = int_byte(d.u8()?);
    let io = guarded(|| show_opt_u64(&r.into_option(&t[..])));
    let uw = guarded(|| r.unwrap(&t[..]).to_string());
    let uo = guarded(|| r.unwrap_or(&t[..], nv).to_string());
    Some(format!("{} {} {} io={} uw={} uo={}", show_alg_result(&r, show_u64), show_table(&t), nv, io, uw, uo))
}

fn op_ar_closures(d: &mut Dec) -> Option<String> {
    let r = dec_ar(d)?;
    let t = dec_table(d)?;
    let show_i = |c: Option<usize>| c.map(|i| i.to_string()).unwrap_or_else(|| "-".into());
    let mut c1 = None;
    let mio = r.map_into_option(|i| { c1 = Some(i); t.get(i).copied() });
    let mut c2 = None;
    let mut c3 = false;
    let uoe = r.unwrap_or_else(|i| { c2 = Some(i); t.get(i).copied().unwrap_or(77) }, || { c3 = true; 99 });
    Some(format!(
        "{} {} mio={}@{} uoe={}@{}{}",
        show_alg_result(&r, show_u64),
        show_table(&t),
        show_opt_u64(&mio),
        show_i(c1),
        uoe,
        show_i(c2),
        if c3 { "n" } else { "" }
    ))
}

fn op_ar_status(d: &mut Dec) -> Option<String> {
    let st = dec_status(d)?;
    let v = int_byte(d.u8()?);
    let fs = AlgebraicResult::from_status(st, || v);
    let ro: AlgebraicResult<Option<u64>> = match d.modn(3)? {
        0 => AlgebraicResult::None,
        1 => AlgebraicResult::Identity(mask_byte(d.u8()?)),
        _ => AlgebraicResult::Element(dec_opt_u64(d)?),
    };
    Some(format!(
        "{:?} {} {} {} {}",
        st,
        v,
        show_alg_result(&fs, show_u64),
        show_alg_result(&ro, show_opt_u64),
        show_alg_result(&ro.flatten(), show_u64)
    ))
}

fn op_ar_eq(d: &mut Dec) -> Option<String> {
    let a = dec_ar(d)?;
    let b = dec_ar(d)?;
    Some(format!("{} {} eq{} ne{}", show_alg_result(&a, show_u64), show_alg_result(&b, show_u64), (a == b) as u8, (a != b) as u8))
}

fn show_pair(p: &(Option<u64>, Option<u64>)) -> String {
    format!("({},{})", show_opt_u64(&p.0), show_opt_u64(&p.1))
}

/// `AlgebraicResult::merge` on raw results and identity tables.
fn op_ar_merge(d: &mut Dec) -> Option<String> {
    let ra = dec_ar(d)?;
    let rb = dec_ar(d)?;
    let ta = [dec_opt_u64(d)?, dec_opt_u64(d)?];
    let tb = [dec_opt_u64(d)?, dec_opt_u64(d)?];
    let fmode = d.modn(2)?;
    let show_i = |c: Option<usize>| c.map(|i| i.to_string()).unwrap_or_else(|| "-".into());
    let (mut ca, mut cb) = (None, None);
    let r = ra.merge(
        rb,
        |i| { ca = Some(i); ta.get(i).copied().flatten() },
        |i| { cb = Some(i); tb.get(i).copied().flatten() },
        |x, y| if fmode == 1 && x.is_none() && y.is_none() { AlgebraicResult::None } else { AlgebraicResult::Element((x, y)) },
    );
    Some(format!(
        "{} {} {},{} {},{} f{} {} a@{} b@{}",
        show_alg_result(&ra, show_u64),
        show_alg_result(&rb, show_u64),
        show_opt_u64(&ta[0]), show_opt_u64(&ta[1]),
        show_opt_u64(&tb[0]), show_opt_u64(&tb[1]),
        fmode,
        show_alg_result(&r, show_pair),
        show_i(ca),
        show_i(cb)
    ))
}

/// `merge` used as its doc intends: compose a pair's result from the
/// per-field results of a real lattice op (`Option<bool>` × `Option<u64>`,
/// absent fields as `None`, as `dense_byte_node`'s co-free join does).
fn op_merge_fields(d: &mut Dec) -> Option<String> {
    let op = d.modn(3)?;
    let a1 = <Option<bool>>::dec(d)?;
    let a2 = <Option<u64>>::dec(d)?;
    let b1 = <Option<bool>>::dec(d)?;
    let b2 = <Option<u64>>::dec(d)?;
    let (r1, r2) = match op {
        0 => (a1.pjoin(&b1), a2.pjoin(&b2)),
        1 => (a1.pmeet(&b1), a2.pmeet(&b2)),
        _ => (a1.psubtract(&b1), a2.psubtract(&b2)),
    };
    let (f1, f2) = (r1.flatten(), r2.flatten());
    let t1 = [a1, b1];
    let t2 = [a2, b2];
    let m = f1.merge(
        f2,
        |i| t1.get(i).copied().flatten(),
        |i| t2.get(i).copied().flatten(),
        |x, y| if x.is_none() && y.is_none() { AlgebraicResult::None } else { AlgebraicResult::Element((x, y)) },
    );
    let sp = |p: &(Option<bool>, Option<u64>)| format!("({},{})", show_opt_bool(&p.0), show_opt_u64(&p.1));
    Some(format!(
        "{} ({},{}) ({},{}) {} {} {}",
        ["join", "meet", "sub"][op],
        show_opt_bool(&a1), show_opt_u64(&a2),
        show_opt_bool(&b1), show_opt_u64(&b2),
        show_alg_result(&f1, |b: &bool| b.to_string()),
        show_alg_result(&f2, show_u64),
        show_alg_result(&m, sp)
    ))
}

fn op_status(d: &mut Dec) -> Option<String> {
    let a = dec_status(d)?;
    let b = dec_status(d)?;
    let an = d.boolean()?;
    let bn = d.boolean()?;
    let cmp = match a.cmp(&b) {
        std::cmp::Ordering::Less => "<",
        std::cmp::Ordering::Equal => "=",
        std::cmp::Ordering::Greater => ">",
    };
    Some(format!(
        "{:?} {:?} {}{} n{}i{}e{} {} max{:?} {:?}",
        a, b, an as u8, bn as u8,
        a.is_none() as u8, a.is_identity() as u8, a.is_element() as u8,
        cmp, a.max(b), a.merge(b, an, bn)
    ))
}

// ---- SetLattice methods ------------------------------------------------------

fn op_setlattice_set(d: &mut Dec) -> Option<String> {
    type S = HashSet<u8>;
    let mut s: S = if d.boolean()? { <S as SetLattice>::with_capacity(d.modn(8)?) } else { S::dec(d)? };
    let mut out = vec![s.show()];
    let n = d.modn(6)?;
    for _ in 0..n {
        let sub = d.modn(9)?;
        let k = d.u8()? % 8;
        out.push(match sub {
            0 => format!("len{}", <S as SetLattice>::len(&s)),
            1 => format!("e{}", <S as SetLattice>::is_empty(&s) as u8),
            2 => format!("c{}{}", k, <S as SetLattice>::contains_key(&s, &k) as u8),
            3 => { <S as SetLattice>::insert(&mut s, k, ()); format!("i{k}") }
            4 => { <S as SetLattice>::remove(&mut s, &k); format!("r{k}") }
            5 => format!("g{}{}", k, if <S as SetLattice>::get(&s, &k).is_some() { "+" } else { "-" }),
            6 => {
                if <S as SetLattice>::contains_key(&s, &k) {
                    <S as SetLattice>::replace(&mut s, &k, ());
                    format!("p{k}")
                } else {
                    "p-".into()
                }
            }
            7 => {
                let mut v: Vec<String> = Vec::new();
                let mut ks: Vec<u8> = <S as SetLattice>::iter(&s).map(|(k, ())| *k).collect();
                ks.sort();
                for k in ks { v.push(k.to_string()); }
                format!("it[{}]", v.join(","))
            }
            _ => { <S as SetLattice>::shrink_to_fit(&mut s); format!("sh{}", s.show()) }
        });
    }
    out.push(s.show());
    Some(out.join(" "))
}

fn op_setlattice_map(d: &mut Dec) -> Option<String> {
    type M = HashMap<u8, u64>;
    let mut s: M = if d.boolean()? { <M as SetLattice>::with_capacity(d.modn(8)?) } else { M::dec(d)? };
    let mut out = vec![s.show()];
    let n = d.modn(6)?;
    for _ in 0..n {
        let sub = d.modn(9)?;
        let k = d.u8()? % 6;
        out.push(match sub {
            0 => format!("len{}", <M as SetLattice>::len(&s)),
            1 => format!("e{}", <M as SetLattice>::is_empty(&s) as u8),
            2 => format!("c{}{}", k, <M as SetLattice>::contains_key(&s, &k) as u8),
            3 => {
                let v = int_byte(d.u8()?);
                <M as SetLattice>::insert(&mut s, k, v);
                format!("i{k}={v}")
            }
            4 => { <M as SetLattice>::remove(&mut s, &k); format!("r{k}") }
            5 => format!("g{}{}", k, show_opt_u64(&<M as SetLattice>::get(&s, &k).copied())),
            6 => {
                let v = int_byte(d.u8()?);
                if <M as SetLattice>::contains_key(&s, &k) {
                    <M as SetLattice>::replace(&mut s, &k, v);
                    format!("p{k}={v}")
                } else {
                    "p-".into()
                }
            }
            7 => {
                let mut v: Vec<(u8, u64)> = <M as SetLattice>::iter(&s).map(|(k, v)| (*k, *v)).collect();
                v.sort();
                let v: Vec<String> = v.iter().map(|(k, x)| format!("{k}:{x}")).collect();
                format!("it[{}]", v.join(","))
            }
            _ => { <M as SetLattice>::shrink_to_fit(&mut s); format!("sh{}", s.show()) }
        });
    }
    out.push(s.show());
    Some(out.join(" "))
}

/// Selector `op` (30..=59) → op name.  `latticeOps` in `Lattice.lean`.
const OPS: [&str; 30] = [
    "ring_pjoin", "ring_pmeet", "ring_psubtract", "ring_join_into", "ring_join_all",
    "ring_lref", "ring_dref", "ring_pjoin", "ring_pmeet", "ring_psubtract",
    "ring_ar_query", "ring_ar_invert", "ring_ar_map", "ring_ar_unwrap", "ring_ar_closures",
    "ring_ar_status", "ring_ar_eq", "ring_ar_merge", "ring_merge_fields", "ring_status",
    "ring_setlattice_set", "ring_setlattice_map", "ring_consts", "ring_join_into", "ring_merge_fields",
    "ring_ar_merge", "ring_pjoin", "ring_pmeet", "ring_psubtract", "ring_join_all",
];

pub fn step(op: usize, d: &mut Dec) -> StepResult {
    let name = OPS[op - 30];
    let r = match name {
        "ring_pjoin" => { let i = d.modn(N_LTY)?; lty!(i, op_pjoin(d)) }
        "ring_pmeet" => {
            let full = d.u8()? == 255;
            let i = d.modn(N_LTY)?;
            let r = lty!(i, op_pmeet(d, full))?;
            return Some((if full { "ring_pmeet!" } else { "ring_pmeet" }, r));
        }
        "ring_psubtract" => { let i = d.modn(N_DTY)?; dty!(i, op_psub(d)) }
        "ring_join_into" => { let i = d.modn(N_LTY)?; lty!(i, op_join_into(d)) }
        "ring_join_all" => { let i = d.modn(N_LTY)?; lty!(i, op_join_all(d)) }
        "ring_lref" => { let mode = d.modn(4)?; let i = d.modn(N_LTY)?; lty!(i, op_lref(d, mode)) }
        "ring_dref" => { let opt = d.boolean()?; let i = d.modn(N_DTY)?; dty!(i, op_dref(d, opt)) }
        "ring_ar_query" => op_ar_query(d),
        "ring_ar_invert" => op_ar_invert(d),
        "ring_ar_map" => op_ar_map(d),
        "ring_ar_unwrap" => op_ar_unwrap(d),
        "ring_ar_closures" => op_ar_closures(d),
        "ring_ar_status" => op_ar_status(d),
        "ring_ar_eq" => op_ar_eq(d),
        "ring_ar_merge" => op_ar_merge(d),
        "ring_merge_fields" => op_merge_fields(d),
        "ring_status" => op_status(d),
        "ring_setlattice_set" => op_setlattice_set(d),
        "ring_setlattice_map" => op_setlattice_map(d),
        _ => { let i = d.modn(N_LTY)?; lty!(i, op_consts(d)) }
    }?;
    Some((name, r))
}
