//! Is a divergence the crate's fault, or the value type's?
//!
//! `(a | b) \ (a & b)` and `(a \ b) | (b \ a)` are equal in any distributive
//! lattice with a relative complement, so a divergence between them is never a
//! matter of convention.  This prints both formulas for several value types and
//! shows which ones are lawful.
//!
//! It also asks a second question, which turns out to be the more important one
//! for fuzzing: does the type's `pjoin`/`pmeet`/`psubtract` ever return
//! `AlgebraicResult::Element` -- a combined value that is not simply one of its
//! operands?  If not, every code path that *stores* a combined value is
//! unreachable from that type, however lawful it is.
//!
//! ```sh
//! cargo run --release -p differential --bin alg_lattice_check
//! ```

use core::fmt::Debug;
use pathmap::ring::{AlgebraicResult, DistributiveLattice, Lattice, COUNTER_IDENT, SELF_IDENT};
use pathmap::utils::ByteMask;

/// Bottom is `None`, as it is everywhere in `pathmap`: a value that cancels
/// becomes an absent value, not a present zero.  Resolving through `Option<T>`
/// uses the crate's own `Option<V>` lattice impls, so this says nothing the
/// trie does not.
fn resolve<T: Clone>(r: AlgebraicResult<Option<T>>, l: &Option<T>, rr: &Option<T>) -> Option<T> {
    match r {
        AlgebraicResult::Element(v) => v,
        AlgebraicResult::Identity(m) => {
            if m & SELF_IDENT != 0 { l.clone() } else { rr.clone() }
        }
        AlgebraicResult::None => None,
    }
}

fn show<T: Debug>(v: &Option<T>) -> String {
    match v {
        None => "BOTTOM".to_string(),
        Some(v) => format!("{v:?}"),
    }
}

/// `(a | b) \ (a & b)` and `(a \ b) | (b \ a)`, each resolved to a value.
fn two_formulas<T>(a: T, b: T) -> (String, String, String, String, bool)
where
    T: Lattice + DistributiveLattice + Clone + Debug,
{
    let (ao, bo) = (Some(a), Some(b));
    let j = resolve(ao.pjoin(&bo), &ao, &bo);
    let m = resolve(ao.pmeet(&bo), &ao, &bo);
    let f1 = resolve(j.psubtract(&m), &j, &m);

    let ab = resolve(ao.psubtract(&bo), &ao, &bo);
    let ba = resolve(bo.psubtract(&ao), &bo, &ao);
    let f2 = resolve(ab.pjoin(&ba), &ab, &ba);

    let agree = show(&f1) == show(&f2);
    (show(&j), show(&m), show(&f1), show(&f2), agree)
}

fn row<T>(label: String, a: T, b: T)
where
    T: Lattice + DistributiveLattice + Clone + Debug,
{
    let (j, m, f1, f2, agree) = two_formulas(a, b);
    println!(
        "  {label:<22} a|b = {j:>9}  a&b = {m:>9}  (a|b)-(a&b) = {f1:>9}  (a-b)|(b-a) = {f2:>9}  {}",
        if agree { "agree" } else { "DIVERGE" }
    );
}

/// Whether each operation ever returns `Element` over a sample of pairs.
fn element_per_op<T>(sample: &[T]) -> (bool, bool, bool)
where
    T: Lattice + DistributiveLattice + Clone,
{
    let mut out = (false, false, false);
    for a in sample {
        for b in sample {
            out.0 |= matches!(a.pjoin(b), AlgebraicResult::Element(_));
            out.1 |= matches!(a.pmeet(b), AlgebraicResult::Element(_));
            out.2 |= matches!(a.psubtract(b), AlgebraicResult::Element(_));
        }
    }
    out
}

fn yn(b: bool) -> &'static str {
    if b { "yes" } else { "NO " }
}

// ---------------------------------------------------------------- candidates

/// Bitmask: `pjoin` is `|`, `pmeet` is `&`, `psubtract` is `& !`, and an empty
/// result collapses to `None`.  A Boolean algebra -- the powerset of 64
/// elements -- so every lattice identity holds.  This is exactly what
/// `[u64; 4]` already does in `pathmap::utils`; only the width differs.
#[derive(Clone, Copy, PartialEq, Eq)]
struct Bits(u64);

impl Debug for Bits {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:04b}", self.0)
    }
}

fn bits_result(r: u64, l: u64, rr: u64) -> AlgebraicResult<Bits> {
    if r == 0 {
        return AlgebraicResult::None;
    }
    let mut m = 0;
    if r == l { m = SELF_IDENT }
    if r == rr { m |= COUNTER_IDENT }
    if m != 0 { AlgebraicResult::Identity(m) } else { AlgebraicResult::Element(Bits(r)) }
}

impl Lattice for Bits {
    fn pjoin(&self, o: &Self) -> AlgebraicResult<Self> { bits_result(self.0 | o.0, self.0, o.0) }
    fn pmeet(&self, o: &Self) -> AlgebraicResult<Self> { bits_result(self.0 & o.0, self.0, o.0) }
}
impl DistributiveLattice for Bits {
    fn psubtract(&self, o: &Self) -> AlgebraicResult<Self> { bits_result(self.0 & !o.0, self.0, o.0) }
}

/// The total order: `pjoin` is `max`, `pmeet` is `min`, bottom is 0.  Also a
/// genuine distributive lattice -- every total order is one -- and here to make
/// the point that lawfulness is not sufficient.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct MinMax(u64);

fn minmax_result(r: u64, l: u64, rr: u64) -> AlgebraicResult<MinMax> {
    if r == 0 {
        return AlgebraicResult::None;
    }
    let mut m = 0;
    if r == l { m = SELF_IDENT }
    if r == rr { m |= COUNTER_IDENT }
    if m != 0 { AlgebraicResult::Identity(m) } else { AlgebraicResult::Element(MinMax(r)) }
}

impl Lattice for MinMax {
    fn pjoin(&self, o: &Self) -> AlgebraicResult<Self> { minmax_result(self.0.max(o.0), self.0, o.0) }
    fn pmeet(&self, o: &Self) -> AlgebraicResult<Self> { minmax_result(self.0.min(o.0), self.0, o.0) }
}
impl DistributiveLattice for MinMax {
    fn psubtract(&self, o: &Self) -> AlgebraicResult<Self> {
        minmax_result(if self.0 > o.0 { self.0 } else { 0 }, self.0, o.0)
    }
}

fn bm(bits: &[u8]) -> ByteMask {
    let mut m = [0u64; 4];
    for b in bits {
        m[(*b / 64) as usize] |= 1 << (*b % 64);
    }
    ByteMask(m)
}

fn main() {
    println!("Are the two formulas for symmetric difference equal?\n");

    println!("u64 -- what the fuzzer uses; pjoin is left-biased, pmeet is Identity(SELF)");
    for (a, b) in [(1u64, 2u64), (3, 7), (5, 5)] {
        row(format!("a={a} b={b}"), a, b);
    }
    println!("  ^ a|b == a&b for every pair, so this is not a lattice: in one,");
    println!("    a&b == a|b forces a == b, i.e. the impl asserts 1 == 2.\n");

    println!("bool -- a real two-element Boolean algebra, same file");
    for (a, b) in [(true, false), (true, true), (false, false)] {
        row(format!("a={a} b={b}"), a, b);
    }

    println!("\nBits(u64) -- pjoin = |, pmeet = &, psubtract = & !, empty -> None");
    for (a, b) in [(0b0011u64, 0b0101u64), (0b0001, 0b0010), (0b0011, 0b0011)] {
        row(format!("a={a:04b} b={b:04b}"), Bits(a), Bits(b));
    }

    println!("\nByteMask -- the crate already implements exactly that, at 256 bits");
    for (a, b) in [(&[0u8, 1][..], &[1u8, 2][..]), (&[0][..], &[1][..]), (&[3][..], &[3][..])] {
        row(format!("a={a:?} b={b:?}"), bm(a), bm(b));
    }

    println!("\nMinMax(u64) -- pjoin = max, pmeet = min; also a lawful distributive lattice");
    for (a, b) in [(5u64, 3u64), (3, 5), (4, 4)] {
        row(format!("a={a} b={b}"), MinMax(a), MinMax(b));
    }

    println!("\n\nDoes each operation ever return AlgebraicResult::Element,");
    println!("i.e. a combined value that is not simply one of its operands?\n");
    println!("  {:<12} {:>7} {:>7} {:>10}", "type", "pjoin", "pmeet", "psubtract");
    let show_ops = |name: &str, (j, m, s): (bool, bool, bool)| {
        println!("  {name:<12} {:>7} {:>7} {:>10}", yn(j), yn(m), yn(s));
    };
    show_ops("u64", element_per_op(&[1u64, 2, 3, 5, 7]));
    show_ops("bool", element_per_op(&[true, false]));
    show_ops("MinMax", element_per_op(&[MinMax(1), MinMax(2), MinMax(3), MinMax(5)]));
    show_ops("Bits", element_per_op(&[Bits(0b0011), Bits(0b0101), Bits(0b1001), Bits(0b0110)]));
    show_ops("ByteMask", element_per_op(&[bm(&[0, 1]), bm(&[1, 2]), bm(&[2, 3]), bm(&[0, 3])]));

    println!("\n  u64's one \"yes\" is `Element(*self)` -- an Element whose value equals self,");
    println!("  which is why PR #115 retags it as Identity(SELF_IDENT).  That is the right");
    println!("  fix, and it leaves u64 unable to produce Element from any operation at all.");
    println!("\n  MinMax is lawful and still answers NO everywhere: max(a,b) and min(a,b)");
    println!("  are always one of the operands, so a lattice can be perfectly correct and");
    println!("  still never exercise the code that stores a combined value.  Only the");
    println!("  bitmask family answers yes, because a|b is genuinely a new value.");
}
