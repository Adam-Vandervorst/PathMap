//! The value types the fuzzer runs every case against.
//!
//! The harness is generic over this trait and the driver instantiates it twice,
//! because the two instantiations answer different questions.
//!
//! * [`Bits`] is a genuine Boolean algebra: `pjoin` is `|`, `pmeet` is `&`,
//!   `psubtract` is `& !`, and an empty result is bottom, which `pathmap`
//!   represents as an absent value.  Every lattice identity holds, so a law
//!   that fails here is a real defect.
//!
//! * `u64` is the type the rest of this crate's fuzzing uses, and its instances
//!   in `pathmap::ring` are **not a lattice**: `pjoin` is `left_biased_pjoin`
//!   and `pmeet` is `Identity(SELF_IDENT)`, so both return the left operand and
//!   `a | b == a & b` for every pair -- which in a lattice would force
//!   `a == b`.  It is kept because it is what real callers use today, and
//!   because dropping it would lose coverage of the `Identity`-heavy paths.
//!
//! Running both is the point.  A finding that appears under `u64` and not under
//! `Bits` is an artefact of that degenerate instance; one that appears under
//! both, or under `Bits` alone, is a defect in the crate.  `bin/alg_fuzz`
//! prints the split explicitly.
//!
//! # Why a bitmask rather than some other lawful lattice
//!
//! Lawfulness alone is not enough.  `max`/`min` on a total order is a perfectly
//! good distributive lattice, and useless here: `max(a, b)` and `min(a, b)` are
//! always *one of the operands*, so they can only ever return
//! `AlgebraicResult::Identity`, and every code path that allocates and stores a
//! genuinely combined value stays unreachable.  `a | b` is a new value, so a
//! bitmask reaches them.  `bin/alg_lattice_check` prints the comparison.

use pathmap::ring::{AlgebraicResult, DistributiveLattice, Lattice, COUNTER_IDENT, SELF_IDENT};

use super::Gen;

/// What the harness needs of a value type.
pub trait FuzzValue:
    Clone
    + Send
    + Sync
    + Unpin
    + PartialEq
    + Ord
    + core::fmt::Debug
    + core::hash::Hash
    + Lattice
    + DistributiveLattice
    + 'static
{
    /// Appears as the first field of every signature, so findings from the two
    /// instantiations never collide.
    const NAME: &'static str;

    /// Whether this type's instances actually form a distributive lattice with a
    /// relative complement.
    ///
    /// `laws.rs` reads this: when it is false, the identities that depend on
    /// join and meet being different functions are checked on path presence
    /// only, and the ones that cannot hold at all are skipped.  When it is true
    /// every identity is checked on values, which is the stronger test and the
    /// reason for having a lawful type at all.
    const LAWFUL: bool;

    /// Whether `pjoin` always yields one of its operands rather than a new
    /// value -- true exactly when the "join" is really "the left one wins".
    ///
    /// This gates the `OverlayZipper` join strategy, and it is not a detail.
    /// `OverlayZipper`'s mapping function has signature
    /// `Fn(Option<&'a AV>, Option<&'a BV>) -> Option<&'a OutV>`: it returns a
    /// *reference*, so it has nowhere to put a value it would have to create.
    /// The module's own comment says as much.  So an overlay can stand in for a
    /// join only when the join never creates anything, and for a real lattice it
    /// cannot be a join at all.  That is a limitation of the zipper, not a
    /// defect, so the strategy is dropped rather than reported.
    const JOIN_PICKS_LEFT: bool;

    fn generate(g: &mut Gen) -> Self;

    fn show(&self) -> String;
}

/// A 64-bit set under union, intersection and relative complement.
///
/// The same construction `pathmap::utils` already uses for `[u64; 4]` and
/// `ByteMask`, at a narrower width: see `bitmask_algebraic_result` there.  An
/// empty result is `AlgebraicResult::None` rather than `Element(Bits(0))`,
/// matching the convention `SetLattice`'s documentation states -- an empty set
/// is equivalent to a nonexistent one.
///
/// Defined here rather than in `pathmap` on purpose: a value type living outside
/// the crate is what a real caller has, so the generic algebra is exercised the
/// way a downstream user would exercise it.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Bits(pub u64);

impl core::fmt::Debug for Bits {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{:b}", self.0)
    }
}

/// Classify a bitwise result exactly as `pathmap::utils` does for `[u64; 4]`.
#[inline]
fn bits_result(result: u64, lhs: u64, rhs: u64) -> AlgebraicResult<Bits> {
    if result == 0 {
        return AlgebraicResult::None;
    }
    let mut mask = 0;
    if result == lhs {
        mask = SELF_IDENT;
    }
    if result == rhs {
        mask |= COUNTER_IDENT;
    }
    if mask != 0 {
        AlgebraicResult::Identity(mask)
    } else {
        AlgebraicResult::Element(Bits(result))
    }
}

impl Lattice for Bits {
    #[inline]
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
        bits_result(self.0 | other.0, self.0, other.0)
    }
    #[inline]
    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> {
        bits_result(self.0 & other.0, self.0, other.0)
    }
}

impl DistributiveLattice for Bits {
    #[inline]
    fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> {
        bits_result(self.0 & !other.0, self.0, other.0)
    }
}

/// Width of the generated masks.
///
/// Four bits, so operands collide constantly -- the whole point of a small
/// alphabet applies to values too -- while still overlapping only partially, so
/// `pjoin` and `pmeet` return `Element` rather than `Identity` most of the time.
pub const BITS_WIDTH: u32 = 4;

impl FuzzValue for Bits {
    const NAME: &'static str = "bits";
    const LAWFUL: bool = true;
    // `Bits(0b01) | Bits(0b10)` is `Bits(0b11)`, which is neither operand.
    const JOIN_PICKS_LEFT: bool = false;

    fn generate(g: &mut Gen) -> Self {
        // Never zero.  Bottom is representable as `Bits(0)`, but the lattice
        // collapses it to `None`, so a stored `Bits(0)` is a value that is also
        // bottom -- a genuinely interesting edge case, and a separate question
        // from the one this type is here to answer.  Excluded deliberately.
        let n = 1u64 << BITS_WIDTH;
        Bits(g.byte() as u64 % (n - 1) + 1)
    }

    fn show(&self) -> String {
        format!("{:b}", self.0)
    }
}

/// The set case: a path is either present or absent, with nothing attached.
///
/// `Option<()>` is exactly the two-element Boolean algebra, so `()` is **lawful**
/// -- unlike `u64`, and for the same reason `bits` is.  It earns a place of its
/// own anyway, for two reasons neither of the others covers.
///
/// First, `PathMap<()>` is what a caller writes when the trie *is* the data, and
/// it is what the `unit-value-optimizations` and `unit-size` branches are about.
/// None of that is on `master` yet, so today this exercises the generic path; if
/// those land it becomes the only thing covering the specialised one.
///
/// Second, and more useful now: `()`'s `pjoin` and `pmeet` return
/// `Identity(SELF_IDENT | COUNTER_IDENT)` *unconditionally* -- **both** identity
/// bits, always.  `u64` returns that only for equal values and `bits` only for
/// equal masks, so neither saturates the "either side will do" path that the node
/// code uses to decide it can hand back an operand unchanged and keep sharing it.
/// Findings 4 and 6 are both about exactly that machinery, so a value type that
/// drives it on every single combination is worth having.
///
/// It cannot produce `Element`, but that is not a gap here: with one inhabitant
/// there is no combined value to store.  `bits` covers that.
impl FuzzValue for () {
    const NAME: &'static str = "unit";
    const LAWFUL: bool = true;
    // Both operands are `()`, so returning either is returning the left one, and
    // `OverlayZipper`'s `a.or(b)` is the join.
    const JOIN_PICKS_LEFT: bool = true;

    fn generate(_g: &mut Gen) -> Self {}

    fn show(&self) -> String {
        "*".to_string()
    }
}

/// Distinct values in circulation for `u64`.
///
/// Tiny on purpose: `psubtract` on `u64` is `None` only when the two values are
/// *equal*, so a large value space would turn subtraction into set difference
/// and never exercise the value comparison at all.
pub const U64_VALUES: u64 = 3;

impl FuzzValue for u64 {
    const NAME: &'static str = "u64";
    const LAWFUL: bool = false;
    const JOIN_PICKS_LEFT: bool = true;

    fn generate(g: &mut Gen) -> Self {
        g.byte() as u64 % U64_VALUES + 1
    }

    fn show(&self) -> String {
        self.to_string()
    }
}

/// Resolve an `AlgebraicResult` over `Option<V>` to a value, which is how
/// `pathmap` stores the outcome: `None` means the value is gone.
///
/// Used by `model.rs` so the reference semantics are derived from the value
/// type's own operations rather than restated by hand -- restating them is how
/// a harness ends up asserting its own idea of the algebra.
pub fn resolve<V: Clone>(
    result: AlgebraicResult<Option<V>>,
    lhs: &Option<V>,
    rhs: &Option<V>,
) -> Option<V> {
    match result {
        AlgebraicResult::Element(v) => v,
        AlgebraicResult::Identity(mask) => {
            if mask & SELF_IDENT != 0 { lhs.clone() } else { rhs.clone() }
        }
        AlgebraicResult::None => None,
    }
}
