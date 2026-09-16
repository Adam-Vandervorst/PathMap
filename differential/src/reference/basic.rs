//! `Basic.lean` — the vocabulary the rest of the model is written in.
//!
//! * [`path`] — keys, and the prefix order on them.
//! * [`ValOps`] / [`ValRes`] — the fragment of `Lattice` / `DistributiveLattice`
//!   that the trie operations actually consume.
//! * [`ByteMask`] — the 256-bit child mask.
//! * [`AlgStatus`] — `pathmap::ring::AlgebraicStatus`.

// ===========================================================================
// Basic.lean — paths
// ===========================================================================

/// Path helpers.
///
/// `Path.isPrefixOf`, `Path.stripPrefix` and `Path.lt` are all provided by
/// `[u8]` itself — `starts_with`, `strip_prefix` and `Ord` respectively — and
/// the slice order is exactly the model's `Path.lt`, so they are not restated.
pub mod path {
    /// `Path.prefixes`: every prefix of `p`, shortest first: `[]`, `p[..1]`, ..., `p`.
    pub fn prefixes(p: &[u8]) -> impl Iterator<Item = &[u8]> {
        (0..=p.len()).map(move |n| &p[..n])
    }

    /// `Path.properPrefixes`: every *proper* prefix of `p`, shortest first.
    ///
    /// Used to phrase "the nearest ancestor such that ..." as a filter over
    /// ancestors rather than as a loop that walks upward.
    pub fn proper_prefixes(p: &[u8]) -> impl Iterator<Item = &[u8]> {
        (0..p.len()).map(move |n| &p[..n])
    }

    /// The deepest proper prefix of `p` satisfying `pred`, if any.
    ///
    /// `proper_prefixes` is shortest-first and the Lean model takes the *last*
    /// qualifying element; scanning from the deep end and stopping at the first
    /// hit is the same answer without building the list.
    pub fn deepest_proper_prefix(p: &[u8], mut pred: impl FnMut(&[u8]) -> bool) -> Option<&[u8]> {
        (0..p.len()).rev().map(|n| &p[..n]).find(|a| pred(a))
    }

    /// `p ++ q`, as an owned path.
    pub fn cat(p: &[u8], q: &[u8]) -> Vec<u8> {
        let mut r = Vec::with_capacity(p.len() + q.len());
        r.extend_from_slice(p);
        r.extend_from_slice(q);
        r
    }

    /// `p ++ [b]`, as an owned path.
    pub fn push(p: &[u8], b: u8) -> Vec<u8> {
        let mut r = Vec::with_capacity(p.len() + 1);
        r.extend_from_slice(p);
        r.push(b);
        r
    }
}

// ===========================================================================
// Basic.lean — value operations
// ===========================================================================

/// `pathmap::ring::AlgebraicResult` at the *value* level: either a freshly
/// computed element, an assertion that the result is already one of the operands
/// (`Identity`, with the `SELF_IDENT` / `COUNTER_IDENT` mask spelled out as two
/// flags), or annihilation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValRes<V> {
    /// `AlgebraicResult::Element`
    Elem(V),
    /// `AlgebraicResult::Identity(mask)`; the flags are `SELF_IDENT`, `COUNTER_IDENT`.
    Identity(bool, bool),
    /// `AlgebraicResult::None`
    None,
}

impl<V> ValRes<V> {
    /// Turn a `ValRes` into the value it denotes, given both operands.
    pub fn resolve(self, a: &V, b: &V) -> Option<V>
    where
        V: Clone,
    {
        match self {
            ValRes::Elem(v) => Some(v),
            ValRes::Identity(s, _) => Some(if s { a.clone() } else { b.clone() }),
            ValRes::None => None,
        }
    }
}

/// A value type together with the algebraic operations `pathmap` requires of it.
///
/// These return [`ValRes`] rather than plain values because `pathmap` reports
/// `AlgebraicStatus` to the caller, and the status depends on *which variant*
/// the value operation returned, not on whether the stored value changed.
/// `u64`'s `pjoin`, for instance, returns `Identity(SELF_IDENT)` rather than
/// `Element` of the value it selected, so a join reports that nothing changed.
pub trait ValOps<V> {
    /// `Lattice::pjoin`
    fn pjoin(&self, a: &V, b: &V) -> ValRes<V>;
    /// `Lattice::pmeet`
    fn pmeet(&self, a: &V, b: &V) -> ValRes<V>;
    /// `DistributiveLattice::psubtract`
    fn psub(&self, a: &V, b: &V) -> ValRes<V>;
    /// Decidable equality on values.
    fn beq(&self, a: &V, b: &V) -> bool;
}

/// The instance `pathmap` provides for `u64` (see `impl Lattice for u64` in
/// `src/ring.rs`).
///
/// Both `pjoin` and `pmeet` return `Identity(SELF_IDENT)`: they are *left-biased
/// projections* that ignore the counterpart value entirely.  `psubtract`
/// annihilates only when the two values are equal, and otherwise returns
/// `Identity(SELF_IDENT)`: subtracting a value that is not there leaves the
/// destination alone, and says so.  This is the instance the differential fuzz
/// target uses, so the model reproduces it exactly rather than assuming a "real"
/// lattice.
#[derive(Clone, Copy, Debug, Default)]
pub struct U64Ops;

impl ValOps<u64> for U64Ops {
    fn pjoin(&self, _: &u64, _: &u64) -> ValRes<u64> {
        ValRes::Identity(true, false)
    }
    fn pmeet(&self, _: &u64, _: &u64) -> ValRes<u64> {
        ValRes::Identity(true, false)
    }
    fn psub(&self, a: &u64, b: &u64) -> ValRes<u64> {
        if a == b { ValRes::None } else { ValRes::Identity(true, false) }
    }
    fn beq(&self, a: &u64, b: &u64) -> bool {
        a == b
    }
}

// ===========================================================================
// Basic.lean — byte masks
// ===========================================================================

/// `pathmap`'s 256-bit child mask, modelled as the ascending, duplicate-free
/// list of its set bytes — the only thing the API observes about it.
///
/// Deliberately *not* `pathmap::utils::ByteMask`: a model that borrowed the
/// crate's mask could not detect a bug in it.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ByteMask(Vec<u8>);

impl ByteMask {
    /// Sort/dedup a byte list into canonical form — `ByteMask.ofList`.
    pub fn of_list(bs: impl IntoIterator<Item = u8>) -> Self {
        let mut v: Vec<u8> = bs.into_iter().collect();
        v.sort_unstable();
        v.dedup();
        ByteMask(v)
    }

    /// Every byte set — the mask a `remove_unmasked_branches` no-op needs.
    pub fn full() -> Self {
        ByteMask((0..=255u8).collect())
    }

    /// The set bytes, ascending.
    pub fn bytes(&self) -> &[u8] {
        &self.0
    }

    /// `ByteMask::count_bits`.
    pub fn count_bits(&self) -> usize {
        self.0.len()
    }

    /// Whether `b` is set.
    pub fn contains(&self, b: u8) -> bool {
        self.0.binary_search(&b).is_ok()
    }

    /// `ByteMask::indexed_bit::<true>` — the `idx`-th set byte in ascending order.
    pub fn indexed_bit(&self, idx: usize) -> Option<u8> {
        self.0.get(idx).copied()
    }

    /// `ByteMask::next_bit` — the least set byte strictly greater than `b`.
    pub fn next_bit(&self, b: u8) -> Option<u8> {
        self.0.iter().copied().find(|&x| x > b)
    }

    /// `ByteMask::prev_bit` — the greatest set byte strictly less than `b`.
    pub fn prev_bit(&self, b: u8) -> Option<u8> {
        self.0.iter().copied().rev().find(|&x| x < b)
    }
}

// ===========================================================================
// Basic.lean — algebraic status
// ===========================================================================

/// `pathmap::ring::AlgebraicStatus`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AlgStatus {
    /// `self` holds the operation's output.
    Element,
    /// `self` was not modified by the operation.
    Identity,
    /// `self` was annihilated and is now empty.
    None,
}

impl AlgStatus {
    /// `AlgebraicStatus::merge`, transcribed from `src/ring.rs`.
    pub fn merge(a: AlgStatus, b: AlgStatus, self_none: bool, b_none: bool) -> AlgStatus {
        match (a, b) {
            (AlgStatus::None, AlgStatus::None) => AlgStatus::None,
            (AlgStatus::None, AlgStatus::Element) => AlgStatus::Element,
            (AlgStatus::None, AlgStatus::Identity) => {
                if self_none { AlgStatus::Identity } else { AlgStatus::Element }
            }
            (AlgStatus::Identity, AlgStatus::Element) => AlgStatus::Element,
            (AlgStatus::Identity, AlgStatus::Identity) => AlgStatus::Identity,
            (AlgStatus::Identity, AlgStatus::None) => {
                if b_none { AlgStatus::Identity } else { AlgStatus::Element }
            }
            (AlgStatus::Element, _) => AlgStatus::Element,
        }
    }

    /// The `AlgebraicStatus` a [`ValRes`] induces.
    pub fn of_val_res<V>(r: &ValRes<V>) -> AlgStatus {
        match r {
            ValRes::Elem(_) => AlgStatus::Element,
            ValRes::Identity(_, _) => AlgStatus::Identity,
            ValRes::None => AlgStatus::None,
        }
    }
}

impl std::fmt::Display for AlgStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            AlgStatus::Element => "Element",
            AlgStatus::Identity => "Identity",
            AlgStatus::None => "None",
        })
    }
}

