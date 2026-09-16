//! `PathMap.lean` — what a `pathmap` trie means.
//!
//! See the module docs in `main.rs` for why the representation is a flat
//! `BTreeMap<Vec<u8>, Option<V>>` and not a prefix tree.

use std::collections::BTreeMap;
use std::collections::btree_map::Entry as BEntry;
use std::ops::Bound;

use crate::reference::basic::{ByteMask, ValOps, path};

// ===========================================================================
// PathMap.lean
// ===========================================================================

/// What a map holds at a path — the whole answer, in one value.
///
/// Named for `HashMap`/`BTreeMap`'s `Entry`, and standing in the same relation
/// to the storage: an element of [`PathMap::entries`] is a location that is
/// *there*, while an `Entry` also answers for a path that is not — Rust's
/// `Occupied` and `Vacant`.  The difference is that a `pathmap` location has
/// **three** states rather than two, and that third one is the whole reason this
/// type exists.
///
/// `create_path` produces it, `remove_val(false)` leaves it behind, and findings
/// 7, 8 and 15 are all about operations that mishandle it.  Asking through
/// `Entry` rather than through `path_exists` and `val` separately means a
/// definition cannot quietly forget that case: the `match` will not compile
/// until it says what happens.  [`Entry::Valued`] implies the location exists, so
/// the impossible combination — a value at a path that is not there — is
/// unrepresentable rather than merely untrue.
///
/// Generic over the value slot so it can be returned borrowed (`Entry<&V>`) or
/// owned (`Entry<V>`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Entry<V> {
    /// The path is not in the map.  Rust's `Vacant`.
    Absent,
    /// The path is in the map but carries no value — a location `path_exists`
    /// reports `true` for and `val` reports `None` for.
    Bare,
    /// The path is in the map and carries this value.  Rust's `Occupied`.
    Valued(V),
}

impl<V> Entry<V> {
    /// The value, if any — what `ZipperValues::val` reports.
    pub fn val(self) -> Option<V> {
        match self {
            Entry::Valued(v) => Some(v),
            _ => None,
        }
    }

    /// Whether the location is in the map — what `Zipper::path_exists` reports.
    ///
    /// Holding a value entails being there: there is no constructor for the
    /// combination, so the Lean model's `present_of_val` needs no counterpart.
    pub fn present(&self) -> bool {
        !matches!(self, Entry::Absent)
    }

    /// Whether the location is there but holds nothing.
    pub fn is_bare(&self) -> bool {
        matches!(self, Entry::Bare)
    }
}

/// A `pathmap` trie: a finite path→value map *plus* the prefix-closed set of
/// existing locations.
///
/// Everything rests on one observation.  A `pathmap` trie is not just a
/// path→value map: `create_path` makes a location that exists *without* carrying
/// a value, and `remove_val(false)` leaves one behind.  So a location, and a
/// value at that location, are separate facts, and both are recorded — in one
/// map rather than a value map beside a path set, so that a value cannot be
/// recorded at a location that does not exist.  A `None` here is exactly a
/// dangling path.
///
/// # Canonical form
///
/// * sorted and duplicate-free — structural, from `BTreeMap`;
/// * prefix-closed, and containing the empty path — maintained by the
///   constructors, checked by [`laws::prefix_closed`].
///
/// Canonical form makes structural equality observational equality, which is
/// what lets [`Zip`] decide `AlgebraicStatus::Identity` against `Element`.
#[derive(Clone, Debug)]
pub struct PathMap<V> {
    /// Every location that exists, in depth-first order, each carrying its value
    /// if it has one.
    pub entries: BTreeMap<Vec<u8>, Option<V>>,
}

impl<V: Clone> Default for PathMap<V> {
    fn default() -> Self {
        Self::empty()
    }
}

impl<V: Clone> PathMap<V> {
    // -- construction -------------------------------------------------------

    /// The empty trie: the root exists, nothing else does.
    pub fn empty() -> Self {
        let mut entries = BTreeMap::new();
        entries.insert(Vec::new(), None);
        PathMap { entries }
    }

    /// Build a canonical map from raw components — the Lean model's `mk'`.
    ///
    /// `paths` is completed with every prefix of every raw path and of every key
    /// carrying a value, so callers never have to maintain closure by hand.
    ///
    /// **Left-biased**, matching the Lean `dedupVals` and `pathmap`'s
    /// `Identity(SELF_IDENT)` value instances: the *first* binding offered for a
    /// key wins.  (`BTreeMap::insert` keeps the last, which is why this goes
    /// through `or_insert`.)
    pub fn mk(
        vals: impl IntoIterator<Item = (Vec<u8>, V)>,
        paths: impl IntoIterator<Item = Vec<u8>>,
    ) -> Self {
        let mut vs: BTreeMap<Vec<u8>, V> = BTreeMap::new();
        for (k, v) in vals {
            if let BEntry::Vacant(e) = vs.entry(k) {
                e.insert(v);
            }
        }
        let mut t = PathMap::empty();
        for p in paths {
            t.ensure_path(&p);
        }
        for (k, v) in vs {
            t.ensure_path(&k);
            t.entries.insert(k, Some(v));
        }
        t
    }

    /// Make `p` and every prefix of it exist, without disturbing any value
    /// already recorded along the way.
    fn ensure_path(&mut self, p: &[u8]) {
        for n in 0..=p.len() {
            self.entries.entry(p[..n].to_vec()).or_insert(None);
        }
    }

    // -- ranges -------------------------------------------------------------
    //
    // The three shapes of query the specification needs.  Locations sharing a
    // prefix are contiguous in `BTreeMap` order, so each is a range plus a
    // `take_while`, and each stops as soon as it leaves the subtree.

    /// Every location at or below `p`, in depth-first order.
    pub(crate) fn at_or_below<'a>(&'a self, p: &'a [u8]) -> impl Iterator<Item = (&'a Vec<u8>, &'a Option<V>)> {
        self.entries
            .range::<[u8], _>((Bound::Included(p), Bound::Unbounded))
            .take_while(move |(q, _)| q.starts_with(p))
    }

    /// Every location strictly below `p`, in depth-first order.
    pub(crate) fn strictly_below<'a>(
        &'a self,
        p: &'a [u8],
    ) -> impl Iterator<Item = (&'a Vec<u8>, &'a Option<V>)> {
        self.entries
            .range::<[u8], _>((Bound::Excluded(p), Bound::Unbounded))
            .take_while(move |(q, _)| q.starts_with(p))
    }

    /// Every location strictly after `from` and at or below `within`, in
    /// depth-first order.  `within` must be a prefix of `from`.
    pub(crate) fn after_within<'a>(
        &'a self,
        from: &'a [u8],
        within: &'a [u8],
    ) -> impl Iterator<Item = (&'a Vec<u8>, &'a Option<V>)> {
        debug_assert!(from.starts_with(within));
        self.entries
            .range::<[u8], _>((Bound::Excluded(from), Bound::Unbounded))
            .take_while(move |(q, _)| q.starts_with(within))
    }

    // -- observations -------------------------------------------------------
    //
    // These are the entire observable interface of a map; every law is phrased
    // in terms of them.

    /// What the map holds at `p`.
    pub fn entry_at(&self, p: &[u8]) -> Entry<&V> {
        match self.entries.get(p) {
            None => Entry::Absent,
            Some(None) => Entry::Bare,
            Some(Some(v)) => Entry::Valued(v),
        }
    }

    /// `Zipper::val` / `PathMap::get_val_at`: the value at `p`, if any.
    pub fn val_at(&self, p: &[u8]) -> Option<&V> {
        self.entry_at(p).val()
    }

    /// `Zipper::path_exists`: whether `p` is a location in the map.  True for
    /// dangling paths (locations with no value and no children).
    pub fn path_exists(&self, p: &[u8]) -> bool {
        self.entries.contains_key(p)
    }

    /// Every existing location, in depth-first order.
    pub fn paths(&self) -> impl Iterator<Item = &Vec<u8>> {
        self.entries.keys()
    }

    /// Every location that carries a value, with it, in depth-first order —
    /// `PathMap::iter`.
    pub fn vals(&self) -> impl Iterator<Item = (&Vec<u8>, &V)> {
        self.entries
            .iter()
            .filter_map(|(k, v)| v.as_ref().map(|v| (k, v)))
    }

    /// `Zipper::child_mask`: the bytes `b` for which `p ++ [b]` exists.
    pub fn child_mask(&self, p: &[u8]) -> ByteMask {
        ByteMask::of_list(
            self.strictly_below(p)
                .filter(|(q, _)| q.len() == p.len() + 1)
                .map(|(q, _)| q[p.len()]),
        )
    }

    /// `Zipper::child_count`.
    pub fn child_count(&self, p: &[u8]) -> usize {
        self.child_mask(p).count_bits()
    }

    /// `ZipperMoving::val_count`: values at and below `p`.
    pub fn val_count(&self, p: &[u8]) -> usize {
        self.at_or_below(p).filter(|(_, v)| v.is_some()).count()
    }

    /// The existing locations at or below `p`, in depth-first order.
    pub fn paths_below(&self, p: &[u8]) -> Vec<Vec<u8>> {
        self.at_or_below(p).map(|(q, _)| q.clone()).collect()
    }

    /// `TrieNode::node_is_empty` applied to the node *below* `p`: no descendants
    /// at all.
    pub fn below_is_empty(&self, p: &[u8]) -> bool {
        self.strictly_below(p).next().is_none()
    }

    /// `PathMap::is_empty`: no values and an empty root node.
    pub fn is_empty_map(&self) -> bool {
        self.vals().next().is_none() && self.below_is_empty(&[])
    }

    /// Whether the map is in canonical form.
    ///
    /// Sortedness and freedom from duplicates are structural — `BTreeMap` cannot
    /// represent a violation — so what is left to check is that the root exists
    /// and that the set of locations is prefix-closed.  Every constructor here
    /// establishes both; this is the assertion a harness can make after each
    /// operation to catch one that does not.
    pub fn is_canonical(&self) -> bool {
        self.path_exists(&[])
            && self
                .entries
                .keys()
                .all(|q| (0..q.len()).all(|n| self.entries.contains_key(&q[..n])))
    }

    /// Structural (hence observational) equality.  Used to decide
    /// `AlgebraicStatus::Identity` — `pathmap` reports `Identity(SELF_IDENT)`
    /// exactly when the operation's output equals `self`.
    ///
    /// Values are compared with [`ValOps::beq`], not with `PartialEq`: the
    /// notion of equality that decides the status is the value type's own.
    pub fn beq_t(&self, ops: &impl ValOps<V>, other: &PathMap<V>) -> bool {
        self.entries.len() == other.entries.len()
            && self
                .entries
                .iter()
                .zip(other.entries.iter())
                .all(|((ka, va), (kb, vb))| {
                    ka == kb
                        && match (va, vb) {
                            (None, None) => true,
                            (Some(x), Some(y)) => ops.beq(x, y),
                            _ => false,
                        }
                })
    }

    // -- sub-maps and grafting ---------------------------------------------

    /// The submap rooted at `p`, **including** the value at `p` as its root
    /// value.  This is `make_map` / `take_map` under the default
    /// `graft_root_vals` feature, and also what a zipper rooted at `p` sees.
    /// Yields [`PathMap::empty`] when `p` does not exist.
    pub fn subtrie(&self, p: &[u8]) -> PathMap<V> {
        let mut entries: BTreeMap<Vec<u8>, Option<V>> = self
            .at_or_below(p)
            .map(|(q, v)| (q[p.len()..].to_vec(), v.clone()))
            .collect();
        entries.entry(Vec::new()).or_insert(None);
        PathMap { entries }
    }

    /// Remove everything at and below `p`; `p` itself stops existing.
    ///
    /// The root always survives: a map with no locations at all is not
    /// representable, and `mk'` in the Lean model re-adds it the same way.
    pub fn remove_at(&mut self, p: &[u8]) {
        let doomed: Vec<Vec<u8>> = self.at_or_below(p).map(|(q, _)| q.clone()).collect();
        for q in doomed {
            self.entries.remove(&q);
        }
        self.entries.entry(Vec::new()).or_insert(None);
    }

    /// Remove everything strictly below `p`; `p` itself, and its value, are
    /// untouched.  This is `ZipperWriting::remove_branches` without pruning.
    pub fn remove_below(&mut self, p: &[u8]) {
        let doomed: Vec<Vec<u8>> = self.strictly_below(p).map(|(q, _)| q.clone()).collect();
        for q in doomed {
            self.entries.remove(&q);
        }
    }

    /// Replace everything strictly below `p` with the strictly-below part of `s`.
    ///
    /// The value at `p` is *not* touched (`graft_internal` only ever replaces a
    /// node); `p` is created iff `s` has any non-root content, mirroring the fact
    /// that grafting an empty node neither creates nor destroys the location.
    pub fn graft_below(&mut self, p: &[u8], s: &PathMap<V>) {
        self.remove_below(p);
        let mut any = false;
        for (q, v) in s.entries.iter() {
            if q.is_empty() {
                continue;
            }
            if !any {
                // The first non-root entry is what creates `p` (and its own
                // ancestors); an empty source leaves the location alone.
                self.ensure_path(p);
                any = true;
            }
            self.entries.insert(path::cat(p, q), v.clone());
        }
    }

    // -- point updates ------------------------------------------------------

    /// `ZipperWriting::set_val` / `PathMap::set_val_at`.  Creates `p` if needed.
    /// Returns the replaced value.
    pub fn set_val(&mut self, p: &[u8], v: V) -> Option<V> {
        self.ensure_path(p);
        self.entries.insert(p.to_vec(), Some(v)).flatten()
    }

    /// `ZipperWriting::remove_val` *without* pruning: the location survives as a
    /// dangling path.  Returns the removed value.  Never creates anything.
    pub fn remove_val(&mut self, p: &[u8]) -> Option<V> {
        self.entries.get_mut(p).and_then(|slot| slot.take())
    }

    /// `ZipperWriting::create_path`: make `p` exist as a dangling path.
    pub fn add_path(&mut self, p: &[u8]) {
        self.ensure_path(p);
    }

    // -- pruning ------------------------------------------------------------

    /// Is `p` a dangling tip — an existing location with neither value nor
    /// children?
    pub fn is_dangling_tip(&self, p: &[u8]) -> bool {
        self.entry_at(p).is_bare() && self.below_is_empty(p)
    }

    /// The number of bytes `prune_path` would remove at focus `p` for a zipper
    /// whose root sits at depth `root_len`.  `0` means "nothing to prune".
    ///
    /// The chain is removed back to the deepest strict ancestor that must be
    /// kept: one carrying a value, one that branches, or the one at the stop
    /// depth.  The ancestor at `root_len` always qualifies, so there is always an
    /// answer, and `max` makes "never prunes above the stop depth" syntactic.
    pub fn prune_count(&self, root_len: usize, p: &[u8]) -> usize {
        if p.len() <= root_len || !self.is_dangling_tip(p) {
            return 0;
        }
        let a = path::deepest_proper_prefix(p, |a| {
            a.len() <= root_len || self.val_at(a).is_some() || self.child_count(a) >= 2
        })
        .map(|a| a.len())
        .unwrap_or(0);
        p.len() - root_len.max(a)
    }

    /// `ZipperWriting::prune_path`: returns the number of bytes removed.
    pub fn prune_path(&mut self, root_len: usize, p: &[u8]) -> usize {
        let n = self.prune_count(root_len, p);
        if n != 0 {
            self.remove_at(&p[..p.len() - n + 1]);
        }
        n
    }
}

// ---------------------------------------------------------------------------
// PathMap.lean — algebraic operations
// ---------------------------------------------------------------------------
//
// These lift `pathmap`'s node-level `pjoin` / `pmeet` / `psubtract` /
// `prestrict` to whole maps.  The interesting content is *which locations
// survive*, since `pathmap` drops any node that ends up empty.

impl<V: Clone> PathMap<V> {
    /// `Option<V>::pjoin` from `src/ring.rs`.
    fn join_val(ops: &impl ValOps<V>, a: Option<&V>, b: Option<&V>) -> Option<V> {
        match (a, b) {
            (None, b) => b.cloned(),
            (Some(a), None) => Some(a.clone()),
            (Some(a), Some(b)) => ops.pjoin(a, b).resolve(a, b),
        }
    }

    /// `Option<V>::pmeet`: a value survives only where *both* sides have one.
    fn meet_val(ops: &impl ValOps<V>, a: Option<&V>, b: Option<&V>) -> Option<V> {
        match (a, b) {
            (Some(a), Some(b)) => ops.pmeet(a, b).resolve(a, b),
            _ => None,
        }
    }

    /// `Option<V>::psubtract`.
    fn sub_val(ops: &impl ValOps<V>, a: Option<&V>, b: Option<&V>) -> Option<V> {
        match (a, b) {
            (None, _) => None,
            (Some(a), None) => Some(a.clone()),
            (Some(a), Some(b)) => ops.psub(a, b).resolve(a, b),
        }
    }

    /// Join (union).  Every location of either side survives; colliding values
    /// are combined with [`ValOps::pjoin`].
    pub fn join(ops: &impl ValOps<V>, a: &PathMap<V>, b: &PathMap<V>) -> PathMap<V> {
        let mut keys: Vec<&Vec<u8>> = a.vals().map(|(k, _)| k).collect();
        keys.extend(b.vals().map(|(k, _)| k));
        keys.sort_unstable();
        keys.dedup();
        let vals = keys.into_iter().filter_map(|k| {
            Self::join_val(ops, a.val_at(k), b.val_at(k)).map(|v| (k.clone(), v))
        });
        // Collected first: `mk` takes the value list by value, and the path
        // iterators borrow `a` and `b` at the same time.
        let vals: Vec<(Vec<u8>, V)> = vals.collect();
        PathMap::mk(vals, a.paths().chain(b.paths()).cloned())
    }

    /// Meet (intersection).  A location exists in the result exactly when it
    /// exists in both operands, dangling or not, and a value exists exactly where
    /// both operands hold one, as the meet of the two.  So meet is commutative,
    /// associative and idempotent on locations, and a meet with an equal trie
    /// changes nothing.
    ///
    /// This is the meet with `prune = false`; see [`PathMap::meet_pruned`].
    pub fn meet(ops: &impl ValOps<V>, a: &PathMap<V>, b: &PathMap<V>) -> PathMap<V> {
        let vals: Vec<(Vec<u8>, V)> = a
            .vals()
            .filter_map(|(k, av)| {
                Self::meet_val(ops, Some(av), b.val_at(k)).map(|v| (k.clone(), v))
            })
            .collect();
        PathMap::mk(vals, a.paths().filter(|q| b.path_exists(q)).cloned())
    }

    /// The trie with every dangling path removed: only the root and the locations
    /// on the way to a value remain.
    pub fn drop_dangling(&self) -> PathMap<V> {
        let vals: Vec<(Vec<u8>, V)> = self.vals().map(|(k, v)| (k.clone(), v.clone())).collect();
        PathMap::mk(vals, std::iter::empty())
    }

    /// The meet with `prune = true`, at its most pruned: the same values as
    /// [`PathMap::meet`], and only the locations on the way to one of them.
    ///
    /// `pathmap` may stop short of this: it can skip a node shared with the source
    /// rather than walk it, so a dangling path inside a shared node may survive.
    /// The result always lies between `meet_pruned` and `meet`, and is not
    /// compared by the fuzzer.
    pub fn meet_pruned(ops: &impl ValOps<V>, a: &PathMap<V>, b: &PathMap<V>) -> PathMap<V> {
        Self::meet(ops, a, b).drop_dangling()
    }

    /// Subtract.
    ///
    /// Two rules interact here.  Where `b` has no node at all, `a`'s subtree is
    /// kept verbatim — *including its dangling paths*.  Where `b` does have a
    /// node, only locations leading to a surviving value are kept.  `pathmap`
    /// gets this from `psubtract_dyn` short-circuiting on absent children; the
    /// model reproduces it by splitting on whether the location leaves `b`.
    pub fn sub(ops: &impl ValOps<V>, a: &PathMap<V>, b: &PathMap<V>) -> PathMap<V> {
        let surviving: Vec<(Vec<u8>, V)> = a
            .vals()
            .filter_map(|(k, av)| {
                Self::sub_val(ops, Some(av), b.val_at(k)).map(|v| (k.clone(), v))
            })
            .collect();
        // The locations at which `a` leaves `b` entirely: below one of these,
        // `psubtract_dyn` never looks again and `a` is copied verbatim.
        let untouched: Vec<&Vec<u8>> = a
            .paths()
            .filter(|q| !q.is_empty() && !b.path_exists(q) && b.path_exists(&q[..q.len() - 1]))
            .collect();
        let kept: Vec<Vec<u8>> = a
            .paths()
            .filter(|q| {
                surviving.iter().any(|(k, _)| k.starts_with(q))
                    || untouched.iter().any(|u| q.starts_with(u.as_slice()))
            })
            .cloned()
            .collect();
        PathMap::mk(surviving, kept)
    }

    /// Is `q` *validated* by `b` — does some non-empty prefix of `q` carry a
    /// value in `b`?
    ///
    /// This is the node-level reading of `prestrict`: a node has no root value,
    /// so the empty prefix never validates.  `PathMap::restrict` adds the empty
    /// prefix back in (see [`map::restrict`]), which is why the map-level and
    /// zipper-level operations disagree when the source has a root value.
    pub fn validated_by(b: &PathMap<V>, q: &[u8]) -> bool {
        (1..=q.len()).any(|i| b.val_at(&q[..i]).is_some())
    }

    /// `prestrict` at node level: keep the locations of `a` validated by `b`.
    /// Once a location is validated, everything below it is kept verbatim.
    pub fn restrict_below_root(a: &PathMap<V>, b: &PathMap<V>) -> PathMap<V> {
        let vals: Vec<(Vec<u8>, V)> = a
            .vals()
            .filter(|(k, _)| Self::validated_by(b, k))
            .map(|(k, v)| (k.clone(), v.clone()))
            .collect();
        let paths: Vec<Vec<u8>> = a
            .paths()
            .filter(|q| Self::validated_by(b, q))
            .cloned()
            .collect();
        PathMap::mk(vals, paths)
    }

    // -- path surgery -------------------------------------------------------

    /// `ZipperWriting::insert_prefix`: put `k` in front of every path below the
    /// root.  The root value is dropped — a node has nowhere to keep one.
    pub fn insert_prefix_below(&self, k: &[u8]) -> PathMap<V> {
        let vals: Vec<(Vec<u8>, V)> = self
            .vals()
            .filter(|(q, _)| !q.is_empty())
            .map(|(q, v)| (path::cat(k, q), v.clone()))
            .collect();
        let paths: Vec<Vec<u8>> = self
            .paths()
            .filter(|q| !q.is_empty())
            .map(|q| path::cat(k, q))
            .collect();
        PathMap::mk(vals, paths)
    }

    /// The existing locations exactly `k` bytes below the root, in depth-first
    /// order.
    pub fn k_paths(&self, k: usize) -> Vec<Vec<u8>> {
        self.paths().filter(|q| q.len() == k).cloned().collect()
    }

    /// `drop_head` / `ZipperWriting::join_k_path_into` at node level: strip the
    /// first `k` bytes from every path and join the results.
    ///
    /// Values sitting at depth *exactly* `k` are **discarded** — the joined node
    /// has nowhere to put a root value.  (`meet_k_path_into` keeps them, because
    /// it routes through `take_map`/`graft_map`, which do carry root values.  The
    /// asymmetry is real.)
    pub fn drop_head(&self, ops: &impl ValOps<V>, k: usize) -> PathMap<V> {
        if k == 0 {
            return self.clone();
        }
        let mut acc = PathMap::empty();
        for q in self.k_paths(k) {
            let mut m = self.subtrie(&q);
            m.remove_val(&[]);
            acc = PathMap::join(ops, &acc, &m);
        }
        acc
    }
}

