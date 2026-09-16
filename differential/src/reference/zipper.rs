//! `Zipper.lean` — the zipper, and its read API.

use crate::reference::basic::{ByteMask, path};
use crate::reference::pathmap::{Entry, PathMap};

// ===========================================================================
// Zipper.lean — the read API
// ===========================================================================

/// A cursor into a map.  Three things determine everything it can observe or do:
///
/// * the **map** it is looking at,
/// * its **root** — the absolute path at which it was created
///   (`root_prefix_path`); the zipper can never ascend above it, and can never
///   see anything outside the submap hanging below it, and
/// * its **path** — the relative path from the root to the current **focus**
///   (`path()`); `origin_path() = root ++ path`.
///
/// Read zippers and write zippers share this state and differ only in which
/// operations are offered, so `Zip` models both.  For a read zipper `trie` is a
/// snapshot taken when the zipper was created (`fork_read_zipper` etc.); for a
/// write zipper it is the live map, so mutations write back through
/// `root ++ path`.
///
/// # The focus may not exist
///
/// `descend_to` moves the focus anywhere, including off the map.  `path_exists`
/// then reports `false` while `path()` still reports the full path and `ascend`
/// still walks back up.  `path` is therefore an unconstrained byte string.
///
/// # The blind-zipper contract
///
/// `ZipperMoving` no longer provides `path()`: a zipper that does not track its
/// own path is a *blind* zipper, and `path()` / `move_to_path()` live in the
/// separate `ZipperPath: ZipperMoving` trait.  The model keeps `path` as a field
/// because it has to represent the location somehow, but it mirrors the split in
/// what each operation is allowed to *observe*: [`Zip::focus_byte`] is the only
/// positional information a blind zipper can read, and its value at the root is
/// deliberately unspecified.
///
/// The migration also changed what the movement operations report: `ascend`,
/// `ascend_until` and `ascend_until_branch` return the **number of bytes
/// ascended**, and `descend_indexed_byte`, `descend_first_byte`,
/// `descend_last_byte`, `to_next_sibling_byte` and `to_prev_sibling_byte` return
/// `Option<u8>` — the byte moved to — rather than a `bool`.
///
/// # Depth-first order is lexicographic order
///
/// Every iteration primitive is specified as "the least existing location
/// strictly after the focus, subject to ...", ordered by `Ord for [u8]`.  That
/// is equivalent to the implementation's node-by-node walk, and far easier to
/// state and to check.
#[derive(Clone, Debug)]
pub struct Zip<V> {
    /// The map: a snapshot, for a read zipper; the live map, for a write zipper.
    pub trie: PathMap<V>,
    /// `root_prefix_path()`: where the zipper was created.
    pub root: Vec<u8>,
    /// `path()`: the relative path from the root to the focus.
    pub path: Vec<u8>,
}

impl<V: Clone> Zip<V> {
    /// A zipper at the root of `trie`.
    pub fn new(trie: PathMap<V>) -> Self {
        Zip { trie, root: Vec::new(), path: Vec::new() }
    }

    /// A zipper rooted at `root`, focused at its root.
    pub fn at(trie: PathMap<V>, root: &[u8]) -> Self {
        Zip { trie, root: root.to_vec(), path: Vec::new() }
    }

    /// A zipper rooted at `root` with its focus already at `path`.
    pub fn at_path(trie: PathMap<V>, root: &[u8], path: &[u8]) -> Self {
        Zip { trie, root: root.to_vec(), path: path.to_vec() }
    }

    /// `ZipperAbsolutePath::origin_path`: the absolute path of the focus.
    pub fn focus(&self) -> Vec<u8> {
        path::cat(&self.root, &self.path)
    }

    /// `ZipperAbsolutePath::root_prefix_path`.
    pub fn root_prefix_path(&self) -> &[u8] {
        &self.root
    }

    // -- trait Zipper -------------------------------------------------------

    /// What the map holds at the focus: the whole answer to `path_exists` and
    /// `val` at once.  Definitions that must handle a location existing *without*
    /// a value are written against this, so the `match` will not compile until
    /// they say what happens to it.
    pub fn entry(&self) -> Entry<&V> {
        self.trie.entry_at(&self.focus())
    }

    /// `Zipper::path_exists`.
    pub fn path_exists(&self) -> bool {
        self.trie.path_exists(&self.focus())
    }

    /// `Zipper::is_val`.
    pub fn is_val(&self) -> bool {
        self.trie.val_at(&self.focus()).is_some()
    }

    /// `Zipper::child_mask`.  Empty on a leaf or a non-existent path.
    pub fn child_mask(&self) -> ByteMask {
        self.trie.child_mask(&self.focus())
    }

    /// `Zipper::child_count`.
    pub fn child_count(&self) -> usize {
        self.child_mask().count_bits()
    }

    /// `ZipperMoving::focus_byte`: the byte last descended to reach the focus.
    ///
    /// **Unspecified at the root.**  A zipper that retains knowledge of the map
    /// above its root may return the byte leading to that root; one that does
    /// not, or one rooted at the map root, returns `None`.  So a `Some` here does
    /// not mean the zipper has descended, and callers needing that distinction
    /// must ask [`Zip::at_root`].  The model returns the last byte of the
    /// relative path; a harness should mask the value at the root rather than
    /// comparing it.
    pub fn focus_byte(&self) -> Option<u8> {
        self.path.last().copied()
    }

    // -- trait ZipperValues / ZipperReadOnlyValues --------------------------

    /// `ZipperValues::val` (and `ZipperReadOnlyValues::get_val`, which differs
    /// only in the lifetime of the returned reference).
    pub fn val(&self) -> Option<&V> {
        self.trie.val_at(&self.focus())
    }

    /// `ZipperValues::val_at`: the value at `k`, relative to the focus.
    pub fn val_at(&self, k: &[u8]) -> Option<&V> {
        self.trie.val_at(&path::cat(&self.focus(), k))
    }

    // -- trait ZipperSubtries / ZipperInfallibleSubtries --------------------

    /// `ZipperInfallibleSubtries::make_map`.  Under the default `graft_root_vals`
    /// feature the value at the focus becomes the new map's root value.
    pub fn make_map(&self) -> PathMap<V> {
        self.trie.subtrie(&self.focus())
    }

    /// The node below the focus — what `get_focus` returns, i.e. `make_map` with
    /// the focus value stripped.  This, not `make_map`, is what the algebraic
    /// operations and `graft_internal` consume.
    pub fn focus_node(&self) -> PathMap<V> {
        let mut m = self.make_map();
        m.remove_val(&[]);
        m
    }

    /// `get_focus().is_none()`: the focus has no descendants.
    pub fn focus_node_is_empty(&self) -> bool {
        self.trie.below_is_empty(&self.focus())
    }

    // -- trait ZipperMoving — position --------------------------------------

    /// `ZipperMoving::at_root`.
    pub fn at_root(&self) -> bool {
        self.path.is_empty()
    }

    /// `ZipperMoving::reset`.
    pub fn reset(&mut self) {
        self.path.clear();
    }

    /// `ZipperMoving::val_count`: values at and below the focus.
    pub fn val_count(&self) -> usize {
        self.trie.val_count(&self.focus())
    }

    /// The absolute path of the relative location `q` — the model's `atPath`,
    /// which lets an ancestor or descendant be *named* and then asked about, so
    /// the specifications can say "the deepest ancestor such that ..." instead of
    /// walking there step by step.
    fn abs(&self, q: &[u8]) -> Vec<u8> {
        path::cat(&self.root, q)
    }

    // -- trait ZipperMoving — descent ---------------------------------------

    /// `ZipperMoving::descend_to`.  Never fails; the focus may end up off-map.
    pub fn descend_to(&mut self, k: &[u8]) {
        self.path.extend_from_slice(k);
    }

    /// `ZipperMoving::descend_to_byte`.
    pub fn descend_to_byte(&mut self, b: u8) {
        self.path.push(b);
    }

    /// `ZipperMoving::descend_to_check`: descend, then report existence.
    pub fn descend_to_check(&mut self, k: &[u8]) -> bool {
        self.descend_to(k);
        self.path_exists()
    }

    /// How far along `k` the path still exists, starting from the focus.
    ///
    /// Existence is prefix-closed, so the prefixes of `k` that still exist form
    /// an initial segment: the answer is the longest prefix of `k` that exists.
    fn reach(&self, k: &[u8]) -> usize {
        let f = self.focus();
        let mut probe = f.clone();
        let mut n = 0;
        if !self.trie.path_exists(&probe) {
            return 0;
        }
        for &b in k {
            probe.push(b);
            if !self.trie.path_exists(&probe) {
                break;
            }
            n += 1;
        }
        n
    }

    /// `ZipperMoving::descend_to_existing`: descend byte by byte, stopping where
    /// the path stops existing.  Returns the number of bytes actually descended.
    pub fn descend_to_existing(&mut self, k: &[u8]) -> usize {
        let n = self.reach(k);
        self.descend_to(&k[..n]);
        n
    }

    /// `ZipperMoving::descend_to_val`: descend byte by byte, stopping at the
    /// first value encountered *below* the starting focus, or where the path
    /// stops existing.
    pub fn descend_to_val(&mut self, k: &[u8]) -> usize {
        let reach = self.reach(k);
        let f = self.focus();
        // A value already at the focus does not stop it, so the scan starts at 1.
        let stop = (1..=reach)
            .find(|&j| self.trie.val_at(&path::cat(&f, &k[..j])).is_some())
            .unwrap_or(reach);
        self.descend_to(&k[..stop]);
        stop
    }

    /// `ZipperMoving::descend_to_existing_byte`.
    pub fn descend_to_existing_byte(&mut self, b: u8) -> bool {
        self.path.push(b);
        if self.path_exists() {
            true
        } else {
            self.path.pop();
            false
        }
    }

    /// `ZipperMoving::descend_indexed_byte`: descend into the `idx`-th child in
    /// ascending byte order, returning the byte moved to.  Out-of-range indices
    /// do nothing and return `None`.
    pub fn descend_indexed_byte(&mut self, idx: usize) -> Option<u8> {
        let b = self.child_mask().indexed_bit(idx)?;
        self.path.push(b);
        Some(b)
    }

    /// `ZipperMoving::descend_first_byte`.
    pub fn descend_first_byte(&mut self) -> Option<u8> {
        self.descend_indexed_byte(0)
    }

    /// `ZipperMoving::descend_last_byte`.
    pub fn descend_last_byte(&mut self) -> Option<u8> {
        let c = self.child_count();
        if c == 0 { None } else { self.descend_indexed_byte(c - 1) }
    }

    /// `ZipperMoving::descend_until`: descend while there is exactly one child,
    /// stopping on a value.  A no-op on a branch, a leaf, or a non-existent path.
    ///
    /// Nothing happens unless the focus has exactly one child.  When it does, the
    /// locations below it form a chain until the first one that branches, ends,
    /// or carries a value — so the destination is simply the *nearest* descendant
    /// that is a value or is not single-childed.  Depth-first order along a chain
    /// is order of increasing depth, so the first hit is the nearest one.
    pub fn descend_until(&mut self) -> bool {
        if self.child_count() != 1 {
            return false;
        }
        let f = self.focus();
        let hit = self
            .trie
            .strictly_below(&f)
            .find(|(q, v)| v.is_some() || self.trie.child_count(q) != 1)
            .map(|(q, _)| q.clone());
        match hit {
            Some(q) => {
                self.path = q[self.root.len()..].to_vec();
                true
            }
            None => false,
        }
    }

    /// `ZipperMoving::descend_until_observed`: `descend_until`, reporting each
    /// byte it descends to a `PathObserver`.
    ///
    /// For the `Vec<u8>` observer — the one the harness uses — the reported
    /// sequence is exactly the path delta, which is the only way a blind zipper
    /// can learn where it ended up.  That equality is the property worth checking.
    pub fn descend_until_observed(&mut self) -> (bool, Vec<u8>) {
        let before = self.path.len();
        let moved = self.descend_until();
        (moved, self.path[before..].to_vec())
    }

    /// `ZipperMoving::descend_until_max_bytes`: `descend_until`, then ascend back
    /// to at most `max_bytes` below the starting depth.
    pub fn descend_until_max_bytes(&mut self, max_bytes: usize) -> bool {
        if max_bytes == 0 {
            return false;
        }
        let target = self.path.len() + max_bytes;
        let moved = self.descend_until();
        if self.path.len() > target {
            self.path.truncate(target);
        }
        moved
    }

    // -- trait ZipperMoving — ascent ----------------------------------------

    /// `ZipperMoving::ascend`: ascend `steps` bytes, clamping at the zipper root.
    /// Returns the **number of bytes actually ascended**, which is smaller than
    /// `steps` when the root was closer than that.
    pub fn ascend(&mut self, steps: usize) -> usize {
        let n = steps.min(self.path.len());
        self.path.truncate(self.path.len() - n);
        n
    }

    /// `ZipperMoving::ascend_byte`: still a `bool`, defined as `ascend(1) == 1`.
    pub fn ascend_byte(&mut self) -> bool {
        self.ascend(1) == 1
    }

    /// `ZipperMoving::ascend_until`: ascend to the nearest strict ancestor that
    /// carries a value or branches, or to the root.  Returns the number of bytes
    /// ascended; `0` means the zipper was already at its root.
    pub fn ascend_until(&mut self) -> usize {
        self.ascend_until_with(|z, a| {
            z.trie.val_at(a).is_some() || z.trie.child_count(a) > 1
        })
    }

    /// `ZipperMoving::ascend_until_branch`: like `ascend_until`, but values do
    /// not stop the ascent.  Returns the number of bytes ascended.
    pub fn ascend_until_branch(&mut self) -> usize {
        self.ascend_until_with(|z, a| z.trie.child_count(a) > 1)
    }

    /// The shared core: the destination is the deepest strict ancestor
    /// satisfying `stop`, or the zipper root, which always qualifies — so there
    /// is always an answer.
    fn ascend_until_with(&mut self, stop: impl Fn(&Self, &[u8]) -> bool) -> usize {
        if self.at_root() {
            return 0;
        }
        let mut dest = 0;
        for n in (1..self.path.len()).rev() {
            let anc = self.abs(&self.path[..n]);
            if stop(self, &anc) {
                dest = n;
                break;
            }
        }
        let moved = self.path.len() - dest;
        self.path.truncate(dest);
        moved
    }

    // -- trait ZipperMoving — lateral movement ------------------------------

    /// `ZipperMoving::to_next_sibling_byte`.
    ///
    /// At the zipper root there is no last byte, so the documented answer — and
    /// the `ZipperMoving` default implementation's answer — is "did not move".
    ///
    /// BUG (`pathmap` 0.3.1): the native `ReadZipper` implementation instead
    /// consults the last byte of the *absolute* origin path, so a read zipper
    /// whose root does not exist but has a sibling **leaves its own root**.  With
    /// map `{[0,0,3] ↦ v}` and a zipper rooted at `[0,0,1]`,
    /// `to_next_sibling_byte()` returns `true`, `path()` still reports `[]` and
    /// `at_root()` still reports `true`, but `origin_path()` is now `[0,0,3]` and
    /// the zipper reads `v`.  That breaks the containment a `ZipperHead` relies
    /// on to hand out non-overlapping zippers.  The model specifies the
    /// documented behaviour; the differential harness skips the operation at the
    /// root so the known bug does not mask others.
    ///
    /// Transcribed from the *current* `Zipper.lean`.  The archive this file came
    /// from described the bug as fixed and ran the op at the root; `Fuzz.lean`
    /// and `harness.rs` both skip it today, so the model follows them.  See the
    /// report accompanying this port for whether the skip is still earned.
    pub fn to_next_sibling_byte(&mut self) -> Option<u8> {
        self.to_sibling_byte(true)
    }

    /// `ZipperMoving::to_prev_sibling_byte`.
    pub fn to_prev_sibling_byte(&mut self) -> Option<u8> {
        self.to_sibling_byte(false)
    }

    /// Both sibling moves are keyed on `focus_byte`, whose value at the root is
    /// unspecified, so the `at_root` guard is what keeps the zipper inside its
    /// own subtree.
    // `to_*` here is `pathmap`'s "move the cursor to", not a conversion, so the
    // `&mut self` receiver is right and clippy's naming convention does not apply.
    #[allow(clippy::wrong_self_convention)]
    fn to_sibling_byte(&mut self, forward: bool) -> Option<u8> {
        let cur = self.focus_byte()?;
        if self.at_root() {
            return None;
        }
        self.path.pop();
        let mask = self.child_mask();
        let hit = if forward { mask.next_bit(cur) } else { mask.prev_bit(cur) };
        match hit {
            Some(b) => {
                self.path.push(b);
                Some(b)
            }
            None => {
                self.path.push(cur);
                None
            }
        }
    }

    /// `ZipperMoving::move_to_path`: jump to `p` relative to the zipper root.
    /// Returns the number of bytes shared between the old and the new location.
    pub fn move_to_path(&mut self, p: &[u8]) -> usize {
        let overlap = p
            .iter()
            .zip(self.path.iter())
            .take_while(|(a, b)| a == b)
            .count();
        self.path = p.to_vec();
        overlap
    }

    // -- trait ZipperMoving — depth-first stepping --------------------------

    /// `ZipperMoving::to_next_step`: the next existing location in depth-first
    /// order.  On exhaustion the focus returns to the root and the result is
    /// `false`.
    pub fn to_next_step(&mut self) -> bool {
        self.step_to(|_, _| true)
    }

    // -- trait ZipperIteration ----------------------------------------------

    /// `ZipperIteration::to_next_val`: the next existing location carrying a
    /// value, in depth-first order.  Never reports the value at the starting
    /// focus.  On exhaustion the focus returns to the root and the result is
    /// `false`.
    pub fn to_next_val(&mut self) -> bool {
        self.step_to(|_, v| v.is_some())
    }

    /// The shared core of the two: the least existing location strictly after the
    /// focus and within the zipper's own subtree that satisfies `pred`.
    fn step_to(&mut self, pred: impl Fn(&[u8], &Option<V>) -> bool) -> bool {
        let f = self.focus();
        let root = self.root.clone();
        let hit = self
            .trie
            .after_within(&f, &root)
            .find(|(q, v)| pred(q, v))
            .map(|(q, _)| q.clone());
        match hit {
            Some(q) => {
                self.path = q[self.root.len()..].to_vec();
                true
            }
            None => {
                self.reset();
                false
            }
        }
    }

    /// `ZipperReadOnlyIteration::to_next_get_val`.
    pub fn to_next_get_val(&mut self) -> Option<&V> {
        if self.to_next_val() { self.val() } else { None }
    }

    /// `ZipperIteration::descend_last_path`: follow the last child to the end of
    /// the depth-first-greatest path below the focus.
    pub fn descend_last_path(&mut self) -> bool {
        let f = self.focus();
        match self.trie.at_or_below(&f).last().map(|(q, _)| q.clone()) {
            Some(q) if q.len() > f.len() => {
                self.path = q[self.root.len()..].to_vec();
                true
            }
            _ => false,
        }
    }

    /// The shared core of `descend_first_k_path` and `to_next_k_path`
    /// (`k_path_internal`): the depth-first-least existing location that is
    /// exactly `k` bytes below the common ancestor at depth `base`, and that
    /// comes strictly after the current focus.  On failure the focus moves to
    /// that ancestor.
    fn k_path_from(&mut self, base: usize, k: usize) -> bool {
        let anc_rel = self.path[..base].to_vec();
        let anc = self.abs(&anc_rel);
        let f = self.focus();
        let want = anc.len() + k;
        let hit = self
            .trie
            .after_within(&f, &anc)
            .find(|(q, _)| q.len() == want)
            .map(|(q, _)| q.clone());
        match hit {
            Some(q) => {
                self.path = q[self.root.len()..].to_vec();
                true
            }
            None => {
                self.path = anc_rel;
                false
            }
        }
    }

    /// `ZipperIteration::descend_first_k_path`: descend to the depth-first-first
    /// existing location exactly `k` bytes below the focus.  Leaves the focus
    /// untouched and returns `false` when there is none.
    pub fn descend_first_k_path(&mut self, k: usize) -> bool {
        let base = self.path.len();
        self.k_path_from(base, k)
    }

    /// `ZipperIteration::to_next_k_path`: the next existing location at the same
    /// depth, under the common ancestor `k` bytes above the focus.  On exhaustion
    /// the focus moves to that ancestor and the result is `false`.
    ///
    /// NOTE: when the focus is shallower than `k`, the *native* `ReadZipper` falls
    /// back to the **zipper root** as the common ancestor — so the call behaves
    /// like `descend_first_k_path(k)` from the root and can succeed.  The
    /// `ZipperIteration` default implementation instead returns `false` without
    /// moving.  The model follows the native `ReadZipper`, which is what the
    /// public API reaches.
    pub fn to_next_k_path(&mut self, k: usize) -> bool {
        if k <= self.path.len() {
            let base = self.path.len() - k;
            self.k_path_from(base, k)
        } else {
            self.k_path_from(0, k)
        }
    }

    // -- trait ZipperForking ------------------------------------------------

    /// `ZipperForking::fork_read_zipper`: a new zipper rooted at the current
    /// focus, over a snapshot of the same map.
    pub fn fork_read_zipper(&self) -> Zip<V> {
        Zip { trie: self.trie.clone(), root: self.focus(), path: Vec::new() }
    }
}

