//! `Write.lean` — the write zipper: everything that mutates `Zip::trie`
//! through the focus `root ++ path`.

use crate::reference::basic::{AlgStatus, ByteMask, ValOps, path};
use crate::reference::pathmap::{Entry, PathMap};
use crate::reference::zipper::Zip;

// ===========================================================================
// Write.lean — the write zipper
// ===========================================================================
//
// Everything here mutates `Zip::trie` through the focus `root ++ path`.  Two
// invariants shape the whole API and are worth stating up front:
//
// 1. **A node is what lies strictly below a location.**  `get_focus`,
//    `graft_internal`, and every `*_dyn` algebraic primitive operate on nodes, so
//    they never see or touch the value *at* the focus.  Operations that do affect
//    the focus value (`graft`, `graft_map`, `make_map`, `take_map`,
//    `join_map_into`, `meet_into`, `subtract_into`) do it in a separate step —
//    this is the `graft_root_vals` cargo feature, which is on by default and
//    which the model assumes throughout.  Note the resulting asymmetry: `graft`
//    adopts the source's focus value but `join_into` does **not** join focus
//    values.
//
// 2. **Pruning is opt-in and local.**  A write leaves dangling paths behind
//    unless `prune` is passed, and even then `prune_path` only fires when the
//    focus is a dangling tip.

impl<V: Clone> Zip<V> {
    // -- values at the focus ------------------------------------------------

    /// `ZipperWriting::get_val_mut` — same observation as [`Zip::val`], mutably.
    /// Returns `Some` exactly when `val` does; it never creates anything.
    pub fn get_val_mut(&mut self) -> Option<&mut V> {
        let f = self.focus();
        self.trie.entries.get_mut(&f).and_then(|slot| slot.as_mut())
    }

    /// `ZipperWriting::set_val`: sets the value at the focus, **creating the
    /// path** if it did not exist.  Returns the replaced value.
    pub fn set_val(&mut self, v: V) -> Option<V> {
        let f = self.focus();
        self.trie.set_val(&f, v)
    }

    /// Writing through the reference `get_val_mut` returns.
    ///
    /// Specified as: when there is a value, this is `set_val`; when there is not,
    /// it is a no-op — in particular it must **not** create the path, which is
    /// what separates it from `set_val`.
    pub fn get_val_mut_write(&mut self, v: V) -> Option<V> {
        match self.get_val_mut() {
            Some(slot) => Some(std::mem::replace(slot, v)),
            None => None,
        }
    }

    /// `ZipperWriting::get_val_or_set_mut`: the value at the focus, inserting
    /// `default` if there is none.  Inserting creates the path, as `set_val` does.
    pub fn get_val_or_set_mut(&mut self, d: V) -> V {
        let (v, _) = self.get_val_or_set_mut_with(d);
        v
    }

    /// `ZipperWriting::get_val_or_set_mut_with`: as above, but the value is
    /// produced by a closure.
    ///
    /// The documented contract is that the closure supplies the value "if no
    /// value exists", so it must be called **exactly when the focus has no
    /// value** — calling it otherwise would be observable to any caller whose
    /// closure has a side effect (allocating, taking a lock, bumping a counter).
    /// The second component of the result records whether it ran, so a harness
    /// can compare that too.
    pub fn get_val_or_set_mut_with(&mut self, d: V) -> (V, bool) {
        match self.val() {
            Some(v) => (v.clone(), false),
            None => {
                self.set_val(d.clone());
                (d, true)
            }
        }
    }

    // -- pruning ------------------------------------------------------------

    /// `ZipperWriting::prune_path`: delete the dangling chain ending at the
    /// focus, stopping at the first location above it that carries a value or
    /// branches.  The focus does **not** move.
    ///
    /// Two things about this differ from the doc comment on
    /// `ZipperWriting::prune_path`, both verified against `pathmap` 0.3.1:
    ///
    /// * **It prunes above the zipper's root.**  The doc says "This method cannot
    ///   prune the trie above the zipper's root", but a write zipper rooted at
    ///   `ab` whose focus is a dangling tip deletes `a` and `ab` too, right up to
    ///   the nearest branch or value in the *whole map*.  The model therefore
    ///   passes `0`, not `self.root.len()`, as the stop depth.
    /// * **The returned count is not well-defined** when the zipper's root is
    ///   non-empty.  `prune_path` returns `max(node_pruned_bytes,
    ///   trie_pruned_bytes)`, and `node_pruned_bytes` depends on where the
    ///   internal node holding the focus happens to begin.  Empirically, a
    ///   40-byte dangling chain under a zipper rooted at depth 5 reports 40
    ///   (absolute) while a 100-byte one reports 95 (relative).  The *effect* is
    ///   the same in both cases; only the number differs.  The model reports the
    ///   absolute count, and a harness should compare the count only for zippers
    ///   rooted at the map root.
    pub fn prune_path(&mut self) -> usize {
        let f = self.focus();
        self.trie.prune_path(0, &f)
    }

    /// `ZipperWriting::prune_ascend`: `prune_path` followed by ascending that far.
    pub fn prune_ascend(&mut self) -> usize {
        let n = self.prune_path();
        self.ascend(n);
        n
    }

    /// `ZipperWriting::remove_val`: removes the value, leaving the location as a
    /// dangling path unless `prune` reclaims it.
    ///
    /// Pruning only happens when a value was actually removed: `remove_val`
    /// returns early on the `None` branch, so `remove_val(true)` at a location
    /// with no value leaves any dangling path in place.
    pub fn remove_val(&mut self, prune: bool) -> Option<V> {
        let valued = match self.entry() {
            // Nothing to remove.  Note the `prune` flag does not fire here:
            // `remove_val` returns early on this branch, so a dangling path is
            // left in place.
            Entry::Absent | Entry::Bare => false,
            Entry::Valued(_) => true,
        };
        if !valued {
            return None;
        }
        let f = self.focus();
        let v = self.trie.remove_val(&f);
        if prune {
            self.trie.prune_path(0, &f);
        }
        v
    }

    /// `ZipperWriting::create_path`: make the focus exist as a dangling path.
    /// Returns whether new bytes were created.
    ///
    /// The guard is on the *absolute* focus, not on `at_root`: `create_path`
    /// bails out when there is no key left to create, which is the map root, not
    /// the zipper root.  A zipper rooted at `ab` whose root does not yet exist
    /// will happily create it.
    pub fn create_path(&mut self) -> bool {
        let f = self.focus();
        if f.is_empty() {
            return false;
        }
        let create = match self.trie.entry_at(&f) {
            Entry::Absent => true,
            // Already there, with or without a value: nothing to create, and in
            // particular an existing value is never disturbed.
            Entry::Bare | Entry::Valued(_) => false,
        };
        if create {
            self.trie.add_path(&f);
        }
        create
    }

    // -- removing subtries --------------------------------------------------

    /// `ZipperWriting::remove_branches`: delete everything strictly below the
    /// focus.  The value at the focus survives.  Returns whether anything was
    /// removed.
    pub fn remove_branches(&mut self, prune: bool) -> bool {
        let f = self.focus();
        let removed = !self.trie.below_is_empty(&f);
        self.trie.remove_below(&f);
        if prune {
            self.trie.prune_path(0, &f);
        }
        removed
    }

    /// `ZipperWriting::remove_unmasked_branches`: keep only the child bytes set
    /// in `mask`; delete the rest along with their subtries.
    pub fn remove_unmasked_branches(&mut self, mask: &ByteMask, prune: bool) {
        let f = self.focus();
        let doomed: Vec<u8> = self
            .child_mask()
            .bytes()
            .iter()
            .copied()
            .filter(|&b| !mask.contains(b))
            .collect();
        for b in doomed {
            self.trie.remove_at(&path::push(&f, b));
        }
        if prune {
            self.trie.prune_path(0, &f);
        }
    }

    // -- grafting -----------------------------------------------------------

    /// Replace the submap at the focus with `m`, treating `m` as a whole
    /// `PathMap`: its root value becomes the focus value (or clears it), and its
    /// branches become the focus's branches.  This is
    /// `ZipperWriting::graft_map`.
    pub fn graft_map(&mut self, m: &PathMap<V>) {
        let f = self.focus();
        graft_map_at(&mut self.trie, &f, m);
    }

    /// `ZipperWriting::graft`: graft the submap at `src`'s focus, root value
    /// included.
    pub fn graft(&mut self, src: &Zip<V>) {
        self.graft_map(&src.make_map());
    }

    /// `ZipperWriting::graft_src_at`: graft the submap `k` bytes below `src`'s
    /// focus.
    pub fn graft_src_at(&mut self, src: &Zip<V>, k: &[u8]) {
        let p = path::cat(&src.focus(), k);
        self.graft_map(&src.trie.subtrie(&p));
    }

    /// `ZipperWriting::graft_masked_branches`: graft the source's child branches
    /// for each byte set in `mask`.
    ///
    /// Each set bit is a `graft_src_at` of the source's corresponding child, so
    /// the child's *value* travels with it, and a set bit whose branch is absent
    /// from the source leaves that branch absent here — grafting nothing removes.
    /// With `remove_unset`, branches for clear bits are removed first, so
    /// `child_mask` afterwards is a subset of `mask`; without it they are left
    /// alone.
    ///
    /// `WriteZipperCore` overrides the trait's default implementation with a
    /// native one, so this op is really comparing two implementations of the same
    /// contract.
    pub fn graft_masked_branches(&mut self, src: &Zip<V>, mask: &ByteMask, remove_unset: bool) {
        if remove_unset {
            self.remove_branches(false);
        }
        let f = self.focus();
        let sf = src.focus();
        for &b in mask.bytes() {
            let m = src.trie.subtrie(&path::push(&sf, b));
            graft_map_at(&mut self.trie, &path::push(&f, b), &m);
        }
    }

    /// `ZipperWriting::graft_child_maps`: as above, but the branches come from an
    /// explicit list of maps rather than from a source zipper.
    ///
    /// Feeding it the source's own child submaps must therefore produce exactly
    /// what [`Zip::graft_masked_branches`] produces from that source — a harness
    /// should check the two against each other as well as against this
    /// definition.
    pub fn graft_child_maps(&mut self, maps: &[(ByteMask, PathMap<V>)], remove_unset: bool) {
        if remove_unset {
            self.remove_branches(false);
        }
        let f = self.focus();
        for (mask, m) in maps {
            if let [b] = mask.bytes() {
                graft_map_at(&mut self.trie, &path::push(&f, *b), m);
            }
        }
    }

    /// `ZipperWriting::take_map`: remove the submap at the focus (value included)
    /// and return it as a `PathMap`.  Returns `None` when there was nothing to
    /// take.
    pub fn take_map(&mut self, prune: bool) -> Option<PathMap<V>> {
        let f = self.focus();
        let rv = self.trie.remove_val(&f);
        if prune {
            self.trie.prune_path(0, &f);
        }
        let below = self.focus_node();
        self.trie.remove_below(&f);
        if prune {
            self.trie.prune_path(0, &f);
        }
        let nothing = below.is_empty_map() && rv.is_none();
        let mut taken = below;
        if let Some(v) = rv {
            taken.set_val(&[], v);
        }
        if nothing { None } else { Some(taken) }
    }

    // -- path surgery -------------------------------------------------------

    /// `ZipperWriting::insert_prefix`: put `pre` in front of every path below the
    /// focus.  The focus value is untouched.  Returns `false` at a location with
    /// no descendants.
    ///
    /// BUG (`pathmap` 0.3.1): with an **empty** prefix this should be the
    /// identity, but `make_parents_in(b"", node)` discards the node — the submap
    /// below the focus is destroyed and `true` is still returned.  The model
    /// specifies the identity; a differential harness should skip
    /// `insert_prefix("")` so the known divergence does not mask others.
    pub fn insert_prefix(&mut self, pre: &[u8]) -> bool {
        if self.focus_node_is_empty() {
            return false;
        }
        let f = self.focus();
        let node = self.focus_node().insert_prefix_below(pre);
        self.trie.graft_below(&f, &node);
        true
    }

    /// `ZipperWriting::remove_prefix`: lift the submap below the focus up by `n`
    /// bytes, replacing whatever was below the new (ascended) focus.  Returns
    /// whether the full `n` bytes could be ascended.
    ///
    /// Note the value at the old focus is *not* carried up — it belonged to the
    /// parent cell, not to the node that gets moved.
    pub fn remove_prefix(&mut self, n: usize) -> bool {
        let below = self.focus_node();
        // `ascend` reports how far it got, so "were all `n` bytes removed" is a
        // comparison rather than the flag it used to return directly.
        let ascended = self.ascend(n);
        let f = self.focus();
        self.trie.graft_below(&f, &below);
        ascended == n
    }
}

/// `graft_map` against a bare map, factored out so the three grafting entry
/// points cannot drift: replace everything below `p` with `m`'s branches, then
/// let `m`'s root value set or clear the value at `p`.
fn graft_map_at<V: Clone>(t: &mut PathMap<V>, p: &[u8], m: &PathMap<V>) {
    t.graft_below(p, m);
    match m.val_at(&[]) {
        Some(v) => {
            t.set_val(p, v.clone());
        }
        None => {
            t.remove_val(p);
        }
    }
}

// ---------------------------------------------------------------------------
// Write.lean — algebraic operations
// ---------------------------------------------------------------------------
//
// `AlgebraicStatus` is decided structurally: `Identity` exactly when the output
// equals the input (`Identity(SELF_IDENT)`), `None` when the output is empty, and
// `Element` otherwise.  `Identity(COUNTER_IDENT)` — the output equals the
// *source* — is reported as `Element` by `pathmap`, and the model agrees because
// the output still differs from `self`.

impl<V: Clone> Zip<V> {
    /// The status of replacing `before` with `after`.
    fn node_status(ops: &impl ValOps<V>, before: &PathMap<V>, after: &PathMap<V>) -> AlgStatus {
        if after.is_empty_map() {
            AlgStatus::None
        } else if after.beq_t(ops, before) {
            AlgStatus::Identity
        } else {
            AlgStatus::Element
        }
    }

    /// Write `r` below the focus, pruning afterwards when the node annihilated
    /// and the caller asked for it.  The shape shared by `meet_into`,
    /// `subtract_into` and their kin.
    fn write_node(&mut self, st: AlgStatus, r: &PathMap<V>, prune: bool) {
        if st == AlgStatus::Identity {
            return;
        }
        let f = self.focus();
        self.trie.graft_below(&f, r);
        if st == AlgStatus::None && prune {
            self.trie.prune_path(0, &f);
        }
    }

    /// `ZipperWriting::join_into`: union the source's submap into the focus's.
    ///
    /// The focus **values are not joined** — only the nodes below the focus are.
    /// (The map-consuming variant [`Zip::join_map_into`] *does* join root values.)
    pub fn join_into(&mut self, ops: &impl ValOps<V>, src: &Zip<V>) -> AlgStatus {
        let self_b = self.focus_node();
        let src_b = src.focus_node();
        if src_b.is_empty_map() {
            return if self_b.is_empty_map() { AlgStatus::None } else { AlgStatus::Identity };
        }
        let r = PathMap::join(ops, &self_b, &src_b);
        if r.beq_t(ops, &self_b) {
            AlgStatus::Identity
        } else {
            let f = self.focus();
            self.trie.graft_below(&f, &r);
            AlgStatus::Element
        }
    }

    /// `ZipperWriting::join_map_into`: union a consumed `PathMap` into the focus.
    ///
    /// Unlike [`Zip::join_into`] this *does* join the map's root value into the
    /// focus value.  It also short-circuits: when the map has no root node, the
    /// node status is returned directly and the value status computed above is
    /// discarded — even though the value has already been written.
    pub fn join_map_into(&mut self, ops: &impl ValOps<V>, m: &PathMap<V>) -> AlgStatus {
        let (val_status, val_was_none) = match (self.val().cloned(), m.val_at(&[]).cloned()) {
            (Some(sv), Some(mv)) => {
                let r = ops.pjoin(&sv, &mv);
                let st = AlgStatus::of_val_res(&r);
                match r.resolve(&sv, &mv) {
                    Some(v) => {
                        self.set_val(v);
                    }
                    None => {
                        self.remove_val(false);
                    }
                }
                (st, false)
            }
            (None, Some(mv)) => {
                self.set_val(mv);
                (AlgStatus::Element, true)
            }
            (Some(_), None) => (AlgStatus::Identity, false),
            (None, None) => (AlgStatus::None, true),
        };
        let mut src_b = m.clone();
        src_b.remove_val(&[]);
        if src_b.is_empty_map() {
            // Short-circuit, and note the asymmetry with `join_into`: this branch
            // tests `self.get_focus().is_none()` (does a node exist at all?), not
            // `node_is_empty()`.  So a *bare* focus reports `Identity` here, where
            // `join_into` on the same state reports `None`.
            return match self.entry() {
                Entry::Bare | Entry::Valued(_) => AlgStatus::Identity,
                Entry::Absent => AlgStatus::None,
            };
        }
        let self_b = self.focus_node();
        let r = PathMap::join(ops, &self_b, &src_b);
        let node_status = if r.beq_t(ops, &self_b) { AlgStatus::Identity } else { AlgStatus::Element };
        if node_status != AlgStatus::Identity {
            let f = self.focus();
            self.trie.graft_below(&f, &r);
        }
        AlgStatus::merge(node_status, val_status, true, val_was_none)
    }

    /// `ZipperWriting::join_into_take`: like [`Zip::join_into`], but the source
    /// submap is removed from the source zipper's map.
    pub fn join_into_take(
        &mut self,
        ops: &impl ValOps<V>,
        src: &mut Zip<V>,
        prune: bool,
    ) -> AlgStatus {
        let src_b = src.focus_node();
        let sf = src.focus();
        src.trie.remove_below(&sf);
        if prune {
            src.trie.prune_path(0, &sf);
        }
        let self_b = self.focus_node();
        if src_b.is_empty_map() {
            return if self_b.is_empty_map() { AlgStatus::None } else { AlgStatus::Identity };
        }
        let r = PathMap::join(ops, &self_b, &src_b);
        let st = if r.beq_t(ops, &self_b) { AlgStatus::Identity } else { AlgStatus::Element };
        let f = self.focus();
        self.trie.graft_below(&f, &r);
        st
    }

    /// `ZipperWriting::meet_into`: intersect the focus's submap with the
    /// source's.
    ///
    /// The value step runs first and can prune the focus out from under the node
    /// step.  A meet drops every dangling path, since a location only survives if
    /// it leads to a surviving value.
    pub fn meet_into(&mut self, ops: &impl ValOps<V>, src: &Zip<V>, prune: bool) -> AlgStatus {
        let (val_status, val_was_none) = match (self.val().cloned(), src.val().cloned()) {
            (Some(sv), Some(ov)) => {
                let r = ops.pmeet(&sv, &ov);
                let st = AlgStatus::of_val_res(&r);
                match r.resolve(&sv, &ov) {
                    Some(v) => {
                        self.set_val(v);
                    }
                    None => {
                        self.remove_val(prune);
                    }
                }
                (st, false)
            }
            (None, Some(_)) => (AlgStatus::None, true),
            (Some(_), None) => {
                self.remove_val(prune);
                (AlgStatus::None, false)
            }
            (None, None) => (AlgStatus::None, true),
        };
        let self_b = self.focus_node();
        let src_b = src.focus_node();
        if self_b.is_empty_map() {
            return AlgStatus::merge(AlgStatus::None, val_status, true, val_was_none);
        }
        if src_b.is_empty_map() {
            let f = self.focus();
            self.trie.remove_below(&f);
            if prune {
                self.trie.prune_path(0, &f);
            }
            return AlgStatus::merge(AlgStatus::None, val_status, false, val_was_none);
        }
        let r = PathMap::meet(ops, &self_b, &src_b);
        let st = Self::node_status(ops, &self_b, &r);
        self.write_node(st, &r, prune);
        AlgStatus::merge(st, val_status, false, val_was_none)
    }

    /// `ZipperWriting::subtract_into`: remove the source's submap from the
    /// focus's.
    ///
    /// Where the source has no node at all, `self`'s subtree survives untouched —
    /// dangling paths included.  Where it does, only locations leading to a
    /// surviving value are kept.
    pub fn subtract_into(&mut self, ops: &impl ValOps<V>, src: &Zip<V>, prune: bool) -> AlgStatus {
        let (val_status, val_was_none) = match (self.val().cloned(), src.val().cloned()) {
            (Some(sv), Some(ov)) => {
                let r = ops.psub(&sv, &ov);
                let st = AlgStatus::of_val_res(&r);
                match r.resolve(&sv, &ov) {
                    Some(v) => {
                        self.set_val(v);
                    }
                    None => {
                        self.remove_val(prune);
                    }
                }
                (st, false)
            }
            (None, Some(_)) => (AlgStatus::None, true),
            (Some(_), None) => (AlgStatus::Identity, false),
            (None, None) => (AlgStatus::None, true),
        };
        let self_b = self.focus_node();
        let src_b = src.focus_node();
        if src_b.is_empty_map() {
            let node = if self_b.is_empty_map() { AlgStatus::None } else { AlgStatus::Identity };
            return AlgStatus::merge(node, val_status, self_b.is_empty_map(), val_was_none);
        }
        if self_b.is_empty_map() {
            return AlgStatus::merge(AlgStatus::None, val_status, true, val_was_none);
        }
        let r = PathMap::sub(ops, &self_b, &src_b);
        let st = Self::node_status(ops, &self_b, &r);
        self.write_node(st, &r, prune);
        AlgStatus::merge(st, val_status, false, val_was_none)
    }

    /// `ZipperWriting::meet_2`: meet two *source* submaps and write the result at
    /// the focus.
    ///
    /// Two things separate this from [`Zip::meet_into`].  It does not consult
    /// what is already at the focus, so — as the implementation notes — it never
    /// reports `Identity`, only `Element` or `None`.  And it works on nodes, so
    /// neither source's focus value is consulted and the focus value here is left
    /// untouched.
    pub fn meet_2(&mut self, ops: &impl ValOps<V>, a: &Zip<V>, b: &Zip<V>) -> AlgStatus {
        let an = a.focus_node();
        let bn = b.focus_node();
        let f = self.focus();
        if an.is_empty_map() || bn.is_empty_map() {
            self.trie.remove_below(&f);
            return AlgStatus::None;
        }
        let r = PathMap::meet(ops, &an, &bn);
        if r.is_empty_map() {
            self.trie.remove_below(&f);
            AlgStatus::None
        } else {
            self.trie.graft_below(&f, &r);
            AlgStatus::Element
        }
    }

    /// `ZipperWriting::restrict`: keep only the paths below the focus that are
    /// prefixed by a path to a value in the source's submap.
    ///
    /// The empty prefix does **not** validate here: the source's *focus value* is
    /// invisible to a node-level `prestrict`.  [`map::restrict`] does consult the
    /// root value, so the two disagree exactly when the source has a value at its
    /// focus.  The focus value of `self` is never touched.
    pub fn restrict(&mut self, ops: &impl ValOps<V>, src: &Zip<V>) -> AlgStatus {
        let src_b = src.focus_node();
        let self_b = self.focus_node();
        if src_b.is_empty_map() {
            let f = self.focus();
            self.trie.remove_below(&f);
            return AlgStatus::None;
        }
        if self_b.is_empty_map() {
            return AlgStatus::None;
        }
        let r = PathMap::restrict_below_root(&self_b, &src_b);
        let st = Self::node_status(ops, &self_b, &r);
        if st == AlgStatus::Identity {
            return AlgStatus::Identity;
        }
        let f = self.focus();
        self.trie.graft_below(&f, &r);
        st
    }

    /// `ZipperWriting::restricting`: the mirror image — fill in `self`'s "stem"
    /// paths with the source's submaps.  `self`'s submap is replaced by the
    /// source's, restricted by the paths to values in `self`.
    ///
    /// Returns `false`, leaving `self` untouched, when either side has nothing
    /// below its focus.  Note this is decided by `get_focus().is_none()`, which
    /// is true when there is no node below the focus but *false* when an empty
    /// node happens to have been materialised there by `create_path` or
    /// `remove_val` — see FINDINGS.md #8.  The model specifies the common case.
    pub fn restricting(&mut self, src: &Zip<V>) -> bool {
        if src.focus_node_is_empty() || self.focus_node_is_empty() {
            return false;
        }
        let r = PathMap::restrict_below_root(&src.focus_node(), &self.focus_node());
        let f = self.focus();
        self.trie.graft_below(&f, &r);
        true
    }

    // -- collapsing path segments -------------------------------------------

    /// `ZipperWriting::join_k_path_into` (a.k.a. `drop_head`): strip the leading
    /// `k` bytes from every path below the focus and join the results.
    ///
    /// Values sitting at depth exactly `k` are **lost**: the joined node has no
    /// root value slot.  Returns whether anything survives below the focus.
    ///
    /// BUG (`pathmap` 0.3.1): `k = 0` should be the identity — dropping no bytes
    /// — but `drop_head_dyn(0)` collapses the submap instead.  On
    /// `{[] ↦ 0, [0] ↦ 0, [0,0] ↦ 0, [1,0] ↦ 0}` it leaves `{[] ↦ 0, [0] ↦ 0}`.
    /// The model specifies the identity; a harness should skip `k = 0`.
    pub fn join_k_path_into(&mut self, ops: &impl ValOps<V>, k: usize, prune: bool) -> bool {
        let below = self.focus_node();
        let res = if below.is_empty_map() {
            false
        } else {
            let r = below.drop_head(ops, k);
            let survives = !r.is_empty_map();
            let f = self.focus();
            self.trie.graft_below(&f, &r);
            survives
        };
        if prune && !res {
            self.prune_path();
        }
        res
    }

    /// `meet_k_path_into` is **not implementable** for these arguments: its
    /// provisional implementation drives `descend_first_k_path` through the
    /// `ZipperIteration` *default* loop, which spins forever when the focus has
    /// no children, and which escapes the focus's subtree entirely when `k = 0`.
    /// Verified against `pathmap` 0.3.1: `meet_k_path_into(1, false)` on a leaf
    /// hangs.
    pub fn meet_k_path_unspecified(&self, k: usize) -> bool {
        k == 0 || self.child_count() == 0
    }

    /// `ZipperWriting::meet_k_path_into`: strip the leading `k` bytes from every
    /// path below the focus and meet the results.
    ///
    /// Unlike [`Zip::join_k_path_into`], this routes through
    /// `take_map`/`graft_map`, so values at depth exactly `k` *are* carried — they
    /// become the focus value.  Only meaningful when
    /// [`Zip::meet_k_path_unspecified`] is `false`.
    pub fn meet_k_path_into(&mut self, ops: &impl ValOps<V>, k: usize, prune: bool) -> bool {
        let f = self.focus();
        let kps = self.trie.subtrie(&f).k_paths(k);
        let mut result: Option<PathMap<V>> = None;
        for q in kps {
            let m = self.trie.subtrie(&path::cat(&f, &q));
            result = Some(match result {
                None => m,
                Some(a) => PathMap::meet(ops, &a, &m),
            });
        }
        match result {
            Some(m) if !m.is_empty_map() => {
                self.graft_map(&m);
                true
            }
            _ => {
                self.remove_branches(prune);
                false
            }
        }
    }
}

