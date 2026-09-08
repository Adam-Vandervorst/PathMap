use std::{cell::Cell, num::NonZeroUsize};

use crate::{
    ring::{self, AlgebraicResult, DistributiveLattice, DistributiveLatticeRef},
    utils::{BitMask, ByteMask},
    zipper::{Zipper, ZipperAbsolutePath, ZipperIteration, ZipperMoving, ZipperPath, ZipperValues},
};

pub struct SubtractZipper<V, A, B> {
    lhs: A,
    rhs: B,

    // To maintain the invariant:
    // lhs.path()[lhs_root_depth..]
    // == self.path()
    lhs_root_depth: usize,

    child_mask: ByteMask,
    val: CachedVal<V>,
    val_count: Cell<Option<usize>>,
}

enum CachedVal<V> {
    None,
    Lhs,
    Owned(V),
}

enum DescendState {
    /// No value at the focus and exactly one surviving child.
    Continue(u8),

    /// A value, leaf, or branch was encountered.
    Stop(DescendStop),
}

enum DescendStop {
    Value,
    Branch(u8), // first surviving child
    Leaf,
    ByteLimit,
}

impl<V, A, B> SubtractZipper<V, A, B>
where
    V: DistributiveLattice + Clone,
    A: ZipperMoving + ZipperValues<V>,
    B: ZipperMoving + ZipperValues<V>,
{
    pub fn new(lhs: A, rhs: B) -> Self {
        let lhs_root_depth = lhs.depth();
        let mut this = Self {
            lhs,
            rhs,
            lhs_root_depth,
            child_mask: ByteMask::default(),
            val: CachedVal::None,
            val_count: Cell::new(None),
        };

        this.refresh();
        this
    }

    /// Rebuilds the cached virtual state for the current backing-zipper focus.
    ///
    /// This recomputes the value and child topology of the materialized
    /// subtraction `lhs - rhs` and invalidates the cached value count.
    fn refresh(&mut self) {
        self.val_count.set(None);

        if !self.lhs.path_exists() {
            self.child_mask = ByteMask::default();
            self.val = CachedVal::None;
            return;
        }

        if !self.rhs.path_exists() {
            self.child_mask = self.lhs.child_mask();
            self.val = CachedVal::Lhs;
            return;
        }

        self.val = self.compute_val();
        self.child_mask = self.compute_child_mask();
    }

    /// Descends both backing zippers by one byte without refreshing the cached
    /// virtual state.
    ///
    /// After this call, cached fields such as `path_exists`, `child_mask`, and
    /// `val` are stale until `refresh()` is called or the movement is undone.
    #[inline]
    fn descend_to_byte_raw(&mut self, byte: u8) {
        self.lhs.descend_to_byte(byte);
        self.rhs.descend_to_byte(byte);
    }

    /// Ascends both backing zippers by one byte without refreshing the cached
    /// virtual state.
    ///
    /// Must not be called at the virtual root. Cached virtual state remains stale
    /// until `refresh()` is called or the movement is undone.
    #[inline]
    fn ascend_byte_raw(&mut self) -> bool {
        debug_assert!(
            self.lhs.depth() > self.lhs_root_depth,
            "SubtractZipper attempted to ascend above its root"
        );

        let lhs = self.lhs.ascend_byte();
        let rhs = self.rhs.ascend_byte();

        debug_assert_eq!(lhs, rhs);
        lhs
    }

    /// Returns whether the child `at` contains anything in the materialized
    /// subtraction.
    ///
    /// Both backing zippers are temporarily descended into the child and restored
    /// to their original focus before this method returns.
    #[inline]
    fn subtree_survives(&mut self, at: u8) -> bool {
        self.descend_to_byte_raw(at);
        let survives = subtree_has_difference::<V, _, _>(&mut self.lhs, &mut self.rhs);
        self.ascend_byte_raw();

        survives
    }

    fn compute_child_mask(&mut self) -> ByteMask {
        if !self.lhs.path_exists() {
            return ByteMask::default();
        }

        // Nothing below this RHS position can exist either.
        if !self.rhs.path_exists() {
            return self.lhs.child_mask();
        }

        let mut out = self.lhs.child_mask();

        for byte in (out & self.rhs.child_mask()).iter() {
            // Both tries contain this branch. Look below it to determine
            // whether anything survives.
            if !self.subtree_survives(byte) {
                out.clear_bit(byte);
            }
        }

        out
    }

    fn compute_val(&self) -> CachedVal<V> {
        let lhs_val = self.lhs.val();
        match lhs_val.psubtract(&self.rhs.val()) {
            AlgebraicResult::None | AlgebraicResult::Element(None) => CachedVal::None,
            AlgebraicResult::Identity(mask) if mask == ring::SELF_IDENT => CachedVal::Lhs,
            AlgebraicResult::Element(Some(v)) => CachedVal::Owned(v),
            _ => unreachable!(),
        }
    }

    /// Returns whether the current focus has a surviving child other than
    /// `cur_byte`.
    ///
    /// `cur_byte` is assumed to be a child of the materialized subtraction.
    fn has_surviving_sibling(&mut self, cur_byte: u8) -> bool {
        let mut candidates = self.lhs.child_mask();

        if !self.rhs.path_exists() {
            // The whole LHS subtree survives, so any other LHS child is enough.
            return candidates.count_bits() > 1;
        }

        candidates.clear_bit(cur_byte);
        let rhs_mask = self.rhs.child_mask();

        // Any LHS-only sibling survives wholesale.
        let lhs_only = (candidates ^ rhs_mask) & candidates;
        if !lhs_only.is_empty_mask() {
            return true;
        }

        // Shared siblings need to be inspected.
        let common = candidates & rhs_mask;
        common.iter().any(|byte| self.subtree_survives(byte))
    }

    /// Classifies the current virtual focus for optimized downward traversal.
    ///
    /// Returns `DescendState::Continue(byte)` only when there is no surviving value and exactly
    /// one surviving child. Otherwise returns the reason traversal must stop.
    fn current_descend_state(&mut self) -> DescendState {
        if !self.rhs.path_exists() {
            // Once RHS no longer contains the current path, subtraction has no
            // further effect below this point: the virtual subtree is exactly LHS.
            if self.lhs.is_val() {
                return DescendState::Stop(DescendStop::Value);
            }

            let mask = self.lhs.child_mask();

            if let Some(first_byte) = mask.indexed_bit::<true>(0) {
                if mask.next_bit(first_byte).is_some() {
                    return DescendState::Stop(DescendStop::Branch(first_byte));
                }

                return DescendState::Continue(first_byte);
            } else {
                return DescendState::Stop(DescendStop::Leaf);
            }
        }

        if value_survives::<V, _, _>(&self.lhs, &self.rhs) {
            // A surviving value at the current focus is a stopping point for
            // descend_until(), regardless of the number of children below it.
            return DescendState::Stop(DescendStop::Value);
        }

        match self.first_surviving_child() {
            Some(byte) => {
                if self.surviving_sibling::<true>(byte).is_some() {
                    DescendState::Stop(DescendStop::Branch(byte))
                } else {
                    DescendState::Continue(byte)
                }
            }
            None => DescendState::Stop(DescendStop::Leaf),
        }
    }

    /// Descends through a virtual unary path using raw backing-zipper movement.
    ///
    /// `byte` must be a known surviving child of the current focus. Traversal
    /// stops at a value, branch, leaf, or when the optional byte budget is
    /// exhausted.
    ///
    /// This method does not refresh cached virtual state.
    fn descend_to_next_stop(
        &mut self,
        mut byte: u8,
        mut remaining: Option<NonZeroUsize>,
    ) -> DescendStop {
        loop {
            self.descend_to_byte_raw(byte);

            if let Some(left) = remaining {
                remaining = NonZeroUsize::new(left.get() - 1);

                if remaining.is_none() {
                    return DescendStop::ByteLimit;
                }
            }

            match self.current_descend_state() {
                DescendState::Continue(next_byte) => {
                    byte = next_byte;
                }
                DescendState::Stop(stop) => {
                    return stop;
                }
            }
        }
    }

    #[inline]
    fn descend_until(&mut self, max_bytes: Option<NonZeroUsize>) -> bool {
        if let Some(byte) = self.child_mask.indexed_bit::<true>(0) {
            if self.child_mask.next_bit(byte).is_some() {
                return false;
            }
            let _ = self.descend_to_next_stop(byte, max_bytes);
            self.refresh();
            true
        } else {
            false
        }
    }

    /// Finds the next surviving sibling of `cur_byte` in the requested direction.
    ///
    /// Shared LHS/RHS children are inspected lazily and skipped when their
    /// materialized subtree difference is empty.
    fn surviving_sibling<const FORWARD: bool>(&mut self, cur_byte: u8) -> Option<u8> {
        let lhs_mask = self.lhs.child_mask();

        let mut candidate = if FORWARD {
            lhs_mask.next_bit(cur_byte)
        } else {
            lhs_mask.prev_bit(cur_byte)
        };

        if !self.rhs.path_exists() {
            return candidate;
        }

        let rhs_mask = self.rhs.child_mask();

        while let Some(byte) = candidate {
            if !rhs_mask.test_bit(byte) || self.subtree_survives(byte) {
                return candidate;
            }
            candidate = if FORWARD {
                lhs_mask.next_bit(byte)
            } else {
                lhs_mask.prev_bit(byte)
            };
        }

        candidate
    }

    /// Returns the first child, in trie order, whose materialized subtraction
    /// subtree is non-empty.
    fn first_surviving_child(&mut self) -> Option<u8> {
        let lhs_mask = self.lhs.child_mask();

        if !self.rhs.path_exists() {
            return lhs_mask.indexed_bit::<true>(0);
        }

        let rhs_mask = self.rhs.child_mask();
        lhs_mask
            .iter()
            .find(|&byte| !rhs_mask.test_bit(byte) || self.subtree_survives(byte))
    }

    /// Advances raw backing zippers to the next surviving subtree in DFS order,
    /// without ascending above `base_idx`.
    ///
    /// Returns `false` after exhausting the search and leaving the zipper at
    /// `base_idx`.
    fn advance_to_next_subtree(&mut self, base_idx: usize) -> bool {
        loop {
            // Reaching the common root means the current DFS subtree has been
            // exhausted and there is no later subtree to visit.
            if self.lhs.depth() == self.lhs_root_depth + base_idx {
                return false;
            }

            let cur_byte = self.lhs.focus_byte().expect("path is below base_idx");

            // Move to the parent without refreshing the virtual zipper state.
            // Intermediate nodes are not externally observable during this search.
            self.ascend_byte_raw();

            // Continue DFS from the next surviving sibling, if one exists.
            // surviving_sibling() accounts for branches removed by subtraction.
            if let Some(byte) = self.surviving_sibling::<true>(cur_byte) {
                self.descend_to_byte_raw(byte);
                return true;
            }

            // No sibling survives at this level. Keep ascending until either a
            // later subtree is found or the common root is reached.
        }
    }

    /// Searches in depth-first order for the first surviving path exactly `k`
    /// bytes below `base_idx`.
    ///
    /// The zipper may be positioned anywhere below `base_idx` on entry.
    /// Intermediate movement is raw; the virtual state is refreshed only when
    /// a matching path is found.
    fn seek_k_path(&mut self, base_idx: usize, k: usize) -> bool {
        let target_idx = base_idx + k;

        loop {
            // The first path encountered at the requested depth is the result,
            // since traversal always prefers the first surviving child.
            if self.lhs.depth() == self.lhs_root_depth + target_idx {
                return true;
            }

            // Continue depth-first through the first surviving child whenever
            // possible.
            if let Some(byte) = self.first_surviving_child() {
                self.descend_to_byte_raw(byte);
                continue;
            }

            // This branch ended before reaching the requested depth. Backtrack
            // until another surviving subtree can continue the DFS.
            if !self.advance_to_next_subtree(base_idx) {
                return false;
            }
        }
    }
}

#[inline]
fn value_survives<V, A, B>(lhs: &A, rhs: &B) -> bool
where
    V: DistributiveLattice + Clone,
    A: ZipperValues<V>,
    B: ZipperValues<V>,
{
    !matches!(lhs.val().psubtract(&rhs.val()), AlgebraicResult::None)
}

/// Returns whether the materialized subtraction of the focused subtrees is
/// non-empty.
///
/// Traverses only the portion shared by both tries and short-circuits as soon
/// as a surviving value or LHS-only branch is found.
///
/// Both zippers are restored to their original focus before returning.
fn subtree_has_difference<V, A, B>(lhs: &mut A, rhs: &mut B) -> bool
where
    V: DistributiveLattice + Clone,
    A: ZipperMoving + ZipperValues<V>,
    B: ZipperMoving + ZipperValues<V>,
{
    let mut depth = 0;
    let mut lhs_mask = lhs.child_mask();
    let mut rhs_mask = rhs.child_mask();
    'descend: loop {
        // Entire LHS-only branches survive.
        // A value at this exact key survives.
        if !((lhs_mask ^ rhs_mask) & lhs_mask).is_empty_mask()
            || value_survives::<V, _, _>(lhs, rhs)
        {
            let lhs_ascended = lhs.ascend(depth);
            let rhs_ascended = rhs.ascend(depth);

            debug_assert!(lhs_ascended == depth);
            debug_assert!(rhs_ascended == depth);

            return true;
        }

        let mut combined_mask = lhs_mask & rhs_mask;
        let mut next_common_byte = combined_mask.indexed_bit::<true>(0);
        'node: loop {
            match next_common_byte {
                Some(byte) => {
                    lhs.descend_to_byte(byte);
                    rhs.descend_to_byte(byte);

                    lhs_mask = lhs.child_mask();
                    rhs_mask = rhs.child_mask();

                    depth += 1;
                    continue 'descend;
                }
                None => {
                    if depth == 0 {
                        break 'descend;
                    }

                    let cur_byte = lhs.focus_byte().expect("non-empty path when depth > 0");
                    lhs.ascend_byte();
                    rhs.ascend_byte();

                    lhs_mask = lhs.child_mask();
                    rhs_mask = rhs.child_mask();
                    combined_mask = lhs_mask & rhs_mask;
                    next_common_byte = combined_mask.next_bit(cur_byte);

                    depth -= 1;
                    continue 'node;
                }
            }
        }
    }

    false
}

/// Counts values in the materialized subtraction below the current focus.
///
/// LHS-only subtrees are counted using the native `val_count()` operation;
/// only overlapping subtrees are traversed explicitly.
///
/// Both zippers are restored to their original focus before returning.
fn subtract_val_count<V, A, B>(lhs: &mut A, rhs: &mut B) -> usize
where
    V: DistributiveLattice + Clone,
    A: ZipperMoving + ZipperValues<V>,
    B: ZipperMoving + ZipperValues<V>,
{
    if !lhs.path_exists() {
        return 0;
    }

    if !rhs.path_exists() {
        return lhs.val_count();
    }

    let mut depth = 0;
    let mut count = 0;
    let mut lhs_mask = lhs.child_mask();
    let mut rhs_mask = rhs.child_mask();

    'descend: loop {
        count += usize::from(value_survives::<V, _, _>(lhs, rhs));

        let lhs_only = (lhs_mask ^ rhs_mask) & lhs_mask;
        for lhs_byte in lhs_only.iter() {
            lhs.descend_to_byte(lhs_byte);
            count += lhs.val_count();
            lhs.ascend_byte();
        }

        let mut combined_mask = lhs_mask & rhs_mask;
        let mut next_common_byte = combined_mask.indexed_bit::<true>(0);
        loop {
            match next_common_byte {
                Some(byte) => {
                    lhs.descend_to_byte(byte);
                    rhs.descend_to_byte(byte);

                    lhs_mask = lhs.child_mask();
                    rhs_mask = rhs.child_mask();

                    depth += 1;
                    continue 'descend;
                }
                None => {
                    if depth == 0 {
                        break 'descend;
                    }

                    let cur_byte = lhs.focus_byte().expect("non-empty path when depth > 0");
                    lhs.ascend_byte();
                    rhs.ascend_byte();

                    lhs_mask = lhs.child_mask();
                    rhs_mask = rhs.child_mask();
                    combined_mask = lhs_mask & rhs_mask;
                    next_common_byte = combined_mask.next_bit(cur_byte);

                    depth -= 1;
                }
            }
        }
    }

    count
}

impl<V, A, B> Zipper for SubtractZipper<V, A, B>
where
    A: Zipper,
    B: Zipper,
{
    #[inline]
    fn path_exists(&self) -> bool {
        self.is_val() || !self.child_mask.is_empty_mask()
    }

    #[inline]
    fn is_val(&self) -> bool {
        match self.val {
            CachedVal::None => false,
            CachedVal::Lhs => self.lhs.is_val(),
            CachedVal::Owned(_) => true,
        }
    }

    #[inline]
    fn child_count(&self) -> usize {
        self.child_mask.count_bits()
    }

    #[inline]
    fn child_mask(&self) -> ByteMask {
        self.child_mask
    }
}

impl<V, A, B> ZipperValues<V> for SubtractZipper<V, A, B>
where
    V: DistributiveLattice + Clone,
    A: ZipperMoving + ZipperValues<V>,
    B: ZipperMoving + ZipperValues<V>,
{
    #[inline]
    fn val(&self) -> Option<&V> {
        match self.val {
            CachedVal::None => None,
            CachedVal::Lhs => self.lhs.val(),
            CachedVal::Owned(ref v) => Some(v),
        }
    }
}

impl<V, A, B> ZipperMoving for SubtractZipper<V, A, B>
where
    V: DistributiveLattice + Clone,
    A: ZipperMoving + ZipperValues<V> + Clone,
    B: ZipperMoving + ZipperValues<V> + Clone,
{
    #[inline]
    fn depth(&self) -> usize {
        self.lhs.depth() - self.lhs_root_depth
    }

    #[inline]
    fn focus_byte(&self) -> Option<u8> {
        self.lhs.focus_byte()
    }

    // #[inline]
    // fn at_root(&self) -> bool {
    //     self.lhs.path().len() == self.lhs_root_depth
    // }

    fn val_count(&self) -> usize {
        if let Some(count) = self.val_count.get() {
            return count;
        }

        let mut lhs = self.lhs.clone();
        let mut rhs = self.rhs.clone();

        let count = subtract_val_count::<V, _, _>(&mut lhs, &mut rhs);

        self.val_count.set(Some(count));
        count
    }

    fn descend_to<K: AsRef<[u8]>>(&mut self, path: K) {
        let path = path.as_ref();
        if path.is_empty() {
            return;
        }

        self.lhs.descend_to(path);
        self.rhs.descend_to(path);

        self.refresh();
    }

    fn ascend(&mut self, steps: usize) -> usize {
        if steps == 0 {
            return 0;
        }

        let actual_steps = steps.min(self.depth());

        self.lhs.ascend(actual_steps);
        self.rhs.ascend(actual_steps);
        self.refresh();

        actual_steps
    }

    fn ascend_until(&mut self) -> usize {
        if self.at_root() {
            return 0;
        }

        let mut ascended = 0;
        loop {
            let cur_byte = self.focus_byte().expect("not at root");

            self.ascend_byte_raw();
            ascended += 1;

            let stop = self.at_root()
                || value_survives::<V, _, _>(&self.lhs, &self.rhs)
                || self.has_surviving_sibling(cur_byte);

            if stop {
                self.refresh();
                return ascended;
            }
        }
    }

    fn ascend_until_branch(&mut self) -> usize {
        if self.at_root() {
            return 0;
        }

        let mut ascended = 0;
        loop {
            let cur_byte = self.focus_byte().expect("not at root");

            self.ascend_byte_raw();
            ascended += 1;

            if self.at_root() || self.has_surviving_sibling(cur_byte) {
                self.refresh();
                return ascended;
            }
        }
    }

    fn reset(&mut self) {
        let depth = self.depth();

        if depth != 0 {
            self.lhs.ascend(depth);
            self.rhs.ascend(depth);
            self.refresh();
        }

        debug_assert!(self.at_root());
    }

    fn descend_to_existing<K: AsRef<[u8]>>(&mut self, k: K) -> usize {
        let k = k.as_ref();

        // The cached virtual child mask is valid at the initial focus, so the
        // first step can be checked without inspecting the subtraction again.
        if k.is_empty() || !self.child_mask.test_bit(k[0]) {
            return 0;
        }

        self.descend_to_byte_raw(k[0]);
        let mut i = 1;

        while i < k.len() {
            let byte = k[i];

            // No such child in A => no such child in A - B.
            if !self.lhs.child_mask().test_bit(byte) {
                break;
            }

            let rhs_gone = !self.rhs.child_mask().test_bit(byte);

            self.descend_to_byte_raw(byte);

            if rhs_gone {
                i += 1;

                // An LHS-only child survives wholesale. From this point downward
                // A - B is exactly A, so delegate the rest to the native LHS zipper.
                let descended = self.lhs.descend_to_existing(&k[i..]);
                self.rhs.descend_to(&k[i..i + descended]);
                i += descended;
                break;
            }

            // Both sides contain the child structurally. It belongs to the
            // materialized difference iff something survives below it.
            if !subtree_has_difference::<V, _, _>(&mut self.lhs, &mut self.rhs) {
                self.ascend_byte_raw();
                break;
            }

            i += 1;
        }

        self.refresh();
        i
    }

    fn descend_to_val<K: AsRef<[u8]>>(&mut self, k: K) -> usize {
        let k = k.as_ref();

        // The cached virtual child mask is valid at the initial focus, so the
        // first step can be checked without inspecting the subtraction again.
        if k.is_empty() || !self.child_mask.test_bit(k[0]) {
            return 0;
        }

        self.descend_to_byte_raw(k[0]);
        let mut i = 1;

        // If RHS disappeared on the first step, subtraction has no further
        // effect below this point. Check the current LHS value first because
        // descend_to_val() deliberately skips a value at its initial focus.
        if !self.rhs.path_exists() {
            if !self.lhs.is_val() {
                let descended = self.lhs.descend_to_val(&k[i..]);
                self.rhs.descend_to(&k[i..i + descended]);
                i += descended;
            }

            self.refresh();
            return i;
        }

        // The first child is known to exist in the virtual trie from the cached
        // child mask. If its value survives subtraction, we are already done.
        if value_survives::<V, _, _>(&self.lhs, &self.rhs) {
            self.refresh();
            return i;
        }

        while i < k.len() {
            let byte = k[i];

            // No such LHS child means there cannot be such a child in A - B.
            if !self.lhs.child_mask().test_bit(byte) {
                break;
            }

            let rhs_gone = !self.rhs.child_mask().test_bit(byte);

            self.descend_to_byte_raw(byte);

            // An LHS-only child survives wholesale. From this point downward
            // A - B is exactly A, so delegate the rest to the native LHS zipper.
            if rhs_gone {
                i += 1;

                // The newly reached focus itself may already contain a value.
                // The native descend_to_val() would intentionally skip it.
                if !self.lhs.is_val() {
                    let descended = self.lhs.descend_to_val(&k[i..]);
                    self.rhs.descend_to(&k[i..i + descended]);
                    i += descended;
                }

                break;
            }

            // A surviving value also proves that this virtual path exists, so
            // avoid the more expensive subtree check in this case.
            if value_survives::<V, _, _>(&self.lhs, &self.rhs) {
                i += 1;
                break;
            }

            // Both tries contain the structural child, but it exists in the
            // materialized difference only if something survives below it.
            if !subtree_has_difference::<V, _, _>(&mut self.lhs, &mut self.rhs) {
                self.ascend_byte_raw();
                break;
            }

            i += 1;
        }

        self.refresh();
        i
    }

    fn descend_to_existing_byte(&mut self, k: u8) -> bool {
        if !self.child_mask.test_bit(k) {
            return false;
        }

        self.descend_to_byte_raw(k);
        self.refresh();
        true
    }

    fn descend_until(&mut self) -> bool {
        self.descend_until(None)
    }

    fn descend_until_max_bytes(&mut self, max_bytes: usize) -> bool {
        match NonZeroUsize::new(max_bytes) {
            Some(limit) => self.descend_until(Some(limit)),
            None => false,
        }
    }

    fn to_next_sibling_byte(&mut self) -> Option<u8> {
        let cur_byte = self.focus_byte()?;

        // Move both backing zippers to the parent without refreshing the
        // virtual state, which is only needed at the final focus.
        self.ascend_byte_raw();

        match self.surviving_sibling::<true>(cur_byte) {
            Some(byte) => {
                self.descend_to_byte_raw(byte);
                self.refresh();
                Some(byte)
            }

            None => {
                // Restore the original focus. Since we return to exactly the
                // same node, the existing cached virtual state is still valid.
                self.descend_to_byte_raw(cur_byte);
                None
            }
        }
    }

    fn to_prev_sibling_byte(&mut self) -> Option<u8> {
        let cur_byte = self.focus_byte()?;

        // Move both backing zippers to the parent without refreshing the
        // virtual state, which is only needed at the final focus.
        self.ascend_byte_raw();

        match self.surviving_sibling::<false>(cur_byte) {
            Some(byte) => {
                self.descend_to_byte_raw(byte);
                self.refresh();
                Some(byte)
            }

            None => {
                // Restore the original focus. Since we return to exactly the
                // same node, the existing cached virtual state is still valid.
                self.descend_to_byte_raw(cur_byte);
                None
            }
        }
    }

    fn to_next_step(&mut self) -> bool {
        // If there is a child, DFS simply descends into the first one.
        if let Some(byte) = self.child_mask.indexed_bit::<true>(0) {
            self.descend_to_byte_raw(byte);
            self.refresh();
            return true;
        }

        // We are at a leaf. Walk upwards without refreshing intermediate
        // virtual nodes until a surviving next sibling is found.
        loop {
            let Some(cur_byte) = self.focus_byte() else {
                return false;
            };

            self.ascend_byte_raw();

            if let Some(byte) = self.surviving_sibling::<true>(cur_byte) {
                self.descend_to_byte_raw(byte);
                self.refresh();
                return true;
            }

            // No sibling at this parent. Unlike to_next_sibling_byte(), we do
            // not restore the previous child: DFS is done with that subtree and
            // continues ascending from the parent.
            if self.at_root() {
                self.refresh();
                return false;
            }
        }
    }
}

impl<V, A, B> ZipperPath for SubtractZipper<V, A, B>
where
    V: DistributiveLattice + Clone,
    A: ZipperMoving + ZipperPath + ZipperValues<V> + Clone,
    B: ZipperMoving + ZipperValues<V> + Clone,
{
    #[inline]
    fn path(&self) -> &[u8] {
        &self.lhs.path()[self.lhs_root_depth..]
    }

    fn move_to_path<K: AsRef<[u8]>>(&mut self, path: K) -> usize {
        let path = path.as_ref();

        let current = self.path();
        let overlap = fast_slice_utils::find_prefix_overlap(path, current);
        let to_ascend = current.len() - overlap;
        let suffix = &path[overlap..];

        if to_ascend == 0 && suffix.is_empty() {
            return overlap;
        }

        if to_ascend != 0 {
            self.lhs.ascend(to_ascend);
            self.rhs.ascend(to_ascend);
        }
        if !suffix.is_empty() {
            self.lhs.descend_to(suffix);
            self.rhs.descend_to(suffix);
        }

        self.refresh();

        debug_assert_eq!(self.path(), path,);

        overlap
    }
}

impl<V, A, B> ZipperIteration for SubtractZipper<V, A, B>
where
    V: DistributiveLattice + Clone + PartialEq,
    A: ZipperMoving + ZipperValues<V> + Clone,
    B: ZipperMoving + ZipperValues<V> + Clone,
{
    fn to_next_val(&mut self) -> bool {
        // The cache is valid at entry, so use it to select the first child
        // without recomputing the virtual topology.
        let mut next_byte = self.child_mask.indexed_bit::<true>(0);

        'search: loop {
            // Search downward, always taking the first child in DFS order.
            while let Some(byte) = next_byte {
                match self.descend_to_next_stop(byte, None) {
                    DescendStop::Value => {
                        self.refresh();
                        return true;
                    }
                    DescendStop::Branch(first_child) => {
                        // There is no value at this branch, so DFS continues
                        // immediately through its first surviving child.
                        next_byte = Some(first_child);
                    }
                    DescendStop::Leaf => {
                        // No value was found on this path. Continue by searching
                        // for the next sibling while walking back up the tree.
                        next_byte = None;
                    }
                    DescendStop::ByteLimit => unreachable!(),
                }
            }

            // Walk upwards until the next surviving sibling is found.
            loop {
                let Some(cur_byte) = self.focus_byte() else {
                    // We are at the root without having moved, so the cached
                    // virtual state is still valid.
                    return false;
                };

                self.ascend_byte_raw();

                if let Some(byte) = self.surviving_sibling::<true>(cur_byte) {
                    next_byte = Some(byte);
                    continue 'search;
                }

                // No later subtree exists. The traversal has returned to the
                // root through raw movement, so rebuild the cached virtual state.
                if self.at_root() {
                    self.refresh();
                    return false;
                }
            }
        }
    }

    fn descend_first_k_path(&mut self, k: usize) -> bool {
        if k == 0 {
            return true;
        }

        let Some(byte) = self.child_mask.indexed_bit::<true>(0) else {
            return false;
        };

        let base_idx = self.depth();
        self.descend_to_byte_raw(byte);
        let found = self.seek_k_path(base_idx, k);

        if found {
            self.refresh();
        }
        // On failure we are back at the original focus, so the old cache
        // is still valid.
        found
    }

    fn to_next_k_path(&mut self, k: usize) -> bool {
        let Some(base_idx) = self.depth().checked_sub(k) else {
            return false;
        };

        if !self.advance_to_next_subtree(base_idx) {
            self.refresh();
            return false;
        }

        let found = self.seek_k_path(base_idx, k);

        // Unlike descend_first_k_path(), failure leaves us at the common root,
        // not at the original focus, so the cached state is stale either way.
        self.refresh();

        found
    }
}

impl<V, A, B> ZipperAbsolutePath for SubtractZipper<V, A, B>
where
    V: DistributiveLattice + Clone,
    A: ZipperMoving + ZipperPath + ZipperValues<V> + Clone,
    B: ZipperMoving + ZipperValues<V> + Clone,
{
    fn origin_path(&self) -> &[u8] {
        self.lhs.path()
    }

    fn root_prefix_path(&self) -> &[u8] {
        &self.lhs.path()[0..self.lhs_root_depth]
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::PathMap;
    use crate::zipper::ReadZipperUntracked;
    use crate::zipper::zipper_iteration_tests::zipper_iteration_tests;
    use crate::zipper::zipper_moving_tests::zipper_moving_tests;
    use std::fmt::Debug;

    type ZipperT<'a, V> =
        SubtractZipper<V, ReadZipperUntracked<'a, 'static, V>, ReadZipperUntracked<'a, 'static, V>>;
    fn subtract_at<'a, V>(a: &'a PathMap<V>, b: &'a PathMap<V>, path: &[u8]) -> ZipperT<'a, V>
    where
        V: DistributiveLattice + Clone + Send + Sync + Unpin,
    {
        let lhs = a.read_zipper_at_path(path);
        let rhs = b.read_zipper_at_path(path);

        SubtractZipper::new(lhs, rhs)
    }

    enum State<V> {
        UnaryNode(u8),
        NonExistentNode,
        Leaf(V),
        Branch(ByteMask),
    }

    impl<V: DistributiveLattice + Clone + Send + Sync + Unpin + PartialEq + Debug> State<V> {
        fn assert(self, zipper: &ZipperT<'_, V>) {
            fn assert_state_impl<'a, V>(
                zipper: &ZipperT<'_, V>,
                expected_exists: bool,
                expected_value: Option<V>,
                expected_children: ByteMask,
            ) where
                V: DistributiveLattice + Clone + Send + Sync + Unpin + PartialEq + Debug,
            {
                let path = zipper.origin_path();

                assert_eq!(
                    zipper.path_exists(),
                    expected_exists,
                    "wrong path_exists at {path:?}"
                );

                assert_eq!(
                    zipper.is_val(),
                    expected_value.is_some(),
                    "wrong is_val at {path:?}"
                );

                assert_eq!(
                    zipper.val(),
                    expected_value.as_ref(),
                    "wrong value at {path:?}"
                );

                assert_eq!(
                    zipper.child_count(),
                    expected_children.count_bits(),
                    "wrong child_count at {path:?}"
                );

                let mask = zipper.child_mask();
                for byte in expected_children.iter() {
                    assert!(mask.test_bit(byte), "unset child {byte} at {path:?}");
                }
                let ghosts = mask & !expected_children;
                assert!(
                    ghosts.is_empty_mask(),
                    "ghost children {ghosts:?} at {path:?}"
                );
            }

            match self {
                State::UnaryNode(expected_child) => {
                    assert_state_impl(zipper, true, None, ByteMask::from(expected_child))
                }
                State::NonExistentNode => assert_state_impl(zipper, false, None, ByteMask::EMPTY),
                State::Leaf(expected_value) => {
                    assert_state_impl(zipper, true, Some(expected_value), ByteMask::EMPTY)
                }
                State::Branch(expected_children) => {
                    assert_state_impl(zipper, true, None, expected_children)
                }
            }
        }
    }

    #[test]
    fn lhs_survives_unchanged() {
        let lhs = PathMap::from_iter([([10, 20], true)]);
        let rhs = PathMap::new();

        let mut zipper = subtract_at(&lhs, &rhs, &[]);
        State::UnaryNode(10).assert(&zipper);

        zipper.descend_to_byte(10);
        State::UnaryNode(20).assert(&zipper);

        zipper.descend_to_byte(20);
        State::Leaf(true).assert(&zipper);
    }

    #[test]
    fn lhs_not_affected() {
        let lhs = PathMap::from_iter([([10], true)]);
        let rhs = PathMap::from_iter([(&[20][..], false), (&[30, 40], false)]);

        let mut zipper = subtract_at(&lhs, &rhs, &[]);
        State::UnaryNode(10).assert(&zipper);

        zipper.descend_to_byte(10);
        State::Leaf(true).assert(&zipper);

        zipper.reset();
        zipper.descend_to_byte(20);
        State::NonExistentNode.assert(&zipper);
    }

    #[test]
    fn lhs_contained_in_rhs() {
        let lhs = PathMap::from_iter([([10, 20], true)]);
        let rhs = PathMap::from_iter([(&[10, 20][..], true), (&[10, 30], false), (&[40], false)]);

        let mut zipper = subtract_at(&lhs, &rhs, &[]);
        State::NonExistentNode.assert(&zipper);

        zipper.descend_to([10, 20]);
        State::NonExistentNode.assert(&zipper);

        zipper.reset();
        zipper.descend_to([10, 30]);
        State::NonExistentNode.assert(&zipper);

        zipper.reset();
        zipper.descend_to_byte(40);
        State::NonExistentNode.assert(&zipper);
    }

    #[test]
    fn rhs_contained_in_lhs() {
        let lhs = PathMap::from_iter([(&[10, 20][..], false), (&[10, 30], false), (&[40], true)]);
        let rhs = PathMap::from_iter([([10, 20], false), ([10, 30], false)]);

        let mut zipper = subtract_at(&lhs, &rhs, &[]);
        State::UnaryNode(40).assert(&zipper);

        zipper.descend_to_byte(40);
        State::Leaf(true).assert(&zipper);
    }

    #[test]
    fn identical_singletons() {
        let lhs = PathMap::from_iter([([10], true)]);
        let rhs = PathMap::from_iter([([10], true)]);

        assert!(!subtract_at(&lhs, &rhs, &[]).path_exists());
    }

    #[test]
    fn common_prefix_survives_if_difference_below_1() {
        let lhs = PathMap::from_iter([([10, 20], true), ([10, 30], true)]);
        let rhs = PathMap::from_iter([([10, 20], true)]);

        let mut zipper = subtract_at(&lhs, &rhs, &[]);
        State::UnaryNode(10).assert(&zipper);

        zipper.descend_to_byte(10);
        State::UnaryNode(30).assert(&zipper);

        zipper.descend_to_byte(20);
        State::NonExistentNode.assert(&zipper);

        zipper.ascend_byte();
        zipper.descend_to_byte(30);
        State::Leaf(true).assert(&zipper);
    }

    #[test]
    fn common_prefix_survives_if_difference_below_2() {
        let lhs = PathMap::from_iter([([10, 20, 30], true)]);
        let rhs = PathMap::from_iter([([10, 20, 40], true)]);

        let mut zipper = subtract_at(&lhs, &rhs, &[]);
        State::UnaryNode(10).assert(&zipper);

        zipper.descend_to_byte(10);
        State::UnaryNode(20).assert(&zipper);

        zipper.descend_to_byte(20);
        State::UnaryNode(30).assert(&zipper);

        zipper.descend_to_byte(30);
        State::Leaf(true).assert(&zipper);
    }

    #[test]
    fn value_is_destroyed_node_survives() {
        let lhs = PathMap::from_iter([(&[10][..], true), (&[10, 20], false)]);
        let rhs = PathMap::from_iter([([10], true)]);

        let mut zipper = subtract_at(&lhs, &rhs, &[]);
        zipper.descend_to([10, 20]);
        State::Leaf(false).assert(&zipper);

        zipper.ascend_byte();
        State::UnaryNode(20).assert(&zipper);
    }

    #[test]
    fn node_survives_children_are_destroyed() {
        let lhs = PathMap::from_iter([(&[10][..], true), (&[10, 20], false)]);
        let rhs = PathMap::from_iter([([10, 20], false)]);

        let mut zipper = subtract_at(&lhs, &rhs, &[]);
        zipper.descend_to([10]);
        State::Leaf(true).assert(&zipper);
    }

    fn assert_subtract_matches_materialized<K, V>(
        lhs: &PathMap<V>,
        rhs: &PathMap<V>,
        paths: impl IntoIterator<Item = K>,
    ) where
        V: DistributiveLattice + Clone + Send + Sync + Unpin + PartialEq + Debug,
        K: AsRef<[u8]> + Debug,
    {
        let expected = lhs.subtract(rhs);
        let mut expected_z = expected.read_zipper();

        for path in paths {
            expected_z.descend_to(path.as_ref());
            let actual = subtract_at(lhs, rhs, path.as_ref());

            assert_eq!(
                actual.path_exists(),
                expected_z.path_exists(),
                "path_exists differs at {path:?}"
            );

            assert_eq!(
                actual.is_val(),
                expected_z.is_val(),
                "is_val differs at {path:?}"
            );

            assert_eq!(actual.val(), expected_z.val(), "val differs at {path:?}");

            assert_eq!(
                actual.child_mask(),
                expected_z.child_mask(),
                "child_mask differs at {path:?}"
            );

            assert_eq!(
                actual.child_count(),
                expected_z.child_count(),
                "child_count differs at {path:?}"
            );

            assert_eq!(
                actual.val_count(),
                expected_z.val_count(),
                "val_count differs at {path:?}"
            );

            expected_z.reset();
        }
    }

    #[test]
    fn subtract_zipper_matches_materialized_subtraction_on_all_prefixes() {
        let lhs = PathMap::from_iter([
            (&[10][..], 1u16),
            (&[10, 20], 2),
            (&[10, 20, 30], 3),
            (&[10, 40], 4),
            (&[50, 60], 5),
            (&[70], 6),
        ]);

        let rhs = PathMap::from_iter([
            (&[10][..], 1),
            (&[10, 20], 7),
            (&[10, 20, 30], 3),
            (&[50, 80], 8),
            (&[90], 9),
        ]);

        let paths = [
            &[],
            &[10][..],
            &[10, 20],
            &[10, 20, 30],
            &[10, 40],
            &[50],
            &[50, 60],
            &[50, 80],
            &[70],
            &[90],
        ];

        assert_subtract_matches_materialized(&lhs, &rhs, paths);
    }

    #[test]
    fn subtract_zipper_matches_materialized_subtraction_on_absent_paths() {
        let lhs = PathMap::from_iter([([10, 20], 1u16), ([10, 30], 2u16)]);

        let rhs = PathMap::from_iter([([10, 20], 1)]);

        let paths = [
            &[],
            &[10][..],
            &[10, 20],
            &[10, 30],
            // Deliberately absent.
            &[11],
            &[10, 21],
            &[10, 30, 40],
            &[200, 201],
        ];

        assert_subtract_matches_materialized(&lhs, &rhs, paths);
    }

    #[test]
    fn subtract_zipper_matches_lhs_when_rhs_is_disjoint() {
        let lhs = PathMap::from_iter([(&[10][..], 1u16), (&[10, 20], 2), (&[30, 40, 50], 3)]);

        let rhs = PathMap::from_iter([(&[100][..], 4), (&[110, 120], 5)]);

        let paths = [
            &[],
            &[10][..],
            &[10, 20],
            &[30],
            &[30, 40],
            &[30, 40, 50],
            &[100],
            &[110],
            &[110, 120],
        ];

        assert_subtract_matches_materialized(&lhs, &rhs, paths);
    }

    zipper_moving_tests!(
        subtract_zipper,
        |keys: &[&[u8]]| {
            let lhs = PathMap::from_iter(keys.iter().zip(std::iter::repeat(true)));
            let mut rhs = PathMap::new();
            if let Some(path) = keys.first() {
                rhs.set_val_at(path, false);
            }
            if let Some(path) = keys.last() {
                rhs.set_val_at(path, false);
            }
            (lhs, rhs)
        },
        |(lhs, rhs): &mut (PathMap<bool>, PathMap<bool>), path: &[u8]| -> ZipperT<'_, bool> {
            subtract_at(lhs, rhs, path)
        }
    );

    zipper_moving_tests!(
        subtract_zipper_demanding,
        |keys: &[&[u8]]| {
            let mut lhs = PathMap::from_iter(keys.iter().zip(std::iter::repeat(true)));
            let mut rhs = PathMap::new();
            keys.iter()
                .enumerate()
                .filter(|(i, _)| i % 2 != 0)
                .for_each(|(_, key)| {
                    rhs.set_val_at(key, false);
                    if key.len() > 1 {
                        let _ = lhs.get_val_or_set_mut_at(&[key[0]], false);
                        rhs.set_val_at(&[key[0]], false);
                    }
                });
            (lhs, rhs)
        },
        |(lhs, rhs): &mut (PathMap<bool>, PathMap<bool>), path: &[u8]| -> ZipperT<'_, bool> {
            subtract_at(lhs, rhs, path)
        }
    );

    zipper_iteration_tests!(
        subtract_zipper,
        |keys: &[&[u8]]| {
            let lhs = PathMap::from_iter(keys.iter().zip(std::iter::repeat(true)));
            let mut rhs = PathMap::new();
            if let Some(path) = keys.first() {
                rhs.set_val_at(path, false);
            }
            if let Some(path) = keys.last() {
                rhs.set_val_at(path, false);
            }
            (lhs, rhs)
        },
        |(lhs, rhs): &mut (PathMap<bool>, PathMap<bool>), path: &[u8]| -> ZipperT<'_, bool> {
            subtract_at(lhs, rhs, path)
        }
    );

    zipper_iteration_tests!(
        subtract_zipper_demanding,
        |keys: &[&[u8]]| {
            let mut lhs = PathMap::from_iter(keys.iter().zip(std::iter::repeat(true)));
            let mut rhs = PathMap::new();
            keys.iter()
                .enumerate()
                .filter(|(i, _)| i % 2 != 0)
                .for_each(|(_, key)| {
                    rhs.set_val_at(key, false);
                    if key.len() > 1 {
                        let _ = lhs.get_val_or_set_mut_at(&[key[0]], false);
                        rhs.set_val_at(&[key[0]], false);
                    }
                });
            (lhs, rhs)
        },
        |(lhs, rhs): &mut (PathMap<bool>, PathMap<bool>), path: &[u8]| -> ZipperT<'_, bool> {
            subtract_at(lhs, rhs, path)
        }
    );
}
