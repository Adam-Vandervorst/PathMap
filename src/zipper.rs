
//! # Zipper Usage
//!
//! A zipper represents a cursor in a trie, and has a location called the focus.  A zipper can be moved
//! within the trie in order to access the trie for reading and/or writing.  A zipper's focus may not be
//! moved above the zipper's root.
//!

use arrayvec::ArrayVec;
use maybe_dangling::MaybeDangling;
use fast_slice_utils::{find_prefix_overlap, starts_with};

use crate::alloc::{Allocator, GlobalAlloc};
use crate::utils::ByteMask;
use crate::trie_node::*;
use crate::PathMap;
use crate::timed_span::{TimingEntries::*, COUNTERS, timed_span};

pub use crate::write_zipper::*;
pub use crate::trie_ref::*;
pub use crate::zipper_head::*;
pub use crate::product_zipper::{ProductZipper, ProductZipperG, ZipperProduct, OneFactor};
pub use crate::overlay_zipper::{OverlayZipper};
pub use crate::prefix_zipper::{PrefixZipper};
pub use crate::path_tracker::{PathTracker};
pub use crate::empty_zipper::{EmptyZipper};
pub use crate::poly_zipper::{PolyZipper, PolyZipperExplicit};
pub use crate::dependent_zipper::DependentProductZipperG;
use crate::zipper_tracking::*;


/// The most fundamantal interface for a zipper, compatible with all zipper types
pub trait Zipper {
    /// Returns `true` if the zipper's focus is on a path within the trie, otherwise `false`
    fn path_exists(&self) -> bool;

    /// Returns `true` if there is a value at the zipper's focus, otherwise `false`
    fn is_val(&self) -> bool;

    /// Deprecated alias for [Zipper::is_val]
    #[deprecated] //GOAT-old-names
    fn is_value(&self) -> bool {
        self.is_val()
    }

    /// Returns the number of child branches from the focus node
    ///
    /// Returns 0 if the focus is on a leaf
    fn child_count(&self) -> usize;

    /// Returns 256-bit mask indicating which children exist from the branch at the zipper's focus
    ///
    /// Returns an empty mask if the focus is on a leaf or non-existent path
    fn child_mask(&self) -> ByteMask;
}

/// Methods for zippers with a known value type
pub trait ZipperValues<V> {
    /// Returns a refernce to the value at the zipper's focus, or `None` if there is no value
    ///
    /// If you have a zipper type that implements [ZipperReadOnlyValues] then [ZipperReadOnlyValues::get_val]
    /// will provide a longer-lived reference to the value.
    fn val(&self) -> Option<&V>;

    /// Returns a refernce to the value at `path`, relative to the zipper's focus, or `None` if there is no value
    ///
    /// If you have a zipper type that implements [ZipperReadOnlyValues] then [ZipperReadOnlyValues::get_val_at]
    /// will provide a longer-lived reference to the value.
    fn val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&V>;

    /// Deprecated alias for [ZipperValues::val]
    #[deprecated] //GOAT-old-names
    fn value(&self) -> Option<&V> {
        self.val()
    }
}

/// Method to fork a read zipper from the parent zipper
pub trait ZipperForking<V> {
    /// The read-zipper type returned from [fork_read_zipper](ZipperForking::fork_read_zipper)
    type ReadZipperT<'a>: ZipperAbsolutePath + ZipperIteration + ZipperValues<V> where Self: 'a;

    /// Returns a new read-only Zipper, with the new zipper's root being at the zipper's current focus
    ///
    /// Discussion: The main uses of this method is to construct a child zipper with a different root
    /// from the parent, to construct a read zipper when you have another zipper type, or to cheaply
    /// create a zipper you can pass to a function that takes ownership.  Often however, you want to
    /// clone the parent zipper instead.
    fn fork_read_zipper<'a>(&'a self) -> Self::ReadZipperT<'a>;
}

/// Methods for zippers that can access concrete subtries
pub trait ZipperSubtries<V: Clone + Send + Sync, A: Allocator = GlobalAlloc>: ZipperValues<V> + Zipper {
    /// Returns `true` if the zipper can access a subtrie in constant time
    ///
    /// Sometimes this trait will be implemented on abstract zipper types, in which case this method will return
    /// `false`.  When it returns `true` other methods in this trait should return `Some`.
    fn native_subtries(&self) -> bool;

    /// Returns a new [PathMap] containing everything below the zipper's focus or `None` if the zipper doesn't
    /// suppot creating a new `PathMap`.
    ///
    /// GOAT: This method's behavior is affected by the `graft_root_vals` feature
    /// This method does not clone the value at the focus as the map's root.
    /// GOAT QUESTION: Should this method include the focus value as the map's root value?  That
    /// makes conceptual sense given the fact that maps have root values, however the main argument
    /// for "no" is keeping compatibility with [ZipperWriting::graft_map] and keeping an analogous API
    /// to [ZipperWriting::take_map].  Changing `ZipperWriting::graft_map` probably entails a corresponding
    /// change to [ZipperWriting::graft] also, to keep API consistency.
    /// Adam: It may not make conceptual sense, as was clear in the original cata definition; the subtrie
    /// can be interpreted as living below a value. This also argues for not having a value at the empty path,
    /// a change I'd also welcome. As for performance, graft is probably the most called zipper method.
    ///
    /// Luke: Personally I think it might make sense for all of the entry points to change behavior.
    /// Perhaps the biggest argument against the change is that it effectively doubles the cost of
    /// graft.  This is related to a similar question on [ZipperWriting::join_map_into]
    fn try_make_map(&self) -> Option<PathMap<V, A>>;

    /// Attempts to return a [TrieRef] from the current focus
    fn trie_ref(&self) -> Option<TrieRef<'_, V, A>>;

    /// Returns a clone of the allocator used by the zipper
    fn alloc(&self) -> A;
}

/// An interface to enable moving a zipper around the trie and inspecting paths
///
/// ## Terminology:
///
/// A zipper's **root** is a point in the trie above which the zipper cannot ascend.  A zipper permits
/// access to a subtrie descending from its root, but that subtrie may be a part of a supertrie that the
/// zipper is unable to access.
///
/// A zipper's **origin** is always equal-to-or-above the zipper's root.  The position of the origin depends
/// on how the zipper was created, and the origin will never be below the root.  The origin of a given zipper
/// will never change.
pub trait ZipperMoving: Zipper {
    /// Returns the number of bytes between the zipper's root and its current focus
    ///
    /// This is equal to `self.path().len()` for zippers that implement [`ZipperPath`], although
    /// implementations are usually able to supply it more cheaply than by measuring a path.  Zippers
    /// that do not retain a contiguous path buffer must still be able to report their depth.
    fn depth(&self) -> usize;

    /// Returns `true` if the zipper's focus is at its root, and it cannot ascend further, otherwise returns `false`
    fn at_root(&self) -> bool {
        self.depth() == 0
    }

    /// Returns the byte that was last descended to reach the zipper's focus, or `None` if that
    /// byte is unavailable
    ///
    /// After a movement that descends one byte, such as [`descend_to_byte`](ZipperMoving::descend_to_byte)
    /// or [`descend_first_byte`](ZipperMoving::descend_first_byte), this returns that byte.
    ///
    /// When [`at_root`](ZipperMoving::at_root) returns `true`, the return value is unspecified.  A
    /// zipper that retains knowledge of the trie upstream of its root may return the byte leading
    /// to its root, while a zipper without that knowledge, or one rooted at the trie root, returns
    /// `None`.  Therefore a `Some` return must not be interpreted to mean the zipper has descended,
    /// and callers needing that distinction must consult [`at_root`](ZipperMoving::at_root).
    fn focus_byte(&self) -> Option<u8>;

    /// Resets the zipper's focus back to its root
    fn reset(&mut self) {
        while !self.at_root() {
            self.ascend_byte();
        }
    }

    /// Returns the total number of values contained at and below the zipper's focus, including the focus itself
    ///
    /// WARNING: This is not a cheap method. It may have an order-N cost
    //GOAT! This doesn't belong here.  Should be a function that uses a non-side-effect catamorphism
    fn val_count(&self) -> usize;

    /// Moves the zipper deeper into the trie, to the `key` specified relative to the current zipper focus
    fn descend_to<K: AsRef<[u8]>>(&mut self, k: K);

    /// Fused [`descend_to`](ZipperMoving::descend_to) and [`path_exists`](Zipper::path_exists).  Moves the
    /// focus and returns whether or not the path exists at the new focus location
    fn descend_to_check<K: AsRef<[u8]>>(&mut self, k: K) -> bool {
        self.descend_to(k);
        self.path_exists()
    }

    /// Moves the zipper deeper into the trie, following the path specified by `k`, relative to the current
    /// zipper focus.  Descent stops at the point where the path does not exist
    ///
    /// Returns the number of bytes descended along the path.  The zipper's focus will always be on an
    /// existing path after this method returns, unless the method was called with the focus on a
    /// non-existent path.
    fn descend_to_existing<K: AsRef<[u8]>>(&mut self, k: K) -> usize {
        let k = k.as_ref();
        let mut i = 0;
        while i < k.len() {
            self.descend_to_byte(k[i]);
            if !self.path_exists() {
                self.ascend_byte();
                return i
            }
            i += 1
        }
        i
    }

    /// Moves the zipper deeper into the trie, following the path specified by `k`, relative to the current
    /// zipper focus.  Descent stops if a value is encountered or if the path ceases to exist.
    ///
    /// Returns the number of bytes descended along the path.
    ///
    /// If the focus is already on a value, this method will descend to the *next* value along
    /// the path.
    //GOAT. this default implementation could certainly be optimized
    fn descend_to_val<K: AsRef<[u8]>>(&mut self, k: K) -> usize {
        let k = k.as_ref();
        let mut i = 0;
        while i < k.len() {
            self.descend_to_byte(k[i]);
            if !self.path_exists() {
                self.ascend_byte();
                return i
            }
            i += 1;
            if self.is_val() {
                return i
            }
        }
        i
    }

    /// Deprecated alias for [ZipperMoving::descend_to_val]
    #[deprecated] //GOAT-old-names
    fn descend_to_value<K: AsRef<[u8]>>(&mut self, k: K) -> usize {
        self.descend_to_val(k)
    }

    /// Moves the zipper one byte deeper into the trie.  Identical in effect to [descend_to](Self::descend_to)
    /// with a 1-byte key argument
    fn descend_to_byte(&mut self, k: u8) {
        self.descend_to(&[k])
    }

    /// Moves the zipper one byte deeper into the trie, if the specified path byte exists in the [`child_mask`](Zipper::child_mask).
    ///
    /// Returns `true` if the zipper's focus moved and `false` if it is still at the original location.
    fn descend_to_existing_byte(&mut self, k: u8) -> bool {
        self.descend_to_byte(k);
        if self.path_exists() {
            true
        } else {
            self.ascend_byte();
            false
        }
    }

    /// Descends the zipper's focus one byte into a child branch uniquely identified by `child_idx`
    ///
    /// `child_idx` must within the range `0..child_count()` or this method will do nothing and return `false`
    ///
    /// WARNING: The branch represented by a given index is not guaranteed to be stable across modifications
    /// to the trie.  This method should only be used as part of a directed traversal operation, but
    /// index-based paths may not be stored as locations within the trie.
    fn descend_indexed_byte(&mut self, idx: usize) -> Option<u8> {
        let mask = self.child_mask();
        let child_byte = match mask.indexed_bit::<true>(idx) {
            Some(byte) => byte,
            None => {
                return None
            }
        };
        self.descend_to_byte(child_byte);
        debug_assert!(self.path_exists());
        Some(child_byte)
    }

    /// A deprecated alias for [ZipperMoving::descend_indexed_byte]
    #[deprecated] //GOAT-old-names
    fn descend_indexed_branch(&mut self, idx: usize) -> bool {
        self.descend_indexed_byte(idx).is_some()
    }

    /// Descends the zipper's focus one step into the first child branch in a depth-first traversal
    ///
    /// NOTE: This method should have identical behavior to passing `0` to [descend_indexed_byte](ZipperMoving::descend_indexed_byte),
    /// although with less overhead
    fn descend_first_byte(&mut self) -> Option<u8> {
        self.descend_indexed_byte(0)
    }

    /// Descends the zipper's focus one step into the last child branch
    ///
    /// NOTE: This method should have identical behavior to passing `child_count() - 1` to [descend_indexed_byte](ZipperMoving::descend_indexed_byte),
    /// although with less overhead
    fn descend_last_byte(&mut self) -> Option<u8> {
        let cc = self.child_count();
        if cc == 0 { None }
        else { self.descend_indexed_byte( cc- 1) }
    }

    /// Convenience form of [`ZipperMoving::descend_until_observed`] that does not observe path movement.
    fn descend_until(&mut self) -> bool {
        self.descend_until_observed(&mut ())
    }

    /// Descends the zipper's focus until a branch or a value is encountered, reporting movement to `obs`.
    /// Returns `true` if the focus moved otherwise returns `false`.
    ///
    /// If there is a value at the focus, the zipper will descend to the next value or branch, however the
    /// zipper will not descend further if this method is called with the focus already on a branch.
    ///
    /// Does nothing and returns `false` if the zipper's focus is on a non-existent path.
    fn descend_until_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        let mut descended = false;
        while self.child_count() == 1 {
            descended = true;
            if let Some(byte) = self.descend_first_byte() {
                obs.descend_to_byte(byte);
            }
            if self.is_val() {
                break;
            }
        }
        descended
    }

    /// Convenience form of [`ZipperMoving::descend_until_max_bytes_observed`] that does not observe
    /// path movement.
    fn descend_until_max_bytes(&mut self, max_bytes: usize) -> bool {
        self.descend_until_max_bytes_observed(max_bytes, &mut ())
    }

    /// Descends the zipper's focus until a branch or a value is encountered, or until `max_bytes`
    /// bytes have been descended, reporting movement to `obs`. Returns `true` if the focus moved
    /// otherwise returns `false`.
    ///
    /// If there is a value at the focus, the zipper will descend to the next value or branch, however the
    /// zipper will not descend further if this method is called with the focus already on a branch.
    ///
    /// Does nothing and returns `false` if the zipper's focus is on a non-existent path or if `max_bytes`
    /// is zero.
    fn descend_until_max_bytes_observed<Obs: PathObserver>(&mut self, max_bytes: usize, obs: &mut Obs) -> bool {
        if max_bytes == 0 {
            return false;
        }
        //`descend_until` is unbounded, so it may overshoot `max_bytes`.  A [TruncatingObserver]
        // forwards only the bytes within the limit to `obs` and counts the rest, so the zipper can
        // be brought back to the last byte that was reported.  Reporting the overshoot and then
        // retracting it would expose movement the caller never asked for.
        let mut truncating = TruncatingObserver::new(obs, max_bytes);
        let descended = self.descend_until_observed(&mut truncating);
        let overshoot = truncating.overshoot();
        if overshoot > 0 {
            self.ascend(overshoot);
        }
        descended
    }

    /// Ascends the zipper `steps` steps.  Returns the number of bytes ascended
    ///
    /// If the zipper's focus is fewer than `steps` steps from the root, then this method will stop at
    /// the root and return the number of steps ascended, which may be smaller than `steps`.
    fn ascend(&mut self, steps: usize) -> usize;

    /// Ascends the zipper up a single byte.  Equivalent to passing `1` to [ascend](Self::ascend)
    fn ascend_byte(&mut self) -> bool {
        self.ascend(1) == 1
    }

    /// Ascends the zipper to the nearest upstream branch point or value.  Returns the number of bytes
    /// ascended.  Returns `0` if the zipper was already at the root
    ///
    /// NOTE: A default implementation could be provided, but all current zippers have more optimal native implementations.
    fn ascend_until(&mut self) -> usize;

    /// Ascends the zipper to the nearest upstream branch point, skipping over values along the way.  Returns
    /// the number of bytes ascended.  Returns `0` if the zipper was already at the root
    ///
    /// NOTE: A default implementation could be provided, but all current zippers have more optimal native implementations.
    fn ascend_until_branch(&mut self) -> usize;

    /// Moves the zipper's focus to the next sibling byte with the same parent
    ///
    /// Returns `Some(byte)` if the focus was moved.  If the focus is already on the last byte among its siblings,
    /// this method returns None, leving the focus unmodified.
    ///
    /// This method is equivalent to calling [ZipperMoving::ascend] with `1`, followed by [ZipperMoving::descend_indexed_byte]
    /// where the index passed is 1 more than the index of the current focus position.
    fn to_next_sibling_byte(&mut self) -> Option<u8> {
        let cur_byte = self.focus_byte()?;
        if !self.ascend_byte() {
            return None
        }
        let mask = self.child_mask();
        match mask.next_bit(cur_byte) {
            Some(byte) => {
                self.descend_to_byte(byte);
                debug_assert!(self.path_exists());
                Some(byte)
            },
            None => {
                self.descend_to_byte(cur_byte);
                None
            }
        }
    }

    /// Moves the zipper's focus to the previous sibling byte with the same parent
    ///
    /// Returns `Some(byte)` if the focus was moved.  If the focus is already on the first byte among its siblings,
    /// this method returns None, leving the focus unmodified.
    ///
    /// This method is equivalent to calling [Self::ascend] with `1`, followed by [Self::descend_indexed_byte]
    /// where the index passed is 1 less than the index of the current focus position.
    fn to_prev_sibling_byte(&mut self) -> Option<u8> {
        let cur_byte = self.focus_byte()?;
        if !self.ascend_byte() {
            return None
        }
        let mask = self.child_mask();
        match mask.prev_bit(cur_byte) {
            Some(byte) => {
                self.descend_to_byte(byte);
                debug_assert!(self.path_exists());
                Some(byte)
            },
            None => {
                self.descend_to_byte(cur_byte);
                debug_assert!(self.path_exists());
                None
            }
        }
    }

    /// Convenience form of [`ZipperMoving::to_next_step_observed`] that does not observe path movement.
    fn to_next_step(&mut self) -> bool {
        self.to_next_step_observed(&mut ())
    }

    /// Advances the zipper to visit every existing path within the trie in a depth-first order,
    /// reporting movement to `obs`.
    ///
    /// Returns `true` if the position of the zipper has moved, or `false` if the zipper has returned
    /// to the root
    /// `obs` is notified of every movement made, so a caller can track the zipper's location without
    /// the zipper needing to maintain a path buffer of its own.  Pass `&mut ()` to discard them.
    fn to_next_step_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {

        //If we're at a leaf ascend until we're not and jump to the next sibling
        if self.child_count() == 0 {
            //We can stop ascending when we succeed in moving to a sibling
            loop {
                match self.to_next_sibling_byte() {
                    Some(byte) => {
                        //A sibling step replaces the last byte rather than adding one, so the
                        //observer sees the old byte retracted before the new one arrives.
                        obs.ascend(1);
                        obs.descend_to_byte(byte);
                        break
                    },
                    None => {
                        if !self.ascend_byte() {
                            return false;
                        }
                        obs.ascend(1);
                    }
                }
            }
        } else {
            return match self.descend_first_byte() {
                Some(byte) => {
                    obs.descend_to_byte(byte);
                    true
                },
                None => false
            }
        }
        true
    }
}

/// Receives notifications about the movements a [Zipper] makes, so a caller can track the
/// zipper's location without the zipper needing to maintain a path buffer of its own
///
/// Implementations decide how much of the movement to retain.  [`Vec<u8>`] accumulates the
/// full path, [`usize`] records only the depth, and `()` discards everything.
pub trait PathObserver {
    /// Informs the `PathObserver` that the zipper is descending `path` bytes, relative
    /// to the zipper's current focus
    fn descend_to(&mut self, path: &[u8]);

    /// Equivalent to `self.descend_to(&[byte])` but with slightly less overhead
    fn descend_to_byte(&mut self, byte: u8) {
        self.descend_to(&[byte]);
    }

    /// Informs the `PathObserver` that the zipper is ascending `steps` bytes, relative
    /// to the zipper's current focus
    fn ascend(&mut self, steps: usize);
}

impl PathObserver for Vec<u8> {
    fn descend_to(&mut self, path: &[u8]) {
        self.extend_from_slice(path);
    }
    fn descend_to_byte(&mut self, byte: u8) {
        self.push(byte)
    }
    fn ascend(&mut self, steps: usize) {
        self.truncate(self.len() - steps)
    }
}

/// Tracks the depth of the zipper's focus, without retaining the path itself
impl PathObserver for usize {
    fn descend_to(&mut self, path: &[u8]) {
        *self += path.len();
    }
    fn descend_to_byte(&mut self, _byte: u8) {
        *self += 1;
    }
    fn ascend(&mut self, steps: usize) {
        *self -= steps;
    }
}

impl PathObserver for () {
    fn descend_to(&mut self, _path: &[u8]) { }
    fn descend_to_byte(&mut self, _byte: u8) { }
    fn ascend(&mut self, _steps: usize) { }
}

/// Captures descended bytes inline, without ever allocating
///
/// A composite zipper can use this to see exactly which bytes one of its source zippers descended,
/// without requiring that source to maintain a path buffer of its own.
///
/// The caller must bound each descent by the remaining capacity — typically by passing it to
/// [`descend_until_max_bytes_observed`](ZipperMoving::descend_until_max_bytes_observed) — because descending more
/// bytes than the buffer can hold will panic.
impl<const CAPACITY: usize> PathObserver for ArrayVec<u8, CAPACITY> {
    #[inline]
    fn descend_to(&mut self, path: &[u8]) {
        debug_assert!(path.len() <= self.remaining_capacity(),
            "ArrayVec PathObserver overflow: bound the descent by the remaining capacity");
        self.try_extend_from_slice(path)
            .expect("ArrayVec PathObserver overflow: bound the descent by the remaining capacity");
    }
    #[inline]
    fn descend_to_byte(&mut self, byte: u8) {
        debug_assert!(self.remaining_capacity() >= 1,
            "ArrayVec PathObserver overflow: bound the descent by the remaining capacity");
        self.push(byte);
    }
    #[inline]
    fn ascend(&mut self, steps: usize) {
        let new_len = self.len().saturating_sub(steps);
        self.truncate(new_len);
    }
}

impl<Obs: PathObserver + ?Sized> PathObserver for &mut Obs {
    fn descend_to(&mut self, path: &[u8]) { (**self).descend_to(path) }
    fn descend_to_byte(&mut self, byte: u8) { (**self).descend_to_byte(byte) }
    fn ascend(&mut self, steps: usize) { (**self).ascend(steps) }
}

/// Forwards every movement to both observers, so a zipper can record a movement for itself
/// while also reporting it onward to its caller
impl<A: PathObserver, B: PathObserver> PathObserver for (A, B) {
    fn descend_to(&mut self, path: &[u8]) {
        self.0.descend_to(path);
        self.1.descend_to(path);
    }
    fn descend_to_byte(&mut self, byte: u8) {
        self.0.descend_to_byte(byte);
        self.1.descend_to_byte(byte);
    }
    fn ascend(&mut self, steps: usize) {
        self.0.ascend(steps);
        self.1.ascend(steps);
    }
}

/// A [PathObserver] that replays the movements it observes onto another zipper
///
/// This lets a composite zipper keep a second zipper in step with a movement made by the first,
/// without needing to buffer the bytes that were moved over.
///
/// NOTE: the mirrored zipper is moved with [`descend_to`](ZipperMoving::descend_to), so it will
/// follow the movement even where that leads off the end of its own trie.
pub struct MirrorPathObserver<'z, Z>(pub &'z mut Z);

impl<Z: ZipperMoving> PathObserver for MirrorPathObserver<'_, Z> {
    #[inline]
    fn descend_to(&mut self, path: &[u8]) {
        self.0.descend_to(path);
    }
    #[inline]
    fn descend_to_byte(&mut self, byte: u8) {
        self.0.descend_to_byte(byte);
    }
    #[inline]
    fn ascend(&mut self, steps: usize) {
        self.0.ascend(steps);
    }
}

/// A [PathObserver] that forwards at most a fixed number of bytes onward to another observer,
/// while counting everything it sees
///
/// This lets a caller impose a byte limit on a descent that reports more than the limit allows.
/// The bytes beyond the limit are counted but not forwarded, so the caller can ascend by
/// [`overshoot`](Self::overshoot) to bring the zipper back to the last byte that was reported.
///
/// Nothing is buffered; bytes are passed through as they arrive.
struct TruncatingObserver<'a, Obs> {
    obs: &'a mut Obs,
    /// The most bytes that may be forwarded to `obs`
    limit: usize,
    /// The total number of bytes observed, including any beyond `limit`.  The number of bytes
    /// forwarded to `obs` is always `descended.min(limit)`, so it doesn't need its own field.
    descended: usize,
}

impl<'a, Obs: PathObserver> TruncatingObserver<'a, Obs> {
    #[inline]
    fn new(obs: &'a mut Obs, limit: usize) -> Self {
        Self { obs, limit, descended: 0 }
    }
    /// The number of bytes forwarded to `obs` so far
    #[inline]
    fn forwarded(&self) -> usize {
        self.descended.min(self.limit)
    }
    /// The number of bytes observed beyond the limit, which were not forwarded to `obs`
    #[inline]
    fn overshoot(&self) -> usize {
        self.descended.saturating_sub(self.limit)
    }
}

impl<Obs: PathObserver> PathObserver for TruncatingObserver<'_, Obs> {
    #[inline]
    fn descend_to(&mut self, path: &[u8]) {
        let take = self.limit.saturating_sub(self.descended).min(path.len());
        if take > 0 {
            self.obs.descend_to(&path[..take]);
        }
        self.descended += path.len();
    }
    #[inline]
    fn descend_to_byte(&mut self, byte: u8) {
        if self.descended < self.limit {
            self.obs.descend_to_byte(byte);
        }
        self.descended += 1;
    }
    #[inline]
    fn ascend(&mut self, steps: usize) {
        //Any overshoot unwinds first, because it was never forwarded.  Only the portion of the
        //ascent that eats into the forwarded bytes is passed onward.
        let before = self.forwarded();
        self.descended = self.descended.saturating_sub(steps);
        let after = self.forwarded();
        if before > after {
            self.obs.ascend(before - after);
        }
    }
}

/// A [PathObserver] that reduces the path it observes to a 64-bit digest
///
/// The digest is independent of how the movements were chunked, so +`12` +`34`, +`1234`, and
/// +`1` +`23` +`4` all produce the same value.  This makes it suitable for comparing two zippers
/// that visit identical paths but report them in different-sized pieces.
///
/// Note this is invariance over *chunking*, not over byte order.  So +`4321` puts different bytes
/// at every depth and therefore does not match +`1234`.
///
/// Ascending zeroes the digest, because the bytes being ascended over aren't reported and their
/// contributions can't be removed.  Two observers tracking the same movements zero together, so they
/// still agree; the digest simply stops carrying information from movements prior to the last ascend.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct HashObserver {
    /// The digest of the observed path
    pub hash: u64,
    /// The depth of the observed path
    pub depth: usize,
}

impl PathObserver for HashObserver {
    #[inline]
    fn descend_to(&mut self, path: &[u8]) {
        for &byte in path {
            self.descend_to_byte(byte);
        }
    }
    #[inline]
    fn descend_to_byte(&mut self, byte: u8) {
        //SplitMix64's finalizer, a bijection, so distinct (depth, byte) pairs contribute
        //distinct values
        let mut z = (((self.depth as u64) << 8) | byte as u64).wrapping_mul(0x9E3779B97F4A7C15);
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
        self.hash ^= z ^ (z >> 27);
        self.depth += 1;
    }
    #[inline]
    fn ascend(&mut self, steps: usize) {
        self.hash = 0;
        self.depth = self.depth.saturating_sub(steps);
    }
}

/// An interface to access values through a [Zipper] that cannot modify the trie.  Allows
/// references with lifetimes that may outlive the zipper
///
/// This trait will never be implemented on the same type as [ZipperWriting]
pub trait ZipperReadOnlyValues<'a, V>: ZipperValues<V> {
    /// Returns a refernce to the value at the zipper's focus, or `None` if there is no value
    ///
    /// NOTE: Unlike [ZipperValues::val], this method returns a reference with the lifetime of `'a`
    /// instead of the temporary lifetime of the method.
    fn get_val(&self) -> Option<&'a V>;

    /// Returns a refernce to the value at `path`, relative to the zipper's focus, or `None` if there is no value
    ///
    /// NOTE: Unlike [ZipperValues::val_at], this method returns a reference with the lifetime of `'a`
    /// instead of the temporary lifetime of the method.
    fn get_val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&'a V>;

    /// Deprecated alias for [ZipperReadOnlyValues::get_val]
    #[deprecated] //GOAT-old-names
    fn get_value(&self) -> Option<&'a V> {
        self.get_val()
    }
}

/// A [`witness`](ZipperReadOnlyConditionalValues::witness) type used by [`ReadZipperTracked`] and [`ReadZipperOwned`]
pub struct ReadZipperWitness<V: Clone + Send + Sync, A: Allocator>(pub(crate) Option<TrieNodeODRc<V, A>>);

crate::impl_name_only_debug!(
    impl<V: Clone + Send + Sync + Unpin, A: Allocator> core::fmt::Debug for ReadZipperWitness<V, A>
);

/// Conceptually similar to [ZipperReadOnlyValues] but requires a [`witness`](ZipperReadOnlyConditionalValues::witness)
/// to ensure the data remains intact.
///
/// NOTE: In a future version of rust, when there is some support for disjoint borrows, we could unify
/// this trait with `ZipperReadOnlyValues` by splitting the "read guard" function of the zipper from
/// the "cursor" function of the zipper.
pub trait ZipperReadOnlyConditionalValues<'a, V>: ZipperValues<V> {
    /// The type that acts as a witness for the validity of the zipper
    type WitnessT;

    /// Creates a witness that can allow acquisition of longer-lived borrows of values, while the
    /// zipper itself is mutated
    fn witness<'w>(&self) -> Self::WitnessT;

    /// Returns a refernce to the value at the zipper's focus, or `None` if there is no value
    ///
    /// NOTE: Unlike [ZipperValues::val], this method returns a reference with the lifetime of `'a`
    /// instead of the temporary lifetime of the method.
    fn get_val_with_witness<'w>(&self, witness: &'w Self::WitnessT) -> Option<&'w V> where 'a: 'w;
}

/// An interface to implement iterating over all values in a subtrie via a zipper
pub trait ZipperReadOnlyIteration<'a, V>: ZipperReadOnlyValues<'a, V> + ZipperIteration {
    /// Advances to the next value with behavior identical to [ZipperIteration::to_next_val], but returns
    /// a reference to the value or `None` if the zipper has encountered the root
    ///
    /// `obs` is notified of every movement made, so a caller can track the zipper's location without
    /// the zipper needing to maintain a path buffer of its own.  Pass `&mut ()` to discard them.
    /// Convenience form of [`ZipperReadOnlyIteration::to_next_get_val_observed`] that does not observe path movement.
    fn to_next_get_val(&mut self) -> Option<&'a V> {
        self.to_next_get_val_observed(&mut ())
    }

    /// Advances to the next value and reports movement to `obs`.
    fn to_next_get_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> Option<&'a V> {
        if self.to_next_val_observed(obs) {
            let val = self.get_val();
            debug_assert!(val.is_some());
            val
        } else {
            None
        }
    }

    /// Convenience form of [`ZipperReadOnlyIteration::to_next_get_value_observed`] that does not observe path movement.
    #[deprecated] //GOAT-old-names
    fn to_next_get_value(&mut self) -> Option<&'a V> {
        self.to_next_get_val_observed(&mut ())
    }

    /// Deprecated observed alias for [`ZipperReadOnlyIteration::to_next_get_val_observed`].
    #[deprecated] //GOAT-old-names
    fn to_next_get_value_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> Option<&'a V> {
        self.to_next_get_val_observed(obs)
    }
}

/// Similar to [ZipperReadOnlyIteration].  See [ZipperReadOnlyConditionalValues] for an explanation about
/// why this trait exists
pub trait ZipperReadOnlyConditionalIteration<'a, V>: ZipperReadOnlyConditionalValues<'a, V> + ZipperIteration {
    /// Convenience form of [`ZipperReadOnlyConditionalIteration::to_next_get_val_with_witness_observed`] that does not observe path movement.
    fn to_next_get_val_with_witness<'w>(&mut self, witness: &'w Self::WitnessT) -> Option<&'w V> where 'a: 'w {
        self.to_next_get_val_with_witness_observed(witness, &mut ())
    }

    /// See [`ZipperReadOnlyIteration::to_next_get_val_observed`] and [`witness`](ZipperReadOnlyConditionalValues::witness).
    ///
    /// `obs` is notified of every movement made, so a caller can track the zipper's location without
    /// the zipper needing to maintain a path buffer of its own.  Pass `&mut ()` to discard them.
    fn to_next_get_val_with_witness_observed<'w, Obs: PathObserver>(&mut self, witness: &'w Self::WitnessT, obs: &mut Obs) -> Option<&'w V> where 'a: 'w {
        if self.to_next_val_observed(obs) {
            let val = self.get_val_with_witness(witness);
            debug_assert!(val.is_some());
            val
        } else {
            None
        }
    }
}

/// Opaque type to access trie internals
#[doc(hidden)]
#[derive(Debug)]
pub struct OpaqueAbstractNodeRef<'trie, V: Clone + Send + Sync, A: Allocator>(pub(crate) AbstractNodeRef<'trie, V, A>);

impl<'a, V: Clone + Send + Sync, A: Allocator> OpaqueAbstractNodeRef<'a, V, A> {
    pub(crate) fn is_none(&self) -> bool { self.0.is_none() }
    #[cfg(feature = "viz")]
    pub(crate) fn borrow(&self) -> Option<&TrieNodeODRc<V, A>> { self.0.borrow() }
    pub(crate) fn into_option(self) -> Option<TrieNodeODRc<V, A>> { self.0.into_option() }
    pub(crate) fn as_tagged(&self) -> TaggedNodeRef<'_, V, A> { self.0.as_tagged() }
    pub(crate) fn try_as_tagged(&self) -> Option<TaggedNodeRef<'_, V, A>> { self.0.try_as_tagged() }
}

/// Opaque type to access trie internals
#[doc(hidden)]
#[derive(Debug)]
pub struct OpaqueTrieNodeRef<'trie, V: Clone + Send + Sync, A: Allocator>(pub(crate) &'trie TrieNodeODRc<V, A>);

/// Similar to [ZipperSubtries], but with the stronger guarantee that subtrie access will be constant-time and won't fail
pub trait ZipperInfallibleSubtries<V: Clone + Send + Sync, A: Allocator = GlobalAlloc>: ZipperValues<V> + Zipper {
    /// Returns a new [PathMap] containing everything below the zipper's focus
    fn make_map(&self) -> PathMap<V, A>;

    /// Return a [TrieRef] from the current focus
    fn get_trie_ref(&self) -> TrieRef<'_, V, A>;

    /// **INTERNAL USE ONLY**  Returns a reference to trie internals
    #[doc(hidden)]
    fn get_focus(&self) -> OpaqueAbstractNodeRef<'_, V, A>;

    /// **INTERNAL USE ONLY**  Returns a reference to trie internals
    #[doc(hidden)]
    fn get_focus_at<K: AsRef<[u8]>>(&self, path: K) -> OpaqueAbstractNodeRef<'_, V, A>;

    /// **INTERNAL USE ONLY**  Attemps to return a node at the zipper's focus.  Returns
    /// `None` if the focus is not on a node.
    ///
    /// DISCUSSION - What's the difference between `try_borrow_focus` and `get_focus`???
    /// The difference is in the intended use each is optimized for.
    ///
    /// * `get_focus` will return something that behaves like a node no matter what, if the
    /// focus is on an existing path.  So it succeeds regardless of the underlying trie
    /// structure.  It is used to get the source for algebraic and graft operations.
    ///
    /// * `try_borrow_focus` will only return a node if the zipper is positioned on a node
    /// in the underlying structure.  This enables the underlying structure to be cut, in
    /// preparation for safely splitting it into multiple independent regions, as when a
    /// [ZipperHead] needs to make a WriteZipper that can be sent to another thread.
    #[doc(hidden)]
    fn try_borrow_focus(&self) -> Option<OpaqueTrieNodeRef<'_, V, A>>;
}

/// An interface to access subtries through a [Zipper] that cannot modify the trie.  Allows
/// references with lifetimes that may outlive the zipper
///
/// This trait will never be implemented on the same type as [ZipperWriting]
pub trait ZipperReadOnlySubtries<'a, V: Clone + Send + Sync, A: Allocator = GlobalAlloc>: ZipperSubtries<V, A> + ZipperReadOnlyPriv<'a, V, A> {
    /// The type of the returned [TrieRef]
    type TrieRefT: Into<TrieRef<'a, V, A>> where V: 'a, A: 'a;

    /// Returns a [TrieRef] for the specified path, relative to the current focus
    fn trie_ref_at_path<K: AsRef<[u8]>>(&self, path: K) -> Self::TrieRefT;
}

/// An interface for advanced [Zipper] movements used for various types of iteration; such as iterating
/// every value, or iterating all paths descending from a common root at a certain depth
///
/// Every method takes a [PathObserver], so these movements are available to "blind" zippers that do
/// not maintain a contiguous path buffer of their own.
pub trait ZipperIteration: ZipperMoving {
    /// Convenience form of [`ZipperIteration::to_next_val_observed`] that does not observe path movement.
    fn to_next_val(&mut self) -> bool {
        self.to_next_val_observed(&mut ())
    }

    /// Systematically advances to the next value accessible from the zipper, traversing in a depth-first
    /// order and reporting movement to `obs`.
    ///
    /// Returns `true` if the zipper is positioned at the next value, or `false` if the zipper has
    /// encountered the root.
    ///
    /// `obs` is notified of every movement made, so a caller can track the zipper's location without
    /// the zipper needing to maintain a path buffer of its own.  Pass `&mut ()` to discard them.
    fn to_next_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        loop {
            if let Some(byte) = self.descend_first_byte() {
                obs.descend_to_byte(byte);
                if self.is_val() {
                    return true
                }
                if self.descend_until_observed(obs) {
                    if self.is_val() {
                        return true
                    }
                }
            } else {
                'ascending: loop {
                    if let Some(byte) = self.to_next_sibling_byte() {
                        //A sibling step replaces the last byte rather than adding one, so the
                        //observer sees the old byte retracted before the new one arrives.
                        obs.ascend(1);
                        obs.descend_to_byte(byte);
                        if self.is_val() {
                            return true
                        }
                        break 'ascending
                    } else {
                        if self.ascend_byte() {
                            obs.ascend(1);
                        }
                        if self.at_root() {
                            return false
                        }
                    }
                }
            }
        }
    }

    /// Convenience form of [`ZipperIteration::descend_last_path_observed`] that does not observe path movement.
    fn descend_last_path(&mut self) -> bool {
        self.descend_last_path_observed(&mut ())
    }

    /// Descends the zipper to the end of the last path (last by sort order) reachable by descent
    /// from the current focus, reporting movement to `obs`.
    ///
    /// This is equivalent to calling [ZipperMoving::descend_last_byte] in a loop.
    ///
    /// Returns `true` if the zipper has sucessfully descended, or `false` if the zipper was already
    /// at the end of a path.  If this method returns `false` then the zipper will be in its original
    /// position.
    ///
    /// `obs` is notified of every movement made, so a caller can track the zipper's location without
    /// the zipper needing to maintain a path buffer of its own.  Pass `&mut ()` to discard them.
    fn descend_last_path_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        let mut any = false;
        while let Some(byte) = self.descend_last_byte() {
            any = true;
            obs.descend_to_byte(byte);
            self.descend_until_observed(obs);
        }
        any
    }

    /// Convenience form of [`ZipperIteration::descend_first_k_path_observed`] that does not observe
    /// path movement.
    fn descend_first_k_path(&mut self, k: usize) -> bool {
        self.descend_first_k_path_observed(k, &mut ())
    }

    /// Descends the zipper's focus `k` bytes, following the first child at each branch, and continuing
    /// with depth-first exploration until a path that is `k` bytes from the focus has been found, reporting
    /// movement to `obs`.
    ///
    /// Returns `true` if the zipper has sucessfully descended `k` steps, or `false` otherwise.  If this
    /// method returns `false` then the zipper will be in its original position.
    ///
    /// WARNING: This is not a constant-time operation, and may be as bad as `order n` with respect to the paths
    /// below the zipper's focus.  Although a typical cost is `order log n` or better.
    ///
    /// `obs` is notified of every movement made, so a caller can track the zipper's location without
    /// the zipper needing to maintain a path buffer of its own.  Pass `&mut ()` to discard them.
    ///
    /// See: [to_next_k_path](ZipperIteration::to_next_k_path)
    fn descend_first_k_path_observed<Obs: PathObserver>(&mut self, k: usize, obs: &mut Obs) -> bool {
        k_path_default_internal(self, k, self.depth(), obs)
    }

    /// Convenience form of [`ZipperIteration::to_next_k_path_observed`] that does not observe path movement.
    fn to_next_k_path(&mut self, k: usize) -> bool {
        self.to_next_k_path_observed(k, &mut ())
    }

    /// Moves the zipper's focus to the next location with the same path length as the current focus,
    /// following a depth-first exploration from a common root `k` steps above the current focus, reporting
    /// movement to `obs`.
    ///
    /// Returns `true` if the zipper has sucessfully moved to a new location at the same level, or `false`
    /// if no further locations exist.  If this method returns `false` then the zipper will be ascended `k`
    /// steps to the common root.  (The focus position when [descend_first_k_path](ZipperIteration::descend_first_k_path) was called)
    ///
    /// If `k` exceeds the current depth this method returns `false` and resets the zipper's focus to the root.
    ///
    /// WARNING: This is not a constant-time operation, and may be as bad as `order n` with respect to the paths
    /// below the zipper's focus.  Although a typical cost is `order log n` or better.
    ///
    /// `obs` is notified of every movement made, so a caller can track the zipper's location without
    /// the zipper needing to maintain a path buffer of its own.  Pass `&mut ()` to discard them.
    ///
    /// See: [descend_first_k_path](ZipperIteration::descend_first_k_path)
    fn to_next_k_path_observed<Obs: PathObserver>(&mut self, k: usize, obs: &mut Obs) -> bool {
        let depth = self.depth();
        let base_idx = if depth < k {
            return k_path_depth_exceeded(self, depth, obs)
        } else {
            depth - k
        };
        k_path_default_internal(self, k, base_idx, obs)
    }
}

/// Handles an out-of-range `to_next_k_path` request without bloating its hot path.
#[cold]
#[inline(never)]
fn k_path_depth_exceeded<Z: ZipperMoving + ?Sized, Obs: PathObserver>(z: &mut Z, depth: usize, obs: &mut Obs) -> bool {
    z.reset();
    obs.ascend(depth);
    false
}

/// The default implementation of both [ZipperIteration::to_next_k_path] and [ZipperIteration::descend_first_k_path]
///
/// `base_idx` is the [`depth`](ZipperMoving::depth) of the common root the traversal explores from, and
/// the traversal is finished when the depth returns to it.
#[inline]
fn k_path_default_internal<Z: ZipperMoving + ?Sized, Obs: PathObserver>(z: &mut Z, k: usize, base_idx: usize, obs: &mut Obs) -> bool {
    loop {
        if z.depth() < base_idx + k {
            while let Some(byte) = z.descend_first_byte() {
                obs.descend_to_byte(byte);
                if z.depth() == base_idx + k { return true }
            }
        }
        //A sibling step replaces the last byte rather than adding one, so the observer sees the old
        //byte retracted before the new one arrives
        if let Some(byte) = z.to_next_sibling_byte() {
            obs.ascend(1);
            obs.descend_to_byte(byte);
            if z.depth() == base_idx + k { return true }
            continue
        }
        while z.depth() > base_idx {
            if z.ascend_byte() {
                obs.ascend(1);
            }
            if z.depth() == base_idx { return false }
            if let Some(byte) = z.to_next_sibling_byte() {
                obs.ascend(1);
                obs.descend_to_byte(byte);
                break
            }
        }
    }
}

/// An interface for a [Zipper] that maintains the path from its root to its current focus
///
/// Zippers that do not retain a contiguous path buffer of their own will not implement this
/// trait.  A caller can track the path of such a zipper by supplying a [PathObserver] to the
/// movement methods that accept one.
pub trait ZipperPath: ZipperMoving {
    /// Returns the path from the zipper's root to the current focus
    ///
    /// This method will always return a zero-length slice when [`at_root`](ZipperMoving::at_root)
    /// returns `true`, and a non-zero-length slice when it returns `false`.
    fn path(&self) -> &[u8];

    /// Moves the zipper's focus to a specific location specified by `path`, relative to the zipper's root
    ///
    /// Returns the number of bytes shared between the old and new location
    fn move_to_path<K: AsRef<[u8]>>(&mut self, path: K) -> usize {
        let path = path.as_ref();
        let p = self.path();
        let overlap = find_prefix_overlap(path, p);
        let to_ascend = p.len() - overlap;
        if overlap == 0 {  // This heuristic can be fine-tuned for performance; the behavior of the two branches is equivalent
            self.reset();
            self.descend_to(path);
            overlap
        } else {
            self.ascend(to_ascend);
            self.descend_to(&path[overlap..]);
            overlap
        }
    }
}

/// An interface for a [Zipper] to support accessing the full path buffer used to create the zipper
pub trait ZipperAbsolutePath: ZipperPath {
    /// Returns the entire path from the zipper's origin to its current focus
    ///
    /// The zipper's origin depends on how the zipper was created.  For zippers created directly from a
    /// [PathMap], `absolute_path` will start at the root of the map, regardless of the prefix path.
    ///
    /// `zip.origin_path() == zip.root_prefix_path() + zip.path()`
    fn origin_path(&self) -> &[u8];

    /// Returns the path from the zipper's origin to the zipper's root
    ///
    /// This function output remains constant throughout the zipper's life.
    ///
    /// After [reset](ZipperMoving::reset) is called, `zip.root_prefix_path() == zip.origin_path()`.
    fn root_prefix_path(&self) -> &[u8];
}

/// Implemented on zippers that traverse in-memory trie structures, as opposed to virtual
/// spaces or abstract projections.
///
/// In some cases `ZipperConcrete` can be implemented on projection zippers, such as [ProductZipper],
/// because it is composed of concrete tries
pub trait ZipperConcrete {
    /// Get an identifier unique to the node at the zipper's focus, if the zipper's focus is at the
    /// root of a node in memory.  When zipper's focus is inside of a node, returns `None`.
    ///
    /// NOTE: The returned value is not a logical hash of the contents, but is based on
    /// the node's memory address.  Therefore it is not stable across runs and can't be
    /// used to infer logical or structural equality.  Furthermore, it is subject to
    /// change when the content of the node is modified.
    ///
    /// However when returned identifiers are equal it means the zipper has arrived at the same node
    /// in memory, even if it got there via different parent paths through the trie.
    fn shared_node_id(&self) -> Option<u64>;

    /// Returns `true` if the zipper's focus is at a location that may be accessed via two or
    /// more distinct paths
    ///
    /// DISCUSSION: the `shared` property applied only to a singular position and is not transitive
    /// to descending locations in the trie.  In other words, if this function returns `true` for
    /// a specific location, it may not return `true` for other paths descended from that location.
    ///
    /// WARNING: your code must never rely on the return value of `is_shared` for correctness; this
    /// information should be used only for optimizations.  The `shared` property may be affected by
    /// a number of internal behaviors that must not be relied upon.  For example, a previously shared
    /// subtrie may be copied for thread isolation, or the internal trie representation might otherwise
    /// change, and alter the shared property.
    ///
    /// GOAT: Make a graphic diagram to illustrate the `shared` property.  The graphic should have
    /// multiple shared subtries accessible via distinct paths, and highlight which locations will be
    /// considered `shared` from the perspective of this method.
    fn is_shared(&self) -> bool;
}

/// Provides more direct control over a [ZipperMoving] zipper's path buffer
pub trait ZipperPathBuffer: ZipperMoving {
    /// Internal method to get the path, beyond its length.  Panics if `len` > the path's capacity, or
    /// if the zipper is relative and doesn't have an `origin_path`
    ///
    /// This method is unsafe because it relies on the caller to not read uninitialized memory, even if
    /// the memory has been allocated.
    unsafe fn origin_path_assert_len(&self, len: usize) -> &[u8];

    /// Make sure the path buffer is allocated, to facilitate zipper movement
    fn prepare_buffers(&mut self);

    /// Reserve buffer space within the zipper's path buffer and node stack
    ///
    /// This method will only grow the buffers and will never shrink them.
    fn reserve_buffers(&mut self, path_len: usize, stack_depth: usize);
}

pub(crate) mod zipper_priv {
    use super::*;

    pub trait ZipperReadOnlyPriv<'a, V: Clone + Send + Sync, A: Allocator> {
        /// Internal method returns the minimal components that compose the zipper, which are:
        ///
        /// `(focus_node, node_key, focus_val)`
        ///
        /// This method will always return either a zero-length `node_key` or `None` for
        /// `focus_val` (it may return both of those things, but always at least one)
        fn borrow_raw_parts(&self) -> (TaggedNodeRef<'_, V, A>, &[u8], Option<&V>);

        /// Returns a the [ReadZipperCore] from inside the zipper leaving a placeholder in the zipper.
        /// Returns `None` if the zipper doesn't support movement
        ///
        /// WARNING: Separating a core from its container is very dangerous.  This method should not be
        /// used lightly.  The reason this method doesn't consume the zipper because we need to keep the
        /// original around to keep the tracker, or parhaps a backing map, active as long as we're working
        /// with this core.
        ///
        /// NOTE: (This isn't in its own trait because I didn't want to further
        /// pollute the API, given we already have [ZipperReadOnly] and [ZipperMoving])
        fn take_core(&mut self) -> Option<ReadZipperCore<'a, 'static, V, A>>;
    }
}
use zipper_priv::*;

macro_rules! zipper_impl_lens {
    (ZipperIteration $s: ident => $e:expr) => {
        fn to_next_val_observed<Obs: PathObserver>(&mut $s, obs: &mut Obs) -> bool { $e.to_next_val_observed(obs) }
        fn descend_last_path_observed<Obs: PathObserver>(&mut $s, obs: &mut Obs) -> bool { $e.descend_last_path_observed(obs) }
        fn descend_first_k_path_observed<Obs: PathObserver>(&mut $s, k: usize, obs: &mut Obs) -> bool { $e.descend_first_k_path_observed(k, obs) }
        fn to_next_k_path_observed<Obs: PathObserver>(&mut $s, k: usize, obs: &mut Obs) -> bool { $e.to_next_k_path_observed(k, obs) }
    };
    (ZipperAbsolutePath $s: ident => $e:expr) => {
        fn origin_path(&$s) -> &[u8] { $e.origin_path() }
        fn root_prefix_path(&$s) -> &[u8] { $e.root_prefix_path() }
    };
    (ZipperPath $s: ident => $e:expr) => {
        #[inline] fn path(&$s) -> &[u8] { $e.path() }
        fn move_to_path<K: AsRef<[u8]>>(&mut $s, path: K) -> usize { $e.move_to_path(path) }
    };
    (Zipper $s: ident => $e:expr) => {
        #[inline] fn path_exists(&$s) -> bool { $e.path_exists() }
        fn is_val(&$s) -> bool { $e.is_val() }
        fn child_count(&$s) -> usize { $e.child_count() }
        fn child_mask(&$s) -> ByteMask { $e.child_mask() }
    };
    (ZipperValues $s: ident => $e:expr) => {
        fn val(&$s) -> Option<&V> { $e.val() }
        fn val_at<K: AsRef<[u8]>>(&$s, path: K) -> Option<&V> { $e.val_at(path) }
    };
    (ZipperForking $s: ident => $e:expr) => {
        fn fork_read_zipper<'a>(&'a $s) -> Self::ReadZipperT<'a> { $e.fork_read_zipper() }
    };
    (ZipperSubtries $s: ident => $e:expr) => {
        fn native_subtries(&$s) -> bool { $e.native_subtries() }
        fn try_make_map(&$s) -> Option<crate::PathMap<V, A>> { $e.try_make_map() }
        fn trie_ref(&$s) -> Option<TrieRef<'_, V, A>> { $e.trie_ref() }
        fn alloc(&$s) -> A { $e.alloc() }
    };
    (ZipperMoving $s: ident => $e:expr) => {
        #[inline] fn depth(&$s) -> usize { $e.depth() }
        fn at_root(&$s) -> bool { $e.at_root() }
        #[inline] fn focus_byte(&$s) -> Option<u8> { $e.focus_byte() }
        fn reset(&mut $s) { $e.reset() }
        fn val_count(&$s) -> usize { $e.val_count() }
        fn descend_to<K: AsRef<[u8]>>(&mut $s, k: K) { $e.descend_to(k) }
        fn descend_to_check<K: AsRef<[u8]>>(&mut $s, k: K) -> bool { $e.descend_to_check(k) }
        fn descend_to_existing<K: AsRef<[u8]>>(&mut $s, k: K) -> usize { $e.descend_to_existing(k) }
        fn descend_to_val<K: AsRef<[u8]>>(&mut $s, k: K) -> usize { $e.descend_to_val(k) }
        fn descend_to_byte(&mut $s, k: u8) { $e.descend_to_byte(k) }
        fn descend_to_existing_byte(&mut $s, k: u8) -> bool { $e.descend_to_existing_byte(k) }
        fn descend_indexed_byte(&mut $s, child_idx: usize) -> Option<u8> { $e.descend_indexed_byte(child_idx) }
        fn descend_first_byte(&mut $s) -> Option<u8> { $e.descend_first_byte() }
        fn descend_until_observed<Obs: PathObserver>(&mut $s, obs: &mut Obs) -> bool { $e.descend_until_observed(obs) }
        fn descend_until_max_bytes_observed<Obs: PathObserver>(&mut $s, max_bytes: usize, obs: &mut Obs) -> bool { $e.descend_until_max_bytes_observed(max_bytes, obs) }
        fn to_next_sibling_byte(&mut $s) -> Option<u8> { $e.to_next_sibling_byte() }
        fn to_prev_sibling_byte(&mut $s) -> Option<u8> { $e.to_prev_sibling_byte() }
        fn ascend(&mut $s, steps: usize) -> usize { $e.ascend(steps) }
        fn ascend_byte(&mut $s) -> bool { $e.ascend_byte() }
        fn ascend_until(&mut $s) -> usize { $e.ascend_until() }
        fn ascend_until_branch(&mut $s) -> usize { $e.ascend_until_branch() }
        fn to_next_step_observed<Obs: PathObserver>(&mut $s, obs: &mut Obs) -> bool { $e.to_next_step_observed(obs) }
    };
    (ZipperInfallibleSubtries $s: ident => $e:expr) => {
        fn make_map(&$s) -> crate::PathMap<V, A> { $e.make_map() }
        fn get_trie_ref(&$s) -> TrieRef<'_, V, A> { $e.get_trie_ref() }
        fn get_focus(&$s) -> OpaqueAbstractNodeRef<'_, V, A> { $e.get_focus() }
        fn get_focus_at<K: AsRef<[u8]>>(&$s, k: K) -> OpaqueAbstractNodeRef<'_, V, A> { $e.get_focus_at(k) }
        fn try_borrow_focus(&$s) -> Option<OpaqueTrieNodeRef<'_, V, A>> { $e.try_borrow_focus() }
    };
    (ZipperReadOnlyValues $s: ident => $e:expr) => {
        fn get_val(&$s) -> Option<&'a V> { $e.get_val() }
        fn get_val_at<K: AsRef<[u8]>>(&$s, path: K) -> Option<&'a V> { $e.get_val_at(path) }
    };
    (ZipperReadOnlyConditionalValues $s: ident => $e:expr) => {
        fn witness<'w>(&$s) -> Self::WitnessT { $e.witness() }
        fn get_val_with_witness<'w>(&$s, witness: &'w Self::WitnessT) -> Option<&'w V> where 'a: 'w { $e.get_val_with_witness(witness) }
    };
    (ZipperReadOnlyIteration $s: ident => $e:expr) => {
        fn to_next_get_val_observed<Obs: PathObserver>(&mut $s, obs: &mut Obs) -> Option<&'a V> { $e.to_next_get_val_observed(obs) }
    };
    (ZipperReadOnlyConditionalIteration $s: ident => $e:expr) => {
        fn to_next_get_val_with_witness_observed<'w, Obs: PathObserver>(&mut $s, witness: &'w Self::WitnessT, obs: &mut Obs) -> Option<&'w V> where 'a: 'w { $e.to_next_get_val_with_witness_observed(witness, obs) }
    };
    (ZipperReadOnlySubtries $s: ident => $e:expr) => {
        type TrieRefT = <Z as ZipperReadOnlySubtries<'a, V, A>>::TrieRefT;
        fn trie_ref_at_path<K: AsRef<[u8]>>(&$s, path: K) -> Self::TrieRefT { $e.trie_ref_at_path(path) }
    };
    (ZipperConcrete $s: ident => $e:expr) => {
        #[inline] fn shared_node_id(&$s) -> Option<u64> { $e.shared_node_id() }
        #[inline] fn is_shared(&$s) -> bool { $e.is_shared() }
    };
    (ZipperPathBuffer $s: ident => $e:expr) => {
        unsafe fn origin_path_assert_len(&$s, len: usize) -> &[u8] { unsafe{ $e.origin_path_assert_len(len) } }
        fn prepare_buffers(&mut $s) { $e.prepare_buffers() }
        fn reserve_buffers(&mut $s, path_len: usize, stack_depth: usize) { $e.reserve_buffers(path_len, stack_depth) }
    };
    (ZipperReadOnlyPriv $s: ident => $e:expr) => {
        fn borrow_raw_parts<'z>(&'z $s) -> (TaggedNodeRef<'z, V, A>, &'z [u8], Option<&'z V>) { $e.borrow_raw_parts() }
        fn take_core(&mut $s) -> Option<ReadZipperCore<'a, 'static, V, A>> { $e.take_core() }
    };
}


impl <Z : Zipper> Zipper for Box<Z> { zipper_impl_lens!(Zipper self => (**self)); }
impl <Z : ZipperAbsolutePath> ZipperAbsolutePath for Box<Z> { zipper_impl_lens!(ZipperAbsolutePath self => (**self)); }
impl <Z : ZipperMoving> ZipperMoving for Box<Z> { zipper_impl_lens!(ZipperMoving self => (**self)); }
impl <Z : ZipperPath> ZipperPath for Box<Z> { zipper_impl_lens!(ZipperPath self => (**self)); }
impl <Z : ZipperIteration> ZipperIteration for Box<Z> { zipper_impl_lens!(ZipperIteration self => (**self)); }
impl <V, Z : ZipperValues<V>> ZipperValues<V> for Box<Z> { zipper_impl_lens!(ZipperValues self => (**self)); }
impl <V, Z : ZipperForking<V>> ZipperForking<V> for Box<Z> { type ReadZipperT<'a> = Z::ReadZipperT<'a> where Self: 'a; zipper_impl_lens!(ZipperForking self => (**self)); }
impl <V: Clone + Send + Sync, A: Allocator, Z : ZipperSubtries<V, A>> ZipperSubtries<V, A> for Box<Z> { zipper_impl_lens!(ZipperSubtries self => (**self)); }
impl <V: Clone + Send + Sync, A: Allocator, Z : ZipperInfallibleSubtries<V, A>> ZipperInfallibleSubtries<V, A> for Box<Z> { zipper_impl_lens!(ZipperInfallibleSubtries self => (**self)); }
impl<'a, V: Clone + Send + Sync, Z> ZipperReadOnlyValues<'a, V> for Box<Z> where Z: ZipperReadOnlyValues<'a, V>, Self: ZipperValues<V> { zipper_impl_lens!(ZipperReadOnlyValues self => (**self)); }
impl<'a, V: Clone + Send + Sync, Z> ZipperReadOnlyConditionalValues<'a, V> for Box<Z> where Z: ZipperReadOnlyConditionalValues<'a, V>, Self: ZipperValues<V> { type WitnessT = Z::WitnessT; zipper_impl_lens!(ZipperReadOnlyConditionalValues self => (**self)); }
impl<'a, V, Z> ZipperReadOnlyIteration<'a, V> for Box<Z> where Z: ZipperReadOnlyIteration<'a, V>, Self: ZipperReadOnlyValues<'a, V> + ZipperIteration { zipper_impl_lens!(ZipperReadOnlyIteration self => (**self)); }
impl<'a, V, Z> ZipperReadOnlyConditionalIteration<'a, V> for Box<Z> where Z: ZipperReadOnlyConditionalIteration<'a, V>, Self: ZipperReadOnlyConditionalValues<'a, V, WitnessT = Z::WitnessT> + ZipperIteration { zipper_impl_lens!(ZipperReadOnlyConditionalIteration self => (**self)); }
impl<'a, V: Clone + Send + Sync + 'a, Z, A: Allocator + 'a> ZipperReadOnlySubtries<'a, V, A> for Box<Z> where Z: ZipperReadOnlySubtries<'a, V, A>, Self: ZipperReadOnlyPriv<'a, V, A> + ZipperSubtries<V, A> { zipper_impl_lens!(ZipperReadOnlySubtries self => (**self)); }
impl<Z> ZipperConcrete for Box<Z> where Z: ZipperConcrete { zipper_impl_lens!(ZipperConcrete self => (**self)); }
impl<Z> ZipperPathBuffer for Box<Z> where Z: ZipperPathBuffer { zipper_impl_lens!(ZipperPathBuffer self => (**self)); }
impl<'a, V: Clone + Send + Sync, Z, A: Allocator> ZipperReadOnlyPriv<'a, V, A> for Box<Z> where Z: ZipperReadOnlyPriv<'a, V, A> { zipper_impl_lens!(ZipperReadOnlyPriv self => (**self)); }

impl <Z : Zipper> Zipper for &mut Z { zipper_impl_lens!(Zipper self => (**self)); }
impl <Z : ZipperAbsolutePath> ZipperAbsolutePath for &mut Z { zipper_impl_lens!(ZipperAbsolutePath self => (**self)); }
impl <Z : ZipperMoving> ZipperMoving for &mut Z { zipper_impl_lens!(ZipperMoving self => (**self)); }
impl <Z : ZipperPath> ZipperPath for &mut Z { zipper_impl_lens!(ZipperPath self => (**self)); }
impl <Z : ZipperIteration> ZipperIteration for &mut Z { zipper_impl_lens!(ZipperIteration self => (**self)); }
impl <V, Z : ZipperValues<V>> ZipperValues<V> for &mut Z { zipper_impl_lens!(ZipperValues self => (**self)); }
impl <V, Z : ZipperForking<V>> ZipperForking<V> for &mut Z { type ReadZipperT<'a> = Z::ReadZipperT<'a> where Self: 'a; zipper_impl_lens!(ZipperForking self => (**self)); }
impl <V: Clone + Send + Sync, A: Allocator, Z : ZipperSubtries<V, A>> ZipperSubtries<V, A> for &mut Z { zipper_impl_lens!(ZipperSubtries self => (**self)); }
impl <V: Clone + Send + Sync, A: Allocator, Z : ZipperInfallibleSubtries<V, A>> ZipperInfallibleSubtries<V, A> for &mut Z { zipper_impl_lens!(ZipperInfallibleSubtries self => (**self)); }
impl<'a, V: Clone + Send + Sync, Z> ZipperReadOnlyValues<'a, V> for &mut Z where Z: ZipperReadOnlyValues<'a, V>, Self: ZipperValues<V> { zipper_impl_lens!(ZipperReadOnlyValues self => (**self)); }
impl<'a, V: Clone + Send + Sync, Z> ZipperReadOnlyConditionalValues<'a, V> for &mut Z where Z: ZipperReadOnlyConditionalValues<'a, V>, Self: ZipperValues<V> { type WitnessT = Z::WitnessT; zipper_impl_lens!(ZipperReadOnlyConditionalValues self => (**self)); }
impl<'a, V, Z> ZipperReadOnlyIteration<'a, V> for &mut Z where Z: ZipperReadOnlyIteration<'a, V>, Self: ZipperReadOnlyValues<'a, V> + ZipperIteration { zipper_impl_lens!(ZipperReadOnlyIteration self => (**self)); }
impl<'a, V, Z> ZipperReadOnlyConditionalIteration<'a, V> for &mut Z where Z: ZipperReadOnlyConditionalIteration<'a, V>, Self: ZipperReadOnlyConditionalValues<'a, V, WitnessT = Z::WitnessT> + ZipperIteration { zipper_impl_lens!(ZipperReadOnlyConditionalIteration self => (**self)); }
impl<'a, V: Clone + Send + Sync + 'a, Z, A: Allocator + 'a> ZipperReadOnlySubtries<'a, V, A> for &mut Z where Z: ZipperReadOnlySubtries<'a, V, A>, Self: ZipperReadOnlyPriv<'a, V, A> + ZipperSubtries<V, A> { zipper_impl_lens!(ZipperReadOnlySubtries self => (**self)); }
impl<Z> ZipperConcrete for &mut Z where Z: ZipperConcrete { zipper_impl_lens!(ZipperConcrete self => (**self)); }
impl<Z> ZipperPathBuffer for &mut Z where Z: ZipperPathBuffer { zipper_impl_lens!(ZipperPathBuffer self => (**self)); }
impl<'a, V: Clone + Send + Sync, Z, A: Allocator> ZipperReadOnlyPriv<'a, V, A> for &mut Z where Z: ZipperReadOnlyPriv<'a, V, A> { zipper_impl_lens!(ZipperReadOnlyPriv self => (**self)); }

/// Internal macro to implement Debug on a number of internal zipper types
macro_rules! impl_zipper_debug {
    (impl $($impl_tail:tt)*) => {
        impl $($impl_tail)* {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                let origin_path = crate::utils::debug::render_debug_path(
                    self.origin_path(),
                    crate::utils::debug::PathRenderMode::TryAscii
                ).unwrap();
                let prefix_len = self.root_prefix_path().len();
                f.debug_struct(core::any::type_name::<Self>())
                    .field("child_mask", &self.child_mask())
                    .field("prefix_len", &prefix_len)
                    .field("origin_path", &origin_path)
                    .finish()
            }
        }
    };
}
pub(crate) use impl_zipper_debug;

// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---
// ReadZipperTracked
// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---

/// A [Zipper] returned from a [ZipperHead] that is unable to modify the trie
#[derive(Clone)]
pub struct ReadZipperTracked<'a, 'path, V: Clone + Send + Sync, A: Allocator = GlobalAlloc> {
    z: ReadZipperCore<'a, 'path, V, A>,
    #[allow(unused)]
    tracker: Option<ZipperTracker<TrackingRead>>,
}

//The Drop impl ensures the tracker gets dropped at the right time
impl<V: Clone + Send + Sync, A: Allocator> Drop for ReadZipperTracked<'_, '_, V, A> {
    fn drop(&mut self) { }
}

impl<V: Clone + Send + Sync + Unpin, A: Allocator> Zipper for ReadZipperTracked<'_, '_, V, A> { zipper_impl_lens!(Zipper self => self.z); }
impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperValues<V> for ReadZipperTracked<'_, '_, V, A>{ zipper_impl_lens!(ZipperValues self => self.z); }
impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperSubtries<V, A> for ReadZipperTracked<'_, '_, V, A> { zipper_impl_lens!(ZipperSubtries self => self.z); }
impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperInfallibleSubtries<V, A> for ReadZipperTracked<'_, '_, V, A> { zipper_impl_lens!(ZipperInfallibleSubtries self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperMoving for ReadZipperTracked<'trie, '_, V, A> { zipper_impl_lens!(ZipperMoving self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperPath for ReadZipperTracked<'trie, '_, V, A> { zipper_impl_lens!(ZipperPath self => self.z); }
impl<'a, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> ZipperReadOnlyConditionalValues<'a, V> for ReadZipperTracked<'a, '_, V, A> { type WitnessT = ReadZipperWitness<V, A>; zipper_impl_lens!(ZipperReadOnlyConditionalValues self => self.z); }
impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperConcrete for ReadZipperTracked<'_, '_, V, A> { zipper_impl_lens!(ZipperConcrete self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperPathBuffer for ReadZipperTracked<'trie, '_, V, A> { zipper_impl_lens!(ZipperPathBuffer self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperIteration for ReadZipperTracked<'trie, '_, V, A> { zipper_impl_lens!(ZipperIteration self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperReadOnlyConditionalIteration<'trie, V> for ReadZipperTracked<'trie, '_, V, A> { }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperAbsolutePath for ReadZipperTracked<'trie, '_, V, A> { zipper_impl_lens!(ZipperAbsolutePath self => self.z); }


impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperForking<V> for ReadZipperTracked<'_, '_, V, A>{
    type ReadZipperT<'a> = ReadZipperUntracked<'a, 'a, V, A> where Self: 'a;
    fn fork_read_zipper<'a>(&'a self) -> Self::ReadZipperT<'a> {
        let forked_zipper = self.z.fork_read_zipper();
        Self::ReadZipperT::new_forked_with_inner_zipper(forked_zipper)
    }
}

impl<'a, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> ZipperReadOnlySubtries<'a, V, A> for ReadZipperTracked<'a, '_, V, A> {
    type TrieRefT = TrieRefOwned<V, A>;
    fn trie_ref_at_path<K: AsRef<[u8]>>(&self, path: K) -> TrieRefOwned<V, A> {
        let path = path.as_ref();
        TrieRefOwned::new_with_key_and_path_in(self.z.focus_parent(), self.val(), self.z.node_key(), path, self.z.alloc.clone())
    }
}


impl<'a, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> ZipperReadOnlyPriv<'a, V, A> for ReadZipperTracked<'a, '_, V, A> {
    fn borrow_raw_parts<'z>(&'z self) -> (TaggedNodeRef<'z, V, A>, &'z [u8], Option<&'z V>) { self.z.borrow_raw_parts() }
    fn take_core(&mut self) -> Option<ReadZipperCore<'a, 'static, V, A>> {
        let mut temp_core = ReadZipperCore::new_with_node_and_path_internal_in(OwnedOrBorrowed::None, &[], 0, None, self.z.alloc.clone());
        core::mem::swap(&mut temp_core, &mut self.z);
        Some(temp_core.make_static_path())
    }
}

impl<'a, 'path, V: Clone + Send + Sync + Unpin, A: Allocator + 'a> ReadZipperTracked<'a, 'path, V, A> {
    /// See [ReadZipperCore::new_with_node_and_path]
    pub(crate) fn new_with_node_and_path_in(root_node: &'a TrieNodeODRc<V, A>, owned_root: bool, path: &'path [u8], root_prefix_len: usize, root_key_start: usize, root_val: Option<&'a V>, alloc: A, tracker: Option<ZipperTracker<TrackingRead>>) -> Self {
        let core = ReadZipperCore::new_with_node_and_path_in(root_node, owned_root, path, root_prefix_len, root_key_start, root_val, alloc);
        Self { z: core, tracker }
    }
    /// See [ReadZipperCore::new_with_node_and_cloned_path]
    pub(crate) fn new_with_node_and_cloned_path_in(root_node: &'a TrieNodeODRc<V, A>, owned_root: bool, path: &[u8], root_prefix_len: usize, root_key_start: usize, root_val: Option<&'a V>, alloc: A, tracker: Option<ZipperTracker<TrackingRead>>) -> Self {
        let core = ReadZipperCore::new_with_node_and_cloned_path_in(root_node, owned_root, path, root_prefix_len, root_key_start, root_val, alloc);
        Self { z: core, tracker }
    }
}

//GOAT, the standard prototype of IntoIterator isn't compatible with ReadZipperTracked anymore because 
// we would need to require a witness to create the iterator.  We could add a special into_iter method
// but I will wait for somebody to ask for it.
//
// impl<'a, 'path, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> std::iter::IntoIterator for ReadZipperTracked<'a, 'path, V, A> {
//     type Item = (Vec<u8>, &'a V);
//     type IntoIter = ReadZipperIter<'a, 'path, V, A>;

//     fn into_iter(self) -> Self::IntoIter {
//         //Destructure `self` without dropping it
//         let zip = core::mem::ManuallyDrop::new(self);
//         let core_z = unsafe { std::ptr::read(&zip.z) };
//         let tracker = unsafe { std::ptr::read(&zip.tracker) };
//         ReadZipperIter {
//             started: false,
//             zipper: Some(core_z),
//             _tracker: Some(tracker)
//         }
//     }
// }

impl_zipper_debug!(
    impl<'a, 'path, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> core::fmt::Debug for ReadZipperTracked<'a, 'path, V, A>
);

// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---
// ReadZipperUntracked
// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---

/// A [Zipper] that is unable to modify the trie, used when it is possible to statically guarantee
/// non-interference between zippers
#[derive(Clone)]
pub struct ReadZipperUntracked<'a, 'path, V: Clone + Send + Sync, A: Allocator = GlobalAlloc> {
    z: ReadZipperCore<'a, 'path, V, A>,
}

impl<V: Clone + Send + Sync + Unpin, A: Allocator> Zipper for ReadZipperUntracked<'_, '_, V, A> { zipper_impl_lens!(Zipper self => self.z); }
impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperValues<V> for ReadZipperUntracked<'_, '_, V, A> { zipper_impl_lens!(ZipperValues self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperPathBuffer for ReadZipperUntracked<'trie, '_, V, A> { zipper_impl_lens!(ZipperPathBuffer self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperIteration for ReadZipperUntracked<'trie, '_, V, A> { zipper_impl_lens!(ZipperIteration self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperReadOnlyConditionalIteration<'trie, V> for ReadZipperUntracked<'trie, '_, V, A> { }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperAbsolutePath for ReadZipperUntracked<'trie, '_, V, A> { zipper_impl_lens!(ZipperAbsolutePath self => self.z); }
impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperSubtries<V, A> for ReadZipperUntracked<'_, '_, V, A> { zipper_impl_lens!(ZipperSubtries self => self.z); }
impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperInfallibleSubtries<V, A> for ReadZipperUntracked<'_, '_, V, A> { zipper_impl_lens!(ZipperInfallibleSubtries self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperMoving for ReadZipperUntracked<'trie, '_, V, A> { zipper_impl_lens!(ZipperMoving self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperPath for ReadZipperUntracked<'trie, '_, V, A> { zipper_impl_lens!(ZipperPath self => self.z); }
impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperConcrete for ReadZipperUntracked<'_, '_, V, A> { zipper_impl_lens!(ZipperConcrete self => self.z); }

impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperForking<V> for ReadZipperUntracked<'_, '_, V, A> {
    type ReadZipperT<'a> = ReadZipperUntracked<'a, 'a, V, A> where Self: 'a;
    fn fork_read_zipper<'a>(&'a self) -> Self::ReadZipperT<'a> {
        let forked_zipper = self.z.fork_read_zipper();
        Self::ReadZipperT::new_forked_with_inner_zipper(forked_zipper)
    }
}

impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperReadOnlyValues<'trie, V> for ReadZipperUntracked<'trie, '_, V, A> {
    fn get_val(&self) -> Option<&'trie V> { unsafe{ self.z.get_val() } }
    fn get_val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&'trie V> { unsafe{ self.z.get_val_at(path) } }
}

impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperReadOnlyConditionalValues<'trie, V> for ReadZipperUntracked<'trie, '_, V, A> {
    type WitnessT = ();
    fn witness<'w>(&self) -> Self::WitnessT { () }
    fn get_val_with_witness<'w>(&self, _witness: &'w Self::WitnessT) -> Option<&'w V> where 'trie: 'w { self.get_val() }
}

impl<'a, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> ZipperReadOnlySubtries<'a, V, A> for ReadZipperUntracked<'a, '_, V, A> {
    type TrieRefT = TrieRefBorrowed<'a, V, A>;
    fn trie_ref_at_path<K: AsRef<[u8]>>(&self, path: K) -> TrieRefBorrowed<'a, V, A> {
        let path = path.as_ref();
        TrieRefBorrowed::new_with_key_and_path_in(self.z.focus_parent_borrowed(), || self.get_val(), self.z.node_key(), path, self.z.alloc.clone())
    }
}

impl<'a, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> ZipperReadOnlyPriv<'a, V, A> for ReadZipperUntracked<'a, '_, V, A>{
    fn borrow_raw_parts<'z>(&'z self) -> (TaggedNodeRef<'z, V, A>, &'z [u8], Option<&'z V>) { self.z.borrow_raw_parts() }
    fn take_core(&mut self) -> Option<ReadZipperCore<'a, 'static, V, A>> {
        let mut temp_core = ReadZipperCore::new_with_node_and_path_internal_in(OwnedOrBorrowed::None, &[], 0, None, self.z.alloc.clone());
        core::mem::swap(&mut temp_core, &mut self.z);
        Some(temp_core.make_static_path())
    }
}


impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperReadOnlyIteration<'trie, V> for ReadZipperUntracked<'trie, '_, V, A> {
    fn to_next_get_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> Option<&'trie V> { unsafe{ self.z.to_next_get_val_observed(obs) } }
}

impl<'a, 'path, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> ReadZipperUntracked<'a, 'path, V, A> {
    /// See [ReadZipperCore::new_with_node_and_path]
    pub(crate) fn new_with_node_and_path_in(root_node: &'a TrieNodeODRc<V, A>, path: &'path [u8], root_prefix_len: usize, root_key_start: usize, root_val: Option<&'a V>, alloc: A) -> Self {
        let core = ReadZipperCore::new_with_node_and_path_in(root_node, false, path, root_prefix_len, root_key_start, root_val, alloc);
        Self { z: core }
    }
    /// See [ReadZipperCore::new_with_node_and_path_internal]
    pub(crate) fn new_with_node_and_path_internal_in(root_node: &'a TrieNodeODRc<V, A>, path: &'path [u8], root_key_start: usize, root_val: Option<&'a V>, alloc: A) -> Self {
        let core = ReadZipperCore::new_with_node_and_path_internal_in(OwnedOrBorrowed::Borrowed(root_node), path, root_key_start, root_val, alloc);
        Self { z: core }
    }
    /// See [ReadZipperCore::new_with_node_and_cloned_path]
    pub(crate) fn new_with_node_and_cloned_path_in(root_node: &'a TrieNodeODRc<V, A>, path: &[u8], root_prefix_len: usize, root_key_start: usize, root_val: Option<&'a V>, alloc: A) -> Self {
        let core = ReadZipperCore::new_with_node_and_cloned_path_in(root_node, false, path, root_prefix_len, root_key_start, root_val, alloc);
        Self { z: core }
    }
    /// Makes a new `ReadZipperUntracked` for use in the implementation of [Zipper::fork_read_zipper].
    /// Forked zippers never need to be tracked because they are always fully covered by their parent's permissions
    pub(crate) fn new_forked_with_inner_zipper(core: ReadZipperCore<'a, 'path, V, A>) -> Self {
        ReadZipperUntracked{ z: core }
    }
}

impl<'a, 'path, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> ReadZipperUntracked<'a, 'path, V, A> {
    /// Consumes the zipper and returns the `Vec` storing its path
    ///
    /// The returned `Vec` will contain bytes equivalent to those provided by [origin_path](ZipperAbsolutePath::origin_path),
    /// unless the internal path has not yet been initialized, in which case it will return `vec![]`.
    pub fn into_path(self) -> Vec<u8> {
        self.z.into_path()
    }

    /// Consumes the zipper and returns an iterator over all terminating paths reachable from the current focus,
    /// including paths that do not hold values
    pub fn into_path_iter(self) -> ReadZipperPathIter<'a, 'path, V, A> {
        ReadZipperPathIter { zipper: Some(self.z) }
    }
}

impl<'a, 'path, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> std::iter::IntoIterator for ReadZipperUntracked<'a, 'path, V, A> {
    type Item = (Vec<u8>, &'a V);
    type IntoIter = ReadZipperIter<'a, 'path, V, A>;

    fn into_iter(self) -> Self::IntoIter {
        ReadZipperIter {
            started: false,
            zipper: Some(self.z),
        }
    }
}
crate::impl_name_only_debug!(
    impl<V: Clone + Send + Sync + Unpin, A: Allocator> core::fmt::Debug for ReadZipperIter<'_, '_, V, A>
);
crate::impl_name_only_debug!(
    impl<V: Clone + Send + Sync + Unpin, A: Allocator> core::fmt::Debug for ReadZipperPathIter<'_, '_, V, A>
);

impl_zipper_debug!(
    impl<'a, 'path, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> core::fmt::Debug for ReadZipperUntracked<'a, 'path, V, A>
);

// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---
// ReadZipperOwned
// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---

/// A [Zipper] that holds ownership of the root node, so there is no need for a lifetime parameter
//
//GOAT ReadZipperOwned doesn't need its internal map anymore.
// Then, ReadZipperTracked is then just a ReadZipperOwned plus a tracker
//**UPDATE** TOo early to make this change; because the root value still lives outside the ReadZipper.  We could move to an owned root value, like we did for TrieRefOwned, but I would rather just push ahead with moving root values inside nodes.  For now I am just trying to get to the right external API.
pub struct ReadZipperOwned<V: Clone + Send + Sync + 'static, A: Allocator + 'static = GlobalAlloc> {
    map: MaybeDangling<Box<PathMap<V, A>>>,
    // NOTE About this Box around the WriteZipperCore... The reason this is needed is for the
    // [WriteZipperOwned::into_map] method.  This box effectively provides a fence, ensuring that the
    // `&mut` references to the `map` and the `prefix_path` are totally gone before we access `map`.
    // But I would like to find a zero-cost way to accomplish the same thing without the indirection.
    //
    // UPDATE: I could give the ReadZipperCore the same ptr treatment that I did to WriteZipper with the
    // WZNodePtr, although it's likely easier for the ReadZipperCore because we don't have to worry about
    // mutability and the constraints of the MutCursorRootedVec
    z: Box<ReadZipperCore<'static, 'static, V, A>>,
}

impl<V: 'static + Clone + Send + Sync + Unpin, A: Allocator> Clone for ReadZipperOwned<V, A> {
    fn clone(&self) -> Self {
        let new_map = (**self.map).clone();
        Self::new_with_map(new_map, self.root_prefix_path())
    }
}

impl<V: 'static + Clone + Send + Sync + Unpin, A: Allocator> ReadZipperOwned<V, A> {
    /// See [ReadZipperCore::new_with_node_and_cloned_path]
    pub(crate) fn new_with_map<K: AsRef<[u8]>>(map: PathMap<V, A>, path: K) -> Self {
        map.ensure_root();
        let alloc = map.alloc.clone();
        let path = path.as_ref();
        let map = MaybeDangling::new(Box::new(map));
        let root_ref = unsafe{ &*(*map).root.get() }.as_ref().unwrap();
        let root_val = Option::as_ref( unsafe{ &*(*map).root_val.get() } );
        let core = ReadZipperCore::new_with_node_and_cloned_path_in(root_ref, true, path, path.len(), 0, root_val, alloc);
        Self { map, z: Box::new(core) }
    }
    /// Consumes the zipper and returns a map contained within the zipper
    pub fn into_map(self) -> PathMap<V, A> {
        drop(self.z);
        let map = MaybeDangling::into_inner(self.map);
        *map
    }
}


impl<V: Clone + Send + Sync + Unpin, A: Allocator> Zipper for ReadZipperOwned<V, A> { zipper_impl_lens!(Zipper self => self.z); }
impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperSubtries<V, A> for ReadZipperOwned<V, A> { zipper_impl_lens!(ZipperSubtries self => self.z); }
impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperInfallibleSubtries<V, A> for ReadZipperOwned<V, A> { zipper_impl_lens!(ZipperInfallibleSubtries self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperMoving for ReadZipperOwned<V, A> { zipper_impl_lens!(ZipperMoving self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperPath for ReadZipperOwned<V, A> { zipper_impl_lens!(ZipperPath self => self.z); }
impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperConcrete for ReadZipperOwned<V, A> { zipper_impl_lens!(ZipperConcrete self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperPathBuffer for ReadZipperOwned<V, A> { zipper_impl_lens!(ZipperPathBuffer self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperIteration for ReadZipperOwned<V, A> { zipper_impl_lens!(ZipperIteration self => self.z); }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperReadOnlyConditionalIteration<'trie, V> for ReadZipperOwned<V, A> { }
impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperAbsolutePath for ReadZipperOwned<V, A> { zipper_impl_lens!(ZipperAbsolutePath self => self.z); }


impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperValues<V> for ReadZipperOwned<V, A> {
    fn val(&self) -> Option<&V> { unsafe{ self.z.get_val() } }
    fn val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&V> { unsafe{ self.z.get_val_at(path) } }
}

impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperForking<V> for ReadZipperOwned<V, A> {
    type ReadZipperT<'a> = ReadZipperUntracked<'a, 'a, V, A> where Self: 'a;
    fn fork_read_zipper<'a>(&'a self) -> Self::ReadZipperT<'a> {
        let forked_zipper = self.z.fork_read_zipper();
        Self::ReadZipperT::new_forked_with_inner_zipper(forked_zipper)
    }
}

impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperReadOnlyConditionalValues<'trie, V> for ReadZipperOwned<V, A> {
    type WitnessT = ReadZipperWitness<V, A>;
    fn witness<'w>(&self) -> ReadZipperWitness<V, A> { self.z.witness() }
    fn get_val_with_witness<'w>(&self, witness: &'w ReadZipperWitness<V, A>) -> Option<&'w V> where 'trie: 'w { self.z.get_val_with_witness(witness) }
}

impl<'a, V: Clone + Send + Sync + Unpin, A: Allocator> ZipperReadOnlySubtries<'a, V, A> for ReadZipperOwned<V, A> where Self: 'a {
    type TrieRefT = TrieRefOwned<V, A>;
    fn trie_ref_at_path<K: AsRef<[u8]>>(&self, path: K) -> TrieRefOwned<V, A> {
        let path = path.as_ref();
        TrieRefOwned::new_with_key_and_path_in(self.z.focus_parent(), self.val(), self.z.node_key(), path, self.z.alloc.clone())
    }
}


impl<'a, V: Clone + Send + Sync + Unpin, A: Allocator> ZipperReadOnlyPriv<'a, V, A> for ReadZipperOwned<V, A> where Self: 'a {
    fn borrow_raw_parts<'z>(&'z self) -> (TaggedNodeRef<'z, V, A>, &'z [u8], Option<&'z V>) { self.z.borrow_raw_parts() }
    fn take_core(&mut self) -> Option<ReadZipperCore<'a, 'static, V, A>> {
        let mut temp_core = ReadZipperCore::new_with_node_and_path_internal_in(OwnedOrBorrowed::None, &[], 0, None, self.z.alloc.clone());
        core::mem::swap(&mut temp_core, &mut self.z);
        Some(temp_core.make_static_path())
    }
}


impl_zipper_debug!(
    impl<V: Clone + Send + Sync + Unpin, A: Allocator> core::fmt::Debug for ReadZipperOwned<V, A>
);

// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---
// ReadZipperCore (the actual implementation)
// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---

/// Size of node stack to preallocate in the zipper
pub(crate) const EXPECTED_DEPTH: usize = 16;

/// Size in bytes to preallocate path storage in the zipper
pub(crate) const EXPECTED_PATH_LEN: usize = 64;

pub(crate) mod read_zipper_core {
    use crate::PathMap;
    use crate::zipper::*;

    /// A [Zipper] that is unable to modify the trie
    ///
    /// (Internal type, but in private module so it can be part of sealed interface)
    pub struct ReadZipperCore<'a, 'path, V: Clone + Send + Sync, A: Allocator> {
        /// A reference to the entire origin path, of which `root_key` is the final subset
        origin_path: SliceOrLen<'path>,
        /// The byte offset in `origin_path` for the start of the root node's key.
        /// `root_key = origin_path[root_key_start..]`
        root_key_start: usize,
        /// The byte offset in `origin_path` for the start of the key in `root_node` that produces the
        /// zipper's root.  This is needed to access to the root value if we have a ReadZipper that was
        /// descended from a [ZipperHead], and thus the `root_node` field is `Owned`
        /// In the cases where this field is not used, it will be set to [usize::MAX]
        root_parent_key_start: usize,
        /// A special-case to access a value at the root node, because that value would be otherwise inaccessible
        /// NOTE: `root_val` will be `None`, except in situations where `ReadZipper` at the root of a map or `ZipperHead`
        root_val: Option<&'a V>,
        /// The [TrieNodeODRc] that contains the root node from which the zipper is descended. If the zipper
        /// is descended from a `ZipperHead`, this field will be `Owned`, otherwise it will be `Borrowed`
        root_node: OwnedOrBorrowed<'a, TrieNodeODRc<V, A>>,
        /// A reference to the focus node
        focus_node: MiriWrapper<TaggedNodeRef<'a, V, A>>,
        /// An iter token corresponding to the location of the `node_key` within the `focus_node`, or NODE_ITER_INVALID
        /// if iteration is not in-process
        focus_iter_token: IterToken,
        /// Stores the entire path from the root node, including the bytes from `root_key`
        prefix_buf: Vec<u8>,
        /// Stores a stack of parent node references.  Does not include the focus_node
        /// The tuple contains: `(node_ref, iter_token, key_offset_in_prefix_buf)`
        ancestors: Vec<(TaggedNodeRef<'a, V, A>, IterToken, usize)>,
        pub(crate) alloc: A,
    }

    //GOAT-TODO, we should unify this `OwnedOrBorrowed` type with [`AbstractNodeRef`], and it should be able to
    // be packed into a single 64-bit word, and do the right thing when it is dropped.
    #[derive(Clone, Debug)]
    pub enum OwnedOrBorrowed<'a, T> {
        Owned(T),
        Borrowed(&'a T),
        None,
    }

    impl<'a, T> From<Option<&'a T>> for OwnedOrBorrowed<'a, T> {
        fn from(opt: Option<&'a T>) -> Self {
            match opt {
                Some(t) => Self::Borrowed(t),
                None => Self::None
            }
        }
    }

    impl<'a, T> OwnedOrBorrowed<'a, T> {
        /// Returns a reference to the content, regardless of whether it is owned or borrowed
        #[inline]
        pub fn as_ref(&self) -> &T {
            match self {
                Self::Owned(t) => &t,
                Self::Borrowed(t) => t,
                Self::None => panic!(),
            }
        }
        //GOAT, may be unneeded
        // /// Returns a reference to the
        // #[inline]
        // pub fn as_option(&self) -> Option<&T> {
        //     match self {
        //         Self::Owned(t) => Some(&t),
        //         Self::Borrowed(t) => Some(t),
        //         Self::None => None,
        //     }
        // }
        /// Returns a reference to the content in the reference lifetime, if it's borrowed.  Panics if the content is owned
        pub fn as_borrowed_ref(&self) -> &'a T {
            match self {
                Self::Borrowed(t) => t,
                Self::Owned(_) => panic!(),
                Self::None => panic!(),
            }
        }
        /// Returns a reference to the owned content, or `None` if the content is borrowed
        pub fn get_owned_ref(&self) -> Option<&T> {
            match self {
                Self::Owned(t) => Some(&t),
                Self::Borrowed(_) => None,
                Self::None => None,
            }
        }
        /// Returns `true` if the content is owned, or `false` otherwise
        pub fn is_owned(&self) -> bool {
            match self {
                Self::Owned(_) => true,
                Self::Borrowed(_) => false,
                Self::None => false,
            }
        }
        //GOAT, maybe unneeded
        // /// Returns `true` if the content is borrowed, or `false` otherwise
        // pub fn is_borrowed(&self) -> bool {
        //     match self {
        //         Self::Borrowed(_) => true,
        //         Self::Owned(_) => false,
        //         Self::None => false,
        //     }
        // }
    }

    #[cfg(miri)]
    type MiriWrapper<T> = Box<T>;

    #[cfg(not(miri))]
    use miri_wrapper::MiriWrapper;
    mod miri_wrapper {
        use std::ops::{Deref, DerefMut};

        /// A type that appears to be a Box but does nothing, so I can replace it with a box under miri
        ///
        /// The issue is how miri scopes its pointer tags, which make self-referential types fail
        /// when they are dropped, because the reference and the referant get dropped within the same
        /// scope.
        #[derive(Clone, Debug)]
        pub struct MiriWrapper<T>(T);

        impl<T> Deref for MiriWrapper<T> {
            type Target = T;
            #[inline]
            fn deref(&self) -> &T {
                &self.0
            }
        }
        impl<T> DerefMut for MiriWrapper<T> {
            #[inline]
            fn deref_mut(&mut self) -> &mut T {
                &mut self.0
            }
        }
        impl<T> MiriWrapper<T> {
            pub fn new(t: T) -> Self {
                Self(t)
            }
        }
    }

    impl<V: Clone + Send + Sync, A: Allocator> Clone for ReadZipperCore<'_, '_, V, A> where V: Clone {
        fn clone(&self) -> Self {
            Self {
                origin_path: self.origin_path.clone(),
                root_key_start: self.root_key_start,
                root_parent_key_start: self.root_parent_key_start,
                root_val: self.root_val,
                root_node: self.root_node.clone(),
                focus_node: self.focus_node.clone(),
                focus_iter_token: NODE_ITER_INVALID,
                prefix_buf: self.prefix_buf.clone(),
                ancestors: self.ancestors.clone(),
                alloc: self.alloc.clone(),
            }
        }
    }

    impl<V: Clone + Send + Sync + Unpin, A: Allocator> Zipper for ReadZipperCore<'_, '_, V, A> {
        #[inline]
        fn path_exists(&self) -> bool {
            let key = self.node_key();
            if key.len() > 0 {
                self.focus_node.node_contains_partial_key(key)
            } else {
                true
            }
        }
        fn is_val(&self) -> bool {
            self.is_val_internal()
        }
        fn child_count(&self) -> usize {
            debug_assert!(self.is_regularized());
            self.focus_node.count_branches(self.node_key())
        }
        fn child_mask(&self) -> ByteMask {
            debug_assert!(self.is_regularized());
            self.focus_node.node_branches_mask(self.node_key())
        }
    }

    impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperValues<V> for ReadZipperCore<'_, '_, V, A> {
        fn val(&self) -> Option<&V> { unsafe{ self.get_val() } }
        fn val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&V> { unsafe{ self.get_val_at(path) } }
    }

    impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperForking<V> for ReadZipperCore<'_, '_, V, A> {
        type ReadZipperT<'a> = ReadZipperCore<'a, 'a, V, A> where Self: 'a;
        fn fork_read_zipper<'a>(&'a self) -> Self::ReadZipperT<'a> {
            timed_span!(ForkReadZipper, COUNTERS);
            let new_root_val = self.val();
            let new_root_path = self.origin_path();
            let new_root_key_start = new_root_path.len() - self.node_key().len();
            Self::ReadZipperT::new_with_node_and_path_internal_in(OwnedOrBorrowed::Borrowed(self.focus_parent()), new_root_path, new_root_key_start, new_root_val, self.alloc.clone())
        }
    }

    impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperSubtries<V, A> for ReadZipperCore<'_, '_, V, A> {
        fn native_subtries(&self) -> bool { true }
        fn try_make_map(&self) -> Option<PathMap<V, A>> {
            Some(self.make_map())
        }
        fn trie_ref(&self) -> Option<TrieRef<'_, V, A>> {
            Some(self.get_trie_ref())
        }
        fn alloc(&self) -> A { self.alloc.clone() }
    }

    impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperInfallibleSubtries<V, A> for ReadZipperCore<'_, '_, V, A> {
        fn make_map(&self) -> PathMap<V, A> {
            #[cfg(not(feature = "graft_root_vals"))]
            let root_val = None;
            #[cfg(feature = "graft_root_vals")]
            let root_val = self.val().cloned();

            let root_node = self.get_focus().0.into_option();
            PathMap::new_with_root_in(root_node, root_val, self.alloc.clone())
        }
        fn get_trie_ref(&self) -> TrieRef<'_, V, A> {
            TrieRefBorrowed::new_with_key_and_path_in(self.focus_parent_borrowed(), || self.val(), self.node_key(), b"", self.alloc.clone()).into()
        }
        fn get_focus(&self) -> OpaqueAbstractNodeRef<'_, V, A> {
            self.get_focus_at([])
        }
        #[inline]
        fn get_focus_at<K: AsRef<[u8]>>(&self, path: K) -> OpaqueAbstractNodeRef<'_, V, A> {
            OpaqueAbstractNodeRef(TrieRefBorrowed::new_with_key_and_path_in(
                self.focus_parent(),
                || self.val(),
                self.node_key(),
                path.as_ref(),
                self.alloc.clone(),
            ).into_focus())
        }
        fn try_borrow_focus(&self) -> Option<OpaqueTrieNodeRef<'_, V, A>> {
            let node_key = self.node_key();
            let (focus_node, node_key) = if node_key.len() == 0 {
                let parent_key = self.parent_key();
                if parent_key.len() == 0 {
                    return Some(OpaqueTrieNodeRef(self.root_node.as_ref()))
                }

                let parent_node = match self.ancestors.last() {
                    Some((focus_node, _iter_tok, _prefix_offset)) => {
                        *focus_node
                    },
                    None => {
                        self.root_node.as_ref().as_tagged()
                    }
                };
                (parent_node, parent_key)
            } else {
                (*self.focus_node, node_key)
            };

            match focus_node.node_get_child(node_key) {
                Some((consumed_bytes, child_node)) => {
                    debug_assert_eq!(consumed_bytes, node_key.len());
                    Some(OpaqueTrieNodeRef(child_node))
                },
                None => None
            }
        }
    }


    impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperMoving for ReadZipperCore<'trie, '_, V, A> {
        #[inline]
        fn depth(&self) -> usize {
            self.prefix_buf.len().saturating_sub(self.origin_path.len())
        }

        fn at_root(&self) -> bool {
            self.prefix_buf.len() <= self.origin_path.len()
        }

        #[inline]
        fn focus_byte(&self) -> Option<u8> {
            self.prefix_buf.last().cloned()
        }

        fn reset(&mut self) {
            timed_span!(Reset, COUNTERS);
            self.ancestors.truncate(1);
            match self.ancestors.pop() {
                Some((node, _tok, _prefix_len)) => {
                    *self.focus_node = node;
                },
                None => {}
            }
            self.focus_iter_token = NODE_ITER_INVALID;
            self.prefix_buf.truncate(self.origin_path.len());
        }

        fn val_count(&self) -> usize {
            timed_span!(ValueCount, COUNTERS);
            let root_val = self.is_val() as usize;
            if self.node_key().len() == 0 {
                val_count_below_root(*self.focus_node) + root_val
            } else {
                let focus = self.get_focus();
                if focus.0.is_none() {
                    root_val
                } else {
                    val_count_below_root(focus.0.as_tagged()) + root_val
                }
            }
        }
        fn descend_to<K: AsRef<[u8]>>(&mut self, k: K) {
            timed_span!(DescendTo, COUNTERS);
            let k = k.as_ref();
            if k.len() == 0 {
                return //Zero-length path is a no-op
            }

            self.prepare_buffers();
            debug_assert!(self.is_regularized());

            self.descend_to_internal(k);
        }

        fn descend_to_check<K: AsRef<[u8]>>(&mut self, k: K) -> bool {
            let k = k.as_ref();
            if k.len() == 0 {
                return self.path_exists() //Zero-length path is a no-op
            }

            self.prepare_buffers();
            debug_assert!(self.is_regularized());

            let (borrowed_self, key) = self.descend_to_internal(k);
            if key.len() == 0 {
                debug_assert!(self.path_exists());
                true
            } else {
                borrowed_self.focus_node.node_contains_partial_key(key)
            }
        }

        #[inline]
        fn descend_to_byte(&mut self, k: u8) {
            timed_span!(DescendToByte, COUNTERS);
            self.prepare_buffers();
            debug_assert!(self.is_regularized());

            self.prefix_buf.push(k);
            self.focus_iter_token = NODE_ITER_INVALID;
            if let Some((_consumed_byte_cnt, next_node)) = self.focus_node.node_get_child(self.node_key()) {
                let next_node = next_node.as_tagged();
                self.ancestors.push((*self.focus_node, self.focus_iter_token, self.prefix_buf.len()));
                *self.focus_node = next_node;
            }
        }

        #[inline]
        fn descend_to_existing_byte(&mut self, k: u8) -> bool {
            self.prepare_buffers();
            debug_assert!(self.is_regularized());

            self.prefix_buf.push(k);
            let node_key = self.node_key();
            if let Some((_consumed_byte_cnt, next_node)) = self.focus_node.node_get_child(node_key) {
                self.focus_iter_token = NODE_ITER_INVALID;
                let next_node = next_node.as_tagged();
                self.ancestors.push((*self.focus_node, self.focus_iter_token, self.prefix_buf.len()));
                *self.focus_node = next_node;
                return true;
            }
            if self.focus_node.node_contains_partial_key(node_key) {
                self.focus_iter_token = NODE_ITER_INVALID;
                true
            } else {
                self.prefix_buf.pop();
                false
            }
        }

        fn descend_indexed_byte(&mut self, child_idx: usize) -> Option<u8> {
            timed_span!(DescendIndexedByte, COUNTERS);
            self.prepare_buffers();
            debug_assert!(self.is_regularized());
            match self.focus_node.nth_child_from_key(self.node_key(), child_idx) {
                (Some(prefix), Some(child_node)) => {
                    self.prefix_buf.push(prefix);
                    self.focus_iter_token = NODE_ITER_INVALID;
                    self.ancestors.push((*self.focus_node.clone(), self.focus_iter_token, self.prefix_buf.len()));
                    *self.focus_node = child_node;
                    Some(prefix)
                },
                (Some(prefix), None) => {
                    self.prefix_buf.push(prefix);
                    self.focus_iter_token = NODE_ITER_INVALID;
                    Some(prefix)
                },
                (None, _) => None
            }
        }

        fn descend_first_byte(&mut self) -> Option<u8> {
            timed_span!(DescendFirstByte, COUNTERS);
            self.prepare_buffers();
            debug_assert!(self.is_regularized());
            debug_assert_ne!(self.focus_iter_token, NODE_ITER_FINISHED);

            if self.focus_iter_token == NODE_ITER_INVALID {
                self.focus_iter_token = self.focus_node.iter_token_for_path(self.node_key());
            }
            if node_iter_token_is_nonexistent(self.focus_iter_token) {
                return None
            }

            let (new_tok, key_bytes, child_node, _value) = self.focus_node.next_items(self.focus_iter_token, false);

            if new_tok != NODE_ITER_FINISHED {
                let node_key = self.node_key();
                let byte_idx = node_key.len();
                //`iter_token_for_path` positions a lower-bound cursor, so when the focus is on a
                // non-existent path the item we get back may belong to a sibling.  Descending into
                // it would splice a foreign byte onto the focus, so only descend when the item
                // actually continues the path we're on.
                if byte_idx >= key_bytes.len() || !starts_with(key_bytes, node_key) {
                    debug_assert!(self.is_regularized());
                    return None; //We can't go any deeper down this path
                }
                let descended_byte = key_bytes[byte_idx];
                self.prefix_buf.push(descended_byte);

                if key_bytes.len() == byte_idx+1 {
                    self.focus_iter_token = new_tok;
                    match child_node {
                        None => {},
                        Some(rec) => {
                            self.ancestors.push((*self.focus_node.clone(), new_tok, self.prefix_buf.len()));
                            *self.focus_node = rec.as_tagged();
                            self.focus_iter_token = self.focus_node.new_iter_token();
                        },
                    }
                } else {
                    self.focus_iter_token = self.focus_node
                        .ascend_iter_token(new_tok, key_bytes.len() - (byte_idx + 1));
                }
                debug_assert!(self.is_regularized());
                Some(descended_byte)
            } else {
                debug_assert!(self.is_regularized());
                None
            }
        }

        fn descend_until_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
            timed_span!(DescendUntil, COUNTERS);
            debug_assert!(self.is_regularized());
            let mut moved = false;
            while self.child_count() == 1 {
                moved = true;
                self.descend_first(obs);
                if self.is_val_internal() {
                    break;
                }
            }
            moved
        }

        fn descend_until_max_bytes_observed<Obs: PathObserver>(&mut self, max_bytes: usize, obs: &mut Obs) -> bool {
            if max_bytes == 0 {
                return false;
            }
            debug_assert!(self.is_regularized());
            let mut remaining = max_bytes;
            let mut moved = false;
            while self.child_count() == 1 && remaining > 0 {
                self.prepare_buffers();
                let (prefix_opt, child_node_opt) = self.focus_node.first_child_from_key(self.node_key());
                let Some(prefix) = prefix_opt else { unreachable!() };

                if prefix.len() == 0 {
                    // Move to child node without consuming bytes.
                    if let Some(child_node) = child_node_opt {
                        moved = true;
                        self.ancestors.push((*self.focus_node.clone(), self.focus_iter_token, self.prefix_buf.len()));
                        *self.focus_node = child_node;
                        self.focus_iter_token = NODE_ITER_INVALID;
                        continue;
                    } else {
                        break;
                    }
                }

                let take = remaining.min(prefix.len());
                moved = true;
                self.prefix_buf.extend(&prefix[..take]);
                obs.descend_to(&prefix[..take]);
                remaining -= take;
                self.focus_iter_token = NODE_ITER_INVALID;

                if take < prefix.len() {
                    break;
                }

                if let Some(child_node) = child_node_opt {
                    self.ancestors.push((*self.focus_node.clone(), self.focus_iter_token, self.prefix_buf.len()));
                    *self.focus_node = child_node;
                    self.focus_iter_token = NODE_ITER_INVALID;
                }

                if self.is_val_internal() {
                    break;
                }
            }
            moved
        }

        fn descend_to_existing<K: AsRef<[u8]>>(&mut self, k: K) -> usize {
            timed_span!(DescendToExisting, COUNTERS);
            let mut k = k.as_ref();
            if k.len() == 0 {
                return 0 //Zero-length path is a no-op
            }
            self.prepare_buffers();
            debug_assert!(self.is_regularized());

            let original_path_len = self.prefix_buf.len();
            let mut key_start = self.node_key_start();

            //Early out if we're on a non-existent path
            if key_start < self.prefix_buf.len() && !self.focus_node.node_contains_partial_key(&self.prefix_buf[key_start..]) {
                return 0
            }

            //Descend through all the existing nodes
            //
            //NOTE: One of the advantages of `descend_to_existing` vs ordinary `descend_to` is that it
            // avoids copying the whole path argument into the path buffer unless that's actually needed.
            // So this loop copies the path arg in chunks.  If we didn't care about this, we could just
            // grow the path buffer in one call with `self.descend_to_internal(k)`, like `descend_to` does
            const CHUNK_SIZE: usize = 64;
            debug_assert!(CHUNK_SIZE >= MAX_NODE_KEY_BYTES);
            while k.len() > 0 {
                let (chunk, remaining) = if k.len() > CHUNK_SIZE {
                    (&k[..CHUNK_SIZE], &k[CHUNK_SIZE..])
                } else {
                    (k, &[][..])
                };
                let _ = self.descend_to_internal(chunk);
                let new_key_start = self.node_key_start();
                if new_key_start == key_start {
                    break;
                }
                key_start = new_key_start;
                k = remaining;
            }

            //Now trim the buffer to the length of the last existing path within the node
            let node_key = &self.prefix_buf[key_start..];
            let overlap = if node_key.len() > 0 {
                self.focus_node.node_key_overlap(node_key)
            } else {
                0
            };
            self.prefix_buf.truncate(key_start+overlap);

            debug_assert!(self.is_regularized());
            self.prefix_buf.len() - original_path_len
        }

        //GOAT, WIP.  I think `node_first_val_depth_along_key` needs to change in order to
        // ignore values with a key length smaller than a specified length
        // fn descend_to_val<K: AsRef<[u8]>>(&mut self, k: K) -> usize {
        //     let mut k = k.as_ref();
        //     if k.len() == 0 {
        //         return 0 //Zero-length path is a no-op
        //     }
        //     self.prepare_buffers();
        //     debug_assert!(self.is_regularized());

        //     self.focus_node.node_first_val_depth_along_key();
        // }

        fn to_next_sibling_byte(&mut self) -> Option<u8> {
            timed_span!(ToNextSiblingByte, COUNTERS);
            if self.at_root() {
                return None;
            }
            self.prepare_buffers();
            if self.prefix_buf.len() == 0 {
                return None
            }
            debug_assert!(self.is_regularized());
            self.deregularize();
            if self.focus_iter_token == NODE_ITER_INVALID {
                self.focus_iter_token = self.focus_node.iter_token_for_path(self.node_key());
            }

            let (new_tok, key_bytes, child_node, _value) = self.focus_node.next_items(self.focus_iter_token, true);
            if new_tok == NODE_ITER_FINISHED {
                self.regularize();
                return None;
            }

            let node_key = self.node_key();
            let node_key_len = node_key.len();

            //The root has no siblings.  But we don't want to underflow the logic after this point
            if node_key_len == 0 {
                debug_assert!(self.at_root());
                return None;
            }

            //Make sure the returned node-path is long enough to be a sibling of the focus
            let fixed_len = node_key_len - 1;
            if fixed_len >= key_bytes.len()
                || key_bytes[..fixed_len] != node_key[..fixed_len]
                || key_bytes[fixed_len] <= node_key[fixed_len]
            {
                self.regularize();
                return None;
            }

            //If the returned node path overshot deeper into the trie we need to walk back to this level
            let byte = key_bytes[fixed_len];
            let focus_iter_token = if key_bytes.len() == node_key_len {
                new_tok
            } else {
                self.focus_node.ascend_iter_token(new_tok, key_bytes.len() - node_key_len)
            };
            *self.prefix_buf.last_mut().unwrap() = byte;
            self.focus_iter_token = focus_iter_token;

            //If this operation landed us at the end of the path within the node, then we
            // should re-regularize the zipper before returning
            if key_bytes.len() == node_key_len {
                match child_node {
                    None => {},
                    Some(rec) => {
                        self.ancestors.push((*self.focus_node.clone(), new_tok, self.prefix_buf.len()));
                        *self.focus_node = rec.as_tagged();
                        self.focus_iter_token = NODE_ITER_INVALID
                    },
                }
            }

            debug_assert!(self.is_regularized());
            Some(byte)
        }

        fn to_prev_sibling_byte(&mut self) -> Option<u8> {
            timed_span!(ToPrevSiblingByte, COUNTERS);
            self.to_sibling(false)
        }

        fn ascend(&mut self, steps: usize) -> usize {
            timed_span!(Ascend, COUNTERS);
            debug_assert!(self.is_regularized());
            if self.at_root() {
                return 0;
            }
            let mut remaining = steps;
            while remaining > 0 {
                if self.excess_key_len() == 0 {
                    match self.ancestors.pop() {
                        Some((node, iter_tok, _prefix_offset)) => {
                            *self.focus_node = node;
                            self.focus_iter_token = iter_tok;
                        },
                        None => {
                            debug_assert!(self.is_regularized());
                            return steps - remaining;
                        }
                    };
                }
                let cur_jump = remaining.min(self.excess_key_len());
                if cur_jump > 0 {
                    self.prefix_buf.truncate(self.prefix_buf.len() - cur_jump);
                    self.reascend_iter_token(cur_jump);
                    remaining -= cur_jump;
                }
            }
            debug_assert!(self.is_regularized());
            steps
        }

        fn ascend_byte(&mut self) -> bool {
            timed_span!(AscendByte, COUNTERS);
            debug_assert!(self.is_regularized());
            if self.at_root() {
                return false;
            }
            if self.excess_key_len() == 0 {
                match self.ancestors.pop() {
                    Some((node, iter_tok, _prefix_offset)) => {
                        *self.focus_node = node;
                        self.focus_iter_token = iter_tok;
                    },
                    None => {
                        debug_assert!(self.is_regularized());
                        return false
                    }
                };
            }
            self.prefix_buf.pop();
            self.reascend_iter_token(1);
            debug_assert!(self.is_regularized());
            true
        }

        fn ascend_until(&mut self) -> usize {
            timed_span!(AscendUntil, COUNTERS);
            debug_assert!(self.is_regularized());
            if self.at_root() {
                return 0;
            }
            let mut ascended = 0;
            loop {
                if self.node_key().len() == 0 {
                    self.ascend_across_nodes();
                }
                let ascended_within_node = self.ascend_within_node();
                ascended += ascended_within_node;
                if self.child_count() > 1 || self.is_val() || self.at_root() {
                    return ascended;
                }
            }
        }

        fn ascend_until_branch(&mut self) -> usize {
            timed_span!(AscendUntilBranch, COUNTERS);
            debug_assert!(self.is_regularized());
            if self.at_root() {
                return 0;
            }
            let mut ascended = 0;
            loop {
                if self.node_key().len() == 0 {
                    self.ascend_across_nodes();
                }
                let ascended_within_node = self.ascend_within_node();
                ascended += ascended_within_node;
                if self.child_count() > 1 || self.at_root() {
                    return ascended;
                }
            }
        }
    }

    impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperPath for ReadZipperCore<'trie, '_, V, A> {
        #[inline]
        fn path(&self) -> &[u8] {
            if self.prefix_buf.len() > 0 {
                &self.prefix_buf[self.origin_path.len()..]
            } else {
                &[]
            }
        }
    }

    impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperPathBuffer for ReadZipperCore<'trie, '_, V, A> {
        unsafe fn origin_path_assert_len(&self, len: usize) -> &[u8] {
            if self.prefix_buf.capacity() > 0 {
                assert!(len <= self.prefix_buf.capacity());
                unsafe{ core::slice::from_raw_parts(self.prefix_buf.as_ptr(), len) }
            } else {
                assert!(len <= self.origin_path.len());
                unsafe{ &self.origin_path.as_slice_unchecked() }
            }
        }
        /// Internal method to ensure buffers to facilitate movement of zipper are allocated and initialized
        #[inline(always)]
        fn prepare_buffers(&mut self) {
            if self.prefix_buf.capacity() == 0 {
                self.reserve_buffers(EXPECTED_PATH_LEN, EXPECTED_DEPTH)
            }
        }
        #[cold]
        fn reserve_buffers(&mut self, path_len: usize, stack_depth: usize) {
            let path_len = path_len.max(self.origin_path.len());
            if self.prefix_buf.capacity() < path_len {
                let was_unallocated = self.prefix_buf.capacity() == 0;
                self.prefix_buf.reserve(path_len.saturating_sub(self.prefix_buf.len()));
                if was_unallocated {
                    self.prefix_buf.extend(unsafe{ self.origin_path.as_slice_unchecked() });
                }
            }
            if self.ancestors.capacity() < stack_depth {
                self.ancestors.reserve(stack_depth.saturating_sub(self.ancestors.len()));
            }
        }
    }

    impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperReadOnlyConditionalValues<'trie, V> for ReadZipperCore<'trie, '_, V, A> {
        type WitnessT = ReadZipperWitness<V, A>;
        fn witness<'w>(&self) -> Self::WitnessT {
            if self.root_node.is_owned() {
                ReadZipperWitness(Some(self.root_node.as_ref().clone()))
            } else {
                ReadZipperWitness(None)
            }
        }
        fn get_val_with_witness<'w>(&self, witness: &'w Self::WitnessT) -> Option<&'w V> where 'trie: 'w {
            assert_eq!(witness.0.as_ref(), self.root_node.get_owned_ref());
            let key = self.node_key();
            if key.len() > 0 {
                self.focus_node.node_get_val(key)
            } else {
                if let Some((parent, _iter_tok, _prefix_offset)) = self.ancestors.last() {
                    parent.node_get_val(self.parent_key())
                } else {
                    if self.root_val.is_some() {
                        self.root_val
                    } else {
                        //We know the node in the witness and the node in self.root_node are the same,
                        // but we borrow it from the witness here because that has the lifetime we need
                        witness.0.as_ref().unwrap().as_tagged().node_get_val(self.root_node_key())
                    }
                }
            }
        }
    }

    impl<'a, V: Clone + Send + Sync + Unpin, A: Allocator + 'a> ZipperReadOnlyPriv<'a, V, A> for ReadZipperCore<'a, '_, V, A> {
        fn borrow_raw_parts(&self) -> (TaggedNodeRef<'_, V, A>, &[u8], Option<&V>) {
            let node_key = self.node_key();
            if node_key.len() > 0 {
                (*self.focus_node, node_key, None)
            } else {
                (*self.focus_node, &[], self.val())
            }
        }
        fn take_core(&mut self) -> Option<ReadZipperCore<'a, 'static, V, A>> {
            unreachable!()
        }
    }

    impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperConcrete for ReadZipperCore<'_, '_, V, A> {
        #[inline]
        fn shared_node_id(&self) -> Option<u64> {
            read_zipper_shared_node_id(self)
        }
        #[inline]
        fn is_shared(&self) -> bool {
            let key = self.node_key();
            if key.len() > 0 {
                false
            } else {
                if let Some((parent, _iter_tok, _prefix_offset)) = self.ancestors.last() {
                    let (_key_len, focus_node) = parent.node_get_child(self.parent_key()).unwrap();
                    !focus_node.is_empty() && focus_node.refcount() > 1
                } else {
                    match &self.root_node {
                        OwnedOrBorrowed::Owned(root) => !root.is_empty() && root.refcount() > 1,
                        OwnedOrBorrowed::Borrowed(root) => !root.is_empty() && root.refcount() > 1,
                        OwnedOrBorrowed::None => false,
                    }
                }
            }
        }
    }

    #[inline]
    pub(crate) fn read_zipper_shared_node_id<'a, V: Clone + Send + Sync + 'a, A: Allocator + 'a, Z: Zipper + ZipperReadOnlyPriv<'a, V, A> + ZipperConcrete>(zipper: &Z) -> Option<u64> {
        let (node, key, value) = zipper.borrow_raw_parts();
        if !zipper.is_shared() || !key.is_empty() || value.is_some() {
            // TODO(igorm): Currently values associated with a nodes that can be shared
            // are stored outside of the node. This means one focus address can
            // correspond to two different points which have different values.
            // Therefore, we can't cache nodes that have values themselves.
            // Relevant discussion:
            // https://github.com/Adam-Vandervorst/PathMap/pull/8#discussion_r2005555762
            // https://github.com/Adam-Vandervorst/PathMap/blob/cleanup_to_release/pathmap-book/src/A.0001_map_root_values.md
            // https://discord.com/channels/@me/1215835387432271922/1352463443541754068
            return None
        }
        Some(node.shared_node_id())
    }

    //GOAT.  Need to add `to_first_val` method that moves the zipper to the root, and if the root contains a
    // value, returns it, and otherwise calls to_next_val().
    //
    //Then I need to port all the iter() conveniences over to use that new method

    impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperIteration for ReadZipperCore<'trie, '_, V, A> {
        fn to_next_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
            timed_span!(ToNextVal, COUNTERS);
            unsafe{ self.to_next_get_val_observed(obs) }.is_some()
        }
        fn descend_first_k_path_observed<Obs: PathObserver>(&mut self, k: usize, obs: &mut Obs) -> bool {
            timed_span!(DescendFirstKPath, COUNTERS);
            self.prepare_buffers();
            debug_assert!(self.is_regularized());

            self.focus_iter_token = self.focus_node.iter_token_for_path(self.node_key());

            self.k_path_internal(k, self.prefix_buf.len(), false, obs)
        }
        fn to_next_k_path_observed<Obs: PathObserver>(&mut self, k: usize, obs: &mut Obs) -> bool {
            timed_span!(ToNextKPath, COUNTERS);
            let path_len = self.path_len();
            let base_idx = if path_len < k {
                return k_path_depth_exceeded(self, path_len, obs)
            } else {
                self.prefix_buf.len() - k
            };
            //De-regularize the zipper
            debug_assert!(self.is_regularized());
            self.deregularize();
            self.k_path_internal(k, base_idx, true, obs)
        }
    }

    impl<'trie, V: Clone + Send + Sync + Unpin + 'trie, A: Allocator + 'trie> ZipperAbsolutePath for ReadZipperCore<'trie, '_, V, A> {
        fn origin_path(&self) -> &[u8] {
            if self.prefix_buf.capacity() > 0 {
                &self.prefix_buf
            } else {
                unsafe{ &self.origin_path.as_slice_unchecked() }
            }
        }
        fn root_prefix_path(&self) -> &[u8] {
            if self.prefix_buf.capacity() > 0 {
                &self.prefix_buf[..self.origin_path.len()]
            } else {
                unsafe{ &self.origin_path.as_slice_unchecked() }
            }
        }
    }

    impl<'a, 'path, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> ReadZipperCore<'a, 'path, V, A> {

        /// Creates a new zipper, with a path relative to a node
        ///
        /// `root_key_start` is the offset in `path` that aligns with the `root_node` that is passed in
        /// It is used to pre-initialize an origin_path / root_prefix_path.
        ///
        /// `root_prefix_len` is the offset in `path` from which the zipper's root begins.
        ///
        /// `path.len() >= root_prefix_len >= root_key_start` or this method will panic.
        /// 
        /// ```text
        /// (dots '.' are node separators in this example path)
        ///
        ///                  ancestors[0]  ancestors[1]    focus_node
        ///                       v             v              v
        /// prefix_buf = "this-is.a-path-to-the.current-zipper.focus"
        ///                       ^         ^
        ///                       |   root_prefix_len
        ///                 root_key_start
        /// ```
        pub(crate) fn new_with_node_and_path_in(root_node: &'a TrieNodeODRc<V, A>, owned_root: bool, path: &'path [u8], root_prefix_len: usize, root_key_start: usize, root_val: Option<&'a V>, alloc: A) -> Self {
            let (node, key, val) = node_along_path(root_node, &path[root_key_start..], root_val, false);
            let node = if owned_root {
                OwnedOrBorrowed::Owned(node.clone())
            } else {
                OwnedOrBorrowed::Borrowed(node)
            };
            let new_root_key_start = root_prefix_len - key.len();
            Self::new_with_node_and_path_internal_in(node, path, new_root_key_start, val, alloc)
        }
        /// Creates a new zipper, with a path relative to a node, assuming the path is fully-contained within
        /// the node
        ///
        /// NOTE: This method currently doesn't descend subnodes.  Use [Self::new_with_node_and_path_in] if you can't
        /// guarantee the path is within the supplied node.
        pub(crate) fn new_with_node_and_path_internal_in(root_node: OwnedOrBorrowed<'a, TrieNodeODRc<V, A>>, path: &'path [u8], mut root_key_start: usize, root_val: Option<&'a V>, alloc: A) -> Self {
            let mut focus: TaggedNodeRef<'a, V, A> = match &root_node {
                OwnedOrBorrowed::Owned(root_node) => {
                    // SAFETY: The root_node makes the ReadZipper essentially a self-referential type.  As long
                    // as the ReadZipperCore is alive, this will remain valid, and the "witness" mechanism in
                    // `ZipperReadOnlyConditionalValues` makes sure the references returned from the `get_val`
                    // method remain valid
                    unsafe{ core::mem::transmute(root_node.as_tagged()) }
                },
                OwnedOrBorrowed::Borrowed(root_node) => {
                    root_node.as_tagged()
                },
                OwnedOrBorrowed::None => {
                    TaggedNodeRef::empty_node()
                }
            };

            //Finish regularizing the zipper, if we stopped short when traversing to the focus node
            let mut root_parent_key_start = usize::MAX;
            if path.len() > root_key_start {
                if let Some((consumed_byte_cnt, next_node)) = focus.node_get_child(&path[root_key_start..]) {
                    focus = next_node.as_tagged();
                    root_parent_key_start = root_key_start;
                    root_key_start += consumed_byte_cnt;
                }
            }
            Self {
                origin_path: SliceOrLen::from(path),
                root_key_start,
                root_parent_key_start,
                root_val: root_val.map(|v| v.into()),
                focus_node: MiriWrapper::new(focus),
                root_node,
                focus_iter_token: NODE_ITER_INVALID,
                prefix_buf: vec![],
                ancestors: vec![],
                alloc,
            }
        }
        /// Same as [Self::new_with_node_and_path_in], but inits the zipper stack ahead of time, allowing a zipper
        /// that isn't bound by `'path`
        pub(crate) fn new_with_node_and_cloned_path_in(root_node: &'a TrieNodeODRc<V, A>, owned_root: bool, path: &[u8], root_prefix_len: usize, root_key_start: usize, root_val: Option<&'a V>, alloc: A) -> Self {
            let (node, key, val) = node_along_path(root_node, &path[root_key_start..], root_val, false);
            let node = if owned_root {
                OwnedOrBorrowed::Owned(node.clone())
            } else {
                OwnedOrBorrowed::Borrowed(node)
            };
            let new_root_key_start = root_prefix_len - key.len();
            let mut new_zipper = ReadZipperCore::<'a, '_, V, A>::new_with_node_and_path_internal_in(node, path, new_root_key_start, val, alloc);

            new_zipper.prefix_buf = Vec::with_capacity(EXPECTED_PATH_LEN);
            new_zipper.prefix_buf.extend(path);
            new_zipper.origin_path = SliceOrLen::new_owned(path.len());
            new_zipper.ancestors = Vec::with_capacity(EXPECTED_DEPTH);

            new_zipper.make_static_path()
        }

        /// Makes a version of `self` that has an allocated path buffer and a `'static`` path lifetime
        #[inline]
        pub(crate) fn make_static_path(mut self) -> ReadZipperCore<'a, 'static, V, A> {
            self.prepare_buffers();
            ReadZipperCore {
                origin_path: SliceOrLen::new_owned(self.origin_path.len()),
                root_key_start: self.root_key_start,
                root_parent_key_start: self.root_parent_key_start,
                root_val: self.root_val,
                root_node: self.root_node,
                focus_node: self.focus_node,
                focus_iter_token: NODE_ITER_INVALID,
                prefix_buf: self.prefix_buf,
                ancestors: self.ancestors,
                alloc: self.alloc
            }
        }

        /// Returns the length of the `self.path()`, saving a couple instructions, but is internal because it may panic
        #[inline(always)]
        fn path_len(&self) -> usize {
            self.prefix_buf.len() - self.origin_path.len()
        }

        /// Ensures the zipper is in its regularized form
        ///
        /// Q: What the heck is "regularized form"?!?!?!
        /// A: The same zipper position may be representated with multiple configurations of the zipper's
        ///  field variables.  Consider the path: `abcd`, where the zipper points to `c`.  This could be
        ///  represented with the `focus_node` of `c` and a `node_key()` of `[]`; called the zipper's
        ///  regularized form.  Alternatively it could be represented with the `focus_node` of `b` and a
        ///  `node_key()` of `c`, which is called a deregularized form.
        #[inline]
        pub(crate) fn regularize(&mut self) {
            debug_assert!(self.prefix_buf.len() >= self.node_key_start()); //If this triggers, we have uninitialized buffers
            if let Some((_consumed_byte_cnt, next_node)) = self.focus_node.node_get_child(self.node_key()) {
                self.ancestors.push((*self.focus_node.clone(), self.focus_iter_token, self.prefix_buf.len()));
                *self.focus_node = next_node.as_tagged();
                self.focus_iter_token = NODE_ITER_INVALID;
            }
        }

        /// Ensures the zipper is in a deregularized form
        ///
        /// While there are dozens of deregularized forms of the zipper and only one regularized, this
        /// method puts the zipper in the state where the focus_node will be as close to the focus as
        /// possible while also ensuring `node_key().len() > 0` or the zipper is at the root.
        #[inline]
        pub(crate) fn deregularize(&mut self) {
            if self.prefix_buf.len() == self.node_key_start() {
                self.ascend_across_nodes();
            }
        }

        /// Returns `true` if the zipper is in a regularized form, otherwise returns the `false`
        ///
        /// See docs for [Self::regularize].
        #[inline]
        fn is_regularized(&self) -> bool {
            let key_start = self.node_key_start();
            if self.prefix_buf.len() > key_start {
                self.focus_node.node_get_child(self.node_key()).is_none()
            } else {
                true
            }
        }

        /// Internal impl is marked `unsafe` because ReadZipperCore::root_node might be `Owned`, meaning
        /// the returned value might outlive the zipper.  We need to only expose this through methods
        /// that have tighter lifetime bounds, or on types that guarantee the root won't be owned
        pub(crate) unsafe fn get_val(&self) -> Option<&'a V> {
            let key = self.node_key();
            if key.len() > 0 {
                self.focus_node.node_get_val(key)
            } else {
                if let Some((parent, _iter_tok, _prefix_offset)) = self.ancestors.last() {
                    parent.node_get_val(self.parent_key())
                } else {
                    //NOTE: It's true that we shouldn't have ZipperReadOnlyValues implemented on a type that comes from a ZipperHead, but
                    // we currently share the same implementation between `val()` and `get_val()` because the only difference is the return
                    // lifetime, and the current ZipperHead implementation is actually ok with referencing the value in the root of the ZipperHead.
                    // debug_assert!(self.root_node.is_borrowed());
                    self.root_val
                }
            }
        }

        /// Internal impl is marked `unsafe` because ReadZipperCore::root_node might be `Owned`, meaning
        /// the returned value might outlive the zipper.  We need to only expose this through methods
        /// that have tighter lifetime bounds, or on types that guarantee the root won't be owned
        pub(crate) unsafe fn get_val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&'a V> {
            let val = TrieRefBorrowed::new_with_key_and_path_in(
                self.focus_parent(),
                || {
                    // SAFETY: `get_val_at` has the same lifetime contract as `get_val`. This closure is
                    // only invoked when the target path resolves to the current focus itself, so using
                    // `self.get_val()` here is equivalent to asking for the current focus value.
                    unsafe { self.get_val() }
                },
                self.node_key(),
                path.as_ref(),
                self.alloc.clone(),
            ).get_val();

            // SAFETY: `val` points into the trie reachable from `self`. The only reason its inferred
            // lifetime is shorter is that `focus_parent()` returns a reference tied to `&self`, even when
            // the underlying trie root is owned by the zipper and is therefore guaranteed to stay alive
            // for `'a`. This method is already `unsafe` for exactly that reason, and callers must uphold
            // the documented requirement that the returned reference not outlive the backing trie storage.
            unsafe { core::mem::transmute::<Option<&V>, Option<&'a V>>(val) }
        }

        /// Convenience form of [`ReadZipperCore::to_next_get_val_observed`] that does not observe path movement.
        pub(crate) unsafe fn to_next_get_val(&mut self) -> Option<&'a V> {
            unsafe { self.to_next_get_val_observed(&mut ()) }
        }

        /// See [ReadZipperCore::get_val] for explanation as to why this is unsafe
        ///
        /// `obs` is notified of every movement made.  This zipper advances by rewinding `prefix_buf`
        /// to a node boundary and then extending it by a whole key run, so the movements reported are
        /// multi-byte and a descent may re-tread bytes the observer already held.  The net position is
        /// always correct; only the granularity differs from a byte-at-a-time traversal.
        pub(crate) unsafe fn to_next_get_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> Option<&'a V> {
            timed_span!(ToNextGetValue, COUNTERS);
            debug_assert_iter_token_layout();
            self.prepare_buffers();
            loop {
                if self.focus_iter_token == NODE_ITER_INVALID {
                    let cur_tok = self.focus_node.iter_token_for_path(self.node_key());
                    self.focus_iter_token = cur_tok;
                }

                let (new_tok, key_bytes, child_node, value) = if self.focus_iter_token < TOKEN_LAST {
                    self.focus_node.next_items(self.focus_iter_token, false)
                } else {
                    (NODE_ITER_FINISHED, &[][..] as &[u8], None, None)
                };

                if new_tok != NODE_ITER_FINISHED {
                    self.focus_iter_token = new_tok;

                    let key_start = self.node_key_start();

                    //Make sure we don't move to a branch that forks above our zipper root
                    let origin_path_len = self.origin_path.len();
                    if key_start < origin_path_len {
                        debug_assert_eq!(self.ancestors.len(), 0);

                        let unmodifiable_len = origin_path_len - key_start;
                        let unmodifiable_subkey = &self.prefix_buf[key_start..origin_path_len];
                        if unmodifiable_len > key_bytes.len() || &key_bytes[..unmodifiable_len] != unmodifiable_subkey {
                            obs.ascend(self.prefix_buf.len() - origin_path_len);
                            self.prefix_buf.truncate(origin_path_len);
                            return None
                        }
                    }

                    //The truncate may rewind past `origin_path_len`, but the bytes below the root are
                    //re-supplied identically by `key_bytes` (checked above), so the focus stays at or
                    //below the root.  The observer tracks the path from the root, so `key_bytes` is
                    //reported from the point where the rewind lands relative to it.
                    //`get` rather than indexing, so the slicing carries no panic path and can be
                    //optimized away entirely when `obs` discards what it is given
                    let obs_skip = origin_path_len.saturating_sub(key_start);
                    obs.ascend(self.prefix_buf.len() - key_start - obs_skip);
                    self.prefix_buf.truncate(key_start);
                    self.prefix_buf.extend(key_bytes);
                    if let Some(reported) = key_bytes.get(obs_skip..) {
                        obs.descend_to(reported);
                    }

                    match child_node {
                        None => {},
                        Some(rec) => {
                            self.ancestors.push((*self.focus_node.clone(), new_tok, self.prefix_buf.len()));
                            *self.focus_node = rec.as_tagged();
                            self.focus_iter_token = self.focus_node.new_iter_token();
                        },
                    }

                    match value {
                        Some(v) => return Some(v),
                        None => {}
                    }
                } else {
                    //Ascend
                    if let Some((focus_node, iter_tok, prefix_offset)) = self.ancestors.pop() {
                        *self.focus_node = focus_node;
                        self.focus_iter_token = iter_tok;
                        obs.ascend(self.prefix_buf.len() - prefix_offset);
                        self.prefix_buf.truncate(prefix_offset);
                    } else {
                        let new_len = self.origin_path.len();
                        self.focus_iter_token = NODE_ITER_INVALID;
                        obs.ascend(self.prefix_buf.len() - new_len);
                        self.prefix_buf.truncate(new_len);
                        return None
                    }
                }
            }
        }

        /// Returns the parent and path from which the top of the focus_stack can be re-acquired
        #[inline]
        pub(crate) fn focus_parent(&self) -> &TrieNodeODRc<V, A> {
            let parent_key = self.parent_key();
            if parent_key.len() == 0 {
                return self.root_node.as_ref()
            }
            self.focus_parent_borrowed()
        }

        /// Same behavior as [Self::focus_parent], but with a less restrictive return lifetime
        #[inline]
        pub(crate) fn focus_parent_borrowed(&self) -> &'a TrieNodeODRc<V, A> {
            let parent_key = self.parent_key();
            if parent_key.len() == 0 {
                return self.root_node.as_borrowed_ref()
            }

            let parent_node = match self.ancestors.last() {
                Some((focus_node, _iter_tok, _prefix_offset)) => {
                    *focus_node
                },
                None => unreachable!()
            };
            let (key_len, node) = parent_node.node_get_child(parent_key).unwrap();
            debug_assert_eq!(key_len, parent_key.len());
            node
        }

        /// Internal method to implement `descend_to` and similar methods, handling the movement
        /// of the focus node, but not necessarily the whole method contract
        ///
        /// Returns the remaining `node_key`, after the node descent has gone as far as possible,
        /// along with a re-borrow of `self` to work around the borrow checker
        #[inline]
        fn descend_to_internal(&mut self, k: &[u8]) -> (&Self, &[u8]) {
            self.focus_iter_token = NODE_ITER_INVALID;
            self.prefix_buf.extend(k);
            let mut key_start = self.node_key_start();
            let mut key = &self.prefix_buf[key_start..];

            //GOAT... WIP.  planning to add a "CheckF: Fn(&dyn TrieNode<V>, &[u8])->Option<usize>"
            // argument that can cause an early return, and be used to look for values as we descend
            //
            // //Run the check_f on the current focus node, before advancing to the next node
            // match check_f(self.focus_node.borrow(), &self.prefix_buf[key_start..]) {
            //     Some(byte_cnt) => {
            //         return (self, &self.prefix_buf[key_start..byte_cnt])
            //     },
            //     None => {}
            // }

            //Step until we get to the end of the key or find a leaf node
            while let Some((consumed_byte_cnt, next_node)) = self.focus_node.node_get_child(key) {
                let next_node = next_node.as_tagged();
                key_start += consumed_byte_cnt;
                self.ancestors.push((*self.focus_node.clone(), NODE_ITER_INVALID, key_start));
                *self.focus_node = next_node;
                if consumed_byte_cnt < key.len() {
                    key = &key[consumed_byte_cnt..]
                } else {
                    return (self, &[]);
                };
            }
            (self, key)
        }

        /// Internal implementation of `to_next_sibling_byte` / `to_prev_sibling_byte`.
        #[inline]
        fn to_sibling(&mut self, next: bool) -> Option<u8> {
            if self.at_root() {
                return None;
            }
            self.prepare_buffers();
            debug_assert!(self.is_regularized());
            if self.node_key().len() != 0 {
                match self.focus_node.get_sibling_of_child(self.node_key(), next) {
                    (Some(prefix), Some(child_node)) => {
                        *self.prefix_buf.last_mut().unwrap() = prefix;
                        self.focus_iter_token = NODE_ITER_INVALID;
                        self.ancestors.push((*self.focus_node.clone(), self.focus_iter_token, self.prefix_buf.len()));
                        *self.focus_node = child_node;
                        Some(prefix)
                    },
                    (Some(prefix), None) => {
                        *self.prefix_buf.last_mut().unwrap() = prefix;
                        self.focus_iter_token = NODE_ITER_INVALID;
                        Some(prefix)
                    },
                    (None, _) => None
                }
            } else {
                let mut should_pop = false;
                let result = match self.ancestors.last() {
                    None => { None }
                    Some((parent, _iter_tok, _prefix_offset)) => {
                        match parent.get_sibling_of_child(self.parent_key(), next) {
                            (Some(prefix), Some(child_node)) => {
                                *self.prefix_buf.last_mut().unwrap() = prefix;
                                *self.focus_node = child_node;
                                self.focus_iter_token = NODE_ITER_INVALID;
                                Some(prefix)
                            },
                            (Some(prefix), None) => {
                                *self.prefix_buf.last_mut().unwrap() = prefix;
                                should_pop = true;
                                Some(prefix)
                            },
                            (None, _) => {
                                None
                            }
                        }
                    }
                };
                if result.is_some() {
                    self.ancestors.last_mut().unwrap().1 = NODE_ITER_INVALID;
                }
                if should_pop {
                    let (focus_node, iter_tok, _prefix_offset) = self.ancestors.pop().unwrap();
                    *self.focus_node = focus_node;
                    self.focus_iter_token = iter_tok;
                }
                result
            }
        }

        fn k_path_internal<Obs: PathObserver>(&mut self, k: usize, base_idx: usize, mut continue_from_focus: bool, obs: &mut Obs) -> bool {
            // Minimum number of bytes beyond the requested path length at which we avoid
            // copying the excess into prefix_buf. For shorter overshoots, copying the full
            // node key and truncating it is cheaper; benchmarks put the crossover near 12.
            const MIN_EXCESS_TO_AVOID_COPY: usize = 12;

            debug_assert_iter_token_layout();

            //Note: we may be able to eke out a win using the guarantees provided by TOKEN_LAST,
            // however all experiements so far have been worse
            let obs_floor = self.origin_path.len();
            let target_idx = base_idx + k;
            loop {
                if self.focus_iter_token == NODE_ITER_INVALID {
                    self.focus_iter_token = self.focus_node.iter_token_for_path(self.node_key());
                    continue_from_focus = true;
                }
                debug_assert_ne!(self.focus_iter_token, NODE_ITER_INVALID);
                debug_assert_ne!(self.focus_iter_token, NODE_ITER_FINISHED);
                debug_assert!(self.prefix_buf.len() <= target_idx);
                debug_assert!(self.prefix_buf.len() >= base_idx);
                let key_start = self.node_key_start();
                let (new_tok, key_bytes, child_node, _value) = self.focus_node.next_items(self.focus_iter_token, continue_from_focus);
                continue_from_focus = false;
                if new_tok != NODE_ITER_FINISHED {
                    if key_start < base_idx {
                        let base_key_len = base_idx - key_start;
                        if base_key_len > key_bytes.len() || &key_bytes[..base_key_len] != &self.prefix_buf[key_start..base_idx] {
                            let excess = self.prefix_buf.len() - base_idx;
                            self.prefix_buf.truncate(base_idx);
                            if excess > 0 {
                                obs.ascend(excess);
                                self.reascend_iter_token(excess);
                            }
                            return false;
                        }
                    }
                    self.focus_iter_token = new_tok;
                    let obs_skip = obs_floor.saturating_sub(key_start);
                    obs.ascend(self.prefix_buf.len().saturating_sub(key_start.max(obs_floor)));
                    self.prefix_buf.truncate(key_start);
                    let remaining = target_idx - key_start;
                    if key_bytes.len() > remaining {
                        let excess = key_bytes.len() - remaining;
                        if excess >= MIN_EXCESS_TO_AVOID_COPY {
                            let key_prefix = &key_bytes[..remaining];
                            self.prefix_buf.extend(key_prefix);
                            if let Some(reported) = key_prefix.get(obs_skip..) { obs.descend_to(reported); }
                        } else {
                            self.prefix_buf.extend(key_bytes);
                            if let Some(reported) = key_bytes.get(obs_skip..) { obs.descend_to(reported); }
                            obs.ascend(excess);
                            self.prefix_buf.truncate(target_idx);
                        }
                        self.focus_iter_token = self.focus_node.ascend_iter_token(new_tok, excess);
                        return true
                    }
                    self.prefix_buf.extend(key_bytes);
                    if let Some(reported) = key_bytes.get(obs_skip..) { obs.descend_to(reported); }
                    match child_node {
                        None => {},
                        Some(rec) => {
                            self.ancestors.push((*self.focus_node.clone(), new_tok, self.prefix_buf.len()));
                            *self.focus_node = rec.as_tagged();
                            self.focus_iter_token = self.focus_node.new_iter_token();
                        },
                    }
                    if self.prefix_buf.len() == target_idx { return true; }
                } else {
                    if key_start <= base_idx {
                        let excess = self.prefix_buf.len() - base_idx;
                        obs.ascend(excess);
                        self.prefix_buf.truncate(base_idx);
                        if excess > 0 {
                            self.reascend_iter_token(excess);
                        }
                        return false
                    }
                    if let Some((focus_node, iter_tok, prefix_offset)) = self.ancestors.pop() {
                        *self.focus_node = focus_node;
                        self.focus_iter_token = iter_tok;
                        obs.ascend(self.prefix_buf.len().saturating_sub(prefix_offset.max(obs_floor)));
                        self.prefix_buf.truncate(prefix_offset);
                    } else {
                        let new_len = self.origin_path.len();
                        self.focus_iter_token = NODE_ITER_INVALID;
                        obs.ascend(self.prefix_buf.len().saturating_sub(new_len));
                        self.prefix_buf.truncate(new_len);
                        return false
                    }
                }
            }
        }

        /// Internal method that implements [Self::is_val], but so it can be inlined elsewhere
        #[inline]
        fn is_val_internal(&self) -> bool {
            let key = self.node_key();
            if key.len() > 0 {
                self.focus_node.node_contains_val(key)
            } else {
                if let Some((parent, _iter_tok, _prefix_offset)) = self.ancestors.last() {
                    parent.node_contains_val(self.parent_key())
                } else {
                    self.root_val.is_some()
                }
            }
        }

        /// Internal method implementing part of [Self::descend_until_observed], but doesn't pay attention to to [Self::child_count]
        #[inline]
        fn descend_first<Obs: PathObserver>(&mut self, obs: &mut Obs) {
            self.prepare_buffers();
            match self.focus_node.first_child_from_key(self.node_key()) {
                (Some(prefix), Some(child_node)) => {
                    //Step to a new node
                    self.prefix_buf.extend(prefix);
                    obs.descend_to(prefix);
                    if !prefix.is_empty() {
                        self.focus_iter_token = NODE_ITER_INVALID;
                    }
                    self.ancestors.push((*self.focus_node.clone(), self.focus_iter_token, self.prefix_buf.len()));
                    *self.focus_node = child_node;
                    self.focus_iter_token = NODE_ITER_INVALID;

                    //If we're at the root of the new node, descend to the first child
                    if prefix.len() == 0 {
                        self.descend_first(obs)
                    }
                },
                (Some(prefix), None) => {
                    //Stay within the same node
                    self.prefix_buf.extend(prefix);
                    obs.descend_to(prefix);
                    if !prefix.is_empty() {
                        self.focus_iter_token = NODE_ITER_INVALID;
                    }
                },
                (None, _) => unreachable!()
            }
        }

        /// Internal method returning the index to the key char beyond the path to the `self.focus_node`
        #[inline]
        fn node_key_start(&self) -> usize {
            self.ancestors.last().map(|(_node, _iter_tok, i)| *i)
                .unwrap_or_else(|| self.root_key_start)
        }
        //GOAT, probably don't need this
        // /// Returns the offset of the end of the focus node's key
        // #[inline]
        // fn node_key_end(&self) -> usize {
        //     if self.prefix_buf.len() > 0 {
        //         self.prefix_buf.len()
        //     } else {
        //         self.origin_path.len()
        //     }
        // }
        /// Internal method returning the key within the focus node
        #[inline]
        pub(crate) fn node_key(&self) -> &[u8] {
            let key_start = self.node_key_start();
            if self.prefix_buf.len() > 0 {
                &self.prefix_buf[key_start..]
            } else {
                if self.origin_path.len() > 0 {
                    unsafe{ &self.origin_path.as_slice_unchecked()[key_start..] }
                } else {
                    &[]
                }
            }
        }
        /// Internal method returning the key that leads to the zipper root within the zipper's root_node
        #[inline]
        fn root_node_key(&self) -> &[u8] {
            //This method should only be called when we have an owned `root_node`, which should go with
            // a valid value for `root_parent_key_start`
            debug_assert!(matches!(self.root_node, OwnedOrBorrowed::Owned(_)));
            debug_assert!(self.root_parent_key_start < usize::MAX);
            if self.prefix_buf.capacity() == 0 && self.origin_path.len() > 0 {
                unsafe{ &self.origin_path.as_slice_unchecked()[self.root_parent_key_start..] }
            } else {
                &self.prefix_buf[self.root_parent_key_start..self.root_key_start]
            }
        }
        /// Internal method returning the key that leads to `self.focus_node` within the parent
        #[inline]
        fn parent_key(&self) -> &[u8] {
            if self.prefix_buf.len() > 0 {
                let key_start = if self.ancestors.len() > 1 {
                    unsafe{ self.ancestors.get_unchecked(self.ancestors.len()-2) }.2
                } else {
                    self.root_key_start
                };
                &self.prefix_buf[key_start..self.node_key_start()]
            } else {
                if self.root_parent_key_start == usize::MAX || self.origin_path.len() == 0 {
                    &[]
                } else {
                    let origin_path = unsafe{ self.origin_path.as_slice_unchecked() };
                    &origin_path[self.root_parent_key_start..self.root_key_start]
                }
            }
        }
        /// Internal method similar to `self.node_key().len()`, but returns the number of chars that can be
        /// legally ascended within the node, taking into account the root_key
        #[inline]
        fn excess_key_len(&self) -> usize {
            self.prefix_buf.len() - self.ancestors.last().map(|(_node, _iter_tok, i)| *i).unwrap_or(self.origin_path.len())
        }
        /// Internal method which doesn't actually move the zipper, but ensures `self.node_key().len() > 0`
        /// WARNING, must never be called if `self.node_key().len() != 0`
        #[inline]
        fn ascend_across_nodes(&mut self) {
            debug_assert!(self.node_key().len() == 0);
            if let Some((focus_node, iter_tok, _prefix_offset)) = self.ancestors.pop() {
                *self.focus_node = focus_node;
                self.focus_iter_token = iter_tok;
            } else {
                self.focus_iter_token = NODE_ITER_INVALID;
            }
        }
        /// Internal method used to impement `ascend_until` when ascending within a node
        #[inline]
        fn ascend_within_node(&mut self) -> usize {
            let branch_key = self.focus_node.prior_branch_key(self.node_key());
            let new_len = self.origin_path.len().max(self.node_key_start() + branch_key.len());
            let old_len = self.prefix_buf.len();
            self.prefix_buf.truncate(new_len);
            let ascended = old_len - new_len;
            if ascended > 0 {
                self.reascend_iter_token(ascended);
            }
            ascended
        }
        /// Updates the compact cursor after removing bytes from within the current node.  An already
        /// invalid cursor remains invalid; otherwise the node implementation must encode the new focus.
        #[inline]
        fn reascend_iter_token(&mut self, byte_count: usize) {
            if self.focus_iter_token == NODE_ITER_INVALID {
                return
            }
            if node_iter_token_is_nonexistent(self.focus_iter_token)
            {
                self.focus_iter_token = NODE_ITER_INVALID;
                return
            }
            self.focus_iter_token = self.focus_node
                .ascend_iter_token(self.focus_iter_token, byte_count);
        }
        /// Push a new node-path pair onto the zipper.  This is used in the internal implementation of
        /// the [crate::zipper::ProductZipper]
        pub(crate) fn push_node(&mut self, node: TaggedNodeRef<'a, V, A>) {
            self.ancestors.push((*self.focus_node.clone(), self.focus_iter_token, self.prefix_buf.len()));
            *self.focus_node = node;
            self.focus_iter_token = NODE_ITER_INVALID;
        }

        pub(crate) fn into_path(self) -> Vec<u8> {
            self.prefix_buf
        }
    }

    /// Validate we don't accidentially reallocate the path buffer when we don't need to
    #[test]
    fn read_zipper_reserve_buffer_test() {
        let map = PathMap::<()>::new();

        //Try with no prefix path
        let mut rz = map.read_zipper();
        assert_eq!(rz.z.prefix_buf.capacity(), 0);
        rz.reserve_buffers(4096, 512);
        assert_eq!(rz.z.prefix_buf.capacity(), 4096);
        let old_ptr = rz.z.prefix_buf.as_ptr();
        rz.descend_to(b"hello");
        assert_eq!(rz.z.prefix_buf.capacity(), 4096);
        assert_eq!(rz.z.prefix_buf.as_ptr(), old_ptr);
        assert_eq!(&rz.z.prefix_buf, b"hello");
        assert_eq!(&rz.path(), b"hello");

        //Try with a prefix path
        let mut rz = map.read_zipper_at_borrowed_path(b"hi");
        assert_eq!(rz.z.prefix_buf.capacity(), 0);
        assert_eq!(rz.path(), b"");
        assert_eq!(rz.origin_path(), b"hi");
        rz.reserve_buffers(4096, 512);
        assert_eq!(rz.z.prefix_buf.capacity(), 4096);
        let old_ptr = rz.z.prefix_buf.as_ptr();
        assert_eq!(rz.path(), b"");
        assert_eq!(rz.origin_path(), b"hi");
        assert_eq!(&rz.z.prefix_buf, b"hi");
        rz.descend_to(b"-howdy");
        assert_eq!(rz.z.prefix_buf.capacity(), 4096);
        assert_eq!(rz.z.prefix_buf.as_ptr(), old_ptr);
        assert_eq!(&rz.z.prefix_buf, b"hi-howdy");
        assert_eq!(&rz.path(), b"-howdy");
        assert_eq!(rz.origin_path(), b"hi-howdy");
    }
}
use read_zipper_core::*;

/// Internal function to walk along a path to the final node reference
pub(crate) fn node_along_path<'a, 'path, V: Clone + Sync + Send, A: Allocator + 'a>(root_node: &'a TrieNodeODRc<V, A>, path: &'path [u8], root_val: Option<&'a V>, stop_short: bool) -> (&'a TrieNodeODRc<V, A>, &'path [u8], Option<&'a V>) {
    let mut key = path;
    let mut node = root_node;
    let mut val = root_val;
    let mut tagged_node = node.as_tagged();

    //Step until we get to the end of the key or find a leaf node
    if key.len() > 0 {
        while let Some((consumed_byte_cnt, next_node)) = tagged_node.node_get_child(key) {
            if consumed_byte_cnt < key.len() {
                node = next_node;
                key = &key[consumed_byte_cnt..];
            } else {
                if !stop_short {
                    val = tagged_node.node_get_val(key);
                    node = next_node;
                    key = &[];
                } else {
                    val = None;
                }
                break;
            };
            tagged_node = node.as_tagged();
        }
    }

    (node, key, val)
}

/// An iterator for depth-first traversal of a [Zipper], returned from [ReadZipperUntracked::into_iter]
///
/// NOTE: This is a convenience to allow access to syntactic sugar like `for` loops, [collect](std::iter::Iterator::collect),
///  etc.  It will always be faster to use the zipper itself for iteration and traversal.
pub struct ReadZipperIter<'a, 'path, V: Clone + Send + Sync, A: Allocator = GlobalAlloc>{
    started: bool,
    zipper: Option<ReadZipperCore<'a, 'path, V, A>>,
}

impl<'a, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> Iterator for ReadZipperIter<'a, '_, V, A> {
    type Item = (Vec<u8>, &'a V);

    fn next(&mut self) -> Option<(Vec<u8>, &'a V)> {
        if !self.started {
            self.started = true;
            if let Some(zipper) = &mut self.zipper {
                //SAFETY: we only allow ReadZipperUntracked to become a `ReadZipperIter`
                if let Some(val) = unsafe{ zipper.get_val() } {
                    return Some((zipper.path().to_vec(), val))
                }
            }
        }
        if let Some(zipper) = &mut self.zipper {
            //SAFETY: we only allow ReadZipperUntracked to become a `ReadZipperIter`
            match unsafe{ zipper.to_next_get_val() } {
                Some(val) => return Some((zipper.path().to_vec(), val)),
                None => self.zipper = None
            }
        }
        None
    }
}

/// An iterator for depth-first traversal of every existing path end (leaf) reachable from a [Zipper],
/// regardless of whether a value exists at that path. Returned from [ReadZipperUntracked::into_path_iter]
///
/// NOTE: This is a convenience to allow access to syntactic sugar like `for` loops, [collect](std::iter::Iterator::collect),
///  etc.  It will always be faster to use the zipper itself for iteration and traversal.
pub struct ReadZipperPathIter<'a, 'path, V: Clone + Send + Sync, A: Allocator = GlobalAlloc>{
    zipper: Option<ReadZipperCore<'a, 'path, V, A>>,
}

impl<V: Clone + Send + Sync + Unpin, A: Allocator> ReadZipperPathIter<'_, '_, V, A> {
    /// Returns a reference to the value at the last-returned path
    pub fn val(&self) -> Option<&V> {
        self.zipper.as_ref().and_then(|z| z.val())
    }
}

impl<'a, V: Clone + Send + Sync + Unpin + 'a, A: Allocator + 'a> Iterator for ReadZipperPathIter<'a, '_, V, A> {
    type Item = Vec<u8>;

    fn next(&mut self) -> Option<Vec<u8>> {
        if let Some(zipper) = &mut self.zipper {
            while zipper.to_next_step() {
                if zipper.path_exists() && zipper.child_count() == 0 {
                    return Some(zipper.path().to_vec());
                }
            }
        }
        self.zipper = None;
        None
    }
}

/// The origin path, will be a slice if it's borrowed from outside the Zipper, or length of the origin path in
/// the `prefix_buf` if it has already been copied
#[derive(Clone, Copy)]
pub(crate) enum SliceOrLen<'a> {
    Slice(&'a [u8]),
    Len(usize),
}

impl<'a> From<&'a [u8]> for SliceOrLen<'a> {
    fn from(slice: &'a [u8]) -> Self {
        Self::Slice(slice)
    }
}

impl SliceOrLen<'static> {
    #[inline]
    pub fn new_owned(len: usize) -> Self {
        if len == 0 {
            Self::Slice(&[])
        } else {
            Self::Len(len)
        }
    }
}

#[allow(unused)]
impl<'a> SliceOrLen<'a> {
    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Self::Slice(slice) => slice.len(),
            Self::Len(len) => {
                debug_assert!(*len > 0); //Zero-length SliceOrLen should always be represented as a `Slice`
                *len
            },
        }
    }
    pub fn make_len(&mut self) {
        if self.len() > 0 {
            match self {
                Self::Slice(slice) => {*self = Self::Len(slice.len())},
                Self::Len(_) => {},
            }
        }
    }
    #[inline]
    pub fn is_slice(&self) -> bool {
        match self {
            Self::Slice(_) => true,
            Self::Len(_) => false,
        }
    }
    #[inline]
    pub fn as_slice(&self) -> &'a[u8] {
        match self {
            Self::Slice(slice) => slice,
            Self::Len(_) => unreachable!()
        }
    }
    #[inline]
    pub fn try_as_slice(&self) -> Option<&'a[u8]> {
        match self {
            Self::Slice(slice) => Some(slice),
            Self::Len(_) => None
        }
    }
    #[inline]
    pub unsafe fn as_slice_unchecked(&self) -> &'a[u8] {
        match self {
            Self::Slice(slice) => slice,
            Self::Len(_) => unsafe{ core::hint::unreachable_unchecked() }
        }
    }
    #[inline]
    pub fn set_slice(&mut self, slice: &'a[u8]) {
        *self = Self::Slice(slice);
    }
    #[inline]
    pub fn set_len(&mut self, len: usize) {
        if len > 0 {
            *self = Self::Len(len)
        } else {
            *self = Self::Slice(&[])
        }
    }
}

/// Implements tests that apply to all [ZipperMoving] types
#[cfg(test)]
pub(crate) mod zipper_moving_tests {
    use crate::trie_map::*;
    use crate::trie_node::MAX_NODE_KEY_BYTES;
    use super::*;

    /// `$ident` is a unique identifier for the zipper, so the generated tests don't collide
    /// `$read_keys` is a function that will create a store containing all paths, from which a zipper can be created
    /// `$make_z` is a function that will create a zipper from a slice of paths
    macro_rules! zipper_moving_tests {
        ($z_name:ident, $read_keys:expr, $make_z:expr)=>{
            paste::paste! {
                #[test]
                fn [<$z_name _zipper_moving_basic_test>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_MOVING_BASIC_TEST_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_moving_basic_test)
                }

                #[test]
                fn [<$z_name _zipper_with_root_path>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_WITH_ROOT_PATH_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, crate::zipper::zipper_moving_tests::ZIPPER_WITH_ROOT_PATH_PATH, crate::zipper::zipper_moving_tests::zipper_with_root_path)
                }

                #[test]
                fn [<$z_name _zipper_dangling_descend_test>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_DANGLING_DESCEND_TEST_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_dangling_descend_test)
                }

                #[test]
                fn [<$z_name _zipper_indexed_bytes_test1>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_INDEXED_BYTE_TEST1_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_indexed_bytes_test1)
                }

                #[test]
                fn [<$z_name _zipper_indexed_bytes_test2>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_INDEXED_BYTE_TEST2_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_indexed_bytes_test2)
                }

                #[test]
                fn [<$z_name _zipper_descend_until_test1>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_DESCEND_UNTIL_TEST1_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_descend_until_test1)
                }

                #[test]
                fn [<$z_name _zipper_descend_until_max_bytes_test1>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_DESCEND_UNTIL_MAX_BYTES_TEST1_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_descend_until_max_bytes_test1)
                }

                #[test]
                fn [<$z_name _zipper_ascend_until_test1>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_ASCEND_UNTIL_TEST1_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_ascend_until_test1)
                }

                #[test]
                fn [<$z_name _zipper_ascend_until_test2>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_ASCEND_UNTIL_TEST2_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_ascend_until_test2)
                }

                #[test]
                fn [<$z_name _zipper_ascend_until_test3>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_ASCEND_UNTIL_TEST3_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_ascend_until_test3)
                }

                #[test]
                fn [<$z_name _zipper_ascend_until_test4>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_ASCEND_UNTIL_TEST4_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_ascend_until_test4)
                }

                #[test]
                fn [<$z_name _zipper_ascend_until_test5>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_ASCEND_UNTIL_TEST5_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_ascend_until_test5)
                }

                #[test]
                fn [<$z_name _indexed_zipper_movement1>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_INDEXED_MOVEMENT_TEST1_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::indexed_zipper_movement1)
                }

                #[test]
                fn [<$z_name _zipper_value_locations>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_VALUE_LOCATIONS_TEST1_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_value_locations)
                }

                #[test]
                fn [<$z_name _zipper_child_mask_test1>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_CHILD_MASK_TEST1_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_child_mask_test1)
                }

                #[test]
                fn [<$z_name _zipper_child_mask_test2>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_CHILD_MASK_TEST2_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_child_mask_test2)
                }

                #[test]
                fn [<$z_name _descend_to_existing_test1>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_DESCEND_TO_EXISTING_TEST1_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::descend_to_existing_test1)
                }

                #[test]
                fn [<$z_name _descend_to_existing_test2>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_DESCEND_TO_EXISTING_TEST2_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::descend_to_existing_test2)
                }

                #[test]
                fn [<$z_name _descend_to_existing_test3>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_DESCEND_TO_EXISTING_TEST3_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::descend_to_existing_test3)
                }

                #[test]
                fn [<$z_name _to_next_step_test1>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_TO_NEXT_STEP_TEST1_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::to_next_step_test1)
                }

                #[test]
                fn [<$z_name _zipper_byte_iter_test1>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_BYTES_ITER_TEST1_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_byte_iter_test1)
                }

                #[test]
                fn [<$z_name _zipper_byte_iter_test2>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_BYTES_ITER_TEST2_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, crate::zipper::zipper_moving_tests::ZIPPER_BYTES_ITER_TEST2_PATH, crate::zipper::zipper_moving_tests::zipper_byte_iter_test2)
                }

                #[test]
                fn [<$z_name _zipper_byte_iter_test3>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_BYTES_ITER_TEST3_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, crate::zipper::zipper_moving_tests::ZIPPER_BYTES_ITER_TEST3_PATH, crate::zipper::zipper_moving_tests::zipper_byte_iter_test3)
                }

                #[test]
                fn [<$z_name _zipper_byte_iter_test4>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_BYTES_ITER_TEST4_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_byte_iter_test4)
                }

                #[test]
                fn [<$z_name _zipper_byte_iter_test5>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_BYTES_ITER_TEST5_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_byte_iter_test5)
                }

                #[test]
                fn [<$z_name _zipper_val_at_test>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_moving_tests::ZIPPER_VAL_AT_TEST_KEYS);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_val_at_test)
                }

                #[test]
                fn [<$z_name _zipper_val_at_long_path_test>]() {
                    let long_key = crate::zipper::zipper_moving_tests::zipper_val_at_long_path_test_key();
                    let keys = [&long_key[..], b"zzz" as &[u8]];
                    let mut temp_store = $read_keys(&keys);
                    crate::zipper::zipper_moving_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_moving_tests::zipper_val_at_long_path_test)
                }
            }
        }
    }
    pub(crate) use zipper_moving_tests;

    /// Internal method to provide a lifetime bound on the macro arguments to the test macro
    pub fn run_test<'a, T: 'a + ZipperMoving, Store>(
        store: &'a mut Store,
        make_t: impl Fn(&'a mut Store, &'a[u8]) -> T,
        z_path: &'a[u8],
        test_f: impl Fn(T)
    ) {
        let t = make_t(store, z_path);
        test_f(t);
    }

    /// from https://en.wikipedia.org/wiki/Radix_tree#/media/File:Patricia_trie.svg
    pub const ZIPPER_MOVING_BASIC_TEST_KEYS: &[&[u8]] = &[b"romane", b"romanus", b"romulus", b"rubens", b"ruber", b"rubicon", b"rubicundus", b"rom'i"];

    pub fn zipper_moving_basic_test<Z: ZipperMoving + ZipperPath>(mut zipper: Z) {
        fn assert_in_list(val: &[u8], list: &[&[u8]]) {
            for test_val in list {
                if *test_val == val {
                    return;
                }
            }
            panic!("val not found in list: {}", std::str::from_utf8(val).unwrap_or(""))
        }

        zipper.descend_to(&[b'r']); zipper.descend_to(&[b'o']); zipper.descend_to(&[b'm']); // focus = rom
        zipper.descend_to(&[b'\'']);
        assert!(zipper.path_exists()); // focus = rom'  (' is the lowest byte)
        assert!(zipper.to_next_sibling_byte().is_some()); // focus = roma  (a is the second byte), but we can't actually guarantee whether we land on 'a' or 'u'
        assert_in_list(zipper.path(), &[b"roma", b"romu"]);
        assert_eq!(zipper.child_mask().iter().collect::<Vec<_>>(), vec![b'n']); // both follow-ups romane and romanus have n following a
        assert!(zipper.to_next_sibling_byte().is_some()); // focus = romu  (u is the third byte)
        assert_in_list(zipper.path(), &[b"roma", b"romu"]);
        assert_eq!(zipper.child_mask().iter().collect::<Vec<_>>(), vec![b'l']); // and romu is followed by lus
        assert_eq!(zipper.to_next_sibling_byte(), None); // fails because there were only 3 children ['\'', 'a', 'u']
        assert!(zipper.to_prev_sibling_byte().is_some()); // focus = roma or romu (we stepped back)
        assert_in_list(zipper.path(), &[b"roma", b"romu"]);
        assert_eq!(zipper.to_prev_sibling_byte(), Some(39)); // focus = rom' (we stepped back to where we began)
        assert_eq!(zipper.path(), b"rom'");
        assert_eq!(zipper.depth(), zipper.path().len());
        assert_eq!(zipper.child_mask().iter().collect::<Vec<_>>(), vec![b'i']);
        assert_eq!(zipper.ascend(1), 1); // focus = rom
        assert_eq!(zipper.child_mask().iter().collect::<Vec<_>>(), vec![b'\'', b'a', b'u']); // all three options we visited
        assert_eq!(zipper.descend_indexed_byte(0), Some(39)); // focus = rom'
        assert_eq!(zipper.child_mask().iter().collect::<Vec<_>>(), vec![b'i']);
        assert_eq!(zipper.ascend(1), 1); // focus = rom
        assert_eq!(zipper.descend_indexed_byte(1), Some(b'a')); // focus = roma
        assert_eq!(zipper.child_mask().iter().collect::<Vec<_>>(), vec![b'n']);
        assert_eq!(zipper.ascend(1), 1);
        assert_eq!(zipper.descend_indexed_byte(2), Some(b'u')); // focus = romu
        assert_eq!(zipper.child_mask().iter().collect::<Vec<_>>(), vec![b'l']);
        assert_eq!(zipper.ascend(1), 1);
        assert_eq!(zipper.descend_indexed_byte(1), Some(b'a')); // focus = roma
        assert_eq!(zipper.child_mask().iter().collect::<Vec<_>>(), vec![b'n']);
        assert_eq!(zipper.ascend(1), 1);
        // ' < a < u
        // 39 105 117
    }

    pub const ZIPPER_WITH_ROOT_PATH_KEYS: &[&[u8]] = &[b"romane", b"romanus", b"romulus", b"rubens", b"ruber", b"rubicon", b"rubicundus", b"rom'i"];
    pub const ZIPPER_WITH_ROOT_PATH_PATH: &[u8] = b"ro";

    /// Tests creating a zipper at a specific key within a map
    pub fn zipper_with_root_path<Z: ZipperMoving + ZipperPath>(mut zipper: Z) {

        //Test `descend_to` and `ascend_until`
        assert_eq!(zipper.path(), b"");
        assert_eq!(zipper.child_count(), 1);
        zipper.descend_to(b"m");
        assert_eq!(zipper.path(), b"m");
        assert_eq!(zipper.child_count(), 3);
        zipper.descend_to(b"an");
        assert_eq!(zipper.path(), b"man");
        //`depth` is relative to the zipper's root, not the map root
        assert_eq!(zipper.depth(), zipper.path().len());
        assert_eq!(zipper.child_count(), 2);
        zipper.descend_to(b"e");
        assert_eq!(zipper.path(), b"mane");
        assert_eq!(zipper.child_count(), 0);
        assert_eq!(zipper.ascend_until(), 1);
        zipper.descend_to(b"us");
        assert_eq!(zipper.path(), b"manus");
        assert_eq!(zipper.child_count(), 0);
        assert_eq!(zipper.ascend_until(), 2);
        assert_eq!(zipper.path(), b"man");
        assert_eq!(zipper.child_count(), 2);
        assert_eq!(zipper.ascend_until(), 2);
        assert_eq!(zipper.path(), b"m");
        assert_eq!(zipper.child_count(), 3);
        assert_eq!(zipper.ascend_until(), 1);
        assert_eq!(zipper.path(), b"");
        assert_eq!(zipper.depth(), 0);
        assert_eq!(zipper.child_count(), 1);
        assert_eq!(zipper.at_root(), true);
        assert_eq!(zipper.ascend_until(), 0);

        //Test `ascend`
        zipper.descend_to(b"manus");
        assert_eq!(zipper.path(), b"manus");
        assert_eq!(zipper.ascend(1), 1);
        assert_eq!(zipper.path(), b"manu");
        assert_eq!(zipper.ascend(5), 4);
        assert_eq!(zipper.path(), b"");
        assert_eq!(zipper.at_root(), true);
        zipper.descend_to(b"mane");
        assert_eq!(zipper.path(), b"mane");
        assert_eq!(zipper.ascend(3), 3);
        assert_eq!(zipper.path(), b"m");
        eprintln!("child_mask = {:?}", zipper.child_mask());
        assert_eq!(zipper.child_count(), 3);
    }

    // A wide shallow trie
    pub const ZIPPER_DANGLING_DESCEND_TEST_KEYS: &[&[u8]] = &[b"b", b"bqqq"];

    /// `descend_first_byte` must agree with `descend_indexed_byte(0)`, including when the focus
    /// sits on a non-existent (dangling) path, where there are no children to descend into
    pub fn zipper_dangling_descend_test<Z: ZipperMoving + ZipperPath>(mut zip: Z) {
        //Descend to a path that doesn't exist in the trie.  `b"bq"` exists as a prefix of
        // `b"bqqq"`, but `b"bb"` does not.
        zip.descend_to(b"bb");
        assert_eq!(zip.path_exists(), false);
        assert_eq!(zip.child_count(), 0);

        //With no children, `descend_indexed_byte(0)` is out of range and must not move
        assert_eq!(zip.descend_indexed_byte(0), None);
        assert_eq!(zip.path(), b"bb");

        //`descend_first_byte` is documented to behave identically to `descend_indexed_byte(0)`
        assert_eq!(zip.descend_first_byte(), None);
        assert_eq!(zip.path(), b"bb");
    }

    pub const ZIPPER_INDEXED_BYTE_TEST1_KEYS: &[&[u8]] = &[b"0", b"1", b"2", b"3", b"4", b"5", b"6"];

    pub fn zipper_indexed_bytes_test1<Z: ZipperMoving + ZipperPath>(mut zip: Z) {
        zip.descend_to("2");
        assert_eq!(zip.is_val(), true);
        assert_eq!(zip.child_count(), 0);
        assert_eq!(zip.descend_indexed_byte(1), None);
        assert_eq!(zip.path(), b"2");

        zip.reset();
        assert_eq!(zip.descend_indexed_byte(2), Some(b'2'));
        assert_eq!(zip.is_val(), true);
        assert_eq!(zip.child_count(), 0);
        assert_eq!(zip.path(), b"2");
        assert_eq!(zip.descend_indexed_byte(1), None);
        assert_eq!(zip.path(), b"2");

        zip.reset();
        assert_eq!(zip.descend_indexed_byte(7), None);
        assert_eq!(zip.is_val(), false);
        assert_eq!(zip.child_count(), 7);
        assert_eq!(zip.path(), b"");

        // Try with a narrow deeper trie
        let keys = ["000", "1Z", "00AAA", "00AA000", "00AA00AAA"];
        let map: PathMap<()> = keys.into_iter().map(|v| (v, ())).collect();
        let mut zip = map.read_zipper();

        zip.descend_to("000");
        assert_eq!(zip.val(), Some(&()));
        assert_eq!(zip.path(), b"000");
        assert_eq!(zip.child_count(), 0);
        assert_eq!(zip.descend_indexed_byte(1), None);
        assert_eq!(zip.path(), b"000");

        zip.reset();
        assert_eq!(zip.descend_indexed_byte(2), None);
        assert_eq!(zip.child_count(), 2);
        assert_eq!(zip.descend_indexed_byte(1), Some(b'1'));
        assert_eq!(zip.path(), b"1");
        assert_eq!(zip.val(), None);
        assert_eq!(zip.child_count(), 1);
        assert_eq!(zip.descend_indexed_byte(1), None);
        assert_eq!(zip.val(), None);
        assert_eq!(zip.path(), b"1");

        zip.reset();
        assert_eq!(zip.descend_indexed_byte(0), Some(b'0'));
        assert_eq!(zip.path(), b"0");
        assert_eq!(zip.val(), None);
        assert_eq!(zip.child_count(), 1);
        assert_eq!(zip.descend_indexed_byte(1), None);
        assert_eq!(zip.val(), None);
        assert_eq!(zip.path(), b"0");
    }

    // A narrow deeper trie
    pub const ZIPPER_INDEXED_BYTE_TEST2_KEYS: &[&[u8]] = &[b"000", b"1Z", b"00AAA", b"00AA000", b"00AA00AAA"];

    pub fn zipper_indexed_bytes_test2<Z: ZipperMoving + ZipperPath>(mut zip: Z) {
        zip.descend_to("000");
        assert_eq!(zip.is_val(), true);
        assert_eq!(zip.path(), b"000");
        assert_eq!(zip.child_count(), 0);
        assert_eq!(zip.descend_indexed_byte(1), None);
        assert_eq!(zip.path(), b"000");

        zip.reset();
        assert_eq!(zip.descend_indexed_byte(2), None);
        assert_eq!(zip.child_count(), 2);
        assert_eq!(zip.descend_indexed_byte(1), Some(b'1'));
        assert_eq!(zip.path(), b"1");
        assert_eq!(zip.is_val(), false);
        assert_eq!(zip.child_count(), 1);
        assert_eq!(zip.descend_indexed_byte(1), None);
        assert_eq!(zip.is_val(), false);
        assert_eq!(zip.path(), b"1");

        zip.reset();
        assert_eq!(zip.descend_indexed_byte(0), Some(b'0'));
        assert_eq!(zip.path(), b"0");
        assert_eq!(zip.is_val(), false);
        assert_eq!(zip.child_count(), 1);
        assert_eq!(zip.descend_indexed_byte(1), None);
        assert_eq!(zip.is_val(), false);
        assert_eq!(zip.path(), b"0");
    }

    // Tests how descend_until treats values along paths
    pub const ZIPPER_DESCEND_UNTIL_TEST1_KEYS: &[&[u8]] = &[b"a", b"ab", b"abCDEf", b"abCDEfGHi"];

    pub fn zipper_descend_until_test1<Z: ZipperMoving + ZipperPath>(mut zip: Z) {
        for key in ZIPPER_DESCEND_UNTIL_TEST1_KEYS {
            assert!(zip.descend_until());
            assert_eq!(zip.path(), *key);
        }
    }

    // Tests how descend_until_max_bytes enforces a max descent length
    pub const ZIPPER_DESCEND_UNTIL_MAX_BYTES_TEST1_KEYS: &[&[u8]] = &[b"a0abcdef", b"a0abcxy", b"a1mnopqr"];

    pub fn zipper_descend_until_max_bytes_test1<Z: ZipperMoving + ZipperPath>(mut zip: Z) {
        zip.descend_to(b"a0");
        assert_eq!(zip.path(), b"a0");
        assert!(zip.descend_until_max_bytes(2));
        assert_eq!(zip.path(), b"a0ab");

        zip.reset();
        zip.descend_to(b"a1");
        assert_eq!(zip.path(), b"a1");
        assert!(zip.descend_until_max_bytes(3));
        assert_eq!(zip.path(), b"a1mno");

        zip.reset();
        zip.descend_to(b"a0");
        assert_eq!(zip.path(), b"a0");
        assert!(zip.descend_until_max_bytes(10));
        assert_eq!(zip.path(), b"a0abc");

        zip.reset();
        zip.descend_to(b"a0");
        assert_eq!(zip.path(), b"a0");
        assert!(!zip.descend_until_max_bytes(0));
        assert_eq!(zip.path(), b"a0");
    }

    // Test a 3-way branch, so we definitely don't have a pair node
    pub const ZIPPER_ASCEND_UNTIL_TEST1_KEYS: &[&[u8]] = &[b"AAa", b"AAb", b"AAc"];

    pub fn zipper_ascend_until_test1<Z: ZipperMoving + ZipperPath>(mut zip: Z) {
        zip.descend_to(b"AAaDDd");
        assert!(!zip.path_exists());
        assert_eq!(zip.path(), b"AAaDDd");
        assert_eq!(zip.depth(), zip.path().len());
        assert_eq!(zip.ascend_until(), 3);
        assert_eq!(zip.path(), b"AAa");
        assert_eq!(zip.depth(), zip.path().len());
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"AA");
        assert_eq!(zip.depth(), zip.path().len());
        assert_eq!(zip.ascend_until(), 2);
        assert_eq!(zip.path(), b"");
        assert_eq!(zip.depth(), 0);
        assert_eq!(zip.ascend_until(), 0);
    }

    // Test what's likely to be represented as a pair node
    pub const ZIPPER_ASCEND_UNTIL_TEST2_KEYS: &[&[u8]] = &[b"AAa", b"AAb"];

    pub fn zipper_ascend_until_test2<Z: ZipperMoving + ZipperPath>(mut zip: Z) {
        zip.descend_to(b"AAaDDd");
        assert!(!zip.path_exists());
        assert_eq!(zip.path(), b"AAaDDd");
        assert_eq!(zip.ascend_until(), 3);
        assert_eq!(zip.path(), b"AAa");
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"AA");
        assert_eq!(zip.ascend_until(), 2);
        assert_eq!(zip.path(), b"");
        assert_eq!(zip.ascend_until(), 0);
    }

    /// Test a straight-line trie
    pub const ZIPPER_ASCEND_UNTIL_TEST3_KEYS: &[&[u8]] = &[b"1", b"12", b"123", b"1234", b"12345"];

    pub fn zipper_ascend_until_test3<Z: ZipperMoving + ZipperPath>(mut zip: Z) {

        //First test that ascend_until stops when transitioning from non-existent path
        zip.descend_to(b"123456");
        assert_eq!(zip.path_exists(), false);
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"12345");

        //Test that ascend_until stops at each value
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"1234");
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"123");
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"12");
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"1");
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"");
        assert_eq!(zip.ascend_until(), 0);
        assert!(zip.at_root());

        //Test that ascend_until_branch skips over all the values
        zip.descend_to(b"12345");
        assert!(zip.path_exists());
        assert_eq!(zip.path(), b"12345");
        assert_eq!(zip.ascend_until_branch(), 5);
        assert_eq!(zip.path(), b"");
        assert!(zip.at_root());

        //Try with some actual branches in the trie.
        //Some paths encountered will be values only, some will be branches only, and some will be both
        let keys = ["1", "123", "12345", "1abc", "1234abc"];
        let map: PathMap<()> = keys.into_iter().map(|v| (v, ())).collect();
        let mut zip = map.read_zipper();

        zip.descend_to(b"12345");
        assert!(zip.path_exists());
        assert_eq!(zip.path(), b"12345");
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"1234"); // "1234" is a branch only
        assert_eq!(zip.is_val(), false);
        assert_eq!(zip.child_count(), 2);
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"123"); // "123" is a value only
        assert_eq!(zip.child_count(), 1);
        assert_eq!(zip.is_val(), true);
        assert_eq!(zip.ascend_until(), 2); // Jump over "12" because it's neither a branch nor a value
        assert_eq!(zip.path(), b"1"); // "1" is both a branch and a value
        assert_eq!(zip.is_val(), true);
        assert_eq!(zip.child_count(), 2);
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"");
        assert_eq!(zip.child_count(), 1);
        assert_eq!(zip.ascend_until(), 0);
        assert!(zip.at_root());

        //Test that ascend_until_branch skips over all the values
        zip.descend_to(b"12345");
        assert!(zip.path_exists());
        assert_eq!(zip.ascend_until_branch(), 1);
        assert_eq!(zip.path(), b"1234");
        assert_eq!(zip.ascend_until_branch(), 3);
        assert_eq!(zip.path(), b"1");
        assert_eq!(zip.ascend_until_branch(), 1);
        assert_eq!(zip.path(), b"");
        assert_eq!(zip.ascend_until_branch(), 0);
        assert!(zip.at_root());
    }

    /// Test a trie with some actual branches
    /// Some paths encountered will be values only, some will be branches only, and some will be both
    pub const ZIPPER_ASCEND_UNTIL_TEST4_KEYS: &[&[u8]] = &[b"1", b"123", b"12345", b"1abc", b"1234abc"];

    pub fn zipper_ascend_until_test4<Z: ZipperMoving + ZipperPath>(mut zip: Z) {

        zip.descend_to(b"12345");
        assert!(zip.path_exists());
        assert_eq!(zip.path(), b"12345");
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"1234"); // "1234" is a branch only
        assert_eq!(zip.is_val(), false);
        assert_eq!(zip.child_count(), 2);
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"123"); // "123" is a value only
        assert_eq!(zip.child_count(), 1);
        assert_eq!(zip.is_val(), true);
        assert_eq!(zip.ascend_until(), 2); // Jump over "12" because it's neither a branch nor a value
        assert_eq!(zip.path(), b"1"); // "1" is both a branch and a value
        assert_eq!(zip.is_val(), true);
        assert_eq!(zip.child_count(), 2);
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"");
        assert_eq!(zip.child_count(), 1);
        assert_eq!(zip.ascend_until(), 0);
        assert!(zip.at_root());

        //Test that ascend_until_branch skips over all the values
        zip.descend_to(b"12345");
        assert!(zip.path_exists());
        assert_eq!(zip.ascend_until_branch(), 1);
        assert_eq!(zip.path(), b"1234");
        assert_eq!(zip.ascend_until_branch(), 3);
        assert_eq!(zip.path(), b"1");
        assert_eq!(zip.ascend_until_branch(), 1);
        assert_eq!(zip.path(), b"");
        assert_eq!(zip.ascend_until_branch(), 0);
        assert!(zip.at_root());
    }

    /// Test ascending over a long key that spans multiple nodes
    pub const ZIPPER_ASCEND_UNTIL_TEST5_KEYS: &[&[u8]] = &[b"A", b"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA"];

    pub fn zipper_ascend_until_test5<Z: ZipperMoving + ZipperPath>(mut zip: Z) {

        //Test that ascend_until stops when transitioning from non-existent path
        zip.descend_to(b"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB");
        assert_eq!(zip.path_exists(), false);
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA");

        //Test that jump all the way back to where we want to be
        assert_eq!(zip.ascend_until(), 126);
        assert_eq!(zip.path(), b"A");
        assert_eq!(zip.ascend_until(), 1);
        assert_eq!(zip.path(), b"");
        assert_eq!(zip.ascend_until(), 0);
    }

    pub const ZIPPER_INDEXED_MOVEMENT_TEST1_KEYS: &[&[u8]] = &[b"arrow", b"bow", b"cannon", b"romane", b"romanus", b"romulus", b"rubens", b"ruber", b"rubicon", b"rubicundus", b"rom'i"];

    pub fn indexed_zipper_movement1<Z: ZipperMoving + ZipperPath>(mut zipper: Z) {
        //descends a single specific byte using `descend_indexed_byte`. Just for testing. A real user would use `descend_to` or `descend_to_byte`
        fn descend_byte<Z: Zipper + ZipperMoving + ZipperPath>(zipper: &mut Z, byte: u8) {
            for i in 0..zipper.child_count() {
                let descended = zipper.descend_indexed_byte(i);
                assert!(descended.is_some());
                if *zipper.path().last().unwrap() == byte {
                    break
                } else {
                    assert_eq!(zipper.ascend(1), 1);
                }
            }
        }

        assert_eq!(zipper.path(), b"");
        assert_eq!(zipper.child_count(), 4);
        descend_byte(&mut zipper, b'r');
        assert_eq!(zipper.path(), b"r");
        assert_eq!(zipper.child_count(), 2);
        assert_eq!(zipper.descend_until(), false);
        descend_byte(&mut zipper, b'o');
        assert_eq!(zipper.path(), b"ro");
        assert_eq!(zipper.child_count(), 1);
        assert_eq!(zipper.descend_until(), true);
        assert_eq!(zipper.path(), b"rom");
        assert_eq!(zipper.child_count(), 3);

        zipper.reset();
        assert_eq!(zipper.descend_until(), false);
        descend_byte(&mut zipper, b'a');
        assert_eq!(zipper.path(), b"a");
        assert_eq!(zipper.child_count(), 1);
        assert_eq!(zipper.descend_until(), true);
        assert_eq!(zipper.path(), b"arrow");
        assert_eq!(zipper.child_count(), 0);

        assert_eq!(zipper.ascend(3), 3);
        assert_eq!(zipper.path(), b"ar");
        assert_eq!(zipper.child_count(), 1);
    }

    pub const ZIPPER_VALUE_LOCATIONS_TEST1_KEYS: &[&[u8]] = &[b"arrow", b"bow", b"cannon", b"roman", b"romane", b"romanus", b"romulus", b"rubens", b"ruber", b"rubicon", b"rubicundus", b"rom'i"];

    pub fn zipper_value_locations<Z: ZipperMoving>(mut zipper: Z) {

        zipper.descend_to(b"ro");
        assert!(zipper.path_exists());
        assert_eq!(zipper.is_val(), false);
        zipper.descend_to(b"mulus");
        assert_eq!(zipper.is_val(), true);

        zipper.reset();
        zipper.descend_to(b"roman");
        assert!(zipper.path_exists());
        assert_eq!(zipper.is_val(), true);
        zipper.descend_to(b"e");
        assert_eq!(zipper.is_val(), true);
        assert_eq!(zipper.ascend(1), 1);
        zipper.descend_to(b"u");
        assert_eq!(zipper.is_val(), false);
        zipper.descend_until();
        assert_eq!(zipper.is_val(), true);
    }

    pub const ZIPPER_CHILD_MASK_TEST1_KEYS: &[&[u8]] = &[&[8, 194, 1, 45, 194, 1], &[34, 193]];

    pub fn zipper_child_mask_test1<Z: ZipperMoving>(mut zipper: Z) {

        zipper.descend_to(&[8, 194, 1]);
        assert_eq!(zipper.path_exists(), true);
        assert_eq!(zipper.child_count(), 1);
        assert_eq!(zipper.child_mask(), [0x200000000000, 0, 0, 0]);

        zipper.reset();
        zipper.descend_to(&[8, 194, 1, 45]);
        assert_eq!(zipper.path_exists(), true);
        assert_eq!(zipper.child_count(), 1);
        assert_eq!(zipper.child_mask(), [0, 0, 0, 0x4]);
    }

    pub const ZIPPER_CHILD_MASK_TEST2_KEYS: &[&[u8]] = &[b"arrow", b"bow", b"cannon", b"roman", b"romane", b"romanus", b"romulus", b"rubens", b"ruber", b"rubicon", b"rubicundus", b"rom'i"];

    pub fn zipper_child_mask_test2<Z: ZipperMoving>(mut zipper: Z) {

        //'a' + 'b' + 'c' + 'r'
        assert_eq!(zipper.child_mask(), [0, 1<<(b'a'-64) | 1<<(b'b'-64) | 1<<(b'c'-64) | 1<<(b'r'-64), 0, 0]);

        let mut i = 0;
        while zipper.to_next_step() {
            match i {
                //'r' descending from 'a' in "arrow"
                0 => assert_eq!(zipper.child_mask(), [0, 1<<(b'r'-64), 0, 0]),
                //'r' descending from "ar" in "arrow"
                1 => assert_eq!(zipper.child_mask(), [0, 1<<(b'r'-64), 0, 0]),
                //'o' descending from "arr" in "arrow"
                2 => assert_eq!(zipper.child_mask(), [0, 1<<(b'o'-64), 0, 0]),
                //'w' descending from "arro" in "arrow"
                3 => assert_eq!(zipper.child_mask(), [0, 1<<(b'w'-64), 0, 0]),
                //leaf node, "arrow"
                4 => assert_eq!(zipper.child_mask(), [0, 0, 0, 0]),
                //'o' + 'u' descending from 'r' in "roman", "rubens", etc.
                14 => assert_eq!(zipper.child_mask(), [0, 1<<(b'o'-64) | 1<<(b'u'-64), 0, 0]),
                _ => {}
            }
            i += 1;
        }
    }

    pub const ZIPPER_DESCEND_TO_EXISTING_TEST1_KEYS: &[&[u8]] = &[b"arrow", b"bow", b"cannon", b"roman", b"romane", b"romanus", b"romulus", b"rubens", b"ruber", b"rubicon", b"rubicundus", b"rom'i"];

    pub fn descend_to_existing_test1<Z: ZipperMoving + ZipperPath>(mut zipper: Z) {

        assert_eq!(3, zipper.descend_to_existing("bowling"));
        assert_eq!("bow".as_bytes(), zipper.path());
        zipper.reset();

        assert_eq!(3, zipper.descend_to_existing("can"));
        assert_eq!("can".as_bytes(), zipper.path());
        zipper.reset();

        assert_eq!(0, zipper.descend_to_existing(""));
        assert_eq!("".as_bytes(), zipper.path());
        zipper.reset();
    }

    pub const ZIPPER_DESCEND_TO_EXISTING_TEST2_KEYS: &[&[u8]] = &[b"arrow"];

    /// Tests a really long path that doesn't exist, to exercise the chunk-descending code
    pub fn descend_to_existing_test2<Z: ZipperMoving + ZipperPath>(mut zipper: Z) {

        assert_eq!(5, zipper.descend_to_existing("arrow0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"));
        assert_eq!(zipper.path(), &b"arrow"[..]);
        zipper.reset();

        assert_eq!(3, zipper.descend_to_existing("arr0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000"));
        assert_eq!(zipper.path(), &b"arr"[..]);
    }

    pub const ZIPPER_DESCEND_TO_EXISTING_TEST3_KEYS: &[&[u8]] = &[b"arrow"];

    /// Tests calling the method when the focus is already on a non-existent path
    pub fn descend_to_existing_test3<Z: ZipperMoving + ZipperPath>(mut zipper: Z) {

        zipper.descend_to("arrow00000");
        assert_eq!(false, zipper.path_exists());
        assert_eq!(zipper.path(), &b"arrow00000"[..]);

        assert_eq!(0, zipper.descend_to_existing("0000"));
        assert_eq!(zipper.path(), &b"arrow00000"[..]);
    }

    pub const ZIPPER_TO_NEXT_STEP_TEST1_KEYS: &[&[u8]] = &[b"arrow", b"bow", b"cannon", b"roman", b"romane", b"romanus", b"romulus", b"rubens", b"ruber", b"rubicon", b"rubicundus", b"rom'i"];

    pub fn to_next_step_test1<Z: ZipperMoving + ZipperPath>(mut zipper: Z) {
        let mut i = 0;
        let mut observed = Vec::<u8>::new();
        while zipper.to_next_step_observed(&mut observed) {
            assert_eq!(&observed[..], zipper.path(), "observer disagreed with path at step {i}");
            match i {
                0 => assert_eq!(zipper.path(), b"a"),
                4 => assert_eq!(zipper.path(), b"arrow"),
                5 => assert_eq!(zipper.path(), b"b"),
                7 => assert_eq!(zipper.path(), b"bow"),
                8 => assert_eq!(zipper.path(), b"c"),
                13 => assert_eq!(zipper.path(), b"cannon"),
                14 => assert_eq!(zipper.path(), b"r"),
                18 => assert_eq!(zipper.path(), b"rom'i"),
                20 => assert_eq!(zipper.path(), b"roman"),
                21 => assert_eq!(zipper.path(), b"romane"),
                23 => assert_eq!(zipper.path(), b"romanus"),
                24 => assert_eq!(zipper.path(), b"romu"),
                25 => assert_eq!(zipper.path(), b"romul"),
                26 => assert_eq!(zipper.path(), b"romulu"),
                27 => assert_eq!(zipper.path(), b"romulus"),
                28 => assert_eq!(zipper.path(), b"ru"),
                32 => assert_eq!(zipper.path(), b"rubens"),
                33 => assert_eq!(zipper.path(), b"ruber"),
                37 => assert_eq!(zipper.path(), b"rubicon"),
                42 => assert_eq!(zipper.path(), b"rubicundus"),
                _ => {}
            }
            i += 1;
        }
    }

    pub const ZIPPER_BYTES_ITER_TEST1_KEYS: &[&[u8]] = &[b"ABCDEFGHIJKLMNOPQRSTUVWXYZ", b"ab",];

    pub fn zipper_byte_iter_test1<Z: ZipperMoving + ZipperPath>(mut zipper: Z) {

        zipper.descend_to_byte(b'A');
        assert_eq!(zipper.path_exists(), true);
        assert_eq!(zipper.descend_first_byte(), Some(b'B'));
        assert_eq!(zipper.path(), b"AB");
        assert_eq!(zipper.to_next_sibling_byte(), None);
        assert_eq!(zipper.path(), b"AB");
    }

    pub const ZIPPER_BYTES_ITER_TEST2_KEYS: &[&[u8]] = &[&[2, 194, 1, 1, 193, 5], &[3, 194, 1, 0, 193, 6, 193, 5], &[3, 193, 4, 193]];
    pub const ZIPPER_BYTES_ITER_TEST2_PATH: &[u8] = &[2, 194];

    pub fn zipper_byte_iter_test2<Z: ZipperMoving + ZipperPath>(mut zipper: Z) {
        assert_eq!(zipper.descend_first_byte(), Some(1));
        assert_eq!(zipper.path(), &[1]);
        assert_eq!(zipper.to_next_sibling_byte(), None);
        assert_eq!(zipper.path(), &[1]);
    }

    pub const ZIPPER_BYTES_ITER_TEST3_KEYS: &[&[u8]] = &[&[3, 193, 4, 193, 5, 2, 193, 6, 193, 7], &[3, 193, 4, 193, 5, 2, 193, 6, 255]];
    pub const ZIPPER_BYTES_ITER_TEST3_PATH: &[u8] = &[3, 193, 4, 193, 5, 2, 193];

    pub fn zipper_byte_iter_test3<Z: ZipperMoving + ZipperPath>(mut zipper: Z) {
        assert_eq!(zipper.path(), &[]);
        assert_eq!(zipper.descend_first_byte(), Some(6));
        assert_eq!(zipper.path(), &[6]);
        assert_eq!(zipper.descend_first_byte(), Some(193));
        assert_eq!(zipper.path(), &[6, 193]);
        assert_eq!(zipper.descend_first_byte(), Some(7));
        assert_eq!(zipper.path(), &[6, 193, 7]);
    }

    pub const ZIPPER_BYTES_ITER_TEST4_KEYS: &[&[u8]] = &[b"ABC", b"ABCDEF", b"ABCdef"];

    pub fn zipper_byte_iter_test4<Z: ZipperMoving + ZipperPath>(mut zipper: Z) {

        //Check that we end up at the first leaf by depth-first search
        while zipper.descend_first_byte().is_some() {}
        assert_eq!(zipper.path(), b"ABCDEF");

        //Try taking a different branch
        zipper.reset();
        zipper.descend_to(b"ABC");
        assert!(zipper.path_exists());
        assert_eq!(zipper.path(), b"ABC");
        assert_eq!(zipper.descend_indexed_byte(1), Some(b'd'));
        assert_eq!(zipper.path(), b"ABCd");
        assert_eq!(zipper.descend_first_byte(), Some(b'e'));
        assert_eq!(zipper.path(), b"ABCde");
        assert_eq!(zipper.descend_first_byte(), Some(b'f'));
        assert_eq!(zipper.path(), b"ABCdef");
        assert_eq!(zipper.descend_first_byte(), None);
    }

    pub const ZIPPER_BYTES_ITER_TEST5_KEYS: &[&[u8]] = &[
        &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 75, 192, 3, 193, 84, 192, 3, 193, 75, 128, 131, 193, 49],
        &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 84, 3, 193, 75, 192, 192, 3, 193, 75, 128, 131, 193, 49],
        &[2, 197, 97, 120, 255, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 84, 3, 193, 75, 192, 192, 3, 193, 75, 128, 131, 193, 49],
    ];

    pub fn zipper_byte_iter_test5<Z: ZipperMoving>(mut zipper: Z) {

        let keys = ZIPPER_BYTES_ITER_TEST5_KEYS;
        for i in 0..keys[0].len() {
            zipper.reset();
            zipper.descend_to(&keys[0][..i]);
            if i != 18 && i != 5 {
                assert_eq!(zipper.to_next_sibling_byte(), None);
            }
        }

        zipper.reset();
        zipper.descend_to([2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 75]);
        assert_eq!(zipper.to_next_sibling_byte(), Some(84));
        zipper.reset();
        zipper.descend_to([2, 197, 97, 120, 105]);
        assert_eq!(zipper.to_next_sibling_byte(), Some(255));
    }

    pub const ZIPPER_VAL_AT_TEST_KEYS: &[&[u8]] = &[
        b"arrow", b"bow", b"cannon", b"roman", b"romane", b"romanus",
        b"romulus", b"rubens", b"ruber", b"rubicon", b"rubicundus", b"rom'i",
    ];

    pub fn zipper_val_at_test<Z: ZipperMoving + ZipperValues<()>>(mut zipper: Z) {
        assert_eq!(zipper.val_at(b""), None);
        assert_eq!(zipper.val_at(b"roman"), Some(&()));
        assert_eq!(zipper.val_at(b"romane"), Some(&()));
        assert_eq!(zipper.val_at(b"roma"), None);
        assert_eq!(zipper.val_at(b"romanu"), None);
        assert_eq!(zipper.val_at(b"ruber"), Some(&()));
        assert_eq!(zipper.val_at(b"rub"), None);
        assert_eq!(zipper.val_at(b"zzz"), None);

        zipper.descend_to(b"ro");
        assert!(zipper.path_exists());
        assert_eq!(zipper.val_at(b""), None);
        assert_eq!(zipper.val_at(b"m"), None);
        assert_eq!(zipper.val_at(b"man"), Some(&()));
        assert_eq!(zipper.val_at(b"mane"), Some(&()));
        assert_eq!(zipper.val_at(b"manus"), Some(&()));
        assert_eq!(zipper.val_at(b"manu"), None);
        assert_eq!(zipper.val_at(b"mulus"), Some(&()));
        assert_eq!(zipper.val_at(b"mulu"), None);
        assert_eq!(zipper.val_at(b"zz"), None);

        zipper.descend_to(b"man");
        assert!(zipper.path_exists());
        assert_eq!(zipper.val_at(b""), Some(&()));
        assert_eq!(zipper.val_at(b"e"), Some(&()));
        assert_eq!(zipper.val_at(b"us"), Some(&()));
        assert_eq!(zipper.val_at(b"u"), None);
        assert_eq!(zipper.val_at(b"zz"), None);

        zipper.reset();
        zipper.descend_to(b"romanx");
        assert!(!zipper.path_exists());
        assert_eq!(zipper.val_at(b""), None);
        assert_eq!(zipper.val_at(b"e"), None);
    }

    pub fn zipper_val_at_long_path_test_key() -> Vec<u8> {
        let mut key = b"rom".to_vec();
        key.extend((0..(MAX_NODE_KEY_BYTES * 2 + 17)).map(|i| b'a' + (i % 26) as u8));
        key
    }

    pub fn zipper_val_at_long_path_test<Z: ZipperMoving + ZipperValues<()>>(mut zipper: Z) {
        let long_key = zipper_val_at_long_path_test_key();
        let relative_long_suffix = &long_key[3..];
        let almost_full_suffix = &relative_long_suffix[..relative_long_suffix.len()-1];

        assert_eq!(relative_long_suffix.len() > MAX_NODE_KEY_BYTES, true);
        assert_eq!(zipper.val_at(&long_key), Some(&()));

        zipper.descend_to(b"rom");
        assert!(zipper.path_exists());
        assert_eq!(zipper.val_at(relative_long_suffix), Some(&()));
        assert_eq!(zipper.val_at(almost_full_suffix), None);
        assert_eq!(zipper.val_at(b"zzz"), None);
    }

}

/// Implements tests that apply to all [ZipperIteration] types
#[cfg(test)]
pub(crate) mod zipper_iteration_tests {
    use super::*;

    /// `$ident` is a unique identifier for the zipper, so the generated tests don't collide
    /// `$read_keys` is a function that will create a store containing all paths, from which a zipper can be created
    /// `$make_z` is a function that will create a zipper from a slice of paths
    macro_rules! zipper_iteration_tests {
        ($z_name:ident, $read_keys:expr, $make_z:expr)=>{
            paste::paste! {
                #[test]
                fn [<$z_name _zipper_iter_test1>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_iteration_tests::ZIPPER_ITER_TEST1_KEYS);
                    crate::zipper::zipper_iteration_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_iteration_tests::zipper_iter_test1)
                }

                #[test]
                fn [<$z_name _zipper_iter_test2>]() {
                    let paths = crate::zipper::zipper_iteration_tests::zipper_iter_test2_paths();
                    let path_refs: Vec<&[u8]> = paths.iter().map(|path| &path[..]).collect();
                    let mut temp_store = $read_keys(&path_refs[..]);
                    crate::zipper::zipper_iteration_tests::run_test(&mut temp_store, $make_z, b"in", crate::zipper::zipper_iteration_tests::zipper_iter_test2)
                }

                #[test]
                fn [<$z_name _k_path_test1>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_iteration_tests::K_PATH_TEST1_KEYS);
                    crate::zipper::zipper_iteration_tests::run_test(&mut temp_store, $make_z, b":", crate::zipper::zipper_iteration_tests::k_path_test1)
                }

                #[test]
                fn [<$z_name _k_path_test2>]() {
                    let paths = crate::zipper::zipper_iteration_tests::k_path_test2_paths();
                    let path_refs: Vec<&[u8]> = paths.iter().map(|path| &path[..]).collect();
                    let mut temp_store = $read_keys(&path_refs[..]);
                    crate::zipper::zipper_iteration_tests::run_test(&mut temp_store, $make_z, &[], crate::zipper::zipper_iteration_tests::k_path_test2)
                }

                #[test]
                fn [<$z_name _k_path_test3>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_iteration_tests::K_PATH_TEST3_KEYS);
                    crate::zipper::zipper_iteration_tests::run_test(&mut temp_store, $make_z, b":", crate::zipper::zipper_iteration_tests::k_path_test3)
                }

                #[test]
                fn [<$z_name _k_path_test4>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_iteration_tests::K_PATH_TEST4_KEYS);
                    crate::zipper::zipper_iteration_tests::run_test(&mut temp_store, $make_z, b"", crate::zipper::zipper_iteration_tests::k_path_test4)
                }

                #[test]
                fn [<$z_name _k_path_test5>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_iteration_tests::K_PATH_TEST5_KEYS);
                    crate::zipper::zipper_iteration_tests::run_test(&mut temp_store, $make_z, b"", crate::zipper::zipper_iteration_tests::k_path_test5)
                }

                #[test]
                fn [<$z_name _k_path_test6>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_iteration_tests::K_PATH_TEST6_KEYS);
                    crate::zipper::zipper_iteration_tests::run_test(&mut temp_store, $make_z, b"", crate::zipper::zipper_iteration_tests::k_path_test6)
                }

                #[test]
                fn [<$z_name _k_path_test7>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_iteration_tests::K_PATH_TEST7_KEYS);
                    crate::zipper::zipper_iteration_tests::run_test(&mut temp_store, $make_z, b"", crate::zipper::zipper_iteration_tests::k_path_test7)
                }

                #[test]
                fn [<$z_name _k_path_test8>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_iteration_tests::K_PATH_TEST8_KEYS);
                    crate::zipper::zipper_iteration_tests::run_test(&mut temp_store, $make_z, b"", crate::zipper::zipper_iteration_tests::k_path_test8)
                }

                #[test]
                fn [<$z_name _k_path_test9>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_iteration_tests::K_PATH_TEST9_KEYS);
                    crate::zipper::zipper_iteration_tests::run_test(&mut temp_store, $make_z, &[2, 194], crate::zipper::zipper_iteration_tests::k_path_test9)
                }

                #[test]
                fn [<$z_name _k_path_testa>]() {
                    let mut temp_store = $read_keys(crate::zipper::zipper_iteration_tests::K_PATH_TESTA_KEYS);
                    crate::zipper::zipper_iteration_tests::run_test(&mut temp_store, $make_z, b"", crate::zipper::zipper_iteration_tests::k_path_testa)
                }
            }
        }
    }
    pub(crate) use zipper_iteration_tests;

    /// Internal method to provide a lifetime bound on the macro arguments to the test macro
    pub fn run_test<'a, T: 'a + ZipperIteration, Store>(
        store: &'a mut Store,
        make_t: impl Fn(&'a mut Store, &[u8]) -> T,
        z_path: &[u8],
        test_f: impl Fn(T)
    ) {
        let t = make_t(store, z_path);
        test_f(t);
    }

    pub const ZIPPER_ITER_TEST1_KEYS: &[&[u8]] = &[b"arrow", b"bow", b"cannon", b"rom'i", b"roman", b"romane", b"romanus", b"romulus", b"rubens", b"ruber", b"rubicon", b"rubicundus"];

    /// Simply calls `to_next_val` over the whole trie, ensuring all paths are visited exactly once
    pub fn zipper_iter_test1<'a, Z: ZipperIteration + ZipperPath>(mut zipper: Z) {
        let keys = ZIPPER_ITER_TEST1_KEYS;

        //Test iteration of the whole tree
        let mut idx = 0;
        let mut observed = Vec::<u8>::new();
        assert_eq!(zipper.is_val(), false);
        while zipper.to_next_val_observed(&mut observed) {
            println!("{idx}  {}", std::str::from_utf8(zipper.path()).unwrap());
            assert_eq!(keys[idx], zipper.path());
            assert_eq!(&observed[..], zipper.path(), "observer disagreed with path at value {idx}");
            idx += 1;
        }
        assert_eq!(idx, keys.len());
    }

    const ZIPPER_ITER_TEST2_COUNT: usize = 32;
    pub fn zipper_iter_test2_paths() -> Vec<Vec<u8>> {
        (0usize..ZIPPER_ITER_TEST2_COUNT).into_iter().map(|i| {
            [b"in", &i.to_be_bytes()[..]].concat()
        }).collect()
    }

    pub fn zipper_iter_test2<'a, Z: ZipperIteration + ZipperPath>(mut zipper: Z) {

        //Test iterating using a zipper that has a root that is not the map root
        let mut count: usize = 0;
        let mut observed = Vec::<u8>::new();
        while zipper.to_next_val_observed(&mut observed) {
            assert_eq!(zipper.is_val(), true);
            assert_eq!(zipper.path(), count.to_be_bytes());
            assert_eq!(&observed[..], zipper.path(), "observer disagreed with path at value {count}");
            count += 1;
        }
        assert_eq!(count, ZIPPER_ITER_TEST2_COUNT);
    }

    /// This is a toy encoding where `:n:` precedes a symbol `n` characters long
    pub const K_PATH_TEST1_KEYS: &[&[u8]] = &[
        b":5:above:3:the:4:fray:",
        b":5:err:",
        b":5:erronious:6:potato:",
        b":5:error:2:is:2:my:4:name:",
        b":5:hello:5:world:",
        b":5:mucky:4:muck:",
        b":5:roger:6:rabbit:",
        b":5:zebra:",
        b":9:muckymuck:5:raker:",
    ];

    pub fn k_path_test1<'a, Z: ZipperIteration + ZipperPath>(mut zipper: Z) {

        //This is a cheesy way to encode lengths, but it's is more readable than unprintable chars
        assert!(zipper.descend_indexed_byte(0).is_some());
        let sym_len = usize::from_str_radix(std::str::from_utf8(&[zipper.path()[0]]).unwrap(), 10).unwrap();
        assert_eq!(sym_len, 5);

        //Step over the ':' character
        assert!(zipper.descend_indexed_byte(0).is_some());
        assert_eq!(zipper.child_count(), 6);

        //The observer starts in sync with the zipper, and must track it through every k_path call
        let mut observed = zipper.path().to_vec();

        //Start iterating over all the symbols of length=sym_len
        assert_eq!(zipper.descend_first_k_path_observed(sym_len+1, &mut observed), true);

        //This should have taken us to "above:"
        assert_eq!(zipper.path(), b"5:above:");
        assert_eq!(&observed[..], zipper.path());

        //Go to the next symbol.
        // Two interesting things will happen.  First, we blow past "err" because its path length is
        // shorter than `k`.  Second, we will stop in the middle of "erronious".
        // These situations would be caused by an encode bug.  Which hopefully we won't have in real
        // paths. But the parser should recognize the last digit of the path isn't ':'
        assert_eq!(zipper.to_next_k_path_observed(sym_len+1, &mut observed), true);
        assert_eq!(zipper.path(), b"5:erroni");
        assert_eq!(&observed[..], zipper.path());
        assert_ne!(zipper.path().last(), Some(&b':'));

        //Now we'll move on to some correctly formed symbols
        for expected in [b"5:error:", b"5:hello:", b"5:mucky:", b"5:roger:", b"5:zebra:"] {
            assert_eq!(zipper.to_next_k_path_observed(sym_len+1, &mut observed), true);
            assert_eq!(zipper.path(), expected);
            assert_eq!(&observed[..], zipper.path());
        }

        //The last step should return false, and put us back to where we began
        assert_eq!(zipper.to_next_k_path_observed(sym_len+1, &mut observed), false);
        assert_eq!(zipper.path(), b"5:");
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.child_count(), 6);
    }

    const K_PATH_TEST2_COUNT: usize = 50;
    pub fn k_path_test2_paths() -> Vec<Vec<u8>> {
        (0..K_PATH_TEST2_COUNT).into_iter().map(|i| {
            let len = (i % 15) + 5; //length between 5 and 20 chars
            (0..len).into_iter().map(|j| ((j+i) % 255) as u8).collect()
        }).collect()
    }

    pub fn k_path_test2<'a, Z: ZipperIteration + ZipperPath>(mut zipper: Z) {

        let mut observed = Vec::<u8>::new();
        zipper.descend_first_k_path_observed(5, &mut observed);
        let mut count = 1;
        while zipper.to_next_k_path_observed(5, &mut observed) {
            assert_eq!(&observed[..], zipper.path());
            count += 1;
        }
        assert_eq!(count, K_PATH_TEST2_COUNT);
    }

    pub const K_PATH_TEST3_KEYS: &[&[u8]] = &[b":1a1A", b":1a1B", b":1a1C", b":1b1A", b":1b1B", b":1b1C", b":1c1A"];

    pub fn k_path_test3<'a, Z: ZipperIteration + ZipperPath>(mut zipper: Z) {

        //Scan over the first symbols in the path (lower case letters)
        zipper.descend_to(b"1");
        assert_eq!(zipper.path_exists(), true);
        assert_eq!(zipper.descend_first_k_path(1), true);
        assert_eq!(zipper.path(), b"1a");
        assert_eq!(zipper.to_next_k_path(1), true);
        assert_eq!(zipper.path(), b"1b");
        assert_eq!(zipper.to_next_k_path(1), true);
        assert_eq!(zipper.path(), b"1c");
        assert_eq!(zipper.to_next_k_path(1), false);
        assert_eq!(zipper.path(), b"1");

        //Scan over the nested second symbols in the path (upper case letters)
        zipper.reset();
        zipper.descend_to(b"1a1");
        assert!(zipper.path_exists());
        assert_eq!(zipper.descend_first_k_path(1), true);
        assert_eq!(zipper.path(), b"1a1A");
        assert_eq!(zipper.to_next_k_path(1), true);
        assert_eq!(zipper.path(), b"1a1B");
        assert_eq!(zipper.to_next_k_path(1), true);
        assert_eq!(zipper.path(), b"1a1C");
        assert_eq!(zipper.to_next_k_path(1), false);
        assert_eq!(zipper.path(), b"1a1");

        //Recursively scan nested symbols within a scan of the first outer symbols
        //A single observer tracks this whole nested sequence, since the only movements are k_path calls
        zipper.reset();
        zipper.descend_to(b"1");
        assert!(zipper.path_exists());
        let mut observed = zipper.path().to_vec();
        assert_eq!(zipper.descend_first_k_path_observed(1, &mut observed), true);
        assert_eq!(zipper.path(), b"1a");
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.descend_first_k_path_observed(2, &mut observed), true);
        assert_eq!(zipper.path(), b"1a1A");
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.to_next_k_path_observed(2, &mut observed), true);
        assert_eq!(zipper.path(), b"1a1B");
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.to_next_k_path_observed(2, &mut observed), true);
        assert_eq!(zipper.path(), b"1a1C");
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.to_next_k_path_observed(2, &mut observed), false);
        assert_eq!(zipper.path(), b"1a");
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.to_next_k_path_observed(1, &mut observed), true);
        assert_eq!(zipper.path(), b"1b");
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.to_next_k_path_observed(1, &mut observed), true);
        assert_eq!(zipper.path(), b"1c");
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.to_next_k_path_observed(1, &mut observed), false);
        assert_eq!(zipper.path(), b"1");
        assert_eq!(&observed[..], zipper.path());

        //Similar to above, but inter-operating with `descend_indexed_byte`
        zipper.reset();
        zipper.descend_to(b"1");
        assert!(zipper.path_exists());
        assert_eq!(zipper.descend_first_k_path(1), true);
        assert_eq!(zipper.path(), b"1a");
        assert!(zipper.descend_indexed_byte(0).is_some());
        assert_eq!(zipper.path(), b"1a1");
        assert_eq!(zipper.descend_first_k_path(1), true);
        assert_eq!(zipper.path(), b"1a1A");
        assert_eq!(zipper.to_next_k_path(1), true);
        assert_eq!(zipper.path(), b"1a1B");
        assert_eq!(zipper.to_next_k_path(1), true);
        assert_eq!(zipper.path(), b"1a1C");
        assert_eq!(zipper.to_next_k_path(1), false);
        assert_eq!(zipper.path(), b"1a1");
        assert_eq!(zipper.ascend(1), 1);
        assert_eq!(zipper.path(), b"1a");
        assert_eq!(zipper.to_next_k_path(1), true);
        assert_eq!(zipper.path(), b"1b");
        assert_eq!(zipper.to_next_k_path(1), true);
        assert_eq!(zipper.path(), b"1c");
        assert_eq!(zipper.to_next_k_path(1), false);
        assert_eq!(zipper.path(), b"1");
    }

    pub const K_PATH_TEST4_KEYS: &[&[u8]] = &[
        &[100, 74, 37, 218, 90, 211, 23, 84, 226, 59, 193, 236],
        &[199, 102, 166, 28, 234, 168, 198, 13],
        &[101, 241, 88, 163, 2, 9, 37, 110, 53, 201, 251, 164, 23, 162, 216],
        &[237, 8, 108, 15, 63, 3, 249, 78, 200, 154, 103, 191],
        &[106, 30, 34, 182, 157, 102, 126, 90, 200, 5, 93, 0, 163, 245, 112],
        &[188, 177, 13, 5, 50, 66, 169, 113, 157, 202, 72, 11, 79, 73],
        &[250, 96, 103, 31, 32, 104],
        &[100, 152, 199, 46, 48, 252, 139, 150, 158, 8, 57, 50, 123],
        &[65, 16, 128, 207, 27, 252, 145, 123, 105, 238, 230],
        &[244, 34, 40, 224, 11, 125, 102],
        &[116, 63, 105, 214, 137, 86, 202],
        &[63, 70, 201, 21, 131, 60],
        &[139, 209, 149, 73, 172, 12, 139, 80, 184, 105],
        &[253, 235, 49, 156, 40, 50, 60, 73, 145, 249],
        &[228, 81, 220, 29, 208, 234, 27],
        &[116, 109, 134, 122, 15, 78, 126, 240, 158, 42, 221, 229, 93, 200, 194],
        &[180, 216, 189, 14, 82, 14, 170, 195, 196, 42, 177, 144, 153, 156, 140, 109, 93, 78, 157],
        &[190, 6, 59, 69, 208, 253, 2, 33, 86],
        &[245, 168, 144, 122, 243, 111],
        &[123, 150, 249, 114, 32, 140, 186, 204, 199, 8, 205, 150, 34, 104, 186, 236],
        &[8, 29, 191, 189, 72, 101, 39, 24, 105, 44, 13, 87, 75, 187],
        &[14, 201, 29, 151, 113, 10, 175],
        &[83, 130, 247, 5, 250, 101, 141, 5, 42, 132, 205, 3, 118, 152, 33, 219, 1, 91, 204],
        &[207, 215, 38, 17, 244, 96],
        &[34, 132, 138, 222, 250, 162, 231, 68, 142, 162, 152, 172, 244, 102, 179, 111, 161, 95],
        &[124, 120, 11, 4, 219, 210, 172, 50, 182, 160, 86, 88, 136, 122, 97, 98],
        &[86, 74, 181, 17, 3, 173, 12],
        &[18, 234, 66, 134, 20],
        &[20, 24, 83, 219, 209, 20, 236, 128, 155, 15, 110, 54, 237, 105, 186, 62],
        &[67, 11, 50, 124, 120, 33, 218],
        &[89, 248, 169, 97, 245, 98, 230, 53, 114, 198, 227, 148, 22, 127, 198, 153, 238, 59, 223],
        &[100, 128, 38, 54, 171, 186, 9, 133, 191, 82, 113, 86, 10, 72, 236, 124, 201, 65],
        &[152, 115, 99, 124, 81, 254, 0, 179, 24, 87, 24, 77, 60],
        &[107, 117, 222, 38, 162, 193, 48, 44, 140, 162, 104, 139, 90],
        &[63, 29, 217, 85, 63, 130, 110, 121, 227, 43, 215, 223, 249, 1, 72, 134, 92, 188],
        &[117, 3, 144, 15, 103, 113, 130, 253, 0, 102, 47, 24, 234, 0, 159],
        &[38, 60, 197, 120, 53, 94, 202, 137, 116, 27, 12, 181],
        &[248, 41, 252, 254, 98, 173, 42, 92, 30, 65, 72],
        &[240, 147, 89, 110, 224, 8],
        &[199, 86, 108, 195, 62, 169, 61],
        &[93, 225, 21, 185, 91, 23, 19, 7, 108, 176, 191, 91],
        &[70, 10, 122, 77, 171],
        &[32, 161, 24, 162, 112, 152, 21, 226, 149, 253, 212, 246, 175, 182],
        &[99, 7, 213, 87, 192, 2, 110, 242, 222, 89, 20, 83, 138, 112],
        &[92, 64, 61, 35, 111, 41, 151, 121, 24, 157],
        &[115, 201, 114, 124, 135, 246, 93, 230, 210, 164, 213, 254, 108, 181, 77, 19, 103, 166],
        &[26, 231, 59, 238, 246],
        &[52, 74, 93, 202, 140, 11, 56, 46, 211, 194, 137, 65, 36, 90, 209],
        &[56, 245, 179, 40, 190, 168, 116, 115],
        &[192, 215, 69, 171, 218, 187, 202, 120, 92, 33, 14, 77, 34, 46, 40, 93, 135, 117, 152],
    ];

    pub fn k_path_test4<'a, Z: ZipperIteration + ZipperPath>(mut zipper: Z) {

        let mut observed = Vec::<u8>::new();
        zipper.descend_first_k_path_observed(5, &mut observed);
        let mut count = 1;
        while zipper.to_next_k_path_observed(5, &mut observed) {
            assert_eq!(&observed[..], zipper.path());
            count += 1;
        }
        assert_eq!(count, K_PATH_TEST4_KEYS.len());
    }

    /// This test triggers an edge-case because the first path is 15 bytes long, but
    /// `LineListNode::KEY_BYTES_CNT` is 14.  That means the path spills over to two nodes, 1 bytes
    /// before the end.  Then, we do `descend_first_k_path(2)`, meaning we end up straddling the
    /// node boundary, so `to_next_k_path(2)` needs to step back across to the parent node, and
    /// truncate the zipper's key, but not truncate too much
    pub const K_PATH_TEST5_KEYS: &[&[u8]] = &[
        &[3, 193, 4, 194, 1, 43, 3, 193, 8, 194, 1, 45, 194, 1, 46],
        &[3, 193, 4, 194, 1, 43, 3, 193, 34, 193],
    ];

    pub fn k_path_test5<'a, Z: ZipperIteration + ZipperPath>(mut zipper: Z) {
        zipper.descend_to(&[3, 193, 4, 194, 1, 43, 3, 193, 8, 194, 1, 45, 194]);
        assert!(zipper.path_exists());
        //This straddles a node boundary, so it exercises the multi-byte movement reporting
        let mut observed = zipper.path().to_vec();
        assert_eq!(zipper.descend_first_k_path_observed(2, &mut observed), true);
        assert_eq!(zipper.path(), &[3, 193, 4, 194, 1, 43, 3, 193, 8, 194, 1, 45, 194, 1, 46]);
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.to_next_k_path_observed(2, &mut observed), false);
        assert_eq!(zipper.path(), &[3, 193, 4, 194, 1, 43, 3, 193, 8, 194, 1, 45, 194]);
        assert_eq!(&observed[..], zipper.path());
    }

    pub const K_PATH_TEST6_KEYS: &[&[u8]] = &[
        &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 75, 192, 3, 193, 84, 192, 3, 193, 75, 128, 131, 193, 49],
        &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 84, 3, 193, 75, 192, 192, 3, 193, 75, 128, 131, 193, 49],
    ];

    /// This tests the k_path methods in the context of using them recursively, to shake out
    /// bugs caused by invalidating the iter token
    pub fn k_path_test6<'a, Z: ZipperIteration + ZipperPath>(mut zipper: Z) {

        fn test_loop<'a, Z: ZipperMoving + ZipperIteration + ZipperPath, AscendF: Fn(&mut Z, usize), DescendF: Fn(&mut Z, &[u8])>(zipper: &mut Z, descend_f: DescendF, ascend_f: AscendF) {
            zipper.reset();

            //L0 descent
            descend_f(zipper, &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193]);
            assert!(zipper.descend_first_k_path(1));
            assert_eq!(zipper.path(), &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 75]);

            //L1 descent
            descend_f(zipper, &[192, 3, 193, 84, 192, 3, 193]);
            assert!(zipper.descend_first_k_path(1));
            assert_eq!(zipper.path(), &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 75, 192, 3, 193, 84, 192, 3, 193, 75]);

            //L2 descent
            descend_f(zipper, &[128, 131, 193]);
            assert!(zipper.descend_first_k_path(1));
            assert_eq!(zipper.path(), &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 75, 192, 3, 193, 84, 192, 3, 193, 75, 128, 131, 193, 49]);

            //L2 next and ascent
            assert!(!zipper.to_next_k_path(1));
            assert_eq!(zipper.path(), &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 75, 192, 3, 193, 84, 192, 3, 193, 75, 128, 131, 193]);

            ascend_f(zipper, 3);

            //L1 next and ascent
            assert!(!zipper.to_next_k_path(1));
            assert_eq!(zipper.path(), &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 75, 192, 3, 193, 84, 192, 3, 193]);

            ascend_f(zipper, 7);

            //L0 next
            assert!(zipper.to_next_k_path(1));
            assert_eq!(zipper.path(), &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 84]);

            ascend_f(zipper, 17);
        }

        //Try with a `descend_to` & `ascend`
        test_loop(&mut zipper,
            |zipper, path| {
                zipper.descend_to(path);
                assert!(zipper.path_exists());
            },
            |zipper, steps| assert_eq!(zipper.ascend(steps), steps),
        );

        //Try with a `descend_to_byte` & `ascend_byte`
        test_loop(&mut zipper,
            |zipper, path| {
                for byte in path {
                    zipper.descend_to_byte(*byte);
                    assert!(zipper.path_exists());
                }
            },
            |zipper, steps| {
                for _ in 0..steps {
                    assert!(zipper.ascend_byte())
                }
            },
        );

        //Try with a `descend_first_byte` & `ascend_byte`
        test_loop(&mut zipper,
            |zipper, path| {
                for _ in 0..path.len() {
                    assert!(zipper.descend_first_byte().is_some());
                }
            },
            |zipper, steps| {
                for _ in 0..steps {
                    assert!(zipper.ascend_byte())
                }
            },
        );
    }

    pub const K_PATH_TEST7_KEYS: &[&[u8]] = &[
        &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 75, 192, 3, 193, 84, 192, 3, 193, 75, 128, 131, 193, 49],
        &[2, 197, 97, 120, 105, 111, 109, 3, 193, 61, 4, 193, 97, 192, 192, 3, 193, 84, 3, 193, 75, 192, 192, 3, 193, 75, 128, 131, 193, 49],
    ];

    /// This uses the k_path methods to descend and then re-ascend a trie, one step at a time.
    pub fn k_path_test7<'a, Z: ZipperIteration + ZipperPath>(mut zipper: Z) {
        let keys = K_PATH_TEST7_KEYS;

        //Only k_path calls move this zipper, so one observer tracks the whole descent and re-ascent
        let mut observed = Vec::<u8>::new();
        for i in 0..keys[0].len() {
            assert_eq!(zipper.path(), &keys[0][..i]);
            assert_eq!(&observed[..], zipper.path());
            assert!(zipper.descend_first_k_path_observed(1, &mut observed));
        }
        for i in (0..keys[0].len()).rev() {
            assert_eq!(zipper.path(), &keys[0][..=i]);
            assert_eq!(&observed[..], zipper.path());
            if i != 17 {
                assert!(!zipper.to_next_k_path_observed(1, &mut observed));
            } else {
                assert!(zipper.to_next_k_path_observed(1, &mut observed));
                assert!(!zipper.to_next_k_path_observed(1, &mut observed));
            }
        }
    }

    pub const K_PATH_TEST8_KEYS: &[&[u8]] = &[b"ABCDEFGHIJKLMNOPQRSTUVWXYZ", b"ab",];

    /// Tests `..k_path` after `descend_to_byte`
    pub fn k_path_test8<'a, Z: ZipperIteration + ZipperPath>(mut zipper: Z) {

        zipper.reset();
        zipper.descend_to_byte(b'A');
        assert_eq!(zipper.path_exists(), true);
        let mut observed = zipper.path().to_vec();
        assert_eq!(zipper.descend_first_k_path_observed(1, &mut observed), true);
        assert_eq!(zipper.path(), b"AB");
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.to_next_k_path_observed(1, &mut observed), false);
        assert_eq!(zipper.path(), b"A");
        assert_eq!(&observed[..], zipper.path());
    }

    pub const K_PATH_TEST9_KEYS: &[&[u8]] = &[
        &[2, 194, 1, 1, 193, 5],
        &[3, 194, 1, 0, 193, 6, 193, 5],
        &[3, 193, 4, 193],
    ];

    /// Tests `..k_path` in a subtrie without attitional branches to descend, when the outer trie does have branches
    pub fn k_path_test9<'a, Z: ZipperIteration + ZipperPath>(mut zipper: Z) {

        zipper.reset();
        let mut observed = Vec::<u8>::new();
        assert_eq!(zipper.descend_first_k_path_observed(1, &mut observed), true);
        assert_eq!(zipper.path(), &[1]);
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.to_next_k_path_observed(1, &mut observed), false);
        assert_eq!(zipper.path(), &[]);
        assert_eq!(&observed[..], zipper.path());
    }

    pub const K_PATH_TESTA_KEYS: &[&[u8]] = &[
        &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
        &[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2],
    ];

    /// Tests `..k_path` in a subtrie without attitional branches to descend, when the outer trie does have branches
    pub fn k_path_testa<'a, Z: ZipperIteration + ZipperPath>(mut zipper: Z) {
        zipper.reset();
        let mut observed = Vec::<u8>::new();
        let k = K_PATH_TESTA_KEYS[0].len();
        assert_eq!(zipper.descend_first_k_path_observed(k, &mut observed), true);
        assert_eq!(zipper.path(), K_PATH_TESTA_KEYS[0]);
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.to_next_k_path_observed(k, &mut observed), true);
        assert_eq!(zipper.path(), K_PATH_TESTA_KEYS[1]);
        assert_eq!(&observed[..], zipper.path());
        assert_eq!(zipper.to_next_k_path_observed(k, &mut observed), false);
        assert_eq!(zipper.path(), []);
        assert_eq!(&observed[..], zipper.path());
    }
}

#[cfg(test)]
mod tests {
    use crate::{alloc::global_alloc, PathMap};
    use super::*;

    /// Drives a [TruncatingObserver] with the supplied movements, returning what reached the
    /// downstream observer along with the observer's final overshoot
    fn run_truncating(limit: usize, movements: &[&[u8]]) -> (Vec<u8>, usize) {
        let mut downstream = Vec::new();
        let mut trunc = TruncatingObserver::new(&mut downstream, limit);
        for m in movements {
            trunc.descend_to(m);
        }
        let overshoot = trunc.overshoot();
        (downstream, overshoot)
    }

    #[test]
    fn truncating_observer_forwards_within_limit() {
        //Everything fits, so all of it is forwarded and nothing overshoots
        let (fwd, over) = run_truncating(10, &[b"abc", b"de"]);
        assert_eq!(fwd, b"abcde");
        assert_eq!(over, 0);
    }

    #[test]
    fn truncating_observer_stops_exactly_at_limit() {
        let (fwd, over) = run_truncating(5, &[b"abc", b"de"]);
        assert_eq!(fwd, b"abcde");
        assert_eq!(over, 0);
    }

    #[test]
    fn truncating_observer_splits_a_segment() {
        //The limit falls in the middle of the second movement
        let (fwd, over) = run_truncating(4, &[b"abc", b"de"]);
        assert_eq!(fwd, b"abcd");
        assert_eq!(over, 1);
    }

    #[test]
    fn truncating_observer_drops_whole_segments_past_limit() {
        let (fwd, over) = run_truncating(3, &[b"abc", b"de", b"fgh"]);
        assert_eq!(fwd, b"abc");
        assert_eq!(over, 5);
    }

    #[test]
    fn truncating_observer_zero_limit_forwards_nothing() {
        let (fwd, over) = run_truncating(0, &[b"abc"]);
        assert_eq!(fwd, b"");
        assert_eq!(over, 3);
    }

    #[test]
    fn truncating_observer_descend_to_byte_respects_limit() {
        let mut downstream = Vec::new();
        let mut trunc = TruncatingObserver::new(&mut downstream, 2);
        trunc.descend_to_byte(b'a');
        trunc.descend_to_byte(b'b');
        trunc.descend_to_byte(b'c');
        assert_eq!(trunc.overshoot(), 1);
        assert_eq!(downstream, b"ab");
    }

    /// An ascent that only unwinds overshoot must not be forwarded, because those bytes were
    /// never reported downstream in the first place
    #[test]
    fn truncating_observer_ascend_unwinds_overshoot_first() {
        let mut downstream = Vec::new();
        let mut trunc = TruncatingObserver::new(&mut downstream, 3);
        trunc.descend_to(b"abcde");     // forwards "abc", overshoots by 2
        assert_eq!(trunc.overshoot(), 2);
        trunc.ascend(2);                // unwinds only the overshoot
        assert_eq!(trunc.overshoot(), 0);
        assert_eq!(downstream, b"abc", "overshoot ascent must not reach downstream");
    }

    /// An ascent that eats past the overshoot must forward only the portion below the limit
    #[test]
    fn truncating_observer_ascend_straddling_the_limit() {
        let mut downstream = Vec::new();
        let mut trunc = TruncatingObserver::new(&mut downstream, 3);
        trunc.descend_to(b"abcde");     // forwards "abc", overshoots by 2
        trunc.ascend(4);                // 2 of overshoot, then 2 of forwarded
        assert_eq!(trunc.overshoot(), 0);
        assert_eq!(downstream, b"a", "only the forwarded portion should be retracted");
    }

    /// With no overshoot, an ascent passes through unchanged
    #[test]
    fn truncating_observer_ascend_without_overshoot() {
        let mut downstream = Vec::new();
        let mut trunc = TruncatingObserver::new(&mut downstream, 10);
        trunc.descend_to(b"abcde");
        trunc.ascend(2);
        assert_eq!(trunc.overshoot(), 0);
        assert_eq!(downstream, b"abc");
    }

    /// `descend_until_max_bytes`'s default impl is used by zippers with no native override.
    /// `PrefixZipper` is one, so it exercises the [TruncatingObserver] path over a real trie.
    #[test]
    fn default_descend_until_max_bytes_respects_limit() {
        use crate::prefix_zipper::PrefixZipper;

        //A single long path, so `descend_until` would run well past any small limit
        let key: Vec<u8> = (0..40u32).map(|i| b'a' + (i % 26) as u8).collect();
        let map = PathMap::from_iter([(key.as_slice(), ())]);

        for limit in [1usize, 2, 7, 39, 40, 41, 100] {
            let mut pz = PrefixZipper::new(b"", map.read_zipper());
            let mut observed = Vec::new();
            let moved = pz.descend_until_max_bytes_observed(limit, &mut observed);

            let expected_len = limit.min(key.len());
            assert_eq!(moved, true, "limit={limit}: should have descended");
            assert_eq!(pz.path().len(), expected_len,
                "limit={limit}: focus must stop at the limit");
            assert_eq!(observed, &key[..expected_len],
                "limit={limit}: observer must receive exactly the bytes descended");
            assert_eq!(observed, pz.path(),
                "limit={limit}: observer must agree with the resulting path");
        }
    }

    /// A zero limit must not move the zipper or report anything
    #[test]
    fn default_descend_until_max_bytes_zero_limit() {
        use crate::prefix_zipper::PrefixZipper;

        let map = PathMap::from_iter([(b"abcdef".as_slice(), ())]);
        let mut pz = PrefixZipper::new(b"", map.read_zipper());
        let mut observed = Vec::new();
        let moved = pz.descend_until_max_bytes_observed(0, &mut observed);

        assert_eq!(moved, false);
        assert_eq!(pz.path(), b"");
        assert_eq!(observed, b"");
    }

    super::zipper_moving_tests::zipper_moving_tests!(read_zipper,
        |keys: &[&[u8]]| {
            let mut btm = PathMap::new();
            keys.iter().for_each(|k| { btm.set_val_at(k, ()); });
            btm
        },
        |btm: &mut PathMap<()>, path: &[u8]| -> ReadZipperUntracked<()> {
            btm.read_zipper_at_path(path)
    });

    super::zipper_iteration_tests::zipper_iteration_tests!(read_zipper,
        |keys: &[&[u8]]| {
            let mut btm = PathMap::new();
            keys.iter().for_each(|k| { btm.set_val_at(k, ()); });
            btm
        },
        |btm: &mut PathMap<()>, path: &[u8]| -> ReadZipperUntracked<()> {
            btm.read_zipper_at_path(path)
    });

    super::zipper_moving_tests::zipper_moving_tests!(read_zipper_owned,
        |keys: &[&[u8]]| {
            let mut btm = PathMap::new();
            keys.iter().for_each(|k| { btm.set_val_at(k, ()); });
            btm
        },
        |btm: &mut PathMap<()>, path: &[u8]| -> ReadZipperOwned<()> {
            core::mem::take(btm).into_read_zipper(path)
    });

    super::zipper_iteration_tests::zipper_iteration_tests!(read_zipper_owned,
        |keys: &[&[u8]]| {
            let mut btm = PathMap::new();
            keys.iter().for_each(|k| { btm.set_val_at(k, ()); });
            btm
        },
        |btm: &mut PathMap<()>, path: &[u8]| -> ReadZipperOwned<()> {
            core::mem::take(btm).into_read_zipper(path)
    });

    /// Tests the integrity of values accessed through [ZipperReadOnlyValues::get_val]
    #[test]
    fn zipper_value_access() {
        let mut btm = PathMap::new();
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().for_each(|r| { btm.set_val_at(r.as_bytes(), *r); });

        let root_key = b"ro";
        let mut zipper = ReadZipperCore::new_with_node_and_path_in(btm.root().unwrap(), false, root_key, root_key.len(), 0, None, global_alloc());
        assert_eq!(zipper.is_val(), false);
        zipper.descend_to(b"mulus");
        assert_eq!(zipper.is_val(), true);
        assert_eq!(zipper.val(), Some(&"romulus"));

        let root_key = b"roman";
        let mut zipper = ReadZipperCore::new_with_node_and_path_in(btm.root().unwrap(), false, root_key, root_key.len(), 0, None, global_alloc());
        assert_eq!(zipper.is_val(), true);
        assert_eq!(zipper.val(), Some(&"roman"));
        zipper.descend_to(b"e");
        assert_eq!(zipper.is_val(), true);
        assert_eq!(zipper.val(), Some(&"romane"));
        assert_eq!(zipper.ascend(1), 1);
        zipper.descend_to(b"u");
        assert_eq!(zipper.is_val(), false);
        assert_eq!(zipper.val(), None);
        zipper.descend_until();
        assert_eq!(zipper.is_val(), true);
        assert_eq!(zipper.val(), Some(&"romanus"));
    }

    /// Tests that a zipper forked at a subtrie will iterate correctly within that subtrie, also tests ReadZipper::IntoIterator impl
    #[test]
    fn read_zipper_special_iter_test1() {
        let mut btm = PathMap::new();
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.set_val_at(r.as_bytes(), i); });
        let mut zipper = btm.read_zipper();

        //Fork a sub-zipper, and test iteration of that subtree
        zipper.descend_to(b"rub");
        let mut sub_zipper = zipper.fork_read_zipper();
        while let Some(&val) = sub_zipper.to_next_get_val() {
            // println!("{val}  {} = {}", std::str::from_utf8(sub_zipper.path()).unwrap(), std::str::from_utf8(&rs[val].as_bytes()[3..]).unwrap());
            assert_eq!(&rs[val].as_bytes()[3..], sub_zipper.path());
        }
        drop(sub_zipper);

        for (path, &val) in zipper {
            // println!("{val}  {} = {}", std::str::from_utf8(&path).unwrap(), std::str::from_utf8(rs[val].as_bytes()).unwrap());
            assert_eq!(rs[val].as_bytes(), path);
        }
    }

    /// Tests that `to_next_val` will behave correctly when the map contains dangling paths, such as those created by zipper heads
    #[test]
    fn read_zipper_special_iter_test2() {
        //This tests iteration over an empty map, with no activity at all
        let mut map = PathMap::<u64>::new();

        let mut observed = Vec::<u8>::new();
        let mut zipper = map.read_zipper();
        assert_eq!(zipper.to_next_val_observed(&mut observed), false);
        assert_eq!(zipper.to_next_val_observed(&mut observed), false);
        //A `false` return means the zipper came back to its root, so the observer must be empty
        assert_eq!(&observed[..], b"");
        drop(zipper);

        //Now test some operations that create nodes, but not values
        let map_head = map.zipper_head();
        let _wz = map_head.write_zipper_at_exclusive_path(b"0");
        drop(_wz);
        drop(map_head);

        let mut observed = Vec::<u8>::new();
        let mut zipper = map.read_zipper();
        assert_eq!(zipper.to_next_val_observed(&mut observed), false);
        assert_eq!(zipper.to_next_val_observed(&mut observed), false);
        assert_eq!(&observed[..], b"");
    }

    /// Tests iterating a subtrie created by a descended WriteZipper
    #[test]
    fn read_zipper_special_iter_test3() {
        const N: usize = 32;

        let mut map = PathMap::<usize>::new();
        let mut zipper = map.write_zipper_at_path(b"in");
        for i in 0usize..N {
            zipper.descend_to(i.to_be_bytes());
            zipper.set_val(i);
            zipper.reset();
        }
        drop(zipper);

        //Test iterating using a ReadZipper that has a root that is not the map root
        let mut reader_z = map.read_zipper_at_path(b"in");
        assert_eq!(reader_z.val_count(), N);
        let mut count = 0;
        while let Some(val) = reader_z.to_next_get_val() {
            assert_eq!(reader_z.get_val(), Some(val));
            assert_eq!(reader_z.get_val(), Some(&count));
            assert_eq!(reader_z.path(), count.to_be_bytes());
            count += 1;
        }
        assert_eq!(count, N);
    }

    /// Test val_count & iteration on a ReadZipper forked off of a WriteZipper
    #[test]
    fn read_zipper_special_iter_test4() {
        const R_KEY_CNT: usize = 9;
        let keys = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        let mut map: PathMap::<()> = keys.into_iter().map(|k| (k, ())).collect();

        // Test val_count & iteration on a ReadZipper
        let rz = map.read_zipper_at_borrowed_path(b"r");
        assert_eq!(rz.val_count(), R_KEY_CNT);
        let mut count = 0;
        for (_path, _) in rz {
            count += 1;
        }
        assert_eq!(count, R_KEY_CNT);

        // Test val_count & iteration on a ReadZipper forked off of a WriteZipper
        let wz = map.write_zipper_at_path(b"r");
        assert_eq!(wz.val_count(), R_KEY_CNT);
        let rz = wz.fork_read_zipper();
        assert_eq!(rz.val_count(), R_KEY_CNT);
        let mut count = 0;
        for (_path, _) in rz {
            count += 1;
        }
        assert_eq!(count, R_KEY_CNT);
    }

    #[test]
    fn read_zipper_path_iter_leaf_paths() {
        pub const ZIPPER_UNIQUE_PATH_KEYS: &[&[u8]] = &[b"arrow", b"bow", b"cannon", b"rom'i", b"romane", b"romanus", b"romulus", b"rubens", b"ruber", b"rubicon", b"rubicundus"];
        let mut map: PathMap<()> = PathMap::new();
        for key in ZIPPER_UNIQUE_PATH_KEYS {
            map.create_path(key);
        }

        let iter_paths: Vec<Vec<u8>> = map.read_zipper().into_path_iter().collect();
        assert_eq!(iter_paths, ZIPPER_UNIQUE_PATH_KEYS);
    }

    /// This test tries to hit an edge case in [ZipperIteration::to_next_val] where we begin iteration in the middle of a node
    #[test]
    fn read_zipper_special_zipper_iter_test5() {
        let mut map = PathMap::<usize>::new();
        let mut zipper = map.write_zipper_at_path(b"in");
        for i in 0usize..2 {
            zipper.descend_to_byte(i as u8);
            zipper.descend_to(i.to_be_bytes());
            zipper.set_val(i);
            zipper.reset();
        }
        drop(zipper);

        let mut reader_z = map.read_zipper_at_path([b'i', b'n', 1]);
        let mut sanity_counter = 0;
        while reader_z.to_next_val() {
            sanity_counter += 1;
        }
        assert_eq!(sanity_counter, 1);
    }

    #[test]
    fn read_zipper_special_byte_iter_test() {
        let keys = vec![[0, 3], [0, 4], [0, 5]];
        let map: PathMap<()> = keys.into_iter().map(|v| (v, ())).collect();

        let mut r0 = map.read_zipper();
        r0.descend_to_byte(0);
        assert_eq!(r0.path_exists(), true);
        let mut r1 = r0.fork_read_zipper();
        assert_eq!(r1.to_next_sibling_byte(), None);
        assert_eq!(r1.child_mask().0[0], (1<<3) | (1<<4) | (1<<5));
        r1.descend_to_byte(3);
        assert_eq!(r1.path_exists(), true);
        assert_eq!(r1.child_mask().0[0], 0);
        assert!(r1.to_next_sibling_byte().is_some());
        assert_eq!(r1.origin_path(), &[0, 4]);
        assert_eq!(r1.path(), &[4]);
        assert!(r1.to_next_sibling_byte().is_some());
        assert_eq!(r1.to_next_sibling_byte(), None);
    }

    #[test]
    fn path_concat_test() {
        let parent_path = "�parent";
        let exprs = [
            "�parent�Tom�Bob",
            "�parent�Pam�Bob",
            "�parent�Tom�Liz",
            "�parent�Bob�Ann",
            "�parent�Bob�Pat",
            "�parent�Pat�Jim",
            "�female�Pam",
            "�male�Tom",
            "�male�Bob",
            "�female�Liz",
            "�female�Pat",
            "�female�Ann",
            "�male�Jim",
        ];
        let family: PathMap<i32> = exprs.iter().enumerate().map(|(i, k)| (k, i as i32)).collect();

        let mut parent_zipper = family.read_zipper_at_path(parent_path.as_bytes());

        assert!(family.path_exists_at(parent_path));

        let mut full_parent_path = parent_path.as_bytes().to_vec();
        full_parent_path.extend(parent_zipper.path());
        assert!(family.path_exists_at(&full_parent_path));

        while parent_zipper.to_next_val() {
            let mut full_parent_path = parent_path.as_bytes().to_vec();
            full_parent_path.extend(parent_zipper.path());
            assert!(family.contains(&full_parent_path));
            assert_eq!(full_parent_path, parent_zipper.origin_path());
        }
    }

    #[test]
    fn full_path_test() {
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        let btm: PathMap<u64> = rs.into_iter().enumerate().map(|(i, k)| (k, i as u64)).collect();

        let mut zipper = btm.read_zipper_at_path(b"roma");
        assert_eq!(format!("roma{}", std::str::from_utf8(zipper.path()).unwrap()), "roma");
        assert_eq!(std::str::from_utf8(zipper.origin_path()).unwrap(), "roma");
        zipper.descend_to(b"n");
        assert_eq!(format!("roma{}", std::str::from_utf8(zipper.path()).unwrap()), "roman");
        assert_eq!(std::str::from_utf8(zipper.origin_path()).unwrap(), "roman");
        let mut observed = zipper.path().to_vec();
        zipper.to_next_val_observed(&mut observed);
        assert_eq!(format!("roma{}", std::str::from_utf8(zipper.path()).unwrap()), "romane");
        assert_eq!(std::str::from_utf8(zipper.origin_path()).unwrap(), "romane");
        assert_eq!(&observed[..], zipper.path());
        zipper.to_next_val_observed(&mut observed);
        assert_eq!(format!("roma{}", std::str::from_utf8(zipper.path()).unwrap()), "romanus");
        assert_eq!(std::str::from_utf8(zipper.origin_path()).unwrap(), "romanus");
        assert_eq!(&observed[..], zipper.path());
        zipper.to_next_val_observed(&mut observed);
        assert_eq!(zipper.path().len(), 0);
        assert_eq!(observed.len(), 0);
    }

    #[test]
    fn read_zipper_is_shared_test1() {
        let l0_keys = vec!["stem0", "stem1", "stem2", "strongbad", "strange", "steam", "stevador", "steeple"];
        let l1_keys = vec!["A-mid0", "B-mid1", "C-mid2", "D-midlands", "D-middling", "D-middlemarch"];
        let l2_keys = vec!["X-top0", "X-top1", "X-top2", "X-top3"];
        let top_map: PathMap<()> = l2_keys.iter().map(|v| (v, ())).collect();

        let mut mid_map = PathMap::<()>::new();
        let mut wz = mid_map.write_zipper();
        for key in l1_keys.iter() {
            wz.reset();
            wz.descend_to(key);
            wz.graft_map(top_map.clone());
        }
        drop(wz);

        let mut map = PathMap::<()>::new();
        let mut wz = map.write_zipper();
        for key in l0_keys.iter() {
            wz.reset();
            wz.descend_to(key);
            wz.graft_map(mid_map.clone());
        }
        drop(wz);

        assert_eq!(map.val_count(), l0_keys.len() * l1_keys.len() * l2_keys.len());

        let mut rz = map.read_zipper();
        let mut shared_cnt = 0;
        while rz.to_next_step() {
            if rz.is_shared() {
                // println!("{}", String::from_utf8_lossy(rz.path()));
                shared_cnt += 1;
            }
        }
        assert_eq!(shared_cnt, l0_keys.len() + l0_keys.len() * l1_keys.len());
    }

    #[test]
    fn read_zipper_is_shared_at_shared_root() {
        let mut map: PathMap<()> = PathMap::new();
        map.set_val_at(b"a", ());
        let snapshot = map.clone();

        let zipper = map.read_zipper();
        assert!(zipper.at_root());
        assert!(zipper.is_shared());
        assert!(zipper.shared_node_id().is_some());
        assert_eq!(zipper.shared_node_id(), snapshot.shared_node_id());
        assert!(snapshot.is_shared());
    }

    /// A retained dangling path is represented by an empty sentinel.  It is not a
    /// physical node and therefore must not be reported as shareable.
    #[test]
    fn read_zipper_shared_node_id_at_dangling_path() {
        let mut map: PathMap<()> = [(b"aa".as_slice(), ()), (b"ab", ()), (b"ba", ()), (b"bb", ()), (b"b", ())]
            .into_iter()
            .collect();

        assert_eq!(map.remove_val_at(b"ba", false), Some(()));
        assert_eq!(map.remove_val_at(b"bb", false), Some(()));

        let zipper = map.read_zipper_at_path(b"ba");
        assert!(zipper.path_exists());
        assert!(!zipper.is_val());
        assert_eq!(zipper.is_shared(), false);
        assert_eq!(zipper.shared_node_id(), None);

        let mut zipper = map.read_zipper();
        zipper.descend_to(b"ba");
        assert!(zipper.path_exists());
        assert!(!zipper.is_val());
        assert_eq!(zipper.is_shared(), false);
        assert_eq!(zipper.shared_node_id(), None);
    }

    /// This behavior is a bit counter-intuitive, but it is correct.
    /// The following happens:
    /// 1. The top_map ["X0", "X1", "X2"] is grafted at "steam" creating ["steamX0",
    ///   "steamX1", steamX2].  At this point, the base of ["X0", "X1", "X2"]
    ///   is shared, because it is shared with the top_map.
    /// 2. The write zipper descends to "steamboat", and modifies it making it unique.
    ///   So the path "steam" now has 2 children, 'X' and 'b', so it's unique
    /// 3. In the process of making the "steam" path writable, and thus unique, the
    ///   "X" in ["X0", "X1", "X2"] becomes the new share point.  So there are 3 share
    ///   points in the trie:
    ///   - "steamX" - Shared twice in the `map` and also one level deep within `top_map`
    ///   - "steamboat" - Sharing the root node of `top_map`
    ///   - "steamboatX" - Sharing the same nodes as "steamX", etc.
    #[test]
    fn read_zipper_is_shared_test2() {
        let l0_keys = vec!["steam", "steamboat"];
        let l1_keys = vec!["X0", "X1", "X2"];
        let top_map: PathMap<()> = l1_keys.iter().map(|v| (v, ())).collect();

        let mut map = PathMap::<()>::new();
        let mut wz = map.write_zipper();
        for key in l0_keys.iter() {
            wz.reset();
            wz.descend_to(key);
            wz.graft_map(top_map.clone());
        }
        drop(wz);

        assert_eq!(map.val_count(), l0_keys.len() * l1_keys.len());

        let mut rz = map.read_zipper();
        let mut shared_cnt = 0;
        while rz.to_next_step() {
            if rz.is_shared() {
                // println!("{}", String::from_utf8_lossy(rz.path()));
                shared_cnt += 1;
            }
        }
        assert_eq!(shared_cnt, 3);
    }

    /// Tests [`ZipperInfallibleSubtries::get_focus`] and [`ZipperInfallibleSubtries::try_borrow_focus`] internal APIs on [`ReadZipperCore`]
    #[test]
    fn read_zipper_focus_nodes() {
        let mut map = PathMap::<()>::new();
        map.set_val_at(b"one.val", ());
        map.set_val_at(b"one.two.val", ());
        map.set_val_at(b"one.two.three.val", ());
        map.set_val_at(b"one.two.three.four.val", ());

        //Test descending a read zipper
        let mut rz = map.read_zipper();
        rz.descend_to(b"one.");

        //We should be at a node boundary, as long as this part of the path got encoded as a PairNode (or a ByteNode)
        let node = rz.try_borrow_focus().unwrap();
        assert_eq!(node.0.as_tagged().count_branches(&[]), 2);
        let expected_mask: ByteMask = [b't', b'v'].into_iter().collect();
        assert_eq!(node.0.as_tagged().node_branches_mask(&[]), expected_mask);
        assert!(matches!(rz.get_focus().0, AbstractNodeRef::BorrowedRc(_))); //Make sure we get the ODRc
        drop(rz);

        //Test creating a read zipper at the location, using `read_zipper_at_path`
        let rz = map.read_zipper_at_borrowed_path(b"one.two.");

        //We should be at a node boundary, as long as this part of the path got encoded as a PairNode (or a ByteNode)
        let node = rz.try_borrow_focus().unwrap();
        assert_eq!(node.0.as_tagged().count_branches(&[]), 2);
        let expected_mask: ByteMask = [b't', b'v'].into_iter().collect();
        assert_eq!(node.0.as_tagged().node_branches_mask(&[]), expected_mask);
        assert!(matches!(rz.get_focus().0, AbstractNodeRef::BorrowedRc(_))); //Make sure we get the ODRc
        drop(rz);

        //Test creating a read zipper from a ZipperHead
        let zh = map.zipper_head();
        let rz = zh.read_zipper_at_borrowed_path(b"one.two.three.").unwrap();

        // We should be at a node boundary, as long as this part of the path got encoded as a PairNode (or a ByteNode)
        let node = rz.try_borrow_focus().unwrap();
        assert_eq!(node.0.as_tagged().count_branches(&[]), 2);
        let expected_mask: ByteMask = [b'f', b'v'].into_iter().collect();
        assert_eq!(node.0.as_tagged().node_branches_mask(&[]), expected_mask);
        assert!(matches!(rz.get_focus().0, AbstractNodeRef::BorrowedRc(_))); //Make sure we get the ODRc
    }

    /// Tests the zipper `val_count` method, including with root values
    /// NOTE: This test isn't in the generic suite because not all zipper types have real implementations of val_count
    const ZIPPER_VAL_COUNT_TEST1_KEYS: &[&[u8]] = &[b"", b"arrow"];
    #[test]
    fn read_zipper_val_count_test1() {
        let map: PathMap<()> = ZIPPER_VAL_COUNT_TEST1_KEYS.into_iter().cloned().collect();
        let mut zipper = map.read_zipper();

        assert_eq!(zipper.path(), b"");
        assert_eq!(zipper.val_count(), 2);
        assert_eq!(zipper.descend_until(), true);
        assert_eq!(zipper.path(), b"arrow");
        assert_eq!(zipper.val_count(), 1);
    }

    #[test]
    fn descend_last_path() {
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        let btm: PathMap<u64> = rs.into_iter().enumerate().map(|(i, k)| (k, i as u64)).collect();

        let mut rz = btm.read_zipper();
        let mut observed = Vec::<u8>::new();
        assert!(rz.descend_last_path_observed(&mut observed));
        assert_eq!(rz.path(), b"rubicundus");
        assert_eq!(&observed[..], rz.path());
    }

    fn value_iteration_history_test_map() -> PathMap<u64> {
        let mut map = PathMap::<u64>::new();
        { let mut w = map.write_zipper(); w.set_val(0); }
        map.insert(&[0u8, 0], 7);
        map.insert(&[1u8], 9);
        map
    }

    fn multi_node_value_iteration_history_test_map() -> (PathMap<u64>, Vec<u8>) {
        let prefix = vec![3; crate::line_list_node::KEY_BYTES_CNT];
        let mut first_key = prefix.clone();
        let mut second_key = prefix.clone();
        first_key.push(0);
        second_key.push(1);

        let mut map = PathMap::<u64>::new();
        map.insert(&first_key, 24);
        map.insert(&second_key, 25);
        (map, prefix)
    }

    fn k_path_history_test_map() -> PathMap<u64> {
        let mut map = PathMap::<u64>::new();
        for key in [&[0u8, 0][..], &[0u8, 1], &[1u8, 0], &[1u8, 1]] {
            map.insert(key, 1);
        }
        map
    }

    fn nested_k_path_history_test_map() -> PathMap<u64> {
        let mut map = PathMap::<u64>::new();
        for key in [&[0u8, 0, 0][..], &[0u8, 1, 0], &[1u8, 0, 0], &[1u8, 1, 0]] {
            map.insert(key, 1);
        }
        map
    }

    /// Mirrors the default `ZipperIteration::to_next_val_observed` implementation without
    /// invoking a concrete zipper's optimized override.
    fn to_next_val_default<Z: ZipperIteration>(zipper: &mut Z) -> bool {
        loop {
            if zipper.descend_first_byte().is_some() {
                if zipper.is_val() {
                    return true
                }
                if zipper.descend_until() && zipper.is_val() {
                    return true
                }
            } else {
                loop {
                    if zipper.to_next_sibling_byte().is_some() {
                        if zipper.is_val() {
                            return true
                        }
                        break
                    }
                    zipper.ascend_byte();
                    if zipper.at_root() {
                        return false
                    }
                }
            }
        }
    }

    /// Tests the particulars of descend_first_byte, which uses the iteration mechanism to find the first byte,
    /// and thus can establish zipper state (iter_token) to speed up subsequent iteration.  But we need to make
    /// sure that the zipper's state isn't poisoned with an incorrect token for the zipper position.
    #[test]
    fn read_zipper_to_next_val_after_descend_first_byte_matches_descend_to() {
        let map = value_iteration_history_test_map();

        let mut from_first_byte = map.read_zipper();
        assert_eq!(from_first_byte.descend_first_byte(), Some(0));

        let mut from_path = map.read_zipper();
        from_path.descend_to(&[0u8]);
        assert_eq!(from_first_byte.path(), from_path.path());
        assert!(from_path.to_next_val());

        assert!(from_first_byte.to_next_val());
        assert_eq!(from_first_byte.path(), from_path.path());
        assert_eq!(from_first_byte.val(), from_path.val());

        //Here the item selected by `descend_first_byte` ends at `[0]`, so its returned
        //token is also the correct continuation token for that focus.
        let mut exact_item_map = PathMap::<u64>::new();
        exact_item_map.insert(&[0u8], 10);
        exact_item_map.insert(&[1u8], 11);

        let mut exact_from_first_byte = exact_item_map.read_zipper();
        assert_eq!(exact_from_first_byte.descend_first_byte(), Some(0));

        let mut exact_from_path = exact_item_map.read_zipper();
        exact_from_path.descend_to(&[0u8]);
        assert_eq!(exact_from_first_byte.path(), exact_from_path.path());
        assert!(exact_from_path.to_next_val());

        assert!(exact_from_first_byte.to_next_val());
        assert_eq!(exact_from_first_byte.path(), exact_from_path.path());
        assert_eq!(exact_from_first_byte.val(), exact_from_path.val());
    }

    /// Tests none of the flavors of ascend corrput internal zipper state relied upon by to_next_val
    #[test]
    fn read_zipper_to_next_val_after_each_ascent_matches_direct_position_in_multi_node_map() {
        let (map, prefix) = multi_node_value_iteration_history_test_map();

        type Rz<'a> = ReadZipperUntracked<'a, 'static, u64>;
        let ascents: [(&str, fn(&mut Rz)); 4] = [
            ("ascend", |z| { assert_eq!(z.ascend(1), 1); }),
            ("ascend_byte", |z| { assert!(z.ascend_byte()); }),
            ("ascend_until", |z| { assert_eq!(z.ascend_until(), 1); }),
            ("ascend_until_branch", |z| { assert_eq!(z.ascend_until_branch(), 1); }),
        ];

        for (label, ascend) in ascents {
            let mut after_ascent = map.read_zipper();
            assert!(after_ascent.to_next_val(), "first value before {label}");
            assert!(after_ascent.to_next_val(), "second value before {label}");
            ascend(&mut after_ascent);
            assert_eq!(after_ascent.path(), &prefix, "{label}");

            let mut direct = map.read_zipper();
            direct.descend_to(&prefix);
            assert_eq!(after_ascent.path(), direct.path(), "{label}");
            assert!(direct.to_next_val(), "direct to_next_val after {label}");

            assert!(after_ascent.to_next_val(), "to_next_val after {label}");
            assert_eq!(after_ascent.path(), direct.path(), "{label}");
            assert_eq!(after_ascent.val(), direct.val(), "{label}");
        }
    }

    #[test]
    fn read_zipper_to_next_sibling_from_partial_focus_matches_direct_focus() {
        let mut map = PathMap::<u64>::new();
        map.insert(b"abc", 10);
        map.insert(b"wxyz", 11);

        let mut after_sibling = map.read_zipper();
        after_sibling.descend_to(b"a");
        assert_eq!(after_sibling.to_next_sibling_byte(), Some(b'w'));
        assert_eq!(after_sibling.path(), b"w");
        assert_eq!(after_sibling.to_next_sibling_byte(), None);
        assert_eq!(after_sibling.path(), b"w");

        let mut direct = map.read_zipper();
        direct.descend_to(b"w");
        assert!(direct.to_next_val());

        assert!(after_sibling.to_next_val());
        assert_eq!(after_sibling.path(), direct.path());
        assert_eq!(after_sibling.val(), direct.val());
    }

    #[test]
    fn read_zipper_to_next_k_path_after_descend_first_k_path_matches_descend_to() {
        let map = k_path_history_test_map();

        let mut from_k_path = map.read_zipper();
        assert!(from_k_path.descend_first_k_path(2));

        let mut from_path = map.read_zipper();
        from_path.descend_to(from_k_path.path());
        assert_eq!(from_k_path.path(), from_path.path());
        assert!(from_path.to_next_k_path(2));

        assert!(from_k_path.to_next_k_path(2));
        assert_eq!(from_k_path.path(), from_path.path());
    }

    #[test]
    fn read_zipper_to_next_k_path_after_k_path_descent_and_ascent_matches_unmoved_focus() {
        let map = nested_k_path_history_test_map();

        let mut after_movement = map.read_zipper();
        assert!(after_movement.descend_first_k_path(2));
        assert_eq!(after_movement.descend_first_byte(), Some(0));
        assert!(after_movement.ascend_byte());

        let mut unmoved = map.read_zipper();
        assert!(unmoved.descend_first_k_path(2));
        assert_eq!(after_movement.path(), unmoved.path());
        assert!(unmoved.to_next_k_path(2));

        assert!(after_movement.to_next_k_path(2));
        assert_eq!(after_movement.path(), unmoved.path());
    }

    #[test]
    fn read_zipper_to_next_k_path_after_prior_k_path_step_matches_unmoved_focus() {
        let map = k_path_history_test_map();

        let mut after_prior_step = map.read_zipper();
        assert!(after_prior_step.descend_first_k_path(2));
        assert!(after_prior_step.to_next_k_path(2));
        assert_eq!(after_prior_step.to_prev_sibling_byte(), Some(0));

        let mut unmoved = map.read_zipper();
        assert!(unmoved.descend_first_k_path(2));
        assert_eq!(after_prior_step.path(), unmoved.path());
        assert!(unmoved.to_next_k_path(2));

        assert!(after_prior_step.to_next_k_path(2));
        assert_eq!(after_prior_step.path(), unmoved.path());
    }

    #[test]
    fn read_zipper_to_next_k_path_after_nested_k_path_step_matches_unmoved_focus() {
        let map = nested_k_path_history_test_map();

        let mut after_nested_step = map.read_zipper();
        assert!(after_nested_step.descend_first_k_path(2));
        assert!(after_nested_step.descend_first_k_path(1));
        assert!(!after_nested_step.to_next_k_path(1));

        let mut unmoved = map.read_zipper();
        assert!(unmoved.descend_first_k_path(2));
        assert_eq!(after_nested_step.path(), unmoved.path());
        assert!(unmoved.to_next_k_path(2));

        assert!(after_nested_step.to_next_k_path(2));
        assert_eq!(after_nested_step.path(), unmoved.path());
    }

    #[test]
    fn read_zipper_descend_first_byte_after_failed_descend_first_k_path() {
        let m: PathMap<()> = [&b"ab"[..]].into_iter().collect();
        let mut z = m.read_zipper();
        assert!(!z.descend_first_k_path(3));
        assert_eq!(z.path(), b"");
        assert_eq!(z.descend_first_byte(), Some(b'a'));
    }

    #[test]
    fn read_zipper_to_next_step_after_exhausted_to_next_k_path() {
        let m: PathMap<()> = [&[0u8, 0, 0, 1, 0, 2, 2, 2, 1, 2, 1, 0, 3][..]]
            .into_iter()
            .collect();
        let mut z = m.read_zipper();
        assert!(z.to_next_val());
        assert!(!z.to_next_k_path(5));
        assert_eq!(z.path(), &[0, 0, 0, 1, 0, 2, 2, 2]);
        assert!(z.to_next_step());
        assert_eq!(z.path(), &[0, 0, 0, 1, 0, 2, 2, 2, 1]);
    }

    #[test]
    fn read_zipper_descend_first_byte_after_exhausted_k_path_and_ascent() {
        let m: PathMap<()> = [&b"ab"[..], b"wxyz"].into_iter().collect();
        let mut z = m.read_zipper();
        z.descend_to(b"w");
        assert!(z.descend_first_k_path(1));
        assert_eq!(z.path(), b"wx");
        assert!(!z.to_next_k_path(1));
        assert_eq!(z.path(), b"w");
        assert!(z.ascend_byte());
        assert_eq!(z.path(), b"");
        assert_eq!(z.descend_first_byte(), Some(b'a'));
    }

    #[test]
    fn read_zipper_reset_at_root_clears_iteration_token() {
        let m: PathMap<()> = [&[24u8][..]].into_iter().collect();
        let mut z = m.read_zipper();
        assert!(z.to_next_step());
        z.reset();
        assert_eq!(z.descend_first_byte(), Some(24));
        z.reset();
        assert!(z.to_next_step());
    }

    #[test]
    fn read_zipper_to_next_k_path_after_path_movement() {
        #[derive(Clone, Copy)]
        enum Movement {
            DescendTo,
            MoveToPath,
            DescendToThenUntil,
        }

        let cases: &[(&str, Movement, &[&[u8]], usize, &[u8])] = &[
            (
                "descend_to across a node boundary",
                Movement::DescendTo,
                &[
                    &[0u8, 0, 1, 1],
                    &[0, 1, 0, 1, 0, 0],
                    &[0, 1, 1, 0, 0, 0, 1, 0],
                ],
                2,
                &[0],
            ),
            (
                "move_to_path",
                Movement::MoveToPath,
                &[&[3u8, 2, 2], &[3, 2, 3, 1, 2, 3, 0], &[3, 2, 3, 3]],
                4,
                b"",
            ),
            (
                "descend_to followed by descend_until",
                Movement::DescendToThenUntil,
                &[&[0u8, 0, 0, 0, 1, 0, 1], &[0, 1, 1, 1]],
                4,
                b"",
            ),
        ];

        for (name, movement, paths, k, expected_path) in cases {
            let m: PathMap<()> = paths.iter().copied().collect();
            let mut z = m.read_zipper();
            match movement {
                Movement::DescendTo => z.descend_to(&[0, 1, 1]),
                Movement::MoveToPath => {
                    z.move_to_path(&[3, 2, 3, 3]);
                }
                Movement::DescendToThenUntil => {
                    z.descend_to(&[0, 1]);
                    assert!(z.descend_until(), "{name}");
                    assert_eq!(z.path(), &[0, 1, 1, 1], "{name}");
                }
            }
            assert!(!z.to_next_k_path(*k), "{name}");
            assert_eq!(z.path(), *expected_path, "{name}");
        }
    }

    #[test]
    fn read_zipper_to_next_k_path_does_not_repeat_prefix_value() {
        let m: PathMap<()> = [&b"a"[..], b"abcd"].into_iter().collect();
        let mut z = m.read_zipper();
        assert!(z.descend_first_k_path(1));
        assert_eq!(z.path(), b"a");
        assert!(!z.to_next_k_path(1));
    }

    #[test]
    fn read_zipper_to_next_val_after_exhausted_k_path() {
        let root: PathMap<()> = [&b"ab"[..], b"wxyz"].into_iter().collect();
        let mut z = root.read_zipper();
        assert!(z.descend_first_k_path(1), "root");
        assert!(z.to_next_k_path(1), "root");
        assert!(!z.to_next_k_path(1), "root");
        assert!(z.at_root(), "root");
        assert!(z.to_next_val(), "root");
        assert_eq!(z.path(), b"ab", "root");

        let subtree: PathMap<()> = [
            &[1u8, 2, 1, 0, 0, 0, 2, 1, 1, 1, 2, 3, 1, 2][..],
            &[2, 2, 1, 2, 3, 2, 3],
            &[3, 3, 3, 2, 3, 0, 0, 3],
        ]
        .into_iter()
        .collect();
        let mut z = subtree.read_zipper();
        assert_eq!(z.descend_indexed_byte(1), Some(2), "subtree");
        assert!(z.descend_to_existing_byte(2), "subtree");
        assert!(!z.to_next_k_path(1), "subtree");
        assert_eq!(z.path(), &[2], "subtree");
        assert!(z.to_next_val(), "subtree");
        assert_eq!(z.path(), &[2, 2, 1, 2, 3, 2, 3], "subtree");
    }

    // Focus state after moving through a nonexistent path.

    #[test]
    fn read_zipper_k_path_edge_cases() {
        let m: PathMap<()> = [
            &b"b"[..],
            b"bb",
            b"bc",
            b"bcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc",
            b"cb",
        ]
        .into_iter()
        .collect();

        for (missing_path, expected_path, depth) in [
            (b"bd".as_slice(), b"b".as_slice(), 1), //Non-existent focus, middle of trie
            (b"", b"", 100), //Trying to descend deeper than any paths
            (b"bbb", b"bb", 1), //Non-existent focus, below trie, ending on existing path
            (b"aa", b"a", 1), //Non-existent focus, before trie
            (b"bbbbb", b"bbbb", 1), //Non-existent focus, below trie, ending on non-existing path
            (b"d", b"", 1), //Non-existent focus, after trie
            (b"cbb", b"", 3), //Non-existent focus, ending higher up
            (b"ba", b"", 3), //to_next_k_path should go to the root
            (b"bcccccccccccccccccccccccccccccccccccccccccccccccccccccccccc", b"", 70), //to_next_k_path returns to root when overshooting a Looooooong path
            ]
        {
            let mut z = m.read_zipper();

            z.descend_to(missing_path);

            assert!(!z.descend_first_k_path(depth), "{missing_path:?}");
            assert_eq!(z.path(), missing_path, "{missing_path:?}");
            assert!(!z.to_next_k_path(depth), "{missing_path:?}");
            assert_eq!(z.path(), expected_path, "{missing_path:?}");
        }
    }

    #[test]
    fn read_zipper_descend_first_byte_then_ascend_from_missing_path() {
        let cases: &[(&str, &[&[u8]], &[u8], u8)] = &[
            (
                "before the first key",
                &[&b"b"[..], &b"c"[..]],
                b"a",
                b'b',
            ),
            (
                "after the last key",
                &[&b"ab"[..], &b"wxyz"[..]],
                b"z",
                b'a',
            ),
        ];

        for (name, paths, missing_path, expected_byte) in cases {
            let m: PathMap<()> = paths.iter().copied().collect();
            let mut z = m.read_zipper();
            z.descend_to(missing_path);
            assert!(!z.path_exists(), "{name}");
            assert_eq!(z.descend_first_byte(), None, "{name}");
            assert!(z.ascend_byte(), "{name}");
            assert_eq!(z.descend_first_byte(), Some(*expected_byte), "{name}");
        }
    }

    #[test]
    fn read_zipper_ascend_until_branch_from_missing_path_below_zipper_root() {
        let m: PathMap<()> = [
            &[1u8, 12, 4, 5, 4][..],
            &[13, 9, 5, 15, 5, 0, 11, 14, 13, 3, 12, 0, 4],
            &[15, 3, 14, 15, 0, 8, 7],
        ]
        .into_iter()
        .collect();
        let mut z = m.read_zipper_at_path(&[1, 12, 4, 5, 4]);
        z.descend_to(&[12, 12]);
        z.descend_to(&[173, 37, 23]);
        assert_eq!(z.descend_first_byte(), None);
        assert_eq!(z.ascend_until_branch(), 5);
        assert!(z.at_root());
    }

    #[test]
    fn read_zipper_to_next_step_after_missing_path() {
        let m: PathMap<()> = [&[0u8][..], &[7], &[14, 5]].into_iter().collect();
        let mut z = m.read_zipper_at_path(&[14, 5]);
        z.descend_to_byte(11);
        z.descend_to_byte(13);
        assert_eq!(z.descend_first_byte(), None);
        assert!(z.ascend_byte());
        assert!(!z.to_next_step());
    }

    #[test]
    fn read_zipper_to_next_val_does_not_escape_zipper_root_after_missing_path() {
        let m: PathMap<()> = [&[7u8, 167, 36, 166, 110][..]].into_iter().collect();
        let mut z = m.read_zipper_at_path(&[7, 167, 36, 166, 110]);
        z.descend_to(&[45, 47, 220]);
        assert_eq!(z.descend_first_byte(), None);
        assert_eq!(z.ascend(1), 1);
        assert!(!z.to_next_val());
    }

    #[test]
    fn read_zipper_to_next_sibling_after_missing_path_below_leaf() {
        let m: PathMap<()> = [&[10u8][..], &[20], &[30]].into_iter().collect();
        let mut z = m.read_zipper();
        z.descend_to(&[10, 99]);
        assert_eq!(z.descend_first_byte(), None);
        assert!(z.ascend_byte());
        assert_eq!(z.path(), &[10]);
        assert_eq!(z.to_next_sibling_byte(), Some(20));
    }

    #[test]
    fn read_zipper_ascend_multiple_bytes_from_missing_path() {
        let m: PathMap<()> = [
            &[24u8][..],
            &[49, 69],
            &[54],
            &[73, 209, 145, 207],
            &[124],
        ]
        .into_iter()
        .collect();
        let mut z = m.read_zipper();
        z.move_to_path(&[133, 52, 64, 90]);
        assert_eq!(z.to_next_sibling_byte(), None);
        assert_eq!(z.ascend(2), 2);
        assert_eq!(z.path(), &[133, 52]);
    }

    #[test]
    fn read_zipper_missing_dense_path_uses_lower_bound_for_iteration() {
        let m: PathMap<()> = [&b"a"[..], b"b", b"z"].into_iter().collect();

        let mut sibling = m.read_zipper();
        sibling.move_to_path(b"m");
        assert!(!sibling.path_exists());
        assert_eq!(sibling.to_next_sibling_byte(), Some(b'z'));
        assert_eq!(sibling.path(), b"z");

        let mut value = m.read_zipper();
        value.move_to_path(b"mm");
        assert!(!value.path_exists());
        assert_eq!(value.to_next_sibling_byte(), None);
        assert!(value.to_next_val());
        assert_eq!(value.path(), b"z");
    }

    // Sibling iteration must stay within a zipper rooted at a path and handle
    // the first child of dense nodes.

    #[test]
    fn read_zipper_sibling_moves_do_not_escape_zipper_root() {
        let m: PathMap<()> = [&[4u8][..], &[5]].into_iter().collect();
        let mut z = m.read_zipper_at_path(&[4]);
        assert_eq!(z.to_next_sibling_byte(), None);
        let m: PathMap<()> = [&[14u8][..], &[15]].into_iter().collect();
        let mut z = m.read_zipper_at_path(&[15]);
        assert_eq!(z.to_prev_sibling_byte(), None);
    }

    #[test]
    fn read_zipper_to_prev_sibling_at_first_dense_child() {
        let m: PathMap<()> = [
            &[0u8, 0, 2][..],
            &[0, 1],
            &[1],
            &[1, 2],
            &[2],
            &[2, 0, 1],
            &[2, 2, 1],
            &[2, 2, 2],
        ]
        .into_iter()
        .collect();
        let mut z = m.read_zipper();
        assert!(z.descend_first_k_path(1));
        assert_eq!(z.to_prev_sibling_byte(), None);
    }

    /// Tests iteration behavior of to_next_val implementations, comparing the default impl
    /// against the native imple, and a third run that interleaves calls to each
    #[test]
    fn read_zipper_native_and_default_value_iteration_can_be_interleaved() {
        let mut map = PathMap::<u64>::new();
        map.insert(&[0u8, 0], 10);
        map.insert(&[0u8, 1], 11);
        map.insert(&[1u8], 12);
        map.insert(&[2u8, 0], 13);
        map.insert(&[2u8, 1], 14);

        let mut native = map.read_zipper();
        let mut native_values = Vec::new();
        while native.to_next_val() {
            native_values.push((native.path().to_vec(), *native.val().unwrap()));
        }

        let mut default = map.read_zipper();
        let mut default_values = Vec::new();
        while to_next_val_default(&mut default) {
            default_values.push((default.path().to_vec(), *default.val().unwrap()));
        }

        let mut mixed = map.read_zipper();
        let mut mixed_values = Vec::new();
        let mut use_native = true;
        loop {
            let moved = if use_native {
                mixed.to_next_val()
            } else {
                to_next_val_default(&mut mixed)
            };
            if !moved {
                break
            }
            mixed_values.push((mixed.path().to_vec(), *mixed.val().unwrap()));
            use_native = !use_native;
        }

        assert_eq!(default_values, native_values);
        assert_eq!(mixed_values, native_values);
    }

    /// Checks that value iteration composes with common zipper movements.  Each movement
    /// below reaches the same focus, from which `to_next_val` visits the values in the
    /// reachable subtrie in depth-first order.  The test also covers restarting a value
    /// walk after reset or ascent, and complete fixed-depth k-path enumeration.
    #[test]
    fn read_zipper_to_next_val_after_every_movement() {
        let mut map = PathMap::<u64>::new();
        { let mut w = map.write_zipper(); w.set_val(0); }
        map.insert(&[0u8, 0], 7);
        map.insert(&[1u8], 9);

        type Rz<'a> = ReadZipperUntracked<'a, 'static, u64>;
        let ways: Vec<(&str, Box<dyn Fn(&mut Rz)>)> = vec![
            ("descend_to([0])", Box::new(|z: &mut Rz| { z.descend_to(&[0u8]); })),
            ("descend_to_byte(0)", Box::new(|z: &mut Rz| { z.descend_to_byte(0); })),
            ("descend_indexed_byte(0)", Box::new(|z: &mut Rz| { z.descend_indexed_byte(0); })),
            ("descend_to_existing_byte(0)", Box::new(|z: &mut Rz| { z.descend_to_existing_byte(0); })),
            ("move_to_path([0])", Box::new(|z: &mut Rz| { z.move_to_path(&[0u8]); })),
            ("descend_first_byte()", Box::new(|z: &mut Rz| { z.descend_first_byte(); })),
            ("to_next_step()", Box::new(|z: &mut Rz| { z.to_next_step(); })),
            ("descend_first_k_path(1)", Box::new(|z: &mut Rz| { z.descend_first_k_path(1); })),
            ("descend_last_byte(), to_prev_sibling_byte()", Box::new(|z: &mut Rz| { z.descend_last_byte(); z.to_prev_sibling_byte(); })),
        ];
        for (label, f) in &ways {
            let mut z = map.read_zipper();
            f(&mut z);
            assert_eq!(z.path(), &[0u8], "{label} did not land on [0]");
            assert!(z.to_next_val(), "to_next_val after {label}");
            assert_eq!(z.path(), &[0u8, 0], "after {label}");
            assert_eq!(z.val(), Some(&7), "after {label}");
            assert!(z.to_next_val(), "second to_next_val after {label}");
            assert_eq!(z.path(), &[1u8], "after {label}");
            assert!(!z.to_next_val(), "third to_next_val after {label}");
        }

        //A finished iteration, then `reset`, must start over
        let mut one = PathMap::<u64>::new();
        one.insert(&[1u8, 1, 1], 72);
        let mut z = one.read_zipper();
        assert!(z.to_next_val());
        assert!(!z.to_next_val());
        z.reset();
        assert!(z.to_next_val(), "to_next_val after reset");
        assert_eq!(z.val(), Some(&72));

        //A finished iteration, then an ascent, must start over
        let mut two = PathMap::<u64>::new();
        two.insert(&[3u8], 24);
        two.insert(&[3u8, 3], 25);
        let ups: Vec<(&str, fn(&mut Rz))> = vec![
            ("ascend", |z| { z.ascend(7); }),
            ("ascend_byte", |z| { z.ascend_byte(); z.ascend_byte(); }),
            ("ascend_until", |z| { z.ascend_until(); z.ascend_until(); }),
            ("ascend_until_branch", |z| { z.ascend_until_branch(); }),
        ];
        for (label, up) in ups {
            let mut z = two.read_zipper();
            assert!(z.to_next_val());
            assert!(z.to_next_val());
            assert_eq!(z.path(), &[3u8, 3]);
            up(&mut z);
            assert!(z.at_root(), "{label}");
            assert!(z.to_next_val(), "to_next_val after {label}");
            assert_eq!(z.val(), Some(&24), "after {label}");
        }

        //The k-path pair visits every path at the requested depth.
        let mut three = PathMap::<u64>::new();
        for k in [&[0u8, 0][..], &[0u8, 1], &[1u8, 0], &[1u8, 1]] { three.insert(k, 1); }
        let mut z = three.read_zipper();
        assert!(z.descend_first_k_path(2));
        let mut seen = vec![z.path().to_vec()];
        while z.to_next_k_path(2) { seen.push(z.path().to_vec()); }
        assert_eq!(seen, vec![vec![0u8, 0], vec![0, 1], vec![1, 0], vec![1, 1]]);
    }

    #[test]
    fn read_zipper_fork_root_to_next_step_terminates() {
        let mut m = PathMap::<u64>::new(); m.set_val_at(&[0u8,0,2,3,0], 1); m.create_path(&[0u8,3]);
        let rz = m.read_zipper_at_path(&[0u8,3]);
        let mut f = rz.fork_read_zipper();
        assert!(!f.ascend_byte());        // fad58f4: true (release) / subtract-with-overflow (debug)
        let mut f = rz.fork_read_zipper();
        assert!(!f.to_next_step());       // fad58f4: never returns
    }

    #[test]
    fn read_zipper_empty_node_below_dangling_path_ascend() {
        let mut m = PathMap::<u64>::new(); m.set_val_at(&[0u8,0,2], 1); m.create_path(&[0u8,3]);
        let mut z = m.read_zipper_at_path(&[0u8,3]);
        z.descend_to(&[1u8]);
        assert_eq!(z.descend_first_byte(), None);
        assert!(z.ascend_byte());         // fad58f4: panic at empty_node.rs:68 (unreachable!)
        assert!(z.at_root());
    }

    #[test]
    fn read_zipper_missing_focus_between_key0_and_descendant_key1() {
        let m: PathMap<()> = [&b"a"[..], b"abcd"].into_iter().collect();
        let mut z = m.read_zipper();
        z.descend_to(b"aa");
        assert_eq!(z.to_next_sibling_byte(), Some(b'b'));   // fad58f4: None
        assert_eq!(z.path(), b"ab");
        let mut z = m.read_zipper();
        z.descend_to(b"aa");
        assert!(z.to_next_k_path(1));                       // fad58f4: false
        assert_eq!(z.path(), b"ab");
    }

    #[test]
    fn read_zipper_k_path_base_mismatch_exit() {
        let m: PathMap<()> = [&[0u8,0,0,0,0,0,1][..], &[2]].into_iter().collect();
        let mut z = m.read_zipper();
        assert!(z.to_next_val());
        assert!(!z.to_next_k_path(2));
        assert_eq!(z.path(), &[0,0,0,0,0]);
        assert_eq!(z.descend_first_byte(), Some(0));        // fad58f4: None
        let mut z = m.read_zipper();
        assert!(z.to_next_val());
        assert!(!z.to_next_k_path(2));
        assert!(z.to_next_val());
        assert_eq!(z.path(), &[0,0,0,0,0,0,1]);             // fad58f4: [2]
    }

    #[test]
    fn read_zipper_rooted_to_next_val_exhaustion() {
        let m: PathMap<()> = [&[1u8,2,3][..], &[1,5]].into_iter().collect();
        let mut z = m.read_zipper_at_path(&[1,2]);
        assert!(z.to_next_val());
        assert!(!z.to_next_val());
        assert!(z.at_root());
        assert_eq!(z.descend_first_byte(), Some(3));        // fad58f4: None
        let mut z = m.read_zipper_at_path(&[1,2]);
        assert!(z.to_next_val());
        assert!(!z.to_next_val());
        assert!(z.to_next_step());                          // fad58f4: false
        assert_eq!(z.path(), &[3]);
    }

    #[test]
    fn read_zipper_prev_sibling_cases() {
        let m: PathMap<()> = [&[10u8][..], &[20], &[70]].into_iter().collect();   // dense node
        let mut z = m.read_zipper(); z.descend_to(&[70]);
        assert_eq!(z.to_prev_sibling_byte(), Some(20));     // fad58f4 and master: Some(10)
        let mut z = m.read_zipper(); z.descend_to(&[60]);   // nonexistent byte
        assert_eq!(z.to_prev_sibling_byte(), Some(20));     // fad58f4 debug: assert in bit_sibling
        let m: PathMap<()> = [&[10u8,1][..], &[200,1]].into_iter().collect();     // line-list node
        let mut z = m.read_zipper(); z.descend_to(&[100]);
        assert_eq!(z.to_prev_sibling_byte(), Some(10));     // fad58f4 and master: None
    }
}
