use crate::{
    utils::ByteMask,
    zipper::{
        PathObserver, Zipper, ZipperAbsolutePath, ZipperMoving, ZipperIteration,
        ZipperPath, ZipperPathBuffer, ZipperValues,
        ZipperReadOnlyValues, ZipperReadOnlyConditionalValues,
    },
};

/// Zipper Wrapper to implement [`ZipperPath`] for zipper types that implement [`ZipperMoving`].
/// This is useful for tracking the path of "blind" zipper types
///
/// The "blind" zipper pattern enables nested virtual zippers to efficiently compose,
/// without repeating the work of copying paths.  A `PathTracker` reinstates a contiguous
/// path buffer at whichever layer actually needs one.
///
/// Example:
/// ```rust
/// use crate::pathmap::zipper::{ZipperPath, ZipperMoving};
/// // the example uses `PathMap`, but this works with any zipper.
/// let btm = pathmap::PathMap::from_iter([(b"hello", ())]);
/// let zipper = btm.read_zipper();
/// let mut with_path = pathmap::zipper::PathTracker::new(zipper);
/// assert_eq!(with_path.descend_to_existing("hello"), 5);
/// assert_eq!(with_path.path(), b"hello");
/// ```
pub struct PathTracker<Z> {
    zipper: Z,
    path: Vec<u8>,
    origin_len: usize,
}

impl<Z: ZipperMoving> PathTracker<Z> {
    /// Returns a new `PathTracker` wrapping `zipper`, tracking the path from the zipper's root
    pub fn new(mut zipper: Z) -> Self {
        zipper.reset();
        Self {
            zipper,
            path: Vec::new(),
            origin_len: 0,
        }
    }
    /// Returns a new `PathTracker` with the supplied
    /// [`root_prefix_path`](ZipperAbsolutePath::root_prefix_path)
    pub fn with_origin(mut zipper: Z, origin: &[u8]) -> Self {
        zipper.reset();
        Self {
            zipper,
            path: origin.to_vec(),
            origin_len: origin.len(),
        }
    }
}

impl<Z: Zipper> Zipper for PathTracker<Z> {
    #[inline] fn path_exists(&self) -> bool { self.zipper.path_exists() }
    #[inline] fn is_val(&self) -> bool { self.zipper.is_val() }
    #[inline] fn child_count(&self) -> usize { self.zipper.child_count() }
    #[inline] fn child_mask(&self) -> ByteMask { self.zipper.child_mask() }
}

impl<Z: ZipperMoving> ZipperMoving for PathTracker<Z> {
    #[inline] fn at_root(&self) -> bool { self.zipper.at_root() }
    fn reset(&mut self) {
        self.zipper.reset();
        self.path.truncate(self.origin_len);
    }
    #[inline]
    fn focus_byte(&self) -> Option<u8> {
        if self.path.len() > self.origin_len {
            self.path.last().cloned()
        } else {
            None
        }
    }
    fn val_count(&self) -> usize { self.zipper.val_count() }
    fn descend_to<K: AsRef<[u8]>>(&mut self, path: K) {
        let path = path.as_ref();
        self.path.extend_from_slice(path);
        self.zipper.descend_to(path)
    }
    fn descend_to_existing<K: AsRef<[u8]>>(&mut self, path: K) -> usize {
        let path = path.as_ref();
        let descended = self.zipper.descend_to_existing(path);
        self.path.extend_from_slice(&path[..descended]);
        descended
    }
    fn descend_to_existing_byte(&mut self, k: u8) -> bool {
        if self.zipper.descend_to_existing_byte(k) {
            self.path.push(k);
            true
        } else {
            false
        }
    }
    fn descend_to_val<K: AsRef<[u8]>>(&mut self, path: K) -> usize {
        let path = path.as_ref();
        let descended = self.zipper.descend_to_val(path);
        self.path.extend_from_slice(&path[..descended]);
        descended
    }
    fn descend_to_byte(&mut self, k: u8) {
        self.path.push(k);
        self.zipper.descend_to_byte(k)
    }
    fn descend_indexed_byte(&mut self, child_idx: usize) -> bool {
        if self.zipper.descend_indexed_byte(child_idx) {
            //The inner zipper picked the byte, so ask it which one it landed on
            let byte = self.zipper.focus_byte().expect("descended zipper must have a focus byte");
            self.path.push(byte);
            true
        } else {
            false
        }
    }
    fn descend_first_byte(&mut self) -> bool {
        if self.zipper.descend_first_byte() {
            let byte = self.zipper.focus_byte().expect("descended zipper must have a focus byte");
            self.path.push(byte);
            true
        } else {
            false
        }
    }
    fn descend_until<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        //Fan the descended bytes out to our own path buffer as well as the caller's observer
        self.zipper.descend_until(&mut (&mut self.path, &mut *obs))
    }
    fn ascend(&mut self, steps: usize) -> bool {
        //`ascend` reports only whether it moved the full distance, so the buffer is trimmed by
        // comparing against the requested `steps` when it succeeds, and by resetting to the root
        // when it does not
        if self.zipper.ascend(steps) {
            let new_len = self.path.len() - steps;
            self.path.truncate(new_len);
            true
        } else {
            self.path.truncate(self.origin_len);
            false
        }
    }
    fn ascend_byte(&mut self) -> bool {
        if self.zipper.ascend_byte() {
            self.path.pop();
            true
        } else {
            false
        }
    }
    fn ascend_until(&mut self) -> bool {
        self.ascend_until_cond(true)
    }
    fn ascend_until_branch(&mut self) -> bool {
        self.ascend_until_cond(false)
    }
    fn to_next_sibling_byte(&mut self) -> bool {
        if self.zipper.to_next_sibling_byte() {
            let byte = self.zipper.focus_byte().expect("moved zipper must have a focus byte");
            *self.path.last_mut().expect("path must not be empty") = byte;
            true
        } else {
            false
        }
    }
    fn to_prev_sibling_byte(&mut self) -> bool {
        if self.zipper.to_prev_sibling_byte() {
            let byte = self.zipper.focus_byte().expect("moved zipper must have a focus byte");
            *self.path.last_mut().expect("path must not be empty") = byte;
            true
        } else {
            false
        }
    }
}

impl<Z: ZipperMoving> PathTracker<Z> {
    /// Shared implementation of [`ascend_until`](ZipperMoving::ascend_until) and
    /// [`ascend_until_branch`](ZipperMoving::ascend_until_branch)
    ///
    /// Neither method reports how far it moved, so the ascent is performed a byte at a time to
    /// keep the tracked path in step with the wrapped zipper.
    //TEMPORARY: this re-derives the wrapped zipper's stopping condition rather than delegating to
    // it, so a zipper that stops somewhere else will disagree.  Once the `ascend_` methods report
    // the distance they moved, this becomes a single delegated call followed by a truncate.
    fn ascend_until_cond(&mut self, allow_stop_on_val: bool) -> bool {
        let mut moved = false;
        while self.ascend_byte() {
            moved = true;
            if self.at_root() {
                break;
            }
            if self.zipper.child_count() > 1 || (allow_stop_on_val && self.zipper.is_val()) {
                break;
            }
        }
        moved
    }
}

impl<Z: ZipperMoving> ZipperIteration for PathTracker<Z> { }

impl<Z: ZipperMoving> ZipperPath for PathTracker<Z> {
    fn path(&self) -> &[u8] { &self.path[self.origin_len..] }
}

impl<Z: ZipperMoving> ZipperAbsolutePath for PathTracker<Z> {
    fn origin_path(&self) -> &[u8] { &self.path }
    fn root_prefix_path(&self) -> &[u8] { &self.path[..self.origin_len] }
}

impl<Z: ZipperValues<V>, V> ZipperValues<V> for PathTracker<Z> {
    fn val(&self) -> Option<&V> { self.zipper.val() }
    fn val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&V> { self.zipper.val_at(path) }
}

impl<'a, Z: ZipperReadOnlyValues<'a, V>, V: Clone + Send + Sync> ZipperReadOnlyValues<'a, V> for PathTracker<Z>
    where Self: ZipperValues<V>
{
    fn get_val(&self) -> Option<&'a V> { self.zipper.get_val() }
    fn get_val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&'a V> { self.zipper.get_val_at(path) }
}

impl<'a, Z: ZipperReadOnlyConditionalValues<'a, V>, V: Clone + Send + Sync> ZipperReadOnlyConditionalValues<'a, V> for PathTracker<Z>
    where Self: ZipperValues<V>
{
    type WitnessT = Z::WitnessT;
    fn witness<'w>(&self) -> Self::WitnessT { self.zipper.witness() }
    fn get_val_with_witness<'w>(&self, witness: &'w Self::WitnessT) -> Option<&'w V> where 'a: 'w {
        self.zipper.get_val_with_witness(witness)
    }
}

impl<Z: ZipperMoving> ZipperPathBuffer for PathTracker<Z> {
    unsafe fn origin_path_assert_len(&self, len: usize) -> &[u8] {
        assert!(len <= self.path.capacity());
        let ptr = self.path.as_ptr();
        unsafe { core::slice::from_raw_parts(ptr, len) }
    }
    fn prepare_buffers(&mut self) { }
    fn reserve_buffers(&mut self, path_len: usize, _stack: usize) {
        self.path.reserve(path_len);
    }
}

#[cfg(test)]
mod tests {
    use super::PathTracker;
    use crate::{
        PathMap,
        zipper::{zipper_iteration_tests, zipper_moving_tests},
    };

    zipper_moving_tests::zipper_moving_tests!(path_tracker,
        |keys: &[&[u8]]| {
            keys.into_iter().map(|k| (k, ())).collect::<PathMap<()>>()
        },
        |trie: &mut PathMap<()>, path: &[u8]| {
            PathTracker::with_origin(trie.read_zipper_at_path(path), path)
        }
    );

    zipper_iteration_tests::zipper_iteration_tests!(path_tracker,
        |keys: &[&[u8]]| {
            keys.into_iter().map(|k| (k, ())).collect::<PathMap<()>>()
        },
        |trie: &mut PathMap<()>, path: &[u8]| {
            PathTracker::with_origin(trie.read_zipper_at_path(path), path)
        }
    );
}
