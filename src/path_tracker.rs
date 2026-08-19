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
    #[inline] fn depth(&self) -> usize { self.path.len() - self.origin_len }
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
    fn descend_indexed_byte(&mut self, child_idx: usize) -> Option<u8> {
        let byte = self.zipper.descend_indexed_byte(child_idx)?;
        self.path.push(byte);
        Some(byte)
    }
    fn descend_first_byte(&mut self) -> Option<u8> {
        let byte = self.zipper.descend_first_byte()?;
        self.path.push(byte);
        Some(byte)
    }
    fn descend_until_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        //Fan the descended bytes out to our own path buffer as well as the caller's observer
        self.zipper.descend_until_observed(&mut (&mut self.path, &mut *obs))
    }
    fn ascend(&mut self, steps: usize) -> usize {
        let ascended = self.zipper.ascend(steps);
        self.path.truncate(self.path.len() - ascended);
        ascended
    }
    fn ascend_byte(&mut self) -> bool {
        if self.zipper.ascend_byte() {
            self.path.pop();
            true
        } else {
            false
        }
    }
    fn ascend_until(&mut self) -> usize {
        let ascended = self.zipper.ascend_until();
        self.path.truncate(self.path.len() - ascended);
        ascended
    }
    fn ascend_until_branch(&mut self) -> usize {
        let ascended = self.zipper.ascend_until_branch();
        self.path.truncate(self.path.len() - ascended);
        ascended
    }
    fn to_next_step<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        self.zipper.to_next_step(&mut (&mut self.path, &mut *obs))
    }
    fn to_next_sibling_byte(&mut self) -> Option<u8> {
        let byte = self.zipper.to_next_sibling_byte()?;
        *self.path.last_mut().expect("path must not be empty") = byte;
        Some(byte)
    }
    fn to_prev_sibling_byte(&mut self) -> Option<u8> {
        let byte = self.zipper.to_prev_sibling_byte()?;
        *self.path.last_mut().expect("path must not be empty") = byte;
        Some(byte)
    }
}


impl<Z: ZipperIteration> ZipperIteration for PathTracker<Z> {
    //Each method delegates to the wrapped zipper, so it can use its own native implementation, and
    //fans the reported movements out to this tracker's path buffer as well as the caller's observer
    fn to_next_val<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        self.zipper.to_next_val(&mut (&mut self.path, &mut *obs))
    }
    fn descend_last_path<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        self.zipper.descend_last_path(&mut (&mut self.path, &mut *obs))
    }
    fn descend_first_k_path<Obs: PathObserver>(&mut self, k: usize, obs: &mut Obs) -> bool {
        self.zipper.descend_first_k_path(k, &mut (&mut self.path, &mut *obs))
    }
    fn to_next_k_path<Obs: PathObserver>(&mut self, k: usize, obs: &mut Obs) -> bool {
        self.zipper.to_next_k_path(k, &mut (&mut self.path, &mut *obs))
    }
}

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
