use core::cell::UnsafeCell;

use num_traits::{PrimInt, zero};
use crate::trie_node::*;
use crate::zipper::*;
use crate::ring::{Lattice, DistributiveLattice, PartialDistributiveLattice, PartialQuantale};
use crate::zipper_tracking::*;

/// A map type that uses byte slices `&[u8]` as keys
///
/// This type is implemented using some of the approaches explained in the
/// ["Bitwise trie with bitmap" Wikipedia article](https://en.wikipedia.org/wiki/Bitwise_trie_with_bitmap).
///
/// ```
/// # use pathmap::trie_map::BytesTrieMap;
/// let mut map = BytesTrieMap::<String>::new();
/// map.insert("one", "1".to_string());
/// map.insert("two", "2".to_string());
///
/// assert!(map.contains("one"));
/// assert_eq!(map.get("two"), Some(&"2".to_string()));
/// assert!(!map.contains("three"));
/// ```
pub struct BytesTrieMap<V> {
    root: UnsafeCell<TrieNodeODRc<V>>,
    zipper_tracker: ZipperTracker,
}

impl<V: Clone> Clone for BytesTrieMap<V> {
    fn clone(&self) -> Self {
        Self::new_with_root(self.root().clone())
    }
}

impl<V: Clone> BytesTrieMap<V> {
    #[inline]
    pub(crate) fn root(&self) -> &TrieNodeODRc<V> {
        unsafe{ &*self.root.get() }
    }
    #[inline]
    pub(crate) fn root_mut(&mut self) -> &mut TrieNodeODRc<V> {
        self.root.get_mut()
    }

    /// Creates a new empty map
    pub fn new() -> Self {
        #[cfg(feature = "all_dense_nodes")]
        let root = TrieNodeODRc::new(crate::dense_byte_node::DenseByteNode::new());
        #[cfg(not(feature = "all_dense_nodes"))]
        let root = TrieNodeODRc::new(crate::line_list_node::LineListNode::new());
        Self::new_with_root(root)
    }

    /// Internal Method.  Creates a new BytesTrieMap with the supplied root node
    #[inline]
    pub(crate) fn new_with_root(root: TrieNodeODRc<V>) -> Self {
        Self {
            root: UnsafeCell::new(root),
            zipper_tracker: ZipperTracker::default(),
        }
    }

    pub fn range<const BE : bool, R : PrimInt + std::ops::AddAssign + num_traits::ToBytes + std::fmt::Display>(start: R, stop: R, step: R, value: V) -> BytesTrieMap<V> {
        // #[cfg(feature = "all_dense_nodes")]
        // we can extremely efficiently generate ranges, but currently we're limited to range(0, BASE**j, k < BASE)
        // let root = crate::dense_byte_node::_so_range(step as u8, 4);
        // BytesTrieMap::<()>::new_with_root(root)
        //fallback

        //GOAT, this method is highly sub-optimal.  It should be possible to populate a range in log n time,
        // rather than linear time.  Adam has already written code for this, but it's specific to the DenseByteNode
        // and is commented out in that file
        let mut new_map = Self::new();
        let mut zipper = new_map.write_zipper();

        let mut i = start;
        let positive = step > zero();
        loop {
            if positive { if i >= stop { break } }
            else { if i <= step { break } }
            // println!("{}", i);
            if BE { zipper.descend_to(i.to_be_bytes()); }
            else { zipper.descend_to(i.to_le_bytes()); }
            zipper.set_value(value.clone());
            zipper.reset();

            i += step;
        }
        drop(zipper);

        new_map
    }

    /// Internal Method.  Removes and returns the root from a BytesTrieMap
    #[inline]
    pub(crate) fn into_root(self) -> Option<TrieNodeODRc<V>> {
        if !self.root().borrow().node_is_empty() {
            Some(self.root.into_inner())
        } else {
            None
        }
    }

    /// Creates a new [ReadZipper] starting at the root of a BytesTrieMap
    pub fn read_zipper(&self) -> ReadZipper<V> {
        let zipper_tracker = self.zipper_tracker.new_read_path(&[]);
        ReadZipper::new_with_node_and_path_internal(self.root().borrow(), &[], Some(0), None, zipper_tracker)
    }

    /// Creates a new [ReadZipper] with the specified path from the root of the map
    pub fn read_zipper_at_path<'a, 'k>(&'a self, path: &'k[u8]) -> ReadZipper<'a, 'k, V> {
        let zipper_tracker = self.zipper_tracker.new_read_path(path);
        ReadZipper::new_with_node_and_path(self.root().borrow(), path.as_ref(), Some(path.len()), zipper_tracker)
    }

    /// Creates a new [WriteZipper] starting at the root of a BytesTrieMap
    pub fn write_zipper(&mut self) -> WriteZipper<V> {
        let zipper_tracker = self.zipper_tracker.new_write_path(&[]);
        WriteZipper::new_with_node_and_path_internal(self.root_mut(), &[], zipper_tracker)
    }

    /// Creates a new [WriteZipper] with the specified path from the root of the map
    pub fn write_zipper_at_path<'a, 'k>(&'a mut self, path: &'k[u8]) -> WriteZipper<'a, 'k, V> {
        let zipper_tracker = self.zipper_tracker.new_write_path(path);
        WriteZipper::new_with_node_and_path(self.root_mut(), path, zipper_tracker)
    }

    /// Creates a new [WriteZipper] with the specified path from the root of the map, where the
    /// caller guarantees that no existing zippers may access the specified path
    ///
    /// NOTE: There is no safe version of this method because we don't want to pay the overhead of
    /// tracking every ReadZipper's path in a release build
    ///
    //GOAT!!  I Realized this is unsound because the TrieMap direct methods can still traverse from the
    // root, and potentially read parts of the trie that a WriteZipper is in the process of modifying.
    //Instead I propose a "ZipperMaker" that takes a mutable borrow of the map, and can dispense both read
    // and write zippers
    pub unsafe fn write_zipper_at_exclusive_path_unchecked<'a, 'k>(&'a self, path: &'k[u8]) -> WriteZipper<'a, 'k, V> {
        let path_len = path.len();
        if path_len == 0 {
            panic!("Fatal Error: Root path cannot be modified without mutable access to the map.  Use TrieMap::write_zipper");
        }
        let zipper_tracker = self.zipper_tracker.new_write_path(path);
        let (_created_node, parent_node) = prepare_exclusive_write_path(&mut *self.root.get(), &path[..path_len-1]);
        let _created_cf = parent_node.make_mut().as_dense_mut().unwrap().prepare_cf(path[path_len-1]);
        //GOAT QUESTION: Do we want to pay for pruning the parent of a zipper when the zipper get's dropped?
        // If we do, we can store (_created_node || _created_cf) in the zipper, so we can opt out of trying
        // to prune the zipper's path.
        WriteZipper::new_with_node_and_path_internal(parent_node, &path[path_len-1..], zipper_tracker)
    }

    /// Returns an iterator over all key-value pairs within the map
    ///
    /// NOTE: This is much less efficient than using the [read_zipper](Self::read_zipper) method
    pub fn iter<'a>(&'a self) -> impl Iterator<Item=(Vec<u8>, &'a V)> + 'a {
        self.read_zipper().into_iter()
    }

    /// Returns a [BytesTrieMapCursor] to traverse all key-value pairs within the map.  This is more efficient
    /// than using [iter](Self::iter), but is not compatible with the [Iterator] trait
    ///
    /// WARNING: This API will be deprecated in favor of the [read_zipper](Self::read_zipper) method
    pub fn cursor<'a>(&'a self) -> BytesTrieMapCursor<'a, V> {
        BytesTrieMapCursor::new(self)
    }

    pub fn old_cursor<'a>(&'a self) -> crate::old_dense_cursor::OldCursor<'a, V> {
        crate::old_dense_cursor::OldCursor::new(self)
    }

    /// Returns `true` if the map contains a value at the specified key, otherwise returns `false`
    pub fn contains<K: AsRef<[u8]>>(&self, k: K) -> bool {
        let k = k.as_ref();

        //NOTE: Here is the old impl traversing without the zipper.  The zipper version appears to be
        // nearly the same perf.  All averages within 3% in both directions, and the zipper impl being
        // faster as often as the native (non-zipper) version
        // let (node, remaining_key) = traverse_to_leaf(self.root.borrow(), k);
        // node.node_contains_val(remaining_key)

        let zipper = self.read_zipper_at_path(k);
        zipper.is_value()
    }

    /// Returns `true` if a path is contained within the map, or `false` otherwise
    pub fn contains_path<K: AsRef<[u8]>>(&self, k: K) -> bool {
        let k = k.as_ref();
        let zipper = self.read_zipper_at_path(k);
        zipper.path_exists()
    }

//GOAT, in light of PathMap's behavior holistically an a potential collision with WriteZipper::insert_prefix,
// `insert` really should be called set_value
    /// Inserts `v` into the map at `k`.  Panics if `k` has a zero length
    ///
    /// Returns `Some(replaced_val)` if an existing value was replaced, otherwise returns `None` if
    /// the value was added to the map without replacing anything.
    pub fn insert<K: AsRef<[u8]>>(&mut self, k: K, v: V) -> Option<V> {
        let k = k.as_ref();

        //NOTE: Here is the old impl traversing without the zipper.  Kept here for benchmarking purposes
        // However, the zipper version is basically identical performance, within the margin of error 
        // traverse_to_leaf_static_result(&mut self.root, k,
        // |node, remaining_key| node.node_set_val(remaining_key, v),
        // |_new_leaf_node, _remaining_key| None)

        let mut zipper = self.write_zipper_at_path(k);
        zipper.set_value(v)
    }

    //GOAT, make a separate `join_with` that is similar to `insert` except replaces V with a merged V rather
    // than replacing it

    /// Removes the value at `k` from the map and returns it, or returns None if there was no value at `k`
    pub fn remove<K: AsRef<[u8]>>(&mut self, k: K) -> Option<V> {
        let k = k.as_ref();
        //NOTE: we're descending the zipper rather than creating it at the path so it will be allowed to
        // prune the branches.  A WriteZipper can't move above its root, so it couldn't prune otherwise
        let mut zipper = self.write_zipper();
        zipper.descend_to(k);
        zipper.remove_value()
    }

    //GOAT-redo this with the WriteZipper::get_value_or_insert, although I may need an alternate function
    // that consumes the zipper in order to be allowed to return the correct lifetime
    //
    // pub fn update<K: AsRef<[u8]>, F: FnOnce()->V>(&mut self, k: K, default_f: F) -> &mut V {
    //     let k = k.as_ref();

    //     traverse_to_leaf_mut(&mut self.root, k,
    //     |node, remaining_key| node.node_update_val(remaining_key, Box::new(default_f)),
    //     |new_leaf_node, remaining_key| new_leaf_node.node_get_val_mut(remaining_key).unwrap())
    // }

    /// Returns `true` if the map is empty, otherwise returns `false`
    pub fn is_empty(&self) -> bool {
        self.root().borrow().node_is_empty()
    }

    /// Returns a reference to the value at the specified path
    pub fn get<K: AsRef<[u8]>>(&self, k: K) -> Option<&V> {
        let k = k.as_ref();

        //NOTE: Here is the old impl traversing without the zipper.  The zipper version appears to be
        // nearly the same perf.  All averages within 3% in both directions, and the zipper impl being
        // faster as often as the native (non-zipper) version
        // let (node, remaining_key) = traverse_to_leaf(self.root.borrow(), k);
        // node.node_get_val(remaining_key)

        let zipper = self.read_zipper_at_path(k);
        zipper.get_value()
    }

    /// Returns the total number of values contained within the map
    ///
    /// WARNING: This is not a cheap method. It may have an order-N cost
    pub fn val_count(&self) -> usize {
        return val_count_below_root(self.root().borrow())
    }

    /// Returns a new `BytesTrieMap` where the paths in `self` are restricted by the paths leading to 
    /// values in `other`
    pub fn restrict(&self, other: &Self) -> Self {
        match self.root().borrow().prestrict_dyn(other.root().borrow()) {
            Some(new_root) => Self::new_with_root(new_root),
            None => Self::new()
        }
    }
}

/// An iterator-like object that traverses key-value pairs in a [BytesTrieMap], however only one
/// returned reference may exist at a given time
///
/// TODO: Soon we may want to deprecate this API entirely, as it is a subset of the functionality
/// available from the [crate::zipper::Zipper].  However, the current implementation is about 25% faster when comparing
/// like-for-like workloads that are non-pathological.  And this is including the overhead of allocating
/// boxed node_iterators.  I haven't investigated why the zipper isn't faster, but my guess is is 
/// that the probable cause is the higher cost of traversing using inner-paths instead of just treating
/// all contained sub-nodes as a flat collection of values and onward-links.  I believe it would probably
/// be possible to exceed the current BytesTrieMapCursor traversal speed with a Zipper, with a little
/// more work.  Possibly by using a fixed-size "token" that the node may used to encode some data about
/// its current position and intermediate traversal state.
pub struct BytesTrieMapCursor<'a, V> where V : Clone {
    prefix_buf: Vec<u8>,
    prefix_idx: Vec<usize>,
    btnis: Vec<Box<dyn Iterator<Item=(&'a[u8], ValOrChildRef<'a, V>)> + 'a>>,
}

impl <'a, V : Clone> BytesTrieMapCursor<'a, V> {
    fn new(btm: &'a BytesTrieMap<V>) -> Self {
        const EXPECTED_DEPTH: usize = 16;
        let mut prefix_idx = Vec::with_capacity(EXPECTED_DEPTH);
        prefix_idx.push(0);
        let mut btnis = Vec::with_capacity(EXPECTED_DEPTH);
        btnis.push(btm.root().borrow().boxed_node_iter());
        Self {
            prefix_buf: Vec::with_capacity(256),
            prefix_idx,
            btnis,
        }
    }
}

impl <'a, V : Clone> BytesTrieMapCursor<'a, V> {
    pub fn next(&mut self) -> Option<(&[u8], &'a V)> {
        loop {
            match self.btnis.last_mut() {
                None => { return None }
                Some(last) => {
                    match last.next() {
                        None => {
                            // decrease view len by one level
                            self.prefix_idx.pop();
                            self.btnis.pop();
                        }
                        Some((key_bytes, item)) => {
                            let key_start = *self.prefix_idx.last().unwrap();
                            self.prefix_buf.truncate(key_start);
                            self.prefix_buf.extend(key_bytes);

                            match item {
                                ValOrChildRef::Val(val) => return Some((&self.prefix_buf[..], val)),
                                ValOrChildRef::Child(child) => {
                                    self.prefix_idx.push(self.prefix_buf.len());
                                    self.btnis.push(child.boxed_node_iter())
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

impl<V: Clone, K: AsRef<[u8]>> FromIterator<(K, V)> for BytesTrieMap<V> {
    fn from_iter<I: IntoIterator<Item=(K, V)>>(iter: I) -> Self {
        let mut map = Self::new();
        for (key, val) in iter {
            map.insert(key, val);
        }
        map
    }
}

impl<V: Clone + Lattice> Lattice for BytesTrieMap<V> {
    fn join(&self, other: &Self) -> Self {
        Self::new_with_root(self.root().join(other.root()))
    }

    fn join_into(&mut self, other: Self) {
        if let Some(other_root) = other.into_root() {
            self.root_mut().join_into(other_root)
        }
    }

    fn meet(&self, other: &Self) -> Self {
        match self.root().meet(other.root()) {
            Some(new_root) => Self::new_with_root(new_root),
            None => Self::new()
        }
    }

    fn bottom() -> Self {
        BytesTrieMap::new()
    }
}

impl<V: Clone + PartialDistributiveLattice> DistributiveLattice for BytesTrieMap<V> {
    fn subtract(&self, other: &Self) -> Self {
        Self::new_with_root(self.root().subtract(other.root()))
    }
}

impl<V: Clone + PartialDistributiveLattice> PartialDistributiveLattice for BytesTrieMap<V> {
    fn psubtract(&self, other: &Self) -> Option<Self> {
        let s = self.root().subtract(other.root());
        if s.borrow().node_is_empty() { None }
        else { Some(Self::new_with_root(s)) }
    }
}

impl<V: Clone> PartialQuantale for BytesTrieMap<V> {
    fn prestrict(&self, other: &Self) -> Option<Self> where Self: Sized {
        self.root().prestrict(other.root()).map(|r| Self::new_with_root(r) )
    }
}

#[cfg(test)]
mod tests {
    use crate::trie_map::*;
    use crate::ring::Lattice;

    #[test]
    fn map_test() {
        let mut map = BytesTrieMap::new();
        //NOW: map contains an empty ListNode

        map.insert("aaaaa", "aaaaa");
        assert_eq!(map.get("aaaaa").unwrap(), &"aaaaa");
        //NOW: map contains a ListNode with slot_0 filled by a value

        map.insert("bbbbb", "bbbbb");
        assert_eq!(map.get("bbbbb").unwrap(), &"bbbbb");
        //NOW: map contains a ListNode with slot_0 and slot_1 filled by values

        map.insert("ccccc", "ccccc");
        assert_eq!(map.get("aaaaa").unwrap(), &"aaaaa");
        assert_eq!(map.get("bbbbb").unwrap(), &"bbbbb");
        assert_eq!(map.get("ccccc").unwrap(), &"ccccc");
        //NOW: map contains a DenseByteNode, with 3 separate ListNodes, each containing one value

        map.insert("ddddd", "ddddd");
        assert_eq!(map.get("ddddd").unwrap(), &"ddddd");
        //NOW: map contains a DenseByteNode, with 4 separate ListNodes, each containing one value

        map.insert("abbbb", "abbbb");
        assert_eq!(map.get("abbbb").unwrap(), &"abbbb");
        //NOW: Dense("a"..) -> List("aaaa", "bbbb")

        map.insert("aaaab", "aaaab");
        assert_eq!(map.get("aaaaa").unwrap(), &"aaaaa");
        assert_eq!(map.get("bbbbb").unwrap(), &"bbbbb");
        assert_eq!(map.get("abbbb").unwrap(), &"abbbb");
        assert_eq!(map.get("aaaab").unwrap(), &"aaaab");
        //NOW: Dense("a"..) -> List("aaa", "bbbb") -> List("a", "b")

        map.insert("aaaac", "aaaac");
        assert_eq!(map.get("aaaaa").unwrap(), &"aaaaa");
        assert_eq!(map.get("aaaab").unwrap(), &"aaaab");
        assert_eq!(map.get("aaaac").unwrap(), &"aaaac");
        //NOW: Dense("a"..) -> List("aaa", "bbbb") -> Dense("a", "b", "c")

        map.insert("acaaa", "acaaa");
        assert_eq!(map.get("aaaaa").unwrap(), &"aaaaa");
        assert_eq!(map.get("aaaab").unwrap(), &"aaaab");
        assert_eq!(map.get("aaaac").unwrap(), &"aaaac");
        assert_eq!(map.get("abbbb").unwrap(), &"abbbb");
        assert_eq!(map.get("acaaa").unwrap(), &"acaaa");
        //NOW: Dense("a"..) -> Dense("a", "b", "c") a-> List("aa") -> Dense("a", "b", "c")
        //                                          b-> List("bbb")
        //                                          c-> List("aaa")
    }

    #[test]
    fn long_key_map_test() {
        let mut map = BytesTrieMap::new();

        map.insert("aaaaaaaaaa01234567890123456789", 30);
        assert_eq!(map.get("aaaaaaaaaa01234567890123456789").unwrap(), &30);

        map.insert("bbbbbbbbbb012345678901234567891", 31);
        assert_eq!(map.get("bbbbbbbbbb012345678901234567891").unwrap(), &31);

        map.insert("cccccccccc012345678901234567890123456789", 40);
        assert_eq!(map.get("cccccccccc012345678901234567890123456789").unwrap(), &40);

        map.insert("dddddddddd01234567890123456789012345678901234", 45);
        assert_eq!(map.get("dddddddddd01234567890123456789012345678901234").unwrap(), &45);

        map.insert("eeeeeeeeee01234567890123456789012345678901234567890123456789012345678901234567890123456789", 90);
        assert_eq!(map.get("eeeeeeeeee01234567890123456789012345678901234567890123456789012345678901234567890123456789").unwrap(), &90);
    }

    #[test]
    fn map_contains_path_test() {
        let mut btm = BytesTrieMap::new();
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

        assert_eq!(btm.contains_path(b"can"), true);
        assert_eq!(btm.contains_path(b"cannon"), true);
        assert_eq!(btm.contains_path(b"cannonade"), false);
        assert_eq!(btm.contains_path(b""), true);
    }

    #[test]
    fn map_remove_test() {
        let mut map = BytesTrieMap::new();
        map.insert("aaaaa", "aaaaa");
        map.insert("bbbbb", "bbbbb");
        map.insert("ccccc", "ccccc");
        map.insert("ddddd", "ddddd");
        map.insert("abbbb", "abbbb");
        map.insert("aaaab", "aaaab");
        map.insert("aaaac", "aaaac");
        map.insert("acaaa", "acaaa");
        assert_eq!(map.val_count(), 8);

        assert_eq!(map.remove(b"aaaaa"), Some("aaaaa"));
        assert_eq!(map.val_count(), 7);
        assert_eq!(map.remove(b"acaaa"), Some("acaaa"));
        assert_eq!(map.val_count(), 6);
        assert_eq!(map.remove(b"cccccnot-a-real-key"), None);
        assert_eq!(map.val_count(), 6);
        assert_eq!(map.remove(b"aaaac"), Some("aaaac"));
        assert_eq!(map.val_count(), 5);
        assert_eq!(map.remove(b"aaaab"), Some("aaaab"));
        assert_eq!(map.val_count(), 4);
        assert_eq!(map.remove(b"abbbb"), Some("abbbb"));
        assert_eq!(map.val_count(), 3);
        assert_eq!(map.remove(b"ddddd"), Some("ddddd"));
        assert_eq!(map.val_count(), 2);
        assert_eq!(map.remove(b"ccccc"), Some("ccccc"));
        assert_eq!(map.val_count(), 1);
        assert_eq!(map.remove(b"bbbbb"), Some("bbbbb"));
        assert_eq!(map.val_count(), 0);
        assert!(map.is_empty());
    }

    #[test]
    fn map_update_test() {
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        let mut btm: BytesTrieMap<u64> = rs.into_iter().enumerate().map(|(i, k)| (k, i as u64)).collect();

        let mut zipper = btm.write_zipper_at_path(b"cannon");
        assert_eq!(zipper.get_value_or_insert(42), &2);
        drop(zipper);

        let mut zipper = btm.write_zipper_at_path(b"dagger");
        assert_eq!(zipper.get_value_or_insert(42), &42);
    }

    #[test]
    fn map_join_test() {
        let mut a = BytesTrieMap::<usize>::new();
        let mut b = BytesTrieMap::<usize>::new();
        let rs = ["Abbotsford", "Abbottabad", "Abcoude", "Abdul Hakim", "Abdulino", "Abdullahnagar", "Abdurahmoni Jomi", "Abejorral", "Abelardo Luz"];
        for (i, path) in rs.into_iter().enumerate() {
            if i % 2 == 0 {
                a.insert(path, i);
            } else {
                b.insert(path, i);
            }
        }

        let joined = a.join(&b);
        for (path, i) in joined.iter() {
            // println!("{} {}", std::str::from_utf8(&path).unwrap(), i);
            assert_eq!(rs[*i].as_bytes(), &path);
        }
        assert_eq!(joined.val_count(), rs.len());
    }
}
