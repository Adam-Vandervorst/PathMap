
use core::ptr::NonNull;
use core::cell::Cell;
use std::marker::PhantomData;
use crate::trie_node::*;
use crate::zipper::*;
use crate::zipper_tracking::*;

/// Used to make multiple simultaneous zippers in the same map
pub struct ZipperHead<'a, V> {
    root: Cell<NonNull<TrieNodeODRc<V>>>,
    tracker_paths: SharedTrackerPaths,
    _variance: PhantomData<&'a mut TrieNodeODRc<V>>
}

impl<'a, V: Clone + Send + Sync> ZipperHead<'a, V> {

    pub(crate) fn new(root: &'a mut TrieNodeODRc<V>) -> Self {
        Self {
            root: Cell::new(NonNull::from(root)),
            tracker_paths: SharedTrackerPaths::default(),
            _variance: PhantomData
        }
    }

    /// A more efficient version of [read_zipper_at_path](Self::read_zipper_at_path), where the returned
    /// zipper is constrained by the `'path` lifetime
    pub fn read_zipper_at_borrowed_path<'path>(&self, path: &'path[u8]) -> ReadZipperTracked<'a, 'path, V> {
        let zipper_tracker = ZipperTracker::new_read_tracker(self.tracker_paths.clone(), path);
        let root = unsafe{ self.root.get().as_ref() };
        ReadZipperTracked::new_with_node_and_path(root.borrow(), path.as_ref(), Some(path.len()), zipper_tracker)
    }

    /// A more efficient version of [read_zipper_at_path_unchecked](Self::read_zipper_at_path_unchecked),
    /// where the returned zipper is constrained by the `'path` lifetime
    pub unsafe fn read_zipper_at_borrowed_path_unchecked<'path>(&self, path: &'path[u8]) -> ReadZipperUntracked<'a, 'path, V> {
        let root = unsafe{ self.root.get().as_ref() };
        #[cfg(debug_assertions)]
        {
            let zipper_tracker = ZipperTracker::new_read_tracker(self.tracker_paths.clone(), path);
            ReadZipperUntracked::new_with_node_and_path(root.borrow(), path.as_ref(), Some(path.len()), Some(zipper_tracker))
        }
        #[cfg(not(debug_assertions))]
        {
            ReadZipperUntracked::new_with_node_and_path(root.borrow(), path.as_ref(), Some(path.len()))
        }
    }

    /// Creates a new [ReadZipper] with the specified path from the `ZipperHead`
    pub fn read_zipper_at_path(&self, path: &[u8]) -> ReadZipperTracked<'a, 'static, V> {
        let zipper_tracker = ZipperTracker::new_read_tracker(self.tracker_paths.clone(), path);
        let root = unsafe{ self.root.get().as_ref() };
        ReadZipperTracked::new_with_node_and_cloned_path(root.borrow(), path.as_ref(), Some(path.len()), zipper_tracker)
    }

    /// Creates a new [ReadZipper] with the specified path from the `ZipperHead`, where the caller
    /// guarantees that there will be no conflicts with any WriteZippers at any time in the future
    pub unsafe fn read_zipper_at_path_unchecked(&self, path: &[u8]) -> ReadZipperUntracked<'a, 'static, V> {
        let root = unsafe{ self.root.get().as_ref() };
        #[cfg(debug_assertions)]
        {
            let zipper_tracker = ZipperTracker::new_read_tracker(self.tracker_paths.clone(), path);
            ReadZipperUntracked::new_with_node_and_cloned_path(root.borrow(), path.as_ref(), Some(path.len()), Some(zipper_tracker))
        }
        #[cfg(not(debug_assertions))]
        {
            ReadZipperUntracked::new_with_node_and_cloned_path(root.borrow(), path.as_ref(), Some(path.len()))
        }
    }

    /// Creates a new [WriteZipper] with the specified path from the `ZipperHead`
    pub fn write_zipper_at_exclusive_path<'k, K: AsRef<[u8]>>(&self, path: K) -> WriteZipperTracked<'a, 'k, V> {
        let path = path.as_ref();
        let zipper_tracker = ZipperTracker::new_write_tracker(self.tracker_paths.clone(), path);
        let root = unsafe{ self.root.get().as_mut() };
        let zipper_root_node = prepare_exclusive_write_path(root, &path);
        WriteZipperTracked::new_with_node_and_path_internal(zipper_root_node, &[], zipper_tracker)
    }

    /// Creates a new [WriteZipper] with the specified path from the `ZipperHead`, where the caller guarantees
    /// that no existing zippers may access the specified path at any time before the `WriteZipper` is dropped
    pub unsafe fn write_zipper_at_exclusive_path_unchecked<'k, K: AsRef<[u8]>>(&self, path: K) -> WriteZipperUntracked<'a, 'k, V> {
        let path = path.as_ref();
        let root = unsafe{ self.root.get().as_mut() };
        let zipper_root_node = prepare_exclusive_write_path(root, &path);

        #[cfg(debug_assertions)]
        {
            let tracker = ZipperTracker::new_write_tracker(self.tracker_paths.clone(), path);
            WriteZipperUntracked::new_with_node_and_path_internal(zipper_root_node, &[], Some(tracker))
        }
        #[cfg(not(debug_assertions))]
        {
            WriteZipperUntracked::new_with_node_and_path_internal(zipper_root_node, &[])
        }
    }
}

#[cfg(test)]
mod tests {
    use std::{thread, thread::ScopedJoinHandle};
    use crate::tests::prefix_key;
    use crate::trie_map::BytesTrieMap;
    use crate::zipper::*;

    #[test]
    fn parallel_insert_test() {
        let thread_cnt = 8;
        let elements = 1024;
        let elements_per_thread = elements / thread_cnt;

        let mut map = BytesTrieMap::<usize>::new();

        thread::scope(|scope| {
            let elements_per_thread = elements / thread_cnt;

            //Preallocate all zippers
            let zipper_head = map.zipper_head();
            let mut zippers = Vec::with_capacity(thread_cnt);
            for n in (0..thread_cnt).into_iter().rev() {
                let path = &[n as u8];
                let zipper = zipper_head.write_zipper_at_exclusive_path(path);
                zippers.push(zipper);
            };

            let mut threads: Vec<ScopedJoinHandle<()>> = Vec::with_capacity(thread_cnt);

            //Spawn all the threads
            for n in 0..thread_cnt {
                let mut zipper = zippers.pop().unwrap();
                let thread = scope.spawn(move || {
                    for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
                        zipper.descend_to(prefix_key(&(i as u64)));
                        assert!(zipper.set_value(i).is_none());
                        zipper.reset();
                    }
                });
                threads.push(thread);
            }

            //Wait for the threads to finish
            for thread in threads {
                thread.join().unwrap();
            }
        });

        //Test that the values set by the threads are correct
        for n in 0..thread_cnt {
            for i in (n * elements_per_thread)..((n+1) * elements_per_thread) {
                let mut path = vec![n as u8];
                path.extend(prefix_key(&(i as u64)));
                assert_eq!(map.get(path), Some(&i));
            }
        }
    }

    #[test]
    fn zipper_head1() {
        let mut map = BytesTrieMap::<isize>::new();

        //Make a ZipperHead for the whole map, and make a WriteZipper for a branch within the map
        let map_head = map.zipper_head();
        let mut zipper = map_head.write_zipper_at_exclusive_path(&[0]);
        zipper.set_value(0);
        drop(zipper);
        assert_eq!(map.get(&[0]), Some(&0));
    }

    #[test]
    fn zipper_head2() {
        let mut map = BytesTrieMap::<isize>::new();

        //Make a ZipperHead for the whole map, and then a zipper at the root
        //This degenerate case should be identical to making a WriteZipper from the map root
        let map_head = map.zipper_head();
        let mut zipper = map_head.write_zipper_at_exclusive_path(&[]);
        zipper.descend_to(b"test");
        zipper.set_value(0);
        drop(zipper);
        assert_eq!(map.get("test"), Some(&0));
    }

    #[test]
    fn zipper_head3() {
        let mut map = BytesTrieMap::<isize>::new();

        //Make a WriteZipper in a plece that will require creating multiple nodes
        let map_head = map.zipper_head();
        let mut zipper = map_head.write_zipper_at_exclusive_path(b"test");
        zipper.descend_to(b":2");
        zipper.set_value(2);
        drop(zipper);
        assert_eq!(map.get("test:2"), Some(&2));
    }

    #[test]
    fn zipper_head4() {
        let mut map = BytesTrieMap::<isize>::new();

        //Make a WriteZipper in a plece that will require splitting an existing path
        map.insert(b"test:3", 3);
        let map_head = map.zipper_head();
        let mut zipper = map_head.write_zipper_at_exclusive_path(b"test");
        zipper.descend_to(b":3");
        assert_eq!(zipper.get_value(), Some(&3));
        zipper.ascend_byte();
        zipper.descend_to_byte(b'2');
        zipper.set_value(2);
        drop(zipper);

// for (k, v) in map.iter() {
//     println!("{} = {v}", String::from_utf8_lossy(&k));
// }
        assert_eq!(map.get("test:2"), Some(&2));
        assert_eq!(map.get("test:3"), Some(&3));
    }

    #[test]
    fn zipper_head5() {
        let mut map = BytesTrieMap::<isize>::new();

        //Work around a "stump" (aka a zipper root, aka a CellByteNodes that belonged to a zipper that was dropped)
        let map_head = map.zipper_head();
        let zipper = map_head.write_zipper_at_exclusive_path([3]);
        drop(zipper);
        let mut zipper = map_head.write_zipper_at_exclusive_path([3, 193, 49]);
        zipper.descend_to_byte(42);
        zipper.set_value(42);
        drop(zipper);
        assert_eq!(map.get([3, 193, 49, 42]), Some(&42));
    }

    #[test]
    fn hierarchical_zipper_heads1() {
        let mut map = BytesTrieMap::<isize>::new();

        //Make a ZipperHead for the whole map, and two child zippers
        let map_head = map.zipper_head();
        let mut a_zipper = map_head.write_zipper_at_exclusive_path(b"a");
        let mut b_zipper = map_head.write_zipper_at_exclusive_path(b"b");

        //Do some interleaved work with the two zippers
        a_zipper.descend_to(b"+value");
        a_zipper.set_value(0);
        a_zipper.reset();
        b_zipper.descend_to(b"+value");
        b_zipper.set_value(1);
        b_zipper.reset();

        //Try pre-creating trie in the parent that will be visited by the child zipper
        b_zipper.descend_to(b"-children-0+metadata");
        b_zipper.set_value(-3);
        b_zipper.ascend(10);

        //Make a ZipperHead on the WriteZipper, and make two more parallel zippers
        let b_head = b_zipper.zipper_head();
        let mut b0_zipper = b_head.write_zipper_at_exclusive_path(b"0");
        let mut b1_zipper = b_head.write_zipper_at_exclusive_path(b"1");

        //Do some interleaved work with them
        b0_zipper.descend_to(b"+value");
        b0_zipper.set_value(4);
        b1_zipper.descend_to(b"+value");
        b1_zipper.set_value(-5);

        //Drop the child zippers, so we can move the parent again
        drop(b0_zipper);
        drop(b1_zipper);

        //Visit some of the nodes the child zippers poked at, and fix their values with the parent
        b_zipper.descend_to(b"0+metadata");
        b_zipper.set_value(3);
        b_zipper.reset();
        b_zipper.descend_to(b"-children-1+value");
        b_zipper.set_value(5);

        //Test chopping an existing non-forking path, and inserting a new ZipperHead in there
        b_zipper.reset();
        b_zipper.descend_to(b"-children-0+meta");
        let b_head = b_zipper.zipper_head();
        let mut b0_zipper = b_head.write_zipper_at_exclusive_path([]);
        b0_zipper.descend_to(b"bolic");
        b0_zipper.set_value(6);
        drop(b0_zipper);

        //Test making a ZipperHead when the parent WriteZipper is at a location that does not exist yet
        a_zipper.reset();
        a_zipper.descend_to(b"-children-");
        let a_head = a_zipper.zipper_head();
        let mut a0_zipper = a_head.write_zipper_at_exclusive_path("0");
        a0_zipper.descend_to(b"+value");
        a0_zipper.set_value(7);
        drop(a0_zipper);

        //We're done.
        drop(a_zipper);
        drop(b_zipper);

        // for (k, v) in map.iter() {
        //     println!("{} {v}", String::from_utf8_lossy(&k));
        // }
        assert_eq!(map.val_count(), 7);
        assert_eq!(map.get(b"a+value").unwrap(), &0);
        assert_eq!(map.get(b"a-children-0+value").unwrap(), &7);
        assert_eq!(map.get(b"b+value").unwrap(), &1);
        assert_eq!(map.get(b"b-children-0+metabolic").unwrap(), &6);
        assert_eq!(map.get(b"b-children-0+metadata").unwrap(), &3);
        assert_eq!(map.get(b"b-children-0+value").unwrap(), &4);
        assert_eq!(map.get(b"b-children-1+value").unwrap(), &5);
    }

    #[test]
    fn hierarchical_zipper_heads2() {
        let mut map = BytesTrieMap::<isize>::new();

        //Make a ZipperHead for the whole map, and two child zippers
        let map_head = map.zipper_head();
        let mut a_zipper = map_head.write_zipper_at_exclusive_path(b"a");
        let mut b_zipper = map_head.write_zipper_at_exclusive_path(b"b");

        //Make a separate ZipperHead on each WriteZipper
        let a_head = a_zipper.zipper_head();
        let b_head = b_zipper.zipper_head();

        //Make some WriteZippers on each head
        let mut a0_zipper = a_head.write_zipper_at_exclusive_path(b"0");
        let mut a1_zipper = a_head.write_zipper_at_exclusive_path(b"1");
        let mut b0_zipper = b_head.write_zipper_at_exclusive_path(b"0");
        let mut b1_zipper = b_head.write_zipper_at_exclusive_path(b"1");

        //Do some interleaved work with them
        a0_zipper.descend_to(b"+value");
        a0_zipper.set_value(0);
        a1_zipper.descend_to(b"+value");
        a1_zipper.set_value(1);
        b0_zipper.descend_to(b"+value");
        b0_zipper.set_value(2);
        b1_zipper.descend_to(b"+value");
        b1_zipper.set_value(3);

        //We're done
        drop(a0_zipper);
        drop(a1_zipper);
        drop(b0_zipper);
        drop(b1_zipper);
        drop(a_zipper);
        drop(b_zipper);

        // for (k, v) in map.iter() {
        //     println!("{} {v}", String::from_utf8_lossy(&k));
        // }
        assert_eq!(map.val_count(), 4);
        assert_eq!(map.get(b"a0+value").unwrap(), &0);
        assert_eq!(map.get(b"a1+value").unwrap(), &1);
        assert_eq!(map.get(b"b0+value").unwrap(), &2);
        assert_eq!(map.get(b"b1+value").unwrap(), &3);
    }

    #[test]
    fn hierarchical_zipper_heads3() {
        let mut map = BytesTrieMap::<isize>::new();

        //Make a ZipperHead for the whole map, and then a zipper for a branch within the map
        let map_head = map.zipper_head();
        let mut top_zipper = map_head.write_zipper_at_exclusive_path(b"0");
        top_zipper.descend_to(b":test:");

        //Make a sub-head at a path that doesn't exist yet
        let sub_head = top_zipper.zipper_head();
        let mut sub_zipper = sub_head.write_zipper_at_exclusive_path(b"5");

        //Set the value at the zipper's root
        sub_zipper.set_value(5);

        //Set a value below the zipper's root
        sub_zipper.descend_to(b":next:1");
        sub_zipper.set_value(1);

        drop(sub_zipper);
        drop(top_zipper);

        assert_eq!(map.get("0:test:5"), Some(&5));
        assert_eq!(map.get("0:test:5:next:1"), Some(&1));
    }
}


//GOAT, Safe zipper_head API should return Option instead of panicking
//
//GOAT, should think harder about a way to avoid carrying around the empty ZipperTracker.
// Maybe try boxing it? A: Boxing doesn't help!!  I should verify that the runtime ZipperTracker is really the issue
// Maybe it's as simple as having a Drop impl?????
