#![cfg_attr(feature = "nightly", allow(internal_features), feature(core_intrinsics))]
#![cfg_attr(feature = "nightly", feature(portable_simd))]

#![doc = include_str!("../README.md")]

#[cfg(feature = "jemalloc")]
use tikv_jemallocator::Jemalloc;

#[cfg(feature = "jemalloc")]
#[global_allocator]
static GLOBAL: Jemalloc = Jemalloc;

/// Traits to implement [ring](https://en.wikipedia.org/wiki/Ring_(mathematics)) and other algebraic
/// operations on tries, such as union, intersection, and subtraction
pub mod ring;

/// A collection indexed by paths of bytes, supporting [algebraic](crate::ring) operations
pub mod trie_map;

/// Cursors that can move over a trie, to inspect and modify contained elements or entire branches
pub mod zipper;

/// Functionality for applying various morphisms to [PathMap] and [Zipper](crate::zipper::Zipper)s
pub mod morphisms;

/// Handy conveniences and utilities to use with a [PathMap]
pub mod utils;

/// Extensions to the API that may or may not become permanant
pub mod experimental;

/// Compact representation of the trie
#[cfg(feature = "arena_compact")]
pub mod arena_compact;

/// Track outstanding zippers to be sure they don't conflict
#[cfg(feature = "zipper_tracking")]
pub mod zipper_tracking;

/// Track outstanding zippers to be sure they don't conflict
#[cfg(not(feature = "zipper_tracking"))]
mod zipper_tracking;

/// Used to create multiple simultaneous zippers from the same parent
mod zipper_head;

/// Used for creating random paths, tries, and zipper movements
#[cfg(feature = "fuzzer")]
pub mod fuzzer;

/// Features to inspect performance properties of trees, for optimizing
#[cfg(feature = "counters")]
pub mod counters;

pub mod timed_span;

pub mod serialization;
pub mod path_serialization;
pub mod tree_serialization;

mod trie_node;
mod write_zipper;
mod product_zipper;
mod trie_ref;
mod dense_byte_node;
pub(crate) mod line_list_node;
mod empty_node;
mod tiny_node;
#[cfg(feature = "bridge_nodes")]
mod bridge_node;

mod old_cursor;

/// A supertrait that encapsulates the bounds for a value that can be put in a [PathMap]
pub trait TrieValue: Clone + Send + Sync + Unpin + 'static {}

impl<T> TrieValue for T where T : Clone + Send + Sync + Unpin + 'static {}

#[cfg(test)]
mod tests {
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use crate::ring::*;
    use crate::trie_map::BytesTrieMap;
    use crate::zipper::*;

    pub(crate) fn prefix_key(k: &u64) -> &[u8] {
        let bs = (8 - k.leading_zeros()/8) as u8;
        let kp: *const u64 = k;
        unsafe { std::slice::from_raw_parts(kp as *const _, (bs as usize).max(1)) }
    }

    pub(crate) fn from_prefix_key(k: Vec<u8>) -> u64 {
        let mut buf = [0u8; 8];
        unsafe { core::ptr::copy_nonoverlapping(k.as_ptr(), buf.as_mut_ptr(), k.len()); }
        let shift = 64usize.saturating_sub(k.len()*8);
        u64::from_le_bytes(buf) & (!0u64 >> shift)
    }

    #[test]
    fn btm_value_only_subtract_test() {
        let mut l: BytesTrieMap<u64> = BytesTrieMap::new();
        l.insert(b"0", 0);
        l.insert(b"1", 1);
        l.insert(b"2", 2);
        let mut r: BytesTrieMap<u64> = BytesTrieMap::new();
        r.insert(b"1", 1);
        r.insert(b"3", 3);
        let l_no_r = l.subtract(&r);
        assert_eq!(l_no_r.get(b"0"), Some(&0));
        assert_eq!(l_no_r.get(b"1"), None);
        assert_eq!(l_no_r.get(b"2"), Some(&2));
        assert_eq!(l_no_r.get(b"3"), None);
    }

    #[test]
    fn btm_compound_tree_subtract_test() {
        let mut l: BytesTrieMap<bool> = BytesTrieMap::new();
        l.insert(b"hello", true);
        l.insert(b"hello world", true);
        l.insert(b"hell no we won't go", true);
        let mut r: BytesTrieMap<bool> = BytesTrieMap::new();
        r.insert(b"hello", true);
        let l_no_r = l.subtract(&r);

        assert_eq!(l_no_r.get(b"hello"), None);
        assert_eq!(l_no_r.get(b"hello world"), Some(&true));
        assert_eq!(l_no_r.get(b"hell no we won't go"), Some(&true));
    }

    #[test]
    fn btm_simple_tree_subtract_test() {
        let mut l: BytesTrieMap<bool> = BytesTrieMap::new();
        l.insert(b"alligator", true);
        l.insert(b"allegedly", true);
        l.insert(b"albatross", true);
        l.insert(b"albino", true);
        let mut r: BytesTrieMap<bool> = BytesTrieMap::new();
        r.insert(b"alligator", true);
        r.insert(b"albino", true);
        let l_no_r = l.subtract(&r);

        assert_eq!(l_no_r.val_count(), 2);
        assert_eq!(l_no_r.get(b"alligator"), None);
        assert_eq!(l_no_r.get(b"albino"), None);
        assert_eq!(l_no_r.get(b"allegedly"), Some(&true));
        assert_eq!(l_no_r.get(b"albatross"), Some(&true));
    }

    #[test]
    fn btm_many_elements_subtract_test() {
        #[cfg(miri)]
        const N: u64 = 20;
        #[cfg(not(miri))]
        const N: u64 = 1000;

        let overlap = 0.5;
        let o = ((1. - overlap) * N as f64) as u64;

        let mut vnl = BytesTrieMap::new();
        let mut vnr = BytesTrieMap::new();
        for i in 0..N { vnl.insert(prefix_key(&i), i); }
        for i in o..(N+o) { vnr.insert(prefix_key(&i), i); }
        let l_no_r = vnl.subtract(&vnr);

        //Validate the ByteTrieMap::subtract against HashSet::difference
        let vnl_set: std::collections::HashSet<Vec<u8>> = vnl.iter().map(|(k, _)| k).collect();
        let vnr_set: std::collections::HashSet<Vec<u8>> = vnr.iter().map(|(k, _)| k).collect();
        let mut l_no_r_set: Vec<Vec<u8>> = l_no_r.iter().map(|(k, _)| k).collect();
        let mut l_no_r_ref_set: Vec<Vec<u8>> = vnl_set.difference(&vnr_set).cloned().collect();
        l_no_r_set.sort();
        l_no_r_ref_set.sort();
        assert_eq!(l_no_r_set, l_no_r_ref_set);
    }

    #[test]
    fn btm_subtract_after_join() {

        //This entire operation works with only ListNodes
        let r: Vec<Vec<u8>> = vec![
            vec![61, 85, 161, 68, 245, 90, 129],
            vec![70, 91, 37, 155, 181, 227, 100, 255, 66, 129, 158, 241, 183, 96, 59],
        ];
        let r: BytesTrieMap<u64> = r.into_iter().map(|v| (v, 0)).collect();

        let l: Vec<Vec<u8>> = vec![
            vec![70, 116, 109, 134, 122, 15, 78, 126, 240, 158, 42, 221],
        ];
        let l: BytesTrieMap<u64> = l.into_iter().map(|v| (v, 0)).collect();

        let joined = l.join(&r);
        let remaining = joined.subtract(&r);
        let remaining_keys: Vec<Vec<u8>> = remaining.iter().map(|(k, _v)| k).collect();
        let l_keys: Vec<Vec<u8>> = l.iter().map(|(k, _v)| k).collect();

        assert_eq!(remaining.val_count(), l.val_count());
        for (rem_k, l_k) in remaining_keys.iter().zip(l_keys.iter()) {
            assert_eq!(rem_k, l_k);
        }

        //This ends up upgrading a node to a dense node, So we test those paths here
        let r: Vec<Vec<u8>> = vec![
            vec![61, 85, 161, 68, 245, 90, 129],
            vec![70, 10, 122, 77, 171, 54, 32, 161, 24, 162, 112, 152],
            vec![70, 91, 37, 155, 181, 227, 100, 255, 66, 129, 158, 241, 183, 96, 59],
        ];
        let r: BytesTrieMap<u64> = r.into_iter().map(|v| (v, 0)).collect();

        let l: Vec<Vec<u8>> = vec![
            vec![70, 116, 109, 134, 122, 15, 78, 126, 240, 158, 42, 221],
        ];
        let l: BytesTrieMap<u64> = l.into_iter().map(|v| (v, 0)).collect();

        let joined = l.join(&r);
        let remaining = joined.subtract(&r);
        let remaining_keys: Vec<Vec<u8>> = remaining.iter().map(|(k, _v)| k).collect();
        let l_keys: Vec<Vec<u8>> = l.iter().map(|(k, _v)| k).collect();

        assert_eq!(remaining.val_count(), l.val_count());
        for (rem_k, l_k) in remaining_keys.iter().zip(l_keys.iter()) {
            assert_eq!(rem_k, l_k);
        }
    }

    #[test]
    fn btm_subtract_after_join_2() {
        #[cfg(miri)]
        const N: u64 = 10;
        #[cfg(not(miri))]
        const N: u64 = 500;

        let mut rng = StdRng::seed_from_u64(1);
        let keys: Vec<Vec<u8>> = (0..N).into_iter().map(|_| {
            let len = (rng.random::<u8>() % 18) + 3; //length between 3 and 20 chars
            (0..len).into_iter().map(|_| rng.random::<u8>()).collect()
        }).collect();

        let mut l: BytesTrieMap<u64> = BytesTrieMap::new();
        for i in 0..(N/2) { l.insert(&keys[i as usize], i); }
        let mut r: BytesTrieMap<u64> = BytesTrieMap::new();
        for i in (N/2)..N { r.insert(&keys[i as usize], i); }

        let joined = l.join(&r);
        let remaining = joined.subtract(&r);
        assert_eq!(remaining.val_count(), l.val_count())
    }

    #[test]
    fn btm_test_restrict1() {
        let mut l: BytesTrieMap<&str> = BytesTrieMap::new();
        l.insert(b"alligator", "alligator");
        l.insert(b"allegedly", "allegedly");
        l.insert(b"albatross", "albatross");
        l.insert(b"albino", "albino");
        let mut r: BytesTrieMap<&str> = BytesTrieMap::new();
        r.insert(b"all", "all");
        let restricted = l.restrict(&r);

        assert_eq!(restricted.val_count(), 2);
        assert_eq!(restricted.get(b"alligator"), Some(&"alligator"));
        assert_eq!(restricted.get(b"albino"), None);
        assert_eq!(restricted.get(b"allegedly"), Some(&"allegedly"));
        assert_eq!(restricted.get(b"albatross"), None);
    }

    /// Tests restrictions on a very dense trie
    #[test]
    fn btm_test_restrict2() {

        // These values are base-4 numbers in "little endian"
        let keys = [
            vec![0],    vec![1],    vec![2],    vec![3],    vec![0, 1], vec![1, 1], vec![2, 1], vec![3, 1],
            vec![0, 2], vec![1, 2], vec![2, 2], vec![3, 2], vec![0, 3], vec![1, 3], vec![2, 3], vec![3, 3],
            vec![0, 0, 1], vec![1, 0, 1], vec![2, 0, 1], vec![3, 0, 1]
        ];
        let map: BytesTrieMap<i32> = keys.iter().enumerate().map(|(i, k)| (k, i as i32)).collect();

        // Restrict to odd numbers
        let odd_keys = [ vec![1], vec![3]];
        let odd_map: BytesTrieMap<i32> = odd_keys.iter().enumerate().map(|(i, k)| (k, i as i32)).collect();
        let restricted = map.restrict(&odd_map);

        assert_eq!(restricted.val_count(), 10);
        assert_eq!(restricted.get([1]), Some(&1));
        assert_eq!(restricted.get([3]), Some(&3));
        assert_eq!(restricted.get([1, 1]), Some(&5));
        assert_eq!(restricted.get([3, 1]), Some(&7));
        assert_eq!(restricted.get([1, 2]), Some(&9));
        assert_eq!(restricted.get([3, 2]), Some(&11));
        assert_eq!(restricted.get([1, 3]), Some(&13));
        assert_eq!(restricted.get([3, 3]), Some(&15));
        assert_eq!(restricted.get([1, 0, 1]), Some(&17));
        assert_eq!(restricted.get([3, 0, 1]), Some(&19));

        // Restrict to numbers divisible by 4 (exluding 0; 0 technically isn't divisible by 4)
        let div4_keys = [ vec![0, 0], vec![0, 1], vec![0, 2], vec![0, 3]];
        let div4_map: BytesTrieMap<i32> = div4_keys.iter().enumerate().map(|(i, k)| (k, i as i32)).collect();
        let restricted = map.restrict(&div4_map);

        assert_eq!(restricted.val_count(), 4);
        assert_eq!(restricted.get([0]), None);
        assert_eq!(restricted.get([0, 0]), None);
        assert_eq!(restricted.get([0, 1]), Some(&4));
        assert_eq!(restricted.get([0, 2]), Some(&8));
        assert_eq!(restricted.get([0, 3]), Some(&12));
        assert_eq!(restricted.get([0, 0, 1]), Some(&16));
    }

    /// Tests restrictions on a fairly sparse trie
    #[test]
    fn btm_test_restrict3() {
        let keys = [
            "a",
            "acting",
            "activated",
            "activation",
            "activities",
            "acute",
            "adaptation",
            "adapter",
        ];
        let map: BytesTrieMap<i32> = keys.iter().enumerate().map(|(i, k)| (k, i as i32)).collect();

        // Restrict to words beginning with "act"
        let restrictor = [ "act" ];
        let restrictor_map: BytesTrieMap<i32> = restrictor.iter().enumerate().map(|(i, k)| (k, i as i32)).collect();
        let restricted = map.restrict(&restrictor_map);

        assert_eq!(restricted.val_count(), 4);
        assert_eq!(restricted.get("acting"), Some(&1));
        assert_eq!(restricted.get("activities"), Some(&4));

        // Restrict to words beginning with "a"
        let restrictor = [ "a" ];
        let restrictor_map: BytesTrieMap<i32> = restrictor.iter().enumerate().map(|(i, k)| (k, i as i32)).collect();
        let restricted = map.restrict(&restrictor_map);

        assert_eq!(restricted.val_count(), 8);
        assert_eq!(restricted.get("a"), Some(&0));
        assert_eq!(restricted.get("acting"), Some(&1));
        assert_eq!(restricted.get("activities"), Some(&4));
        assert_eq!(restricted.get("adapter"), Some(&7));
    }

    /// Tests values that are attached along the paths to other keys, and also tests the absence of keys
    /// after existing values.
    #[test]
    fn path_prefix_test() {
        let mut map = BytesTrieMap::<u64>::new();

        map.insert(&[0u8], 1);
        assert_eq!(map.get(&[0u8]), Some(&1));
        assert_eq!(map.get(&[0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8]), None);

        map.insert(&[0u8, 0u8, 0u8, 0u8], 4);
        assert_eq!(map.get(&[0u8]), Some(&1));
        assert_eq!(map.get(&[0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8]), Some(&4));

        map.insert(&[0u8, 0u8, 0u8, 0u8, 0u8], 5);
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8]), Some(&4));
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8]), Some(&5));

        map.insert(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8], 9);
        assert_eq!(map.get(&[0u8]), Some(&1));
        assert_eq!(map.get(&[0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8]), Some(&4));
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8]), Some(&5));
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), None);
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), Some(&9));
        assert_eq!(map.get(&[0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8]), None);
    }

    #[test]
    fn map_meet_after_join_test() {
        #[cfg(miri)]
        const N: u64 = 20;
        #[cfg(not(miri))]
        const N: u64 = 1000;

        let mut l: BytesTrieMap<u64> = BytesTrieMap::new();
        for i in 0..(N/2) { l.insert(prefix_key(&i), i); }
        let mut r: BytesTrieMap<u64> = BytesTrieMap::new();
        for i in (N/2)..N { r.insert(prefix_key(&i), i); }

        let joined = l.join(&r);
        let met = joined.meet(&l);
        for (met, l) in met.iter().zip(l.iter()) {
            assert_eq!(met, l);
        }

        let met = met.meet(&r);
        assert!(met.is_empty());
    }

    #[test]
    fn map_meet_big_test() {
        #[cfg(miri)]
        const N: u64 = 20;
        #[cfg(not(miri))]
        const N: u64 = 16000;

        let overlap = 0.5;
        let o = ((1. - overlap) * N as f64) as u64;

        let mut rng = StdRng::seed_from_u64(1);
        let keys: Vec<Vec<u8>> = (0..N+o).into_iter().map(|_| {
            let len = (rng.random::<u8>() % 18) + 3; //length between 3 and 20 chars
            (0..len).into_iter().map(|_| rng.random::<u8>()).collect()
        }).collect();

        let mut l: BytesTrieMap<u64> = BytesTrieMap::new();
        for i in 0..N { l.insert(&keys[i as usize], i); }
        let mut r: BytesTrieMap<u64> = BytesTrieMap::new();
        for i in o..(N+o) { r.insert(&keys[i as usize], i); }

        let intersection = l.meet(&r);
        assert_eq!(intersection.val_count(), (N/2) as usize);
    }

    /// This test is a minimal repro case for a bug where a list node is intersected with a byte node,
    /// and both slots in the list node match items in the byte node, but the byte node carries extra elements
    #[test]
    fn map_meet_lil_test() {
        let l_keys = [
            vec![207, 27],  //NON-OVERLAP!
            vec![207, 117], //Overlap
            vec![207, 142], //Overlap
            // vec![208, 250], //Overlap
            // vec![213, 63],  //Overlap
        ];
        let r_keys = [
            vec![207, 117], //Overlap
            vec![207, 142], //Overlap
            // vec![208, 157], //NON-OVERLAP!
            // vec![208, 250], //Overlap
            // vec![213, 63],  //Overlap
        ];
        let l: BytesTrieMap<u64> = l_keys.into_iter().map(|v| (v, 0)).collect();
        let r: BytesTrieMap<u64> = r_keys.into_iter().map(|v| (v, 0)).collect();

        let intersection = l.meet(&r);
        assert_eq!(intersection.val_count(), 2);
    }

    #[test]
    fn btm_ops_test() {
        #[cfg(miri)]
        const N: u64 = 20;
        #[cfg(not(miri))]
        const N: u64 = 5000;

        for n in (0..N).into_iter().step_by(97) {
            // println!("n={n}");

            let overlap = 0.5;
            let o = ((1. - overlap) * n as f64) as u64;
            {
                let mut vnl = BytesTrieMap::new();
                let mut vnr = BytesTrieMap::new();
                for i in 0..n { vnl.insert(prefix_key(&i), i); }
                // println!("{:?}", vnl.root);
                for i in 0..n { assert_eq!(vnl.get(prefix_key(&i)), Some(i).as_ref()); }
                for i in n..2*n { assert_eq!(vnl.get(prefix_key(&i)), None); }
                let mut c: Vec<u64> = Vec::with_capacity(n as usize);
                vnl.iter().for_each(|(k, v)| {
                    assert!(*v < n);
                    assert_eq!(k, prefix_key(&v));
                    c.push(from_prefix_key(k.clone()));
                });
                c.sort();
                assert_eq!(c, (0..n).collect::<Vec<u64>>());
                for i in o..(n+o) { vnr.insert(prefix_key(&i), i); }

                let j: BytesTrieMap<u64> = vnl.join(&vnr);
                let m = vnl.meet(&vnr);
                let l_no_r = vnl.subtract(&vnr);

                for i in 0..o { assert_eq!(l_no_r.get(prefix_key(&i)), vnl.get(prefix_key(&i))); }
                for i in o..(n+o) { assert!(!l_no_r.contains(prefix_key(&i))); }

                for i in o..n { assert!(vnl.contains(prefix_key(&i)) && vnr.contains(prefix_key(&i))); }
                for i in 0..o { assert!(vnl.contains(prefix_key(&i)) && !vnr.contains(prefix_key(&i))); }
                for i in n..(n+o) { assert!(!vnl.contains(prefix_key(&i)) && vnr.contains(prefix_key(&i))); }
                for i in 0..(2*n) { assert_eq!(j.contains(prefix_key(&i)), (vnl.contains(prefix_key(&i)) || vnr.contains(prefix_key(&i)))); }
                for i in 0..(2*n) { assert_eq!(m.contains(prefix_key(&i)), (vnl.contains(prefix_key(&i)) && vnr.contains(prefix_key(&i)))); }
                for i in 0..(n+o) { assert_eq!(j.get(prefix_key(&i)).map(|v| *v), vnl.get(prefix_key(&i)).pjoin(&vnr.get(prefix_key(&i))).into_option([vnl.get(prefix_key(&i)).cloned(), vnr.get(prefix_key(&i)).cloned()]).flatten()); }
                for i in o..n { assert_eq!(m.get(prefix_key(&i)).map(|v| *v), vnl.get(prefix_key(&i)).pmeet(&vnr.get(prefix_key(&i))).into_option([vnl.get(prefix_key(&i)).cloned(), vnr.get(prefix_key(&i)).cloned()]).flatten()); }
                // for i in 0..(2*N) { println!("{} {} {} {}", i, r.contains(i), vnl.contains(i), vnr.contains(i)); } // assert!(r.contains(i));
            }
        }
    }

    /// This tests longer and longer keys to see if / where we blow the stack
    #[test]
    fn map_very_long_key_test() {

        let test_key_len = |len: usize| {
            let mut map: BytesTrieMap<u64> = BytesTrieMap::new();
            let mut z = map.write_zipper();
            let key = vec![0u8; len];
            z.descend_to(&key);
            z.set_value(42);
            drop(z);
            assert_eq!(map.get(&key), Some(&42));
        };

        test_key_len(1024); //2^10 bytes
        test_key_len(2048); //2^11 bytes

        //all_dense_nodes are terrible at chaining, but there isn't much point in an optimized path for them
        #[cfg(not(feature = "all_dense_nodes"))]
        #[cfg(not(miri))]
        {
            test_key_len(4096); //2^12 bytes
            test_key_len(16384); //2^14 bytes
            test_key_len(32768); //2^15 bytes //Failed here with recursive drop
            test_key_len(65536); //2^16 bytes
            test_key_len(262144); //2^18 bytes
            test_key_len(1048576); //2^20 bytes
            // test_key_len(4194304); //2^22 bytes //Disabled from here so tests run quickly
            // test_key_len(16777216); //2^24 bytes
            // test_key_len(67108864); //2^26 bytes
            // test_key_len(268435456); //2^28 bytes
            // test_key_len(1073741824); //2^30 bytes //Still no failure at 1GB keys
        }
    }

}
