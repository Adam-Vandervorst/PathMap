
/// Traits to implement [ring](https://en.wikipedia.org/wiki/Ring_(mathematics)) and other algebraic
/// operations on tries, such as union, intersection, and subtraction
pub mod ring;

/// A collection indexed by paths of bytes, supporting [algebraic](crate::ring) operations
pub mod trie_map;

/// Cursors that can move over a trie, to inspect and modify contained elements or entire branches
pub mod zipper;

/// Track outstanding zippers to be sure they don't conflict
pub(crate) mod zipper_tracking;

/// Features to inspect performance properties of trees, for optimizing
#[cfg(feature = "counters")]
pub mod counters;

mod trie_node;
mod write_zipper;
mod dense_byte_node;
pub mod line_list_node;
mod empty_node;
mod tiny_node;

mod old_cursor;

#[cfg(test)]
mod tests {
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use crate::ring::*;
    use crate::trie_map::BytesTrieMap;
    use crate::zipper::*;

    fn prefix_key(k: &u64) -> &[u8] {
        let bs = (8 - k.leading_zeros()/8) as u8;
        let kp: *const u64 = k;
        unsafe { std::slice::from_raw_parts(kp as *const _, (bs as usize).max(1)) }
    }

    fn from_prefix_key(k: Vec<u8>) -> u64 {
        let kp =  k.as_ptr() as *const u64;
        let shift = 64usize.saturating_sub(k.len()*8);
        unsafe { (*kp) & (!0u64 >> shift) }
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
        let mut l: BytesTrieMap<&str> = BytesTrieMap::new();
        l.insert(b"hello", "hello");
        l.insert(b"hello world", "hello world");
        l.insert(b"hell no we won't go", "hell no we won't go");
        let mut r: BytesTrieMap<&str> = BytesTrieMap::new();
        r.insert(b"hello", "hello");
        let l_no_r = l.subtract(&r);

        assert_eq!(l_no_r.get(b"hello"), None);
        assert_eq!(l_no_r.get(b"hello world"), Some(&"hello world"));
        assert_eq!(l_no_r.get(b"hell no we won't go"), Some(&"hell no we won't go"));
    }

    #[test]
    fn btm_simple_tree_subtract_test() {
        let mut l: BytesTrieMap<&str> = BytesTrieMap::new();
        l.insert(b"alligator", "alligator");
        l.insert(b"allegedly", "allegedly");
        l.insert(b"albatross", "albatross");
        l.insert(b"albino", "albino");
        let mut r: BytesTrieMap<&str> = BytesTrieMap::new();
        r.insert(b"alligator", "alligator");
        r.insert(b"albino", "albino");
        let l_no_r = l.subtract(&r);

        assert_eq!(l_no_r.val_count(), 2);
        assert_eq!(l_no_r.get(b"alligator"), None);
        assert_eq!(l_no_r.get(b"albino"), None);
        assert_eq!(l_no_r.get(b"allegedly"), Some(&"allegedly"));
        assert_eq!(l_no_r.get(b"albatross"), Some(&"albatross"));
    }

    #[test]
    fn btm_many_elements_subtract_test() {
        let n: u64 = 1000; //Arbitrary number of elements
        let overlap = 0.5;
        let o = ((1. - overlap) * n as f64) as u64;

        let mut vnl = BytesTrieMap::new();
        let mut vnr = BytesTrieMap::new();
        for i in 0..n { vnl.insert(prefix_key(&i), i); }
        for i in o..(n+o) { vnr.insert(prefix_key(&i), i); }
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
        const N: u64 = 500;
        let mut rng = StdRng::seed_from_u64(1);
        let keys: Vec<Vec<u8>> = (0..N).into_iter().map(|_| {
            let len = (rng.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
            (0..len).into_iter().map(|_| rng.gen::<u8>()).collect()
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
    fn btm_simple_tree_restrict_test() {
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
        const N: u64 = 16000;
        let overlap = 0.5;
        let o = ((1. - overlap) * N as f64) as u64;

        let mut rng = StdRng::seed_from_u64(1);
        let keys: Vec<Vec<u8>> = (0..N+o).into_iter().map(|_| {
            let len = (rng.gen::<u8>() % 18) + 3; //length between 3 and 20 chars
            (0..len).into_iter().map(|_| rng.gen::<u8>()).collect()
        }).collect();

        let mut l: BytesTrieMap<u64> = BytesTrieMap::new();
        for i in 0..N { l.insert(&keys[i as usize], i); }
        let mut r: BytesTrieMap<u64> = BytesTrieMap::new();
        for i in o..(N+o) { r.insert(&keys[i as usize], i); }

        let intersection = l.meet(&r);
        assert_eq!(intersection.val_count(), 8000);
    }

    #[test]
    fn btm_ops_test() {
        for n in (0..5000).into_iter().step_by(97) {
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
                for i in 0..(n+o) { assert_eq!(j.get(prefix_key(&i)), vnl.get(prefix_key(&i)).join(&vnr.get(prefix_key(&i)))); }
                for i in o..n { assert_eq!(m.get(prefix_key(&i)), vnl.get(prefix_key(&i)).meet(&vnr.get(prefix_key(&i)))); }
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
