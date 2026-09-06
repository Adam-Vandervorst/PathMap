
//GOAT: Internal Discussion: What do we ultimately want this API to look like?
//
// * Firstly, we probably ought to make a writable trait, in the vein of `ZipperSubtries` that allows
// merkleization on any object that has a mutable trie node (PathMaps, WriteZippers, etc.)
// I've wanted that anyway for a while because I felt like a lot of the API between ZipperWriting and
// PathMap should be merged together.
//
// * Secondly, I think we ought to allow the client to exfiltrate and store the `memo`, wrapped in some
// kind of black box.  That way, they could perform "gradual merkleization", as an opportunistic background
// process.
//
// However, the `memo` is liable to get huge in real-world situations, therefore we also want some kind of
// way to implement a heuristic to evict nodes that are unlikely to be duplicated.  I'm not totally sure what
// that heuristic(s) would be.  My first guess would be to try an LRU cache, but also, higher nodes are less
// likely to be identical, but also we get more "bang" if we find higher-level sharing.  So perhaps finding
// a that's shared means we make sure its parents are refreshed into the cache...  Anyway, gotta try stuff
// and measure.
//
// One additional consideration if we go the persistent memo route is that the very existence of the memo
// structure, under the present implementation, would increase the node refcounts and lead to copying... So
// we might want to explore something like a "weak" pointer to keep in the memo (semantics wouldn't be exactly
// the same as an Rc `weak`, but a similar idea)

use crate::alloc::Allocator;
use crate::trie_node::*;
use crate::gxhash;

/// Statistics created after merkleization
#[derive(Default, Debug)]
pub struct MerkleizeResult {
    /// The hash of the entire trie beneath the root
    pub hash: u128,
    /// The number of shared node references that replaced identical copies during the merkleization
    pub reused: usize,
    //GOAT, not sure how to describe this
    pub cloned: usize,
    //GOAT, not sure how to describe this
    pub replaced: usize,
}

pub(crate) fn merkleize_impl<V, A>(
    counters: &mut MerkleizeResult,
    memo: &mut gxhash::HashMap<u128, TrieNodeODRc<V, A>>,
    node: &TrieNodeODRc<V, A>,
) -> (u128, Option<TrieNodeODRc<V, A>>)
    where
        V: Clone + Send + Sync + std::hash::Hash,
        A: Allocator,
{
    // hash = [(path, child_hash)]
    // child_hash = (val, node_hash)
    use std::hash::{Hash};
    use std::collections::hash_map::Entry;
    const INITIAL_SEED: i64 = 0;
    let mut hasher = gxhash::GxHasher::with_seed(INITIAL_SEED);
    let mut replacement = None;

    let node_ref = node.as_tagged();
    let mut it = node_ref.new_iter_token();
    while it != NODE_ITER_FINISHED {
        let (next, path, child, val) = node_ref.next_items(it);
        it = next;
        path.hash(&mut hasher);
        let child_hash;
        if let Some(child) = child {
            let (node_hash, replace) = merkleize_impl(counters, memo, child);
            // combine the child's structural hash with the value reached via this edge
            let mut hasher = gxhash::GxHasher::with_seed(INITIAL_SEED);
            val.hash(&mut hasher);
            node_hash.hash(&mut hasher);
            child_hash = hasher.finish_u128();
            if let Some(replace) = replace {
                let node = replacement.get_or_insert_with(|| {
                    counters.cloned += 1;
                    node.clone()
                });
                counters.replaced += 1;
                node.make_mut().node_replace_child(path, replace);
            }
        } else {
            // value and no child -> pretend there's an empty node
            let mut hasher = gxhash::GxHasher::with_seed(INITIAL_SEED);
            val.hash(&mut hasher);
            child_hash = hasher.finish_u128();
        }
        child_hash.hash(&mut hasher);
    }
    let hash = hasher.finish_u128();
    match memo.entry(hash) {
        Entry::Vacant(entry) => {
            counters.cloned += 1;
            if let Some(replacement) = &replacement {
                entry.insert(replacement.clone());
            } else {
                entry.insert(node.clone());
            }
        }
        // if we've seen the hash before, do the replacement
        Entry::Occupied(entry) => {
            counters.reused += 1;
            replacement = Some(entry.get().clone());
        }
    }
    (hash, replacement)
}

#[cfg(test)]
mod tests {
    use crate::PathMap;
    use crate::trie_node::{TrieNodeODRc, NODE_ITER_FINISHED};
    use crate::gxhash;

    /// Walks every node reachable from `map`'s root and groups them by an
    /// independently-computed *structural* key: the sorted list of
    /// `(path, edge_value_hash, child_structural_key)` triples a node carries,
    /// computed bottom-up without any reference to `merkleize_impl`'s own
    /// hashing.  Returns, per structural key, every distinct node identity
    /// (`shared_node_id`) found with that key -- callers decide what to
    /// assert, since "before merkleize" legitimately has multiple identities
    /// per class (that's the diversity merkleize exists to remove).
    fn structural_classes<V>(map: &PathMap<V>) -> std::collections::HashMap<u128, Vec<u64>>
        where V: Clone + Send + Sync + Unpin + std::hash::Hash
    {
        use std::hash::Hash;
        use std::collections::HashMap;

        fn structural_key<V>(
            node: &TrieNodeODRc<V, crate::alloc::GlobalAlloc>,
            seen: &mut HashMap<u64, u128>,
            classes: &mut HashMap<u128, Vec<u64>>,
        ) -> u128
            where V: Clone + Send + Sync + std::hash::Hash
        {
            let id = node.shared_node_id();
            if let Some(key) = seen.get(&id) {
                return *key;
            }
            let mut parts: Vec<(Vec<u8>, u128)> = Vec::new();
            let node_ref = node.as_tagged();
            let mut it = node_ref.new_iter_token();
            while it != NODE_ITER_FINISHED {
                let (next, path, child, val) = node_ref.next_items(it);
                it = next;
                let edge_key = if let Some(child) = child {
                    let child_key = structural_key(child, seen, classes);
                    let mut hasher = gxhash::GxHasher::with_seed(0);
                    val.hash(&mut hasher);
                    child_key.hash(&mut hasher);
                    hasher.finish_u128()
                } else {
                    let mut hasher = gxhash::GxHasher::with_seed(0);
                    val.hash(&mut hasher);
                    hasher.finish_u128()
                };
                parts.push((path.to_vec(), edge_key));
            }
            parts.sort();
            let mut hasher = gxhash::GxHasher::with_seed(0);
            parts.hash(&mut hasher);
            let key = hasher.finish_u128();
            seen.insert(id, key);
            classes.entry(key).or_default().push(id);
            key
        }

        let mut seen = HashMap::new();
        let mut classes: HashMap<u128, Vec<u64>> = HashMap::new();
        if let Some(root) = map.root() {
            structural_key(root, &mut seen, &mut classes);
        }
        classes
    }

    /// Asserts that every structural class contains exactly one node
    /// identity -- i.e. merkleization achieved *maximal* sharing.  Meant to
    /// be called only on a trie that has already been merkleized; calling it
    /// beforehand would spuriously fail, since un-merkleized tries are
    /// expected to hold distinct-but-identical-shaped nodes.
    ///
    /// Returns the number of distinct structural classes found (a proxy for
    /// "how many distinct node shapes remain").
    fn assert_maximal_sharing<V>(map: &PathMap<V>) -> usize
        where V: Clone + Send + Sync + Unpin + std::hash::Hash
    {
        let classes = structural_classes(map);
        for (key, ids) in &classes {
            let mut dedup_ids = ids.clone();
            dedup_ids.sort();
            dedup_ids.dedup();
            assert_eq!(
                dedup_ids.len(), 1,
                "under-shared structural class {key:#x}: {} distinct node identities \
                 ({} references) should have been merged into one",
                dedup_ids.len(), ids.len(),
            );
        }
        classes.len()
    }

    /// Regression test for the parent-edge-value-leaking-into-child-hash bug:
    /// every bitstring of length 1..=4 over {0,1} ending in `1`, plus the empty
    /// path.  Before the fix, `merkleize` folded the value reached via a
    /// node's *parent* edge into the hash used to memoize the node itself, so
    /// the same child node reached through a valued slot and an unvalued slot
    /// were never deduplicated.  This trie is built so every level has one
    /// child ending the path (valued) and one child continuing it
    /// (unvalued), reaching an *otherwise identical* subtrie -- which
    /// collapses to a single chain of 4 shared nodes once merkleization is
    /// correct (was 7 with the bug).
    #[test]
    fn test_merkleize_dedups_value_vs_no_value_edges() {
        let mut paths: Vec<Vec<u8>> = vec![vec![]];
        for len in 1..=4usize {
            for bits in 0..(1u32 << len) {
                let p: Vec<u8> = (0..len)
                    .map(|i| ((bits >> (len - 1 - i)) & 1) as u8)
                    .collect();
                if *p.last().unwrap() == 1 {
                    paths.push(p);
                }
            }
        }
        let mut map = PathMap::from_iter(paths.iter().map(|p| (p.as_slice(), ())));
        let before_ids: usize = structural_classes(&map).values().flatten().collect::<std::collections::HashSet<_>>().len();

        let result = map.merkleize();
        eprintln!("merkleize result: {result:?}");

        let after_classes = assert_maximal_sharing(&map);
        // The whole trie is one repeating shape, so after merkleization there
        // should be exactly 4 distinct structural classes: the 4 nesting
        // depths (the "()" leaf value counts as its own class, folded into
        // the deepest node), each now backed by exactly one node identity.
        assert_eq!(after_classes, 4, "expected exactly 4 distinct node shapes after merkleize");
        assert!(after_classes < before_ids, "merkleize should have reduced the number of distinct node identities");
        assert!(result.reused > 0, "merkleize should have found reusable nodes");
    }

    /// Adversarial: two sibling subtries are byte-for-byte identical *except*
    /// that one is reached through a valued parent slot and the other
    /// through an unvalued (dangling) one.  Structurally the two subtries
    /// are identical, so they must merge.
    #[test]
    fn test_merkleize_value_and_dangling_siblings_share() {
        let mut map = PathMap::<()>::new();
        // valued edge into a subtrie: [0] itself carries a value
        map.insert(&[0u8][..], ());
        map.insert(&[0u8, 1, 0][..], ());
        map.insert(&[0u8, 1, 1][..], ());
        // dangling (no value) edge into the identical subtrie: [1] exists but is unvalued
        map.create_path(&[1u8]);
        map.insert(&[1u8, 1, 0][..], ());
        map.insert(&[1u8, 1, 1][..], ());
        let result = map.merkleize();
        eprintln!("merkleize result: {result:?}");
        assert_maximal_sharing(&map);
        assert!(result.reused > 0);
    }

    /// Adversarial: identical subtries reached via *different* values at the
    /// parent edge (not just "value" vs "no value").  These must remain
    /// distinct (the edge value differs), but the child subtrie beneath each
    /// must still be the same shared node.
    #[test]
    fn test_merkleize_distinguishes_different_edge_values_but_shares_children() {
        let mut map = PathMap::<u8>::new();
        map.insert(&[0u8][..], 1);
        map.insert(&[0u8, 5, 0][..], 9);
        map.insert(&[0u8, 5, 1][..], 9);
        map.insert(&[1u8][..], 2); // different value at this edge
        map.insert(&[1u8, 5, 0][..], 9);
        map.insert(&[1u8, 5, 1][..], 9);
        let before = crate::merkleization::tests::snapshot(&map);
        let result = map.merkleize();
        eprintln!("merkleize result: {result:?}");
        assert_maximal_sharing(&map);
        let after = crate::merkleization::tests::snapshot(&map);
        assert_eq!(before, after, "merkleize must not change observable content");
        assert!(result.reused > 0);
    }

    /// Adversarial: deeply nested, asymmetric repetition -- a chain of
    /// dangling paths of increasing depth, where only some branches are
    /// dangling and others carry values, all funnelling into the same
    /// terminal shape.  Exercises multiple levels of the value/no-value
    /// distinction stacked on top of each other, rather than just one level.
    #[test]
    fn test_merkleize_nested_mixed_dangling_and_valued() {
        let mut map = PathMap::<()>::new();
        for prefix in [
            &[0u8][..], &[0u8, 0][..], &[1u8][..], &[1u8, 1][..], &[2u8, 0, 0][..],
        ] {
            // half dangling, half valued at each prefix
            map.create_path(prefix);
        }
        map.insert(&[0u8, 1][..], ());
        map.insert(&[1u8, 0][..], ());
        map.insert(&[2u8, 0, 1][..], ());
        // give every branch the same terminal subtrie shape
        for base in [&[0u8, 0][..], &[0u8, 1][..], &[1u8, 0][..], &[1u8, 1][..], &[2u8, 0, 0][..], &[2u8, 0, 1][..]] {
            let mut k = base.to_vec();
            k.push(7);
            map.insert(&k[..], ());
            k.pop();
            k.push(8);
            map.insert(&k[..], ());
        }
        let before = crate::merkleization::tests::snapshot(&map);
        let result = map.merkleize();
        eprintln!("merkleize result: {result:?}");
        assert_maximal_sharing(&map);
        let after = crate::merkleization::tests::snapshot(&map);
        assert_eq!(before, after, "merkleize must not change observable content");
        assert!(result.reused > 0);
    }

    /// Snapshot the full observable (path, value) contents of a map, so tests
    /// can assert `merkleize` never changes what the trie means, only how
    /// it's represented.
    pub(crate) fn snapshot<V: Clone + std::fmt::Debug>(map: &PathMap<V>) -> std::collections::BTreeMap<Vec<u8>, Option<V>>
        where V: Send + Sync + Unpin
    {
        use crate::zipper::*;
        let mut rz = map.read_zipper();
        let mut out = std::collections::BTreeMap::new();
        out.insert(Vec::new(), rz.val().cloned());
        while rz.to_next_step() {
            out.insert(rz.path().to_vec(), rz.val().cloned());
        }
        out
    }

    #[test]
    fn test_btm_merkleize() {
        let paths: &[&[u8]] = &[
            b"axx",
            b"ayy",
            b"bxx",
            b"byy",
            b"cxx",
            b"cyy",
            b"ddxx",
            b"ddyy",
        ];
        let paths = paths.iter()
            .map(|&path| (path, ()));
        let mut btm = crate::PathMap::from_iter(paths);
        #[cfg(feature="viz")] {
            let mut before = Vec::new();
            use crate::viz::{viz_maps, DrawConfig};
            viz_maps(&[btm.clone()], &DrawConfig::default(), &mut before).unwrap();
            eprintln!("before:");
            eprintln!("```mermaid\n{}```", std::str::from_utf8(&before).unwrap());
        }
        let result = btm.merkleize();
        eprintln!("merkleize result: {result:?}\n");
        #[cfg(feature="viz")] {
            use crate::viz::{viz_maps, DrawConfig};
            let mut after = Vec::new();
            viz_maps(&[btm], &DrawConfig::default(), &mut after).unwrap();
            eprintln!("after:");
            eprintln!("```mermaid\n{}```", std::str::from_utf8(&after).unwrap());
        }
    }
}