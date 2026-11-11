
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

use core::convert::Infallible;
use std::collections::hash_map::Entry;

use crate::alloc::Allocator;
use crate::gxhash;
use crate::morphisms::trie_hash::HashScheme;
use crate::trie_node::*;
use crate::utils::ByteMask;

/// Statistics created after merkleization
#[derive(Default, Debug)]
pub struct MerkleizeResult {
    /// The hash of the entire trie beneath the root, equal to [`CatamorphismCached::hash`](crate::morphisms::CatamorphismCached::hash)
    pub hash: u128,
    /// The number of shared node references that replaced identical copies during the merkleization
    pub reused: usize,
    //GOAT, not sure how to describe this
    pub cloned: usize,
    //GOAT, not sure how to describe this
    pub replaced: usize,
}

/// Merkleizes the trie below `root`, returning the statistics and the replacement for the root node
/// if it was rewritten
///
/// Nodes are identified by the hash of the **logical** trie below them, computed by the cached
/// catamorphism with the same algebra as [`CatamorphismCached::hash`](crate::morphisms::CatamorphismCached::hash).
/// Two nodes therefore merge whenever they hold the same paths and values, regardless of how those
/// paths are laid out in nodes and key segments, and regardless of the value the parent stores for
/// the node's root position.
///
/// The cata records the value-free hash of every node, in the order it finishes them.  A second,
/// bottom-up pass over the physical nodes then replaces every child whose hash was seen before with
/// the first node that produced that hash.
///
/// `scheme` is the [`HashScheme`] the hashes are computed with.  Only
/// [`GxHashScheme`](crate::morphisms::trie_hash::GxHashScheme) is used outside of tests: merkleize
/// merges subtries whose hashes are equal, so the scheme must be one whose collisions are negligible
pub(crate) fn merkleize_root<V, A, S>(root: &TrieNodeODRc<V, A>, root_val: Option<&V>, scheme: &S) -> (MerkleizeResult, Option<TrieNodeODRc<V, A>>)
    where
        V: Clone + Send + Sync,
        A: Allocator,
        S: HashScheme<V>,
{
    let mut result = MerkleizeResult::default();

    let mut hashes = NodeHashes {
        order: Vec::new(),
        shared: gxhash::HashMap::default(),
        cursor: 0,
        by_address: None,
        collapse_value: |v: &V, below| scheme.with_value(scheme.value(v), below),
    };
    let start_f = |bm: &ByteMask| Ok::<_, Infallible>(scheme.start(bm));
    let fold_child_f = |_bm: &ByteMask, child: NodeHash, acc: &mut S::Acc| {
        scheme.child(acc, child.full);
        Ok(())
    };
    let finalize_f = |bm: &ByteMask, value: Option<&V>, acc: Option<S::Acc>, prefix: &[u8]| {
        let below = scheme.finish(acc.unwrap_or_else(|| scheme.start(bm)));
        let mut full = match value {
            Some(v) => scheme.with_value(scheme.value(v), below),
            None => below,
        };
        for byte in prefix.iter().rev() {
            full = scheme.step(*byte, full);
        }
        // A nonempty prefix starts above `value`, at an unvalued position. The two hashes
        // differ only when this callback summarizes a value at the start position itself.
        Ok(NodeHash { full, without_value: if prefix.is_empty() { below } else { full } })
    };
    result.hash = recursive_cata_cached::<_, _, _, _, Infallible, _, _, _, true>(root, root_val, start_f, fold_child_f, finalize_f, &mut hashes)
        .unwrap_or_else(|never| match never {}).full;

    let mut memo = gxhash::HashMap::<u128, TrieNodeODRc<V, A>>::default();
    let mut visited = gxhash::HashMap::<u64, Option<TrieNodeODRc<V, A>>>::default();
    let new_root = merkleize_impl(&mut result, &mut hashes, &mut memo, &mut visited, root);
    (result, new_root)
}

/// Both hashes describe the same starting position. `full` includes its value, while
/// `without_value` excludes only that position's value, retaining every descendant value.
#[derive(Clone, Copy)]
struct NodeHash {
    full: u128,
    without_value: u128,
}

/// The cata cache used for merkleization: every node's hash is recorded, in the order the cata
/// finishes nodes, and nodes that are physically shared are additionally indexed by address so
/// the cata summarizes them once
struct NodeHashes<F> {
    collapse_value: F,
    /// `(address, hash)` for every node the cata finished, in post-order
    order: Vec<(u64, u128)>,
    /// Hashes of nodes with more than one parent, so the cata can reuse them
    shared: gxhash::HashMap<u64, NodeHash>,
    /// Read position in `order` for the rewrite pass
    cursor: usize,
    /// Built from `order` if the rewrite pass ever visits nodes in a different order than the cata did
    by_address: Option<gxhash::HashMap<u64, u128>>,
}

impl<V: Clone + Send + Sync, A: Allocator, F: Fn(&V, u128) -> u128> CataCache<V, A, NodeHash> for NodeHashes<F> {
    #[inline]
    fn caches(&self, node: &TrieNodeODRc<V, A>) -> bool {
        !node.is_empty()
    }
    #[inline]
    fn get(&self, key: u64) -> Option<&NodeHash> {
        self.shared.get(&key)
    }
    #[inline]
    fn get_with_value(&self, key: u64, value: &V) -> Option<NodeHash> {
        let without_value = self.shared.get(&key)?.without_value;
        Some(NodeHash { full: (self.collapse_value)(value, without_value), without_value })
    }
    #[inline]
    fn insert(&mut self, key: u64, node: &TrieNodeODRc<V, A>, _value: Option<&V>, w: &NodeHash) {
        self.order.push((key, w.without_value));
        if node.refcount() > 1 {
            // Every parent has its own slot value, so reuse only the value-free summary.
            self.shared.insert(key, NodeHash { full: w.without_value, without_value: w.without_value });
        }
    }
}

impl<F> NodeHashes<F> {
    /// Whether the node at `address` had more than one parent when the cata ran
    #[inline]
    fn is_shared(&self, address: u64) -> bool {
        !self.shared.is_empty() && self.shared.contains_key(&address)
    }
    /// The hash recorded for the node at `address`, which the rewrite pass reaches in the cata's order
    #[inline]
    fn take(&mut self, address: u64) -> Option<u128> {
        if let Some(by_address) = &self.by_address {
            return by_address.get(&address).copied();
        }
        if let Some(&(recorded, hash)) = self.order.get(self.cursor) {
            if recorded == address {
                self.cursor += 1;
                return Some(hash);
            }
        }
        // The traversal orders diverged; the remaining lookups go through an index
        let by_address = self.order.iter().copied().collect::<gxhash::HashMap<u64, u128>>();
        let hash = by_address.get(&address).copied();
        self.by_address = Some(by_address);
        hash
    }
}

/// Rewrites the trie below `node`, returning the node the parent must store in its slot instead of
/// `node`, if any
fn merkleize_impl<V, A, F>(
    counters: &mut MerkleizeResult,
    hashes: &mut NodeHashes<F>,
    memo: &mut gxhash::HashMap<u128, TrieNodeODRc<V, A>>,
    visited: &mut gxhash::HashMap<u64, Option<TrieNodeODRc<V, A>>>,
    node: &TrieNodeODRc<V, A>,
) -> Option<TrieNodeODRc<V, A>>
    where
        V: Clone + Send + Sync,
        A: Allocator,
{
    // The cata does not visit the empty node
    if node.is_empty() {
        return None;
    }
    let address = node.shared_node_id();
    // A node with more than one parent is rewritten once, and every parent gets the same answer.  Only
    // such nodes can be reached twice, so only they are tracked.  The cata recorded which nodes those
    // are; refcounts are no guide here because rewriting a parent shares its children with the copy
    let shared = hashes.is_shared(address);
    if shared {
        if let Some(previous) = visited.get(&address) {
            return previous.clone();
        }
    }

    let mut replacement = None;
    let node_ref = node.as_tagged();
    let mut it = node_ref.new_iter_token();
    while it != NODE_ITER_FINISHED {
        let (next, path, child, _val) = node_ref.next_items(it, false);
        it = next;
        if let Some(child) = child {
            if let Some(replace) = merkleize_impl(counters, hashes, memo, visited, child) {
                let node = replacement.get_or_insert_with(|| {
                    counters.cloned += 1;
                    node.clone()
                });
                counters.replaced += 1;
                node.make_mut().node_replace_child(path, replace);
            }
        }
    }

    let hash = hashes.take(address).expect("the cata visits every non-empty node");
    match memo.entry(hash) {
        Entry::Vacant(entry) => {
            entry.insert(replacement.clone().unwrap_or_else(|| node.clone()));
        },
        // Another node with the same logical contents was seen first: point the parent at it
        Entry::Occupied(entry) => {
            counters.reused += 1;
            replacement = Some(entry.get().clone());
        },
    }
    if shared {
        visited.insert(address, replacement.clone());
    }
    replacement
}

#[cfg(test)]
mod tests {

    /// Regression test: the memo key must not include the value stored in the *parent's* slot for
    /// a child, otherwise byte-identical nodes reached through a valued slot and an unvalued slot are
    /// never merged.
    ///
    /// The trie contains every bitstring over {0, 1} of length 0..=4 that ends in `1`, plus the
    /// empty path.  The subtrie below byte `0` and the subtrie below byte `1` are identical, except
    /// that the path `[1]` carries a value, which lives in the root node's slot, not in the child.
    /// So after merkleization there should be exactly one physical node per depth: 4 in total.
    #[cfg(feature="viz")]
    #[test]
    fn merkleize_parent_slot_value_should_not_split_identical_children() {
        use crate::viz::{viz_maps, DrawConfig, VizMode};

        // All paths over {0,1} of length 1..=4 whose last byte is 1, plus the empty path
        let mut paths: Vec<Vec<u8>> = vec![vec![]];
        for len in 1..=4usize {
            for bits in 0..(1u32 << len) {
                let path: Vec<u8> = (0..len).map(|i| ((bits >> (len - 1 - i)) & 1) as u8).collect();
                if *path.last().unwrap() == 1 {
                    paths.push(path);
                }
            }
        }
        assert_eq!(paths.len(), 16);
        let mut map = crate::PathMap::from_iter(paths.iter().map(|p| (p.as_slice(), ())));
        assert_eq!(map.val_count(), 16);

        let count_physical_nodes = |map: &crate::PathMap<()>| {
            let dc = DrawConfig{ mode: VizMode::Mermaid, ascii_path: false, hide_value_paths: true, minimize_values: true, logical: false, color: false };
            let mut out = Vec::new();
            viz_maps(std::slice::from_ref(map), &dc, &mut out).unwrap();
            let out = String::from_utf8(out).unwrap();
            // `viz_node_physical` emits one `shape: rect` line per distinct node address
            let n = out.lines().filter(|l| l.contains("shape: rect")).count();
            (n, out)
        };

        let (before, _) = count_physical_nodes(&map);
        let result = map.merkleize();
        let (after, rendered) = count_physical_nodes(&map);
        eprintln!("physical nodes before merkleize: {before}, after: {after}\nmerkleize result: {result:?}\n```mermaid\n{rendered}```");
        assert_eq!(map.val_count(), 16, "merkleize must not change the logical contents");
        assert_eq!(after, 4, "expected one physical node per depth after merkleize, got {after}");
    }

    use std::collections::HashSet;
    use crate::PathMap;
    use crate::morphisms::CatamorphismCached;
    use crate::trie_node::{TrieNodeODRc, NODE_ITER_FINISHED};
    use crate::zipper::*;
    use crate::gxhash;

    // ---- Sharing tests ported from the merkleize-fix branch ----

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
                let (next, path, child, val) = node_ref.next_items(it, false);
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


    /// Counts the distinct physical nodes reachable from the map root
    fn physical_node_count(map: &PathMap<()>) -> usize {
        fn visit(node: &TrieNodeODRc<(), crate::alloc::GlobalAlloc>, seen: &mut HashSet<u64>) {
            if node.is_empty() || !seen.insert(node.shared_node_id()) {
                return;
            }
            let node_ref = node.as_tagged();
            let mut it = node_ref.new_iter_token();
            while it != NODE_ITER_FINISHED {
                let (next, _path, child, _val) = node_ref.next_items(it, false);
                it = next;
                if let Some(child) = child {
                    visit(child, seen);
                }
            }
        }
        let mut seen = HashSet::new();
        if let Some(root) = map.root() {
            visit(root, &mut seen);
        }
        seen.len()
    }

    fn all_paths(map: &PathMap<()>) -> Vec<Vec<u8>> {
        let mut rz = map.read_zipper();
        let mut paths = Vec::new();
        while rz.to_next_val() {
            paths.push(rz.path().to_vec());
        }
        paths
    }

    /// The same four paths, either inserted directly (`abcd`/`abce` become `a` -> `bc` -> `{d, e}`)
    /// or assembled by grafting `{cd, ce}` under `ab` (which leaves `a` -> `b` -> `c` -> `{d, e}`)
    fn insert_copy(map: &mut PathMap<()>, prefix: &[u8], grafted: bool) {
        let mut wz = map.write_zipper_at_path(prefix);
        if grafted {
            let sub: PathMap<()> = [b"cd".as_slice(), b"ce"].into_iter().map(|leaf| (leaf, ())).collect();
            wz.descend_to(b"ab");
            wz.graft_map(sub);
            wz.reset();
            for path in [b"m".as_slice(), b"n"] {
                wz.descend_to(path);
                wz.set_val(());
                wz.reset();
            }
        } else {
            for path in [b"abcd".as_slice(), b"abce", b"m", b"n"] {
                wz.descend_to(path);
                wz.set_val(());
                wz.reset();
            }
        }
    }

    #[test]
    fn merkleize_hash_is_the_cata_hash_and_keeps_the_contents() {
        let mut map = PathMap::<()>::new();
        insert_copy(&mut map, b"1", false);
        insert_copy(&mut map, b"2", true);
        map.set_val_at(b"1", ());
        let paths = all_paths(&map);
        let hash = CatamorphismCached::hash(&map);

        let result = map.merkleize();

        assert_eq!(result.hash, hash);
        assert_eq!(all_paths(&map), paths);
        assert_eq!(CatamorphismCached::hash(&map), hash);
    }

    #[test]
    fn merkleize_merges_logically_equal_subtries_with_different_layouts() {
        let mut direct = PathMap::<()>::new();
        insert_copy(&mut direct, b"", false);
        let mut split = PathMap::<()>::new();
        insert_copy(&mut split, b"", true);
        let split = split;
        assert_eq!(all_paths(&direct), all_paths(&split));
        let (direct_nodes, grafted_nodes) = (physical_node_count(&direct), physical_node_count(&split));
        assert_ne!(direct_nodes, grafted_nodes, "the two copies should differ in layout for this test to mean anything");

        let mut map = PathMap::<()>::new();
        insert_copy(&mut map, b"1", false);
        insert_copy(&mut map, b"2", true);
        let before = physical_node_count(&map);
        assert_eq!(before, 1 + direct_nodes + grafted_nodes);

        let result = map.merkleize();
        let after = physical_node_count(&map);
        eprintln!("direct copy: {direct_nodes} nodes, grafted copy: {grafted_nodes} nodes, before: {before}, after: {after}, {result:?}");
        // The second copy collapses onto the first, node for node, so only the root is left on top
        // of one copy (whose own internal duplicates are merged as well)
        direct.merkleize();
        assert_eq!(after, 1 + physical_node_count(&direct));
        assert!(result.reused >= 1);
    }

    #[test]
    fn merkleize_is_idempotent_and_leaves_shared_nodes_alone() {
        let mut map = PathMap::<()>::new();
        for prefix in [b"1".as_slice(), b"2", b"3"] {
            insert_copy(&mut map, prefix, prefix == b"2");
        }
        let first = map.merkleize();
        assert!(first.reused > 0);
        let after_first = physical_node_count(&map);

        let second = map.merkleize();
        assert_eq!(second.hash, first.hash);
        assert_eq!((second.reused, second.replaced, second.cloned), (0, 0, 0));
        assert_eq!(physical_node_count(&map), after_first);

        // A trie that already shares its nodes physically is left untouched too
        let mut grafted = PathMap::<()>::new();
        let mut shared = PathMap::<()>::new();
        insert_copy(&mut shared, b"", false);
        for prefix in [b"1".as_slice(), b"2", b"3"] {
            let mut wz = grafted.write_zipper_at_path(prefix);
            wz.graft_map(shared.clone());
        }
        let before = physical_node_count(&grafted);
        let result = grafted.merkleize();
        assert_eq!((result.reused, result.replaced, result.cloned), (0, 0, 0));
        assert_eq!(physical_node_count(&grafted), before);
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

    // ---- Exploration: node topology from IMG_0825 ----
    //
    // Requested topology, keys written as byte strings over {0, 1}:
    //   root [ 0: [00: [0: V, 1: V]],  1: [0: [00: V, 01: V]] ]
    // Both halves hold the paths {000, 001} below the root byte, laid out with node boundaries
    // in different places.  Node 4 in the picture, a ListNode holding two values under keys `00`
    // and `01`, is an "unfactored divergent prefix" and is rejected by `validate_node`.

    fn dump_layout<V: Clone + Send + Sync + Unpin + std::fmt::Debug>(map: &PathMap<V>) -> String {
        use crate::trie_node::TaggedNodeRef;
        fn kind<V: Clone + Send + Sync, A: crate::alloc::Allocator>(t: &TaggedNodeRef<'_, V, A>) -> &'static str {
            match t {
                TaggedNodeRef::DenseByteNode(_) => "Dense",
                TaggedNodeRef::LineListNode(_) => "List",
                TaggedNodeRef::CellByteNode(_) => "Cell",
                TaggedNodeRef::TinyRefNode(_) => "Tiny",
                TaggedNodeRef::EmptyNode => "Empty",
            }
        }
        fn walk<V: Clone + Send + Sync + std::fmt::Debug>(node: &TrieNodeODRc<V, crate::alloc::GlobalAlloc>, depth: usize, ids: &mut Vec<u64>, out: &mut String) {
            let id = node.shared_node_id();
            let idx = match ids.iter().position(|x| *x == id) { Some(i) => i, None => { ids.push(id); ids.len() - 1 } };
            let t = node.as_tagged();
            out.push_str(&format!("{}#{idx} {} rc={}\n", "  ".repeat(depth), kind(&t), node.refcount()));
            let mut it = t.new_iter_token();
            while it != NODE_ITER_FINISHED {
                let (next, path, child, val) = t.next_items(it, false);
                it = next;
                if val.is_none() && child.is_none() { continue; }
                out.push_str(&format!("{}  key {:?}{}{}\n", "  ".repeat(depth), path,
                    if val.is_some() { " V" } else { "" }, if child.is_some() { " ->" } else { "" }));
                if let Some(child) = child { walk(child, depth + 2, ids, out); }
            }
        }
        let mut out = String::new();
        let mut ids = Vec::new();
        if let Some(root) = map.root() { walk(root, 0, &mut ids, &mut out); }
        out.push_str(&format!("distinct nodes: {}\n", ids.len()));
        out
    }

    fn assert_same_paths_and_report(label: &str, map: &mut PathMap<()>) -> MerkleizeResultView {
        let before_paths = all_paths(map);
        let before_layout = dump_layout(map);
        let before_nodes = physical_node_count(map);
        let result = map.merkleize();
        let after_layout = dump_layout(map);
        let after_nodes = physical_node_count(map);
        eprintln!("==== {label} ====\n-- before ({before_nodes} nodes):\n{before_layout}-- merkleize: {result:?}\n-- after ({after_nodes} nodes):\n{after_layout}");
        assert_eq!(all_paths(map), before_paths, "merkleize must not change contents");
        assert_maximal_sharing(map);
        MerkleizeResultView { before_nodes, after_nodes, reused: result.reused }
    }
    struct MerkleizeResultView { before_nodes: usize, after_nodes: usize, reused: usize }

    /// The topology built by plain insertion, and by grafting so the `1` half gets different
    /// node boundaries than the `0` half
    #[test]
    fn topology_img_0825_legal_layouts() {
        // (a) natural layout from direct insertion
        let mut natural = PathMap::<()>::new();
        for p in [[0u8, 0, 0, 0], [0, 0, 0, 1], [1, 0, 0, 0], [1, 0, 0, 1]] { natural.insert(&p[..], ()); }
        let r = assert_same_paths_and_report("natural insertion", &mut natural);
        assert!(r.after_nodes <= r.before_nodes);

        // (b) `0` half by insertion: 0 -> [00 -> {0: V, 1: V}]
        //     `1` half by grafting:  1 -> [0 -> [0 -> {0: V, 1: V}]]  (the legal stand-in for [0 -> [00: V, 01: V]])
        let mut map = PathMap::<()>::new();
        map.insert(&[0u8, 0, 0, 0][..], ());
        map.insert(&[0u8, 0, 0, 1][..], ());
        let leaf: PathMap<()> = [[0u8].as_slice(), &[1u8]].into_iter().map(|k| (k, ())).collect();
        let mut mid = PathMap::<()>::new();
        { let mut wz = mid.write_zipper_at_path(&[0u8]); wz.graft_map(leaf); }
        let mut outer = PathMap::<()>::new();
        { let mut wz = outer.write_zipper_at_path(&[0u8]); wz.graft_map(mid); }
        { let mut wz = map.write_zipper_at_path(&[1u8]); wz.graft_map(outer); }
        let r = assert_same_paths_and_report("grafted: different boundaries under 1", &mut map);
        assert!(r.reused >= 1, "the {{000, 001}} subtrie under `1` should collapse onto the one under `0`");

        // (c) the reverse: `1` half by insertion, `0` half with the boundary directly below the root byte:
        //     0 -> [0 -> [00 -> {0: V, 1: V}]] is not constructible either (a node with a single 2-byte
        //     child key `00` and nothing else gets folded), so use 0 -> [0 -> [0 -> {0, 1}]] vs 1 -> [00 -> {0, 1}]
        let mut map = PathMap::<()>::new();
        map.insert(&[1u8, 0, 0, 0][..], ());
        map.insert(&[1u8, 0, 0, 1][..], ());
        let leaf: PathMap<()> = [[0u8].as_slice(), &[1u8]].into_iter().map(|k| (k, ())).collect();
        let mut mid = PathMap::<()>::new();
        { let mut wz = mid.write_zipper_at_path(&[0u8]); wz.graft_map(leaf); }
        let mut outer = PathMap::<()>::new();
        { let mut wz = outer.write_zipper_at_path(&[0u8]); wz.graft_map(mid); }
        { let mut wz = map.write_zipper_at_path(&[0u8]); wz.graft_map(outer); }
        let r = assert_same_paths_and_report("grafted: different boundaries under 0", &mut map);
        assert!(r.reused >= 1);
    }

    /// Hand-builds the picture's node 4, `[00: V, 01: V]`, which the trie invariant forbids, to see
    /// what the validator and merkleize do with it
    #[test]
    fn topology_img_0825_illegal_node4() {
        use crate::alloc::global_alloc;
        use crate::line_list_node::LineListNode;
        use crate::trie_node::ValOrChild;

        // `0` half: natural {000, 001} layout, taken from a map
        let a: PathMap<()> = [[0u8, 0, 0].as_slice(), &[0u8, 0, 1]].into_iter().map(|k| (k, ())).collect();
        let (a_root, _) = a.into_root();
        let a_root = a_root.unwrap();

        // `1` half: [0 -> [00: V, 01: V]]
        let mut node4 = LineListNode::<(), _>::new_in(global_alloc());
        unsafe {
            node4.set_payload_owned::<0>(&[0u8, 0], ValOrChild::Val(()));
            node4.set_payload_owned::<1>(&[0u8, 1], ValOrChild::Val(()));
        }
        let node4 = TrieNodeODRc::new_in(node4, global_alloc());
        let mut node3 = LineListNode::<(), _>::new_in(global_alloc());
        unsafe { node3.set_payload_owned::<0>(&[0u8], ValOrChild::Child(node4)); }
        let node3 = TrieNodeODRc::new_in(node3, global_alloc());

        let mut root = LineListNode::<(), _>::new_in(global_alloc());
        unsafe {
            root.set_payload_owned::<0>(&[0u8], ValOrChild::Child(a_root));
            root.set_payload_owned::<1>(&[1u8], ValOrChild::Child(node3));
        }
        let root = TrieNodeODRc::new_in(root, global_alloc());
        let mut map = PathMap::<()>::new_with_root_in(Some(root), None, global_alloc());

        eprintln!("-- hand-built layout:\n{}", dump_layout(&map));
        eprintln!("-- paths: {:?}", all_paths(&map));
        let valid = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| crate::trie_node::assert_valid_trie(map.root())));
        eprintln!("-- assert_valid_trie: {}", if valid.is_ok() { "ok" } else { "PANICKED (invariant violated)" });

        // The cata's ListNode case 7 assumes the invariant (`debug_assert_eq!(key0.len(), 1)`), so
        // merkleize on this layout is expected to panic in a debug build
        let merk = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let r = assert_same_paths_and_report("illegal node 4", &mut map);
            (r.reused, r.before_nodes, r.after_nodes)
        }));
        match merk {
            Ok((reused, before, after)) => eprintln!("-- merkleize survived the illegal node: reused={reused} before={before} after={after}"),
            Err(_) => eprintln!("-- merkleize PANICKED on the illegal node (cata assumes the ListNode invariant)"),
        }
    }
}

#[cfg(test)]
mod cache_tests {
    use super::*;
    use crate::{
        PathMap,
        morphisms::{CatamorphismCached, trie_hash::GxHashScheme},
        zipper::*,
    };
    use std::cell::Cell;
    struct CountValues(Cell<usize>);
    impl HashScheme<u64> for CountValues {
        type Acc = <GxHashScheme as HashScheme<u64>>::Acc;
        fn start(&self, m: &ByteMask) -> Self::Acc {
            <GxHashScheme as HashScheme<u64>>::start(&GxHashScheme, m)
        }
        fn child(&self, a: &mut Self::Acc, h: u128) {
            <GxHashScheme as HashScheme<u64>>::child(&GxHashScheme, a, h)
        }
        fn finish(&self, a: Self::Acc) -> u128 {
            <GxHashScheme as HashScheme<u64>>::finish(&GxHashScheme, a)
        }
        fn value(&self, v: &u64) -> u128 {
            self.0.set(self.0.get() + 1);
            GxHashScheme.value(v)
        }
        fn with_value(&self, v: u128, h: u128) -> u128 {
            <GxHashScheme as HashScheme<u64>>::with_value(&GxHashScheme, v, h)
        }
    }
    #[test]
    fn valued_shared_nodes_are_reused() {
        let mut map = PathMap::from_iter([(b"".as_slice(), 1u64), (b"leaf".as_slice(), 2)]);
        for _ in 0..10 {
            let mut next = PathMap::from_iter([(b"".as_slice(), 1u64)]);
            for prefix in [b"a", b"b"] {
                next.write_zipper_at_path(prefix).graft_map(map.clone());
            }
            map = next;
        }
        let scheme = CountValues(Cell::new(0));
        let (result, _) = merkleize_root(map.root().unwrap(), map.root_val(), &scheme);
        // Each shared node is summarized once; values in its incoming slots are hashed separately.
        assert_eq!(scheme.0.get(), 22);
        assert_eq!(result.hash, CatamorphismCached::hash(&map));
    }
}
