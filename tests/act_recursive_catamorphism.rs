#![cfg(feature = "arena_compact")]

use pathmap::PathMap;
use pathmap::arena_compact::ArenaCompactTree;
use pathmap::morphisms::CatamorphismCached;
use pathmap::zipper::{ZipperAbsolutePath, ZipperMoving, ZipperWriting};

// Include unvalued paths as well as values, so compressed runs and dangling
// paths must reconstruct the same logical trie, byte for byte.
fn logical_nodes<Z: CatamorphismCached<u64>>(zipper: &Z) -> Vec<(Vec<u8>, Option<u64>)> {
    zipper.cata_cached(
        |mask, children: &mut [Vec<(Vec<u8>, Option<u64>)>], value| {
            let mut result = vec![(Vec::new(), value.copied())];
            for (byte, child) in mask.iter().zip(children) {
                for (mut path, value) in std::mem::take(child) {
                    path.insert(0, byte);
                    result.push((path, value));
                }
            }
            result
        },
    )
}

#[test]
fn recursive_act_matches_native_from_every_focus() {
    let mut dangling = PathMap::<u64>::new();
    dangling.set_val_at(b"dangling", 1);
    dangling.write_zipper_at_path(b"dangling").remove_val(false);
    let fixtures = [
        PathMap::<u64>::new(),
        dangling,
        PathMap::from_iter([(b"".as_slice(), u64::MAX)]),
        PathMap::from_iter([(b"abcdefghij".as_slice(), 248)]),
        PathMap::from_iter([
            (b"".as_slice(), 0),
            (b"a", 247),
            (b"ab", 248),
            (b"abcdef", 65535),
            (b"abcxyz", u64::MAX),
            (b"z", 1),
        ]),
        PathMap::from_iter((0..=255u64).map(|byte| (vec![byte as u8, 1, 2], byte))),
    ];
    for map in fixtures {
        let mut focuses = vec![Vec::new(), b"missing".to_vec(), b"dangling".to_vec()];
        for (path, _) in map.iter() {
            for depth in 0..=path.len() {
                focuses.push(path[..depth].to_vec());
            }
            let mut missing = path;
            missing.push(255);
            focuses.push(missing);
        }
        focuses.sort();
        focuses.dedup();
        for tree in [
            ArenaCompactTree::from_zipper(map.read_zipper(), |&value| value),
            ArenaCompactTree::from_zipper_cached(map.read_zipper(), |&value| value),
        ] {
            for focus in &focuses {
                let native = map.read_zipper_at_path(focus);
                let mut act = tree.read_zipper_u64();
                act.descend_to(focus);
                let before = act.origin_path().to_vec();
                assert_eq!(
                    logical_nodes(&act),
                    logical_nodes(&native),
                    "focus {focus:?}"
                );
                let expected = map
                    .iter()
                    .filter(|(path, _)| path.starts_with(focus))
                    .count();
                assert_eq!(act.val_count(), expected, "focus {focus:?}");
                assert_eq!(
                    pathmap::morphisms::CatamorphismCachedIterative::val_count(&act),
                    expected,
                );
                assert_eq!(act.origin_path(), before);
                assert_eq!(tree.read_zipper_at_path_u64(focus).val_count(), expected);
                assert_eq!(tree.read_zipper_at_path(focus).val_count(), expected);
            }
        }
    }
}

#[test]
fn both_act_strategies_revisit_shared_subtries() {
    use std::cell::Cell;

    let mut map = PathMap::from_iter([(b"leaf".as_slice(), 7u64)]);
    for _ in 0..8 {
        let mut next = PathMap::new();
        for prefix in [b"left".as_slice(), b"right"] {
            next.write_zipper_at_path(prefix).graft(&map.read_zipper());
        }
        map = next;
    }
    let tree = ArenaCompactTree::from_zipper_cached(map.read_zipper(), |&value| value);
    let recursive_values = Cell::new(0);
    let zipper = tree.read_zipper_u64();
    let count = zipper.cata_jumping_cached(|_, children: &mut [usize], value, _| {
        recursive_values.set(recursive_values.get() + value.is_some() as usize);
        value.is_some() as usize + children.iter().sum::<usize>()
    });
    let iterative_values = Cell::new(0);
    let iterative_count = pathmap::morphisms::CatamorphismCachedIterative::cata_jumping_cached(
        &zipper,
        |_, children: &mut [usize], value, _| {
            iterative_values.set(iterative_values.get() + value.is_some() as usize);
            value.is_some() as usize + children.iter().sum::<usize>()
        },
    );
    assert_eq!(count, 1 << 8);
    assert_eq!(iterative_count, count);
    // ACT has no sharing metadata: both strategies currently visit each
    // logical value, even when the serialized subtree is shared.
    assert_eq!(recursive_values.get(), count);
    assert_eq!(iterative_values.get(), count);
    assert_eq!(zipper.val_count(), count);
}

#[test]
fn recursive_act_reads_mapped_storage() {
    let map = PathMap::from_iter([(b"a".as_slice(), 248u64), (b"abcdef", u64::MAX)]);
    let tree = ArenaCompactTree::from_zipper(map.read_zipper(), |&value| value);
    let file = tempfile::NamedTempFile::new().unwrap();
    std::fs::write(file.path(), tree.get_data()).unwrap();
    let mapped = ArenaCompactTree::open_mmap(file.path()).unwrap();
    assert_eq!(
        logical_nodes(&mapped.read_zipper_u64()),
        logical_nodes(&map.read_zipper())
    );
    assert_eq!(mapped.read_zipper_at_path_u64(b"abc").val_count(), 1);
}
