use pathmap::{
    PathMap,
    morphisms::{CatamorphismCached, CatamorphismCachedIterative},
    zipper::*,
};

fn snapshot(map: &PathMap<u64>) -> Vec<(Vec<u8>, Option<u64>)> {
    let mut z = map.read_zipper();
    let mut result = vec![(vec![], z.val().copied())];
    while z.to_next_step() {
        result.push((z.path().to_vec(), z.val().copied()));
    }
    result
}

#[test]
fn empty_and_root_only() {
    for mut map in [
        PathMap::<u64>::new(),
        PathMap::from_iter([(b"".as_slice(), 42)]),
    ] {
        let expected = CatamorphismCached::hash(&map);
        assert_eq!(expected, CatamorphismCachedIterative::hash(&map));
        assert_eq!(map.merkleize().hash, expected);
    }
}

#[test]
fn seeded_mixed_paths() {
    use rand::{Rng, SeedableRng};
    let mut rng = rand::rngs::StdRng::seed_from_u64(12345);
    for case in 0..100 {
        let mut map = PathMap::<u64>::new();
        for _ in 0..100 {
            let len = rng.random_range(0..12);
            let path: Vec<u8> = (0..len).map(|_| rng.random_range(0..4)).collect();
            if rng.random_bool(0.3) {
                map.create_path(&path);
            } else {
                map.set_val_at(&path, rng.random_range(0..5));
            }
        }
        let before = snapshot(&map);
        let hash = CatamorphismCached::hash(&map);
        assert_eq!(hash, CatamorphismCachedIterative::hash(&map), "case {case}");
        let result = map.merkleize();
        assert_eq!(result.hash, hash, "case {case}");
        assert_eq!(snapshot(&map), before, "case {case}");
        assert_eq!(CatamorphismCached::hash(&map), hash, "case {case}");
        assert_eq!(CatamorphismCachedIterative::hash(&map), hash, "case {case}");
        let second = map.merkleize();
        assert_eq!(
            (second.reused, second.replaced, second.cloned),
            (0, 0, 0),
            "case {case}"
        );
    }
}
