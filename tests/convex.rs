use pathmap::{
    PathMap,
    experimental::{convex::*, path_sets::retain},
    zipper::*,
};
use std::collections::{BTreeMap, BTreeSet};

type Space = BTreeSet<Vec<u8>>;
fn value(p: &[u8]) -> u64 {
    p.iter()
        .fold(7u64, |v, b| v.wrapping_mul(257).wrapping_add(*b as u64 + 1))
}
fn map(s: &Space) -> PathMap<u64> {
    let mut m = PathMap::new();
    for p in s {
        m.set_val_at(p, value(p));
    }
    m
}
fn vals(m: &PathMap<u64>) -> BTreeMap<Vec<u8>, u64> {
    m.iter().map(|(p, v)| (p, *v)).collect()
}
fn hull(s: &Space) -> Space {
    s.iter()
        .filter(|p| !s.iter().any(|q| p != &q && q.starts_with(p)))
        .cloned()
        .collect()
}
// Independent repeated-removal oracle, not the implementation's postorder rule.
fn prune(mut x: Space, protected: Space) -> BTreeMap<Vec<u8>, u64> {
    loop {
        let remove: Vec<_> = hull(&x).difference(&protected).cloned().collect();
        if remove.is_empty() {
            break;
        }
        for p in remove {
            x.remove(&p);
        }
    }
    x.into_iter()
        .map(|p| {
            let v = value(&p);
            (p, v)
        })
        .collect()
}
fn check(a: &Space, b: &Space, ma: &PathMap<u64>, mb: &PathMap<u64>) {
    let meet = prune(
        a.intersection(b).cloned().collect(),
        hull(a).intersection(&hull(b)).cloned().collect(),
    );
    let sub = prune(a.clone(), hull(a).difference(b).cloned().collect());
    let common = map(&a.intersection(b).cloned().collect());
    let common_tips = map(&hull(a).intersection(&hull(b)).cloned().collect());
    let surviving_tips = map(&hull(a).difference(b).cloned().collect());
    assert_eq!(
        vals(&retain(&common, &common_tips)),
        meet,
        "retain meet {a:?} {b:?}"
    );
    assert_eq!(
        vals(&retain(ma, &surviving_tips)),
        sub,
        "retain subtract {a:?} {b:?}"
    );
    assert_eq!(vals(&convex_meet(ma, mb)), meet, "node meet {a:?} {b:?}");
    assert_eq!(
        vals(&convex_subtract(ma, mb)),
        sub,
        "node subtract {a:?} {b:?}"
    );
    let mut out = PathMap::new();
    zipper_convex_meet(
        &mut ma.read_zipper(),
        &mut mb.read_zipper(),
        &mut out.write_zipper(),
    );
    assert_eq!(vals(&out), meet, "zipper meet {a:?} {b:?}");
    zipper_convex_subtract(
        &mut ma.read_zipper(),
        &mut mb.read_zipper(),
        &mut out.write_zipper(),
    );
    assert_eq!(vals(&out), sub, "zipper subtract {a:?} {b:?}");
}
fn spaces() -> Vec<Space> {
    let ps = [
        vec![],
        vec![0],
        vec![1],
        vec![0, 0],
        vec![0, 1],
        vec![1, 0],
        vec![1, 1],
    ];
    (0..128)
        .map(|mask| {
            ps.iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, p)| p.clone())
                .collect()
        })
        .collect()
}
#[test]
fn exhaustive_binary_spaces() {
    let ss = spaces();
    let maps: Vec<_> = ss.iter().map(map).collect();
    for (i, a) in ss.iter().enumerate() {
        for (j, b) in ss.iter().enumerate() {
            check(a, b, &maps[i], &maps[j]);
        }
    }
}
#[test]
fn dangling_paths_are_not_tips() {
    let ss = spaces();
    let maps: Vec<_> = ss
        .iter()
        .enumerate()
        .map(|(i, s)| {
            let mut m = map(s);
            for p in [vec![0, 0, 0], vec![1, 0, 1], vec![i as u8, 255, 0]] {
                m.write_zipper_at_path(&p).create_path();
            }
            m
        })
        .collect();
    for (i, a) in ss.iter().enumerate() {
        let clone = maps[i].clone();
        check(a, a, &maps[i], &clone);
        for (j, b) in ss.iter().enumerate() {
            check(a, b, &maps[i], &maps[j]);
        }
    }
}
#[test]
fn compressed_edges_dense_nodes_and_shared_subtrees() {
    for width in [1usize, 2, 16, 80, 256] {
        let mut a = Space::new();
        let mut b = Space::new();
        a.insert(vec![]);
        b.insert(vec![]);
        for n in 0..width {
            let mut p = vec![n as u8; 151];
            for len in [1, 47, 48, 49, 97, 150] {
                a.insert(p[..len].to_vec());
                if n % 3 != 0 {
                    b.insert(p[..len].to_vec());
                }
            }
            a.insert(p.clone());
            if n % 2 == 0 {
                b.insert(p.clone());
            } else {
                p.push(255);
                b.insert(p);
            }
        }
        let ma = map(&a);
        let mb = map(&b);
        check(&a, &b, &ma, &mb);
        let mut shared = ma.clone();
        for p in b.iter().take(width) {
            shared.set_val_at(p, value(p));
        }
        let union: Space = shared.iter().map(|(p, _)| p).collect();
        check(&a, &union, &ma, &shared);
    }
}
#[test]
fn focused_zipper_restores_cursors_and_preserves_outside() {
    let mut a = PathMap::new();
    let mut b: PathMap<u8> = PathMap::new();
    for (p, v) in [
        (b"x".as_slice(), 1),
        (b"xa", 2),
        (b"xab", 3),
        (b"xac", 4),
        (b"z", 99),
    ] {
        a.set_val_at(p, v);
    }
    for p in [b"y".as_slice(), b"ya", b"yab", b"yada"] {
        b.set_val_at(p, 9);
    }
    for subtract in [false, true] {
        let mut out = PathMap::new();
        out.set_val_at(b"p", 80);
        out.set_val_at(b"po", 81);
        out.set_val_at(b"po/old", 82);
        out.set_val_at(b"q", 83);
        let mut l = a.read_zipper();
        l.descend_to(b"x");
        let mut r = b.read_zipper();
        r.descend_to(b"y");
        {
            let mut o = out.write_zipper();
            o.descend_to(b"po");
            if subtract {
                zipper_convex_subtract(&mut l, &mut r, &mut o);
            } else {
                zipper_convex_meet(&mut l, &mut r, &mut o);
            }
            assert_eq!(o.path(), b"po");
        }
        assert_eq!(l.path(), b"x");
        assert_eq!(r.path(), b"y");
        let mut expected = BTreeMap::from([
            (b"p".to_vec(), 80),
            (b"q".to_vec(), 83),
            (b"po".to_vec(), 1),
            (b"poa".to_vec(), 2),
        ]);
        expected.insert(
            if subtract {
                b"poac".to_vec()
            } else {
                b"poab".to_vec()
            },
            if subtract { 4 } else { 3 },
        );
        assert_eq!(vals(&out), expected);
        let mut empty = b.read_zipper_at_path(b"missing");
        zipper_convex_meet(&mut l, &mut empty, &mut out.write_zipper_at_path(b"po"));
        assert!(empty.path().is_empty());
        assert_eq!(
            vals(&out),
            BTreeMap::from([(b"p".to_vec(), 80), (b"q".to_vec(), 83)])
        );
    }
    let _ = convex_meet(&a, &b);
    let _ = convex_subtract(&a, &b);
}
#[test]
fn deep_chain_prunes_to_stability() {
    let a: Space = (0..1024).map(|n| vec![0; n]).collect();
    let mut b = a.clone();
    b.remove(&vec![0; 1023]);
    b.insert([vec![0; 1022], vec![1]].concat());
    let ma = map(&a);
    let mb = map(&b);
    assert_eq!(convex_meet(&ma, &mb).val_count(), 0);
    let mut out = PathMap::new();
    zipper_convex_meet(
        &mut ma.read_zipper(),
        &mut mb.read_zipper(),
        &mut out.write_zipper(),
    );
    assert_eq!(out.val_count(), 0);
    assert_eq!(vals(&convex_subtract(&ma, &mb)), vals(&ma));
}

#[test]
fn randomized_shapes_and_partial_sharing() {
    use rand::{Rng, SeedableRng, rngs::StdRng};
    let mut rng = StdRng::seed_from_u64(0xC0A7E);
    for _ in 0..300 {
        let mut pool = Space::new();
        for _ in 0..rng.random_range(1..80) {
            let len = rng.random_range(0..90);
            let p: Vec<u8> = (0..len).map(|_| rng.random_range(0..6)).collect();
            pool.insert(p[..rng.random_range(0..=len)].to_vec());
            pool.insert(p);
        }
        let a: Space = pool
            .iter()
            .filter(|_| rng.random_bool(0.7))
            .cloned()
            .collect();
        let b: Space = pool
            .iter()
            .filter(|_| rng.random_bool(0.6))
            .cloned()
            .collect();
        let mut ma = map(&a);
        let mut mb = ma.clone();
        for p in a.difference(&b) {
            mb.remove_val_at(p, false);
        }
        for p in b.difference(&a) {
            mb.set_val_at(p, value(p));
        }
        for p in &pool {
            ma.write_zipper_at_path(p).create_path();
            mb.write_zipper_at_path(p).create_path();
        }
        check(&a, &b, &ma, &mb);
        assert_eq!(vals(&ma), a.iter().map(|p| (p.clone(), value(p))).collect());
        assert_eq!(vals(&mb), b.iter().map(|p| (p.clone(), value(p))).collect());
    }
}

#[test]
fn subtree_reuse_does_not_clone_payloads() {
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };
    struct Counted(Arc<AtomicUsize>);
    impl Clone for Counted {
        fn clone(&self) -> Self {
            self.0.fetch_add(1, Ordering::Relaxed);
            Self(self.0.clone())
        }
    }
    let clones = Arc::new(AtomicUsize::new(0));
    let mut a = PathMap::new();
    let mut mask = PathMap::<()>::new();
    for n in 0..2000u32 {
        let p = n.to_be_bytes();
        a.set_val_at(p, Counted(clones.clone()));
        a.set_val_at([p.as_slice(), &[0]].concat(), Counted(clones.clone()));
        mask.set_val_at(p, ());
    }
    let shared = a.clone();
    clones.store(0, Ordering::Relaxed);
    assert_eq!(convex_meet(&a, &shared).val_count(), 4000);
    assert_eq!(convex_subtract(&a, &mask).val_count(), 4000);
    assert_eq!(convex_subtract(&a, &shared).val_count(), 0);
    assert_eq!(clones.load(Ordering::Relaxed), 0);
    let mut out = PathMap::new();
    zipper_convex_meet(
        &mut a.read_zipper(),
        &mut shared.read_zipper(),
        &mut out.write_zipper(),
    );
    assert_eq!(out.val_count(), 4000);
    assert_eq!(clones.load(Ordering::Relaxed), 0);
}

#[test]
fn extracted_subtries_and_empty_bare_shared_roots() {
    let mut source = PathMap::new();
    for (p, v) in [(b"abcdef".as_slice(), 10), (b"abcdefgh", 20)] {
        source.set_val_at(p, v);
    }
    source.write_zipper_at_path(b"abcdef/bare").create_path();
    let a = source.read_zipper_at_path(b"abc").make_map();
    let mut b = PathMap::<()>::new();
    b.set_val_at(b"def", ());
    b.set_val_at(b"defgh", ());
    assert_eq!(
        vals(&convex_meet(&a, &b)),
        BTreeMap::from([(b"def".to_vec(), 10), (b"defgh".to_vec(), 20)])
    );
    b.remove_val_at(b"defgh", true);
    assert_eq!(convex_meet(&a, &b).val_count(), 0);
    assert_eq!(vals(&convex_subtract(&a, &b)), vals(&a));
    let mut empty = PathMap::<u64>::new();
    empty.write_zipper_at_path(b"bare/only").create_path();
    let mut root = empty.clone();
    root.set_val_at([], 55);
    assert_eq!(
        vals(&convex_subtract(&root, &empty)),
        BTreeMap::from([(vec![], 55)])
    );
    assert_eq!(convex_meet(&root, &empty).val_count(), 0);
    assert_eq!(convex_subtract(&empty, &root).val_count(), 0);
}

#[test]
fn zipper_head_cell_nodes_match_dense_and_list_nodes() {
    let a: Space = (0..=255u8)
        .flat_map(|b| [vec![0, b], vec![0, b, 0], vec![0, b, 1]])
        .collect();
    let b: Space = (0..=255u8)
        .flat_map(|b| [vec![0, b], vec![0, b, b % 3]])
        .collect();
    let mut ma = map(&a);
    let mut mb = map(&b);
    for m in [&mut ma, &mut mb] {
        let head = m.zipper_head();
        for b in 0..=255u8 {
            let path = [0, b, 255];
            let mut z = head.write_zipper_at_exclusive_path(path).unwrap();
            z.create_path();
        }
    }
    check(&a, &b, &ma, &mb);
    check(&a, &b, &ma, &map(&b));
    check(&a, &b, &map(&a), &mb);
}
