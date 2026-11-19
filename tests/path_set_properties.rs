//! Properties outside the generated algebraic expression laws, including
//! cardinality, prefix coverage, recursive specifications, and closure generators.
//! Exportable equations are generated in differential/src/algebraic/path_set_laws.rs.
use pathmap::{
    PathMap,
    experimental::path_sets::{basis, branches as br, divergence as d, hull, retain},
    zipper::*,
};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::collections::BTreeSet;

type KeySet = BTreeSet<Vec<u8>>;
type M = PathMap<()>;

fn e() -> M {
    M::single([], ())
}

fn count(a: &M) -> usize {
    a.val_count()
}

fn height(a: &M) -> usize {
    a.iter().map(|(p, _)| p.len()).max().unwrap_or(0)
}

fn interior(a: &M) -> M {
    a.subtract(&hull(a))
}

fn completion(a: &M) -> M {
    a.join(&br(a))
}

fn raff(a: &M, p: &M) -> M {
    a.subtract(&a.restrict(p))
}

fn sym(a: &M, b: &M) -> M {
    a.subtract(b).join(&b.subtract(a))
}

fn covers(a: &M, b: &M) -> bool {
    a.iter()
        .all(|(p, _)| b.iter().any(|(q, _)| q.starts_with(&p)))
}

fn prefix_free(a: &M) -> bool {
    set_from_map(a) == set_from_map(&basis(a))
}

fn wrap(p: &[u8], a: &M) -> M {
    let mut out = M::new();
    let mut z = out.write_zipper_at_path(p);
    z.join_map_into(a.clone());
    // Make the helper independent of the graft_root_vals feature.
    if a.get([]).is_some() {
        z.set_val(());
    }
    out
}

fn unwrap(a: &M, p: &[u8]) -> M {
    let z = a.read_zipper_at_path(p);
    let mut out = z.make_map();
    if z.is_val() {
        out.set_val_at([], ());
    }
    out
}

fn product(a: &M, b: &M) -> M {
    let mut out = M::new();
    for (p, _) in a.iter() {
        let mut z = out.write_zipper_at_path(&p);
        z.join_map_into(b.clone());
        if b.get([]).is_some() {
            z.set_val(());
        }
    }
    out
}

fn head(a: &M) -> M {
    let mut out = M::new();
    for (p, _) in a.iter() {
        if let Some(&c) = p.first() {
            out.set_val_at([c], ());
        }
    }
    out
}

fn tails(a: &M) -> M {
    let mut out = M::new();
    for (p, _) in a.iter() {
        if !p.is_empty() {
            out.set_val_at(&p[1..], ());
        }
    }
    out
}

fn lcp(a: &[u8], b: &[u8]) -> Vec<u8> {
    a[..a.iter().zip(b).take_while(|(x, y)| x == y).count()].to_vec()
}

fn lcp_product(a: &M, b: &M) -> M {
    let mut out = M::new();
    for (p, _) in a.iter() {
        for (q, _) in b.iter() {
            out.set_val_at(lcp(&p, &q), ());
        }
    }
    out
}

fn common_prefix(a: &M) -> Vec<u8> {
    let mut it = a.iter();
    let Some((p, _)) = it.next() else {
        return vec![];
    };
    it.fold(p, |p, (q, _)| lcp(&p, &q))
}

fn power(a: &M, n: usize) -> M {
    (0..n).fold(e(), |b, _| product(a, &b))
}

fn branch_iter(a: &M, n: usize) -> M {
    (0..n).fold(a.clone(), |b, _| br(&b))
}

// Independent recursive specifications (no call to the operation under test).

fn basis_rec(a: &M) -> M {
    if a.get([]).is_some() {
        return e();
    }
    head(a).iter().fold(M::new(), |out, (p, _)| {
        out.join(&wrap(&p, &basis_rec(&unwrap(a, &p))))
    })
}

fn hull_rec(a: &M) -> M {
    let h = head(a);
    let root = if a.get([]).is_some() && h.is_empty() {
        e()
    } else {
        M::new()
    };
    h.iter().fold(root, |out, (p, _)| {
        out.join(&wrap(&p, &hull_rec(&unwrap(a, &p))))
    })
}

fn divergence_rec(a: &M, b: &M) -> M {
    let ha = head(a);
    let hb = head(b);
    let cross = ha.iter().any(|(p, _)| hb.iter().any(|(q, _)| p != q));
    let root = if cross { e() } else { M::new() };
    ha.meet(&hb).iter().fold(root, |out, (p, _)| {
        out.join(&wrap(&p, &divergence_rec(&unwrap(a, &p), &unwrap(b, &p))))
    })
}

fn retain_rec(p: &M, a: &M) -> M {
    let root = if p.get([]).is_some() && !a.is_empty() {
        e()
    } else {
        M::new()
    };
    head(p).meet(&head(a)).iter().fold(root, |out, (q, _)| {
        out.join(&wrap(&q, &retain_rec(&unwrap(p, &q), &unwrap(a, &q))))
    })
}

fn overlaps(a: &M, b: &M, x: &M, y: &M) -> M {
    let mut out = M::new();
    for (p, _) in a.iter() {
        for (q, _) in b.iter() {
            if q.len() > p.len() && q.starts_with(&p) {
                out = out.join(&wrap(&p, &d(x, &wrap(&q[p.len()..], y))));
            }
            if p.len() > q.len() && p.starts_with(&q) {
                out = out.join(&wrap(&q, &d(&wrap(&p[q.len()..], x), y)));
            }
        }
    }
    out
}

#[track_caller]
fn assert_same(a: &M, b: &M) {
    assert_eq!(set_from_map(a), set_from_map(b));
}

#[track_caller]
fn assert_subset(a: &M, b: &M) {
    let a = set_from_map(a);
    let b = set_from_map(b);
    assert!(a.is_subset(&b), "{a:?} is not a subset of {b:?}");
}

fn retention_properties(a: &M, b: &M) {
    assert_eq!(retain(a, b).is_empty(), b.restrict(a).is_empty());
    assert_eq!(set_from_map(&retain(a, b)) == set_from_map(a), covers(a, b));
    assert!(count(&retain(a, b)) <= count(a));
}

fn closure_properties(a: &M, b: &M, c: &M) {
    let ca = completion(a);
    let cb = completion(b);
    let cc = completion(c);
    let ab = lcp_product(a, b);
    let ga = a.subtract(&br(a));
    let same = |x: &M, y: &M| set_from_map(x) == set_from_map(y);
    let subset = |x: &M, y: &M| set_from_map(x).is_subset(&set_from_map(y));
    assert_same(&lcp_product(&ab, a), &ab);
    assert_same(&lcp_product(&ab, b), &ab);
    assert!(subset(&ca, &cb) == subset(a, &cb));
    assert!(same(&cb, &ca) == (subset(&ga, b) && subset(b, &ca)));
    assert!(same(&ca, &cb) == same(&ga, &b.subtract(&br(b))));
    assert!(same(&completion(&ca.join(&cb)), &ca.join(&cb)) == subset(&d(&ca, &cb), &ca.join(&cb)));
    assert!(subset(&completion(&a.join(b)), &cc) == (subset(a, &cc) && subset(b, &cc)));
    assert!(same(&ab, a) == (covers(a, b) && subset(&d(a, b), a) && subset(&retain(b, a), a)));
    assert!(
        same(&lcp_product(a, &lcp_product(b, c)), a)
            == (same(&ab, a) && same(&lcp_product(a, c), a))
    );
    assert!(count(&ca) <= count(a) + count(&hull(a)).saturating_sub(1));
    assert!(count(a) <= count(&ca) && count(&ca) <= (2 * count(a)).saturating_sub(1));
    if !a.is_empty() {
        assert_same(&basis(&ca), &M::single(common_prefix(a), ()));
    }
}

fn properties(a: &M, b: &M, c: &M, f: &M) {
    closure_properties(a, b, c);
    retention_properties(a, b);
    let x = d(a, b);
    let ba = br(a);
    let ha = hull(a);
    let hb = hull(b);
    let zero = M::new();
    assert_subset(&br(&ba), &ba);
    assert_subset(&basis(a), a);
    assert_subset(&ha, a);
    assert_eq!(basis(a).is_empty(), a.is_empty());
    assert_eq!(ha.is_empty(), a.is_empty());
    assert!(covers(a, &ha) && covers(&basis(a), a));
    assert_same(&basis_rec(a), &basis(a));
    assert_same(&hull_rec(a), &ha);
    assert_same(&divergence_rec(a, a), &ba);
    assert!(count(&hull(&ba)) <= count(&ha) / 2);
    if !a.is_empty() {
        assert!(set_from_map(&ba) != set_from_map(a));
    }
    assert_same(&branch_iter(a, height(a) + 1), &zero);
    assert_subset(&br(&a.meet(b)), &ba.meet(&br(b)));
    assert_subset(&ba.meet(&br(b)), &x);
    assert_subset(&x, &br(&a.join(b)));
    assert_subset(&interior(&x), &ba.join(&br(b)));
    assert_subset(&br(&x), &x.meet(&ba.meet(&br(b))));
    if !x.is_empty() {
        assert_same(&basis(&x), &M::single(common_prefix(&ha.join(&hb)), ()));
    }
    let all_prefix = |u: &M, v: &M| {
        u.iter()
            .all(|(p, _)| v.iter().all(|(q, _)| q.starts_with(&p)))
    };
    assert!(
        x.is_empty()
            == (a.is_empty()
                || b.is_empty()
                || count(&ha) == 1 && all_prefix(&ha, &hb)
                || count(&hb) == 1 && all_prefix(&hb, &ha))
    );
    assert_subset(&head(&x), &head(a).meet(&head(b)));
    assert_subset(&tails(&x), &d(&tails(a), &tails(b)));
    assert_same(&divergence_rec(a, b), &x);
    assert_same(&retain_rec(a, b), &retain(a, b));
    assert!(count(&x) <= count(&hull(&a.join(b))).saturating_sub(1));
    assert!(count(&hull(&x)) <= count(&ha).min(count(&hb)));
    if !x.is_empty() {
        assert!(height(&x) < height(a).min(height(b)));
    }
    assert!(covers(&x, a) && covers(&x, b));
    // The generated expression for LCP uses divergence and retain. Check it
    // against the independent all-pairs definition as well.
    let m = lcp_product(a, b);
    assert_same(&m, &x.join(&retain(a, b)).join(&retain(b, a)));
    assert_subset(&d(&a.meet(b), c), &d(a, c).meet(&d(b, c)));
    assert_subset(&d(a, c).subtract(&d(b, c)), &d(&a.subtract(b), c));
    assert_subset(&d(&a.subtract(b), c), &d(a, c));
    assert_subset(&sym(&d(a, c), &d(b, c)), &d(&sym(a, b), c));
    if set_from_map(a).is_subset(&set_from_map(b)) {
        assert_subset(&d(a, c), &d(b, c));
    }
    if covers(a, b) {
        assert_subset(&d(a, c), &d(b, c));
    }
    if covers(b, a) {
        assert_same(&d(&a.join(b), c), &d(a, c));
    }
    assert_subset(&d(&x, c), &d(a, c).meet(&d(b, c)));
    assert_subset(&x.meet(&br(c)), &d(a, c).meet(&d(b, c)));
    assert_subset(
        &d(&x, &d(c, f)),
        &d(a, c).meet(&d(a, f)).meet(&d(b, c)).meet(&d(b, f)),
    );
    assert_subset(
        &x.meet(&d(c, f)),
        &d(a, c).meet(&d(b, f)).join(&d(a, f).meet(&d(b, c))),
    );
    assert_subset(&d(&raff(a, c), &raff(b, f)), &raff(&x, &c.join(f)));
    let prod_rhs = if c.is_empty() || f.is_empty() {
        M::new()
    } else {
        x.join(&product(&a.meet(b), &d(c, f)))
            .join(&overlaps(a, b, c, f))
    };
    assert_same(&d(&product(a, c), &product(b, f)), &prod_rhs);
    let mut paths = vec![vec![], vec![0], vec![0, 1, 0]];
    paths.extend(a.iter().take(2).map(|(p, _)| p));
    for p in paths {
        let single = M::single(&p, ());
        let chain = d(&single, b);
        assert_same(&d(&unwrap(a, &p), &unwrap(b, &p)), &unwrap(&x, &p));
        assert!(count(&chain) <= p.len().min(count(&hb)));
        assert_subset(&interior(&chain), &br(b));
        assert!(count(&br(&b.join(&single)).subtract(&br(b))) <= 1);
        assert!(count(&d(&a.join(&single), b).subtract(&x)) <= p.len().min(count(&hb)));
    }
}

fn power_properties(a: &M) {
    assert!(prefix_free(a));
    let max_power = if cfg!(miri) { 2 } else { 3 };
    for n in 0..=max_power {
        for m in 0..=max_power {
            let rhs =
                (0..m.min(n)).fold(M::new(), |out, i| out.join(&product(&power(a, i), &br(a))));
            assert_same(&d(&power(a, m), &power(a, n)), &rhs);
        }
    }
    for n in 0..=3 {
        if !branch_iter(a, n).is_empty() {
            assert!(2usize.pow(n as u32) <= count(&hull(a)));
        }
    }
}

fn map_from_set(keys: &KeySet) -> M {
    keys.iter().map(|p| (p.clone(), ())).collect()
}

fn set_from_map(a: &M) -> KeySet {
    a.iter().map(|(p, _)| p).collect()
}

fn small(seed: u64, salt: u64) -> M {
    let mut rng = StdRng::seed_from_u64(seed ^ salt);
    let n = rng.random_range(0..7);
    let keys: KeySet = (0..n)
        .map(|_| {
            let len = rng.random_range(0..6);
            (0..len).map(|_| rng.random_range(0..3)).collect()
        })
        .collect();
    map_from_set(&keys)
}

/// All subsets of a depth-two binary tree, including every closed subspace.
/// Check anti-exchange and the necessity of each least generator.

#[test]
fn exhaustive_branch_closure_generators() {
    let paths = [
        vec![],
        vec![0],
        vec![1],
        vec![0, 0],
        vec![0, 1],
        vec![1, 0],
        vec![1, 1],
    ];
    let paths = &paths[..if cfg!(miri) { 4 } else { paths.len() }];
    for mask in 0..(1usize << paths.len()) {
        let keys: KeySet = paths
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, p)| p.clone())
            .collect();
        let a = map_from_set(&keys);
        let closed = completion(&a);
        let closed_keys = set_from_map(&closed);
        let generators = a.subtract(&br(&a));
        for x in paths {
            // Deleting a least generator strictly changes the closure.
            if generators.get(x).is_some() {
                assert_ne!(
                    closed_keys,
                    set_from_map(&completion(&a.subtract(&M::single(x, ()))))
                );
            }
            if closed_keys.contains(x) {
                continue;
            }
            let with_x = completion(&a.join(&M::single(x, ())));
            for y in paths {
                if x == y || closed_keys.contains(y) {
                    continue;
                }
                let with_y = completion(&a.join(&M::single(y, ())));
                if with_y.get(x).is_some() {
                    assert!(
                        with_x.get(y).is_none(),
                        "anti-exchange: {keys:?}, {x:?}, {y:?}"
                    );
                }
            }
        }
    }
}

#[test]
fn seeded_path_set_properties() {
    let seeds = if cfg!(miri) { 2 } else { 256 };
    for seed in 0..seeds {
        let case = std::panic::catch_unwind(|| {
            let a = small(seed, 11);
            let b = small(seed, 23);
            let c = small(seed, 47);
            let f = small(seed, 97);
            properties(&a, &b, &c, &f);
            // Correlated operands exercise the conditional properties.
            properties(&hull(&a), &hull(&a).join(&hull(&b)), &e(), &e());
            properties(&a.join(&b), &b, &c, &f);
            power_properties(&hull(&a));
        });
        assert!(case.is_ok(), "path-set properties failed at seed {seed}");
    }
}

#[test]
fn dense_path_set_properties() {
    // Values and children coexist at dense nodes, with shared prefixes and
    // unequal depths. Include the root, NUL, and maximum byte explicitly.
    let width = if cfg!(miri) { 4 } else { 48 };
    let mut a = e();
    let mut b = M::single([255], ());
    for i in 0..width {
        a.set_val_at([0, i], ());
        a.set_val_at([0, i, 0], ());
        a.set_val_at([0, i, 255], ());
        b.set_val_at([0, i, 0], ());
        b.set_val_at([0, i, 1, 255], ());
    }
    properties(&a, &b, &e(), &e());
    properties(&b, &a, &e(), &e());
}

#[test]
fn balanced_branch_powers() {
    // The third branch iterate is nonempty, so its leaf bound is exercised.
    let balanced: KeySet = (0..8)
        .map(|i| vec![(i >> 2) & 1, (i >> 1) & 1, i & 1])
        .collect();
    power_properties(&map_from_set(&balanced));
}
