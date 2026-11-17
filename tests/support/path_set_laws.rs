//! The full named Lean catalogue, evaluated as Rust PathMap expressions.
//! Shared seeded generators come from the existing algebra differential suite.
use super::{KeySet, map_from_set, next_u64, prefix_heavy_set, set_from_map, wide_set};
use pathmap::{
    PathMap,
    experimental::path_sets::{basis, branches as br, divergence as d, hull},
    zipper::*,
};
use std::collections::BTreeSet;
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
fn live(p: &M, a: &M) -> M {
    let mut out = M::new();
    for (q, _) in p.iter() {
        if a.read_zipper_at_path(&q).val_count() != 0 {
            out.set_val_at(q, ());
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
fn live_rec(p: &M, a: &M) -> M {
    let root = if p.get([]).is_some() && !a.is_empty() {
        e()
    } else {
        M::new()
    };
    head(p).meet(&head(a)).iter().fold(root, |out, (q, _)| {
        out.join(&wrap(&q, &live_rec(&unwrap(p, &q), &unwrap(a, &q))))
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
#[derive(Default)]
struct Coverage(BTreeSet<&'static str>);
impl Coverage {
    fn check(&mut self, name: &'static str, ok: bool) {
        assert!(ok, "path-set law {name}");
        self.0.insert(name);
    }
    fn eq(&mut self, name: &'static str, a: &M, b: &M) {
        assert_eq!(set_from_map(a), set_from_map(b), "path-set law {name}");
        self.0.insert(name);
    }
    fn sub(&mut self, name: &'static str, a: &M, b: &M) {
        assert!(
            set_from_map(a).is_subset(&set_from_map(b)),
            "path-set law {name}: {:?} not subset of {:?}",
            set_from_map(a),
            set_from_map(b)
        );
        self.0.insert(name);
    }
}
fn laws(t: &mut Coverage, a: &M, b: &M, c: &M, f: &M) {
    let x = d(a, b);
    let ba = br(a);
    let ha = hull(a);
    let hb = hull(b);
    let ca = completion(a);
    let zero = M::new();
    let ep = e();
    let fork = M::single([0], ()).join(&M::single([1], ()));
    t.eq("diagonal", &d(a, a), &ba);
    t.eq("empty_left", &d(&zero, a), &zero);
    t.eq("empty_right", &d(a, &zero), &zero);
    t.eq("epsilon_left", &d(&ep, a), &zero);
    t.eq("epsilon_right", &d(a, &ep), &zero);
    t.eq("branch_completion", &br(&ca), &ba);
    t.eq("completion_idempotent", &completion(&ca), &ca);
    t.eq("branch_hull", &br(&ha), &ba);
    t.eq("branch_epsilon", &br(&a.join(&ep)), &ba);
    t.sub("branch_second_subset", &br(&ba), &ba);
    t.eq("interior_branches", &d(a, &ba), &interior(&ba));
    t.sub("basis_subset", &basis(a), a);
    t.sub("hull_subset", &ha, a);
    t.eq("basis_idempotent", &basis(&basis(a)), &basis(a));
    t.eq("hull_idempotent", &hull(&ha), &ha);
    t.eq("basis_of_hull", &basis(&ha), &ha);
    t.eq("hull_of_basis", &hull(&basis(a)), &basis(a));
    t.check("basis_antichain", prefix_free(&basis(a)));
    t.check("hull_antichain", prefix_free(&ha));
    t.check("basis_nonempty", basis(a).is_empty() == a.is_empty());
    t.check("hull_nonempty", ha.is_empty() == a.is_empty());
    t.check("basis_covers", covers(a, &ha) && covers(&basis(a), a));
    t.eq("basis_recursive", &basis_rec(a), &basis(a));
    t.eq("hull_recursive", &hull_rec(a), &ha);
    t.eq("branch_recursive", &divergence_rec(a, a), &ba);
    t.check("maximal_branch_count", count(&hull(&ba)) <= count(&ha) / 2);
    if !a.is_empty() {
        t.check(
            "no_nonempty_branch_fixed_point",
            set_from_map(&ba) != set_from_map(a),
        );
    }
    t.eq(
        "branch_depth_nilpotence",
        &branch_iter(a, height(a) + 1),
        &zero,
    );
    t.eq("symmetry", &x, &d(b, a));
    t.eq("terminal_invariance", &d(&a.join(&ep), &b.join(&ep)), &x);
    t.eq("hull_invariance", &d(&ha, &hb), &x);
    t.eq("completion_invariance", &d(&ca, &completion(b)), &x);
    t.eq("branch_union", &br(&a.join(b)), &ba.join(&br(b)).join(&x));
    t.sub(
        "branch_intersection_lower",
        &br(&a.meet(b)),
        &ba.meet(&br(b)),
    );
    t.sub("branch_sandwich_lower", &ba.meet(&br(b)), &x);
    t.sub("branch_sandwich_upper", &x, &br(&a.join(b)));
    t.eq("output_completion", &completion(&x), &x);
    t.eq("absorbed_branch_marks", &br(&a.join(&x)), &ba);
    t.eq("nested_exact", &d(a, &x), &ba.meet(&interior(&x)));
    t.eq("interior_exact", &d(&a.join(b), &x), &interior(&x));
    t.sub("interior_attribution", &interior(&x), &ba.join(&br(b)));
    t.sub("output_branches", &br(&x), &x.meet(&ba.meet(&br(b))));
    if !x.is_empty() {
        t.eq(
            "first_divergence",
            &basis(&x),
            &M::single(common_prefix(&ha.join(&hb)), ()),
        );
    }
    let all_prefix = |u: &M, v: &M| {
        u.iter()
            .all(|(p, _)| v.iter().all(|(q, _)| q.starts_with(&p)))
    };
    t.check(
        "zero_criterion",
        x.is_empty()
            == (a.is_empty()
                || b.is_empty()
                || count(&ha) == 1 && all_prefix(&ha, &hb)
                || count(&hb) == 1 && all_prefix(&hb, &ha)),
    );
    t.eq("root_heads", &d(&head(a), &head(b)), &x.meet(&ep));
    t.sub("output_heads", &head(&x), &head(a).meet(&head(b)));
    t.sub("tails_bound", &tails(&x), &d(&tails(a), &tails(b)));
    t.eq("recursive_divergence", &divergence_rec(a, b), &x);
    t.eq("live_recursive", &live_rec(a, b), &live(a, b));
    t.check(
        "output_cardinality",
        count(&x) <= count(&hull(&a.join(b))).saturating_sub(1),
    );
    t.check(
        "output_hull_cardinality",
        count(&hull(&x)) <= count(&ha).min(count(&hb)),
    );
    if !x.is_empty() {
        t.check("output_depth", height(&x) < height(a).min(height(b)));
    }
    t.check("output_covered", covers(&x, a) && covers(&x, b));
    t.eq("fork_completion", &br(&product(a, &fork)), &ca);
    let m = lcp_product(a, b);
    t.eq("fork_lcp", &d(&product(a, &fork), &product(b, &fork)), &m);
    t.eq("lcp_correction", &m, &x.join(&live(a, b)).join(&live(b, a)));
    t.eq("lcp_diagonal", &lcp_product(a, a), &ca);
    t.eq("lcp_symmetry", &m, &lcp_product(b, a));
    t.eq("lcp_output_completion", &completion(&m), &m);
    t.eq("range_realization", &br(&product(&ca, &fork)), &ca);
    t.eq(
        "basis_union",
        &basis(&a.join(b)),
        &basis(&basis(a).join(&basis(b))),
    );
    t.eq("hull_union", &hull(&a.join(b)), &hull(&ha.join(&hb)));
    t.eq(
        "restriction_basis_mask",
        &a.restrict(b),
        &a.restrict(&basis(b)),
    );
    t.eq("left_union", &d(&a.join(b), c), &d(a, c).join(&d(b, c)));
    t.eq("right_union", &d(a, &b.join(c)), &d(a, b).join(&d(a, c)));
    t.sub(
        "intersection_bound",
        &d(&a.meet(b), c),
        &d(a, c).meet(&d(b, c)),
    );
    t.sub(
        "difference_lower",
        &d(a, c).subtract(&d(b, c)),
        &d(&a.subtract(b), c),
    );
    t.sub("difference_upper", &d(&a.subtract(b), c), &d(a, c));
    t.sub(
        "symmetric_difference_bound",
        &sym(&d(a, c), &d(b, c)),
        &d(&sym(a, b), c),
    );
    if set_from_map(a).is_subset(&set_from_map(b)) {
        t.sub("monotonicity", &d(a, c), &d(b, c));
    }
    if covers(a, b) {
        t.sub("prefix_extension_monotonicity", &d(a, c), &d(b, c));
    }
    if covers(b, a) {
        t.eq("covered_mark_invariance", &d(&a.join(b), c), &d(a, c));
    }
    t.sub("nested_absorption", &d(&x, c), &d(a, c).meet(&d(b, c)));
    t.eq("witness_absorption", &d(&a.join(&x), c), &d(a, c));
    t.sub(
        "branch_probe_exchange",
        &x.meet(&br(c)),
        &d(a, c).meet(&d(b, c)),
    );
    t.eq(
        "lcp_associativity",
        &lcp_product(&m, c),
        &lcp_product(a, &lcp_product(b, c)),
    );
    t.eq(
        "lcp_bilinearity",
        &lcp_product(&a.join(b), c),
        &lcp_product(a, c).join(&lcp_product(b, c)),
    );
    t.eq(
        "one_mask",
        &d(&a.restrict(c), b),
        &x.restrict(c).join(&d(&live(c, a), b)),
    );
    t.eq(
        "same_mask",
        &d(&a.restrict(c), &b.restrict(c)),
        &x.restrict(c).join(&d(&live(c, a), &live(c, b))),
    );
    t.eq(
        "filter_partition",
        &x,
        &d(&a.restrict(c), b).join(&d(&raff(a, c), b)),
    );
    if prefix_free(a) && !b.is_empty() && !c.is_empty() {
        t.eq(
            "common_prefix_code",
            &d(&product(a, b), &product(a, c)),
            &ba.join(&product(a, &d(b, c))),
        );
    }
    t.sub(
        "four_point_absorption",
        &d(&x, &d(c, f)),
        &d(a, c).meet(&d(a, f)).meet(&d(b, c)).meet(&d(b, f)),
    );
    t.sub(
        "four_point_exchange",
        &x.meet(&d(c, f)),
        &d(a, c).meet(&d(b, f)).join(&d(a, f).meet(&d(b, c))),
    );
    t.eq(
        "incremental_update",
        &d(&a.join(c), &b.join(f)),
        &x.join(&d(c, b)).join(&d(a, f)).join(&d(c, f)),
    );
    t.eq(
        "two_masks",
        &d(&a.restrict(c), &b.restrict(f)),
        &x.restrict(c)
            .restrict(f)
            .join(&d(a, &live(f, b)).restrict(c))
            .join(&d(&live(c, a), b).restrict(f))
            .join(&d(&live(c, a), &live(f, b))),
    );
    t.sub(
        "raffination_bound",
        &d(&raff(a, c), &raff(b, f)),
        &raff(&x, &c.join(f)),
    );
    let prod_rhs = if c.is_empty() || f.is_empty() {
        M::new()
    } else {
        x.join(&product(&a.meet(b), &d(c, f)))
            .join(&overlaps(a, b, c, f))
    };
    t.eq(
        "general_product",
        &d(&product(a, c), &product(b, f)),
        &prod_rhs,
    );
    if prefix_free(&a.join(b)) && !c.is_empty() && !f.is_empty() {
        t.eq(
            "prefix_free_product",
            &d(&product(a, c), &product(b, f)),
            &x.join(&product(&a.meet(b), &d(c, f))),
        );
    }
    let mut paths = vec![vec![], vec![0], vec![0, 1, 0]];
    paths.extend(a.iter().take(2).map(|(p, _)| p));
    for p in paths {
        let single = M::single(&p, ());
        let chain = d(&single, b);
        t.eq("wrap", &d(&wrap(&p, a), &wrap(&p, b)), &wrap(&p, &x));
        t.eq(
            "unwrap",
            &d(&unwrap(a, &p), &unwrap(b, &p)),
            &unwrap(&x, &p),
        );
        t.eq(
            "single_prefix_restriction",
            &d(&a.restrict(&single), &b.restrict(&single)),
            &x.restrict(&single),
        );
        t.eq("singleton_chain", &br(&chain), &zero);
        t.check("singleton_bound", count(&chain) <= p.len().min(count(&hb)));
        t.sub("singleton_existing_branches", &interior(&chain), &br(b));
        t.check(
            "singleton_branch_update",
            count(&br(&b.join(&single)).subtract(&br(b))) <= 1,
        );
        t.check(
            "singleton_divergence_update",
            count(&d(&a.join(&single), b).subtract(&x)) <= p.len().min(count(&hb)),
        );
    }
}
fn power_laws(t: &mut Coverage, a: &M) {
    for n in 0..=3 {
        for m in 0..=3 {
            if prefix_free(a) {
                let rhs =
                    (0..m.min(n)).fold(M::new(), |out, i| out.join(&product(&power(a, i), &br(a))));
                t.eq("prefix_code_powers", &d(&power(a, m), &power(a, n)), &rhs);
            }
            if !branch_iter(a, n).is_empty() {
                t.check("branch_leaf_bound", 2usize.pow(n as u32) <= count(&hull(a)));
            }
        }
    }
}
fn small(seed: u64, salt: u64) -> KeySet {
    let mut state = seed ^ salt;
    let n = next_u64(&mut state) % 7;
    (0..n)
        .map(|_| {
            let len = next_u64(&mut state) % 6;
            (0..len)
                .map(|_| ((next_u64(&mut state) >> 32) % 3) as u8)
                .collect()
        })
        .collect()
}
#[test]
fn seeded_full_path_set_law_catalogue() {
    let mut t = Coverage::default();
    #[cfg(not(miri))]
    let seeds = 256;
    #[cfg(miri)]
    let seeds = 2;
    for seed in 0..seeds {
        // Report the complete reproducible seed on any assertion failure.
        let case = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let a = map_from_set(&small(seed, 11));
            let b = map_from_set(&small(seed, 23));
            let c = map_from_set(&small(seed, 47));
            let f = map_from_set(&small(seed, 97));
            laws(&mut t, &a, &b, &c, &f);
            // Deliberate correlated operands exercise the guards non-vacuously.
            laws(&mut t, &hull(&a), &hull(&a).join(&hull(&b)), &e(), &e());
            laws(&mut t, &a.join(&b), &b, &c, &f);
            power_laws(&mut t, &hull(&a));
        }));
        assert!(
            case.is_ok(),
            "full path-set law catalogue failed at seed {seed}"
        );
    }
    // Dense children and overlapping prefix terminals using existing fuzz generators.
    for seed in 0..2 {
        let a = map_from_set(&prefix_heavy_set(seed, 11));
        let b = map_from_set(&wide_set(seed, 23));
        laws(&mut t, &a, &b, &e(), &e());
    }
    // Balanced depth-three binary trie exercises a nonempty third branch iterate.
    let balanced: KeySet = (0..8)
        .map(|i| vec![(i >> 2) & 1, (i >> 1) & 1, i & 1])
        .collect();
    power_laws(&mut t, &map_from_set(&balanced));
    // Ensure every catalogue name is executed, with guarded laws counted only
    // when the guard is true. New Lean laws automatically require Rust coverage.
    let catalog = include_str!("../../lean/PathMapModel/PathSetLaws.lean");
    let expected: BTreeSet<_> = catalog
        .lines()
        .filter_map(|line| {
            let start = line.find("(\"")? + 2;
            let tail = &line[start..];
            Some(&tail[..tail.find('"')?])
        })
        .collect();
    assert_eq!(t.0, expected, "Rust / Lean law catalogue coverage drift");
}
