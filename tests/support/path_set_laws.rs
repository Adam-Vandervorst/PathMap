//! The full named Lean catalogue, evaluated as Rust PathMap expressions.
//! Shared seeded generators come from the existing algebra differential suite.
use super::{KeySet, map_from_set, next_u64, prefix_heavy_set, set_from_map, wide_set};
use pathmap::{
    PathMap,
    experimental::{
        convex::{convex_meet as cm, convex_subtract as cs},
        path_sets::{basis, branches as br, divergence as d, hull, retain},
    },
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
fn retention_laws(t: &mut Coverage, a: &M, b: &M, c: &M, f: &M) {
    let zero = M::new();
    let same = |a: M, b: M| assert_eq!(set_from_map(&a), set_from_map(&b));
    same(cm(a, b), retain(&a.meet(b), &hull(a).meet(&hull(b))));
    same(cs(a, b), retain(a, &hull(a).subtract(b)));
    same(cm(a, b).restrict(c), cm(&a.restrict(c), &b.restrict(c)));
    same(cs(a, b).restrict(c), cs(&a.restrict(c), b));
    same(cs(a, b).restrict(c), cs(&a.restrict(c), &b.restrict(c)));
    let tips = hull(a).meet(c);
    let other_tips = hull(b).meet(f);
    same(
        cm(&retain(a, &tips), b),
        retain(&a.meet(b), &tips.meet(&hull(b))),
    );
    same(
        cm(&retain(a, &tips), &retain(b, &other_tips)),
        retain(&a.meet(b), &tips.meet(&other_tips)),
    );
    same(cs(&retain(a, &tips), b), retain(a, &tips.subtract(b)));
    same(cm(a, &retain(a, &tips)), retain(a, &tips));
    t.eq("retain_empty_left", &retain(&zero, a), &zero);
    t.eq("retain_empty_right", &retain(a, &zero), &zero);
    t.eq("retain_self", &retain(a, a), a);
    t.eq(
        "retain_union_left",
        &retain(&a.join(b), c),
        &retain(a, c).join(&retain(b, c)),
    );
    t.eq(
        "retain_inter_left",
        &retain(&a.meet(b), c),
        &retain(a, c).meet(&retain(b, c)),
    );
    t.eq(
        "retain_diff_left",
        &retain(&a.subtract(b), c),
        &retain(a, c).subtract(&retain(b, c)),
    );
    t.eq(
        "retain_symDiff_left",
        &retain(&sym(a, b), c),
        &sym(&retain(a, c), &retain(b, c)),
    );
    t.eq(
        "retain_union_right",
        &retain(a, &b.join(c)),
        &retain(a, b).join(&retain(a, c)),
    );
    t.eq(
        "retain_filter_inter",
        &retain(&retain(a, b), c),
        &retain(a, b).meet(&retain(a, c)),
    );
    t.eq(
        "retain_filter_comm",
        &retain(&retain(a, b), c),
        &retain(&retain(a, c), b),
    );
    t.eq(
        "retain_filter_idem",
        &retain(&retain(a, b), b),
        &retain(a, b),
    );
    t.eq("retain_hull_mask", &retain(a, &hull(b)), &retain(a, b));
    t.eq(
        "retain_completion_mask",
        &retain(a, &completion(b)),
        &retain(a, b),
    );
    t.eq(
        "retain_restrict_witnesses",
        &retain(a, &b.restrict(a)),
        &retain(a, b),
    );
    t.eq(
        "restrict_retain_mask",
        &a.restrict(&retain(b, a)),
        &a.restrict(b),
    );
    t.eq("retain_restrict_disjoint", &retain(a, &raff(b, a)), &zero);
    t.eq(
        "retain_restrict_source",
        &retain(&a.restrict(b), c),
        &retain(a, c).restrict(b),
    );
    t.eq(
        "retain_raffinate_source",
        &retain(&raff(a, b), c),
        &raff(&retain(a, c), b),
    );
    t.eq(
        "retain_lcp_masks",
        &retain(&retain(a, b), c),
        &retain(a, &lcp_product(b, c)),
    );
    t.eq(
        "retain_divergence_masks",
        &retain(&retain(a, b), c),
        &retain(a, &d(b, c).join(&retain(b, c)).join(&retain(c, b))),
    );
    t.eq(
        "restrict_overlap_masks",
        &a.restrict(b).restrict(c),
        &a.restrict(&b.restrict(c).join(&c.restrict(b))),
    );
    t.eq(
        "retain_restrict_mask",
        &retain(a, &b.restrict(c)),
        &retain(a, b).restrict(c).join(&retain(a, &retain(c, b))),
    );
    t.eq(
        "restrict_retain_lcp",
        &a.restrict(&retain(b, c)),
        &a.restrict(&lcp_product(a, c).restrict(b)),
    );
    t.eq("basis_retain", &basis(&retain(a, b)), &retain(&basis(a), b));
    t.eq("hull_restrict", &hull(&a.restrict(b)), &hull(a).restrict(b));
    t.sub("retain_subset", &retain(a, b), a);
    t.sub(
        "retain_inter_right_bound",
        &retain(a, &b.meet(c)),
        &retain(a, b).meet(&retain(a, c)),
    );
    t.sub(
        "retain_diff_right_bound",
        &retain(a, b).subtract(&retain(a, c)),
        &retain(a, &b.subtract(c)),
    );
    t.sub(
        "retain_nested_bound",
        &retain(a, &retain(b, c)),
        &retain(&retain(a, b), c),
    );
    t.sub(
        "retain_hull_source_bound",
        &retain(&hull(a), b),
        &hull(&retain(a, b)),
    );
    t.sub(
        "divergence_retain_bound",
        &d(&retain(a, c), &retain(b, f)),
        &d(a, b).meet(&d(c, f)),
    );
    t.sub(
        "branches_retain_bound",
        &br(&retain(a, b)),
        &br(a).meet(&br(b)),
    );
    t.check(
        "retain_empty_duality",
        retain(a, b).is_empty() == b.restrict(a).is_empty(),
    );
    t.check(
        "retain_identity",
        (set_from_map(&retain(a, b)) == set_from_map(a)) == covers(a, b),
    );
    t.check("retain_count_bound", count(&retain(a, b)) <= count(a));
}
fn closed_laws(t: &mut Coverage, a: &M, b: &M, c: &M, f: &M) {
    let ca = completion(a);
    let cb = completion(b);
    let cc = completion(c);
    let ab = lcp_product(a, b);
    let ga = a.subtract(&br(a));
    let same = |x: &M, y: &M| set_from_map(x) == set_from_map(y);
    let subset = |x: &M, y: &M| set_from_map(x).is_subset(&set_from_map(y));
    t.eq(
        "completion_union",
        &completion(&a.join(b)),
        &ca.join(&cb).join(&d(a, b)),
    );
    t.eq(
        "completion_union_lcp",
        &completion(&a.join(b)),
        &ca.join(&cb).join(&ab),
    );
    t.eq(
        "completion_union_absorb",
        &completion(&ca.join(&cb)),
        &completion(&a.join(b)),
    );
    t.eq("hull_completion", &hull(&ca), &hull(a));
    t.eq("completion_hull", &a.join(&completion(&hull(a))), &ca);
    t.eq("hull_remove_branches", &hull(&ga), &hull(a));
    t.eq("branches_remove_branches", &br(&ga), &br(a));
    t.eq("completion_remove_branches", &completion(&ga), &ca);
    t.eq("completion_diff_branches", &ca.subtract(&br(a)), &ga);
    t.eq("lcp_completion_left", &lcp_product(&ca, b), &ab);
    t.eq("lcp_completion_right", &lcp_product(a, &cb), &ab);
    t.eq("lcp_completion", &lcp_product(&ca, &cb), &ab);
    t.eq("lcp_repeat", &lcp_product(a, &ab), &ab);
    t.eq(
        "lcp_medial",
        &lcp_product(&ab, &lcp_product(c, f)),
        &lcp_product(&lcp_product(a, c), &lcp_product(b, f)),
    );
    t.eq(
        "lcp_four_factors",
        &lcp_product(&a.join(b), &c.join(f)),
        &lcp_product(a, c)
            .join(&lcp_product(a, f))
            .join(&lcp_product(b, c))
            .join(&lcp_product(b, f)),
    );
    t.eq(
        "lcp_closed_join",
        &lcp_product(a, &completion(&b.join(c))),
        &ab.join(&lcp_product(a, c)),
    );
    t.eq(
        "lcp_new_marks",
        &ab.subtract(&a.join(b)),
        &d(a, b).subtract(&a.join(b)),
    );
    t.eq("retain_lcp_operand", &retain(a, &ab), &retain(a, b));
    t.eq(
        "hull_lcp_hulls",
        &hull(&lcp_product(&hull(a), &hull(b))),
        &hull(&ab),
    );
    t.eq(
        "completion_restrict",
        &completion(&a.restrict(b)),
        &ca.restrict(b).join(&br(&retain(b, a))),
    );
    t.eq(
        "completion_restrict_closed",
        &completion(&a.restrict(&cb)),
        &ca.restrict(&cb),
    );
    t.eq(
        "lcp_restrict",
        &lcp_product(&a.restrict(c), &b.restrict(c)),
        &ab.restrict(c).join(&d(&retain(c, a), &retain(c, b))),
    );
    t.eq(
        "lcp_restrict_closed",
        &lcp_product(&a.restrict(&cc), &b.restrict(&cc)),
        &ab.restrict(&cc),
    );
    t.eq("closed_inter", &completion(&ca.meet(&cb)), &ca.meet(&cb));
    t.eq(
        "closed_retain",
        &completion(&retain(&ca, b)),
        &retain(&ca, b),
    );
    t.eq(
        "closed_restrict",
        &completion(&ca.restrict(&cb)),
        &ca.restrict(&cb),
    );
    t.eq(
        "closed_raffinate",
        &completion(&raff(&ca, b)),
        &raff(&ca, b),
    );
    t.eq(
        "closed_lcp_union",
        &completion(&ab.join(&lcp_product(a, c))),
        &ab.join(&lcp_product(a, c)),
    );
    t.eq(
        "closed_join_assoc",
        &completion(&completion(&a.join(b)).join(c)),
        &completion(&a.join(&completion(&b.join(c)))),
    );
    t.eq(
        "closed_join_comm",
        &completion(&a.join(b)),
        &completion(&b.join(a)),
    );
    t.eq("closed_join_idem", &completion(&ca.join(&ca)), &ca);
    t.eq("closed_join_empty", &completion(&ca.join(&M::new())), &ca);
    t.eq(
        "closed_join_absorption",
        &completion(&ca.join(&ca.meet(b))),
        &ca,
    );
    t.eq(
        "closed_meet_absorption",
        &a.meet(&completion(&a.join(b))),
        a,
    );
    t.eq("lcpLE_product_left", &lcp_product(&ab, a), &ab);
    t.eq("lcpLE_product_right", &lcp_product(&ab, b), &ab);
    t.eq(
        "completion_wrap",
        &completion(&wrap(&[0, 1], a)),
        &wrap(&[0, 1], &ca),
    );
    t.eq(
        "completion_unwrap",
        &completion(&unwrap(a, &[0])),
        &unwrap(&ca, &[0]),
    );
    t.sub("completion_extensive", a, &ca);
    t.sub(
        "completion_inter_bound",
        &completion(&a.meet(b)),
        &ca.meet(&cb),
    );
    t.sub("lcp_inter_lower", &a.meet(b), &ab);
    t.sub(
        "lcp_inter_bound",
        &lcp_product(&a.meet(b), c),
        &lcp_product(a, c).meet(&lcp_product(b, c)),
    );
    t.sub(
        "lcp_diff_bound",
        &lcp_product(a, c).subtract(&lcp_product(b, c)),
        &lcp_product(&a.subtract(b), c),
    );
    t.sub("lcp_union_bound", &ab, &completion(&a.join(b)));
    t.sub(
        "lcp_retain_bound",
        &lcp_product(&retain(a, c), &retain(b, f)),
        &retain(&ab, &lcp_product(c, f)),
    );
    t.sub(
        "completion_retain_bound",
        &completion(&retain(a, b)),
        &retain(&ca, b),
    );
    t.sub(
        "completion_raffinate_bound",
        &completion(&raff(a, b)),
        &raff(&ca, b),
    );
    t.check("completion_least", subset(&ca, &cb) == subset(a, &cb));
    t.check(
        "completion_generators",
        same(&cb, &ca) == (subset(&ga, b) && subset(b, &ca)),
    );
    t.check(
        "completion_equiv_generators",
        same(&ca, &cb) == same(&ga, &b.subtract(&br(b))),
    );
    t.check(
        "closed_union_iff",
        same(&completion(&ca.join(&cb)), &ca.join(&cb)) == subset(&d(&ca, &cb), &ca.join(&cb)),
    );
    t.check(
        "closed_join_least",
        subset(&completion(&a.join(b)), &cc) == (subset(a, &cc) && subset(b, &cc)),
    );
    t.check(
        "lcpLE_iff",
        same(&ab, a) == (covers(a, b) && subset(&d(a, b), a) && subset(&retain(b, a), a)),
    );
    t.check(
        "lcpLE_product_iff",
        same(&lcp_product(a, &lcp_product(b, c)), a)
            == (same(&ab, a) && same(&lcp_product(a, c), a)),
    );
    t.check(
        "completion_cardinality",
        count(&ca) <= count(a) + count(&hull(a)).saturating_sub(1),
    );
    t.check(
        "completion_cardinality_linear",
        count(a) <= count(&ca) && count(&ca) <= (2 * count(a)).saturating_sub(1),
    );
    if !a.is_empty() {
        t.eq(
            "basis_completion",
            &basis(&ca),
            &M::single(common_prefix(a), ()),
        );
    }
    assert!(same(&completion(&cm(&ca, &cb)), &cm(&ca, &cb)));
    assert!(same(&completion(&cs(&ca, b)), &cs(&ca, b)));
    assert!(subset(&completion(&cm(a, b)), &cm(&ca, &cb)));
    assert!(subset(&completion(&cs(a, b)), &cs(&ca, b)));
    assert!(same(&hull(&completion(&cm(a, b))), &hull(&cm(&ca, &cb))));
    assert!(same(&hull(&completion(&cs(a, b))), &hull(&cs(&ca, b))));
}
fn laws(t: &mut Coverage, a: &M, b: &M, c: &M, f: &M) {
    closed_laws(t, a, b, c, f);
    retention_laws(t, a, b, c, f);
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
    t.eq("retain_recursive", &retain_rec(a, b), &retain(a, b));
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
    t.eq(
        "lcp_correction",
        &m,
        &x.join(&retain(a, b)).join(&retain(b, a)),
    );
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
        &x.restrict(c).join(&d(&retain(c, a), b)),
    );
    t.eq(
        "same_mask",
        &d(&a.restrict(c), &b.restrict(c)),
        &x.restrict(c).join(&d(&retain(c, a), &retain(c, b))),
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
            .join(&d(a, &retain(f, b)).restrict(c))
            .join(&d(&retain(c, a), b).restrict(f))
            .join(&d(&retain(c, a), &retain(f, b))),
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
/// All subsets of a depth-two binary tree, including every closed subspace.
/// Check anti-exchange and least generators independently of the named catalogue.
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
        assert_eq!(closed_keys, set_from_map(&lcp_product(&a, &a)));
        let generators = a.subtract(&br(&a));
        assert_eq!(closed_keys, set_from_map(&completion(&generators)));
        for x in &paths {
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
            for y in &paths {
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
    let catalog = include_str!("../../lean/PrunedModel/Convex/PathSetLaws.lean");
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
