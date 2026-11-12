//! Algebraic operations on tries that share a subtrie.  A node shared by both operands is its own
//! join, meet and restriction, so those operations must leave it shared, and must not copy it.

use std::sync::{Mutex, MutexGuard};

use pathmap::PathMap;
use pathmap::ring::{AlgebraicStatus, Lattice};
use pathmap::zipper::*;

/// The `counters` feature's copy-on-write counters are process-wide, so the tests in this file run
/// one at a time
static SERIAL: Mutex<()> = Mutex::new(());

fn serial() -> MutexGuard<'static, ()> {
    SERIAL.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// The path the shared subtrie sits at, in the tests that give it byte-node siblings
const P: &[u8] = b"p";

/// A subtrie that branches at several depths, so copying it takes several node clones
fn subtrie() -> PathMap<u64> {
    let mut m = PathMap::new();
    for (i, key) in [&b"alpha"[..], b"alps", b"beta", b"bet", b"gamma", b"gam", b"delta", b"del"].iter().enumerate() {
        m.insert(key, i as u64);
    }
    m
}

/// A map holding `m` at `path`, with a value at each of `siblings`.  Three or more first bytes make
/// the root a byte node, so `m` sits in one of its slots
fn holding(m: &PathMap<u64>, path: &[u8], siblings: &[&[u8]]) -> PathMap<u64> {
    let mut map = PathMap::new();
    for (i, key) in siblings.iter().enumerate() {
        map.insert(key, i as u64);
    }
    map.write_zipper_at_path(path).graft_map(m.clone());
    map
}

/// `Some` only while the node at `path` is shared and has no value at `path`
fn node_id(map: &PathMap<u64>, path: &[u8]) -> Option<u64> {
    map.read_zipper_at_path(path).shared_node_id()
}

/// The id of `m`'s root, which it reports only while shared, so this takes it through a second handle
fn root_id(m: &PathMap<u64>) -> Option<u64> {
    let id = node_id(&m.clone(), b"");
    assert!(id.is_some());
    id
}

fn entries(map: &PathMap<u64>) -> Vec<(Vec<u8>, u64)> {
    map.iter().map(|(path, val)| (path, *val)).collect()
}

/// Runs `op` and checks that it cloned no node, when the `counters` feature is on
fn without_clones<R>(case: &str, op: impl FnOnce() -> R) -> R {
    #[cfg(feature = "counters")]
    let before = pathmap::counters::cow_counters();
    let result = op();
    #[cfg(feature = "counters")]
    assert_eq!(pathmap::counters::cow_counters().cow_clones, before.cow_clones, "{case}: cloned a node");
    #[cfg(not(feature = "counters"))]
    let _ = case;
    result
}

/// Joining a map into one that already holds the same subtrie is the identity and keeps the subtrie
/// shared: the byte-node child join, the list-node merge and the focus join all meet the shared node
/// as `TrieNodeODRc::join_into(x, x)`
#[test]
fn join_of_a_shared_subtrie_is_identity() {
    let _serial = serial();
    let m = subtrie();
    let m_id = root_id(&m);

    // Byte node into byte node, through the `CoFree` join
    let mut a = holding(&m, P, &[b"a", b"b", b"c"]);
    let b = holding(&m, P, &[b"a", b"b"]);
    assert_eq!(node_id(&b, P), m_id);
    let status = without_clones("byte node into byte node", || a.join_into(b));
    assert_eq!(status, AlgebraicStatus::Identity);
    assert_eq!(node_id(&a, P), m_id);

    // List node into byte node, through `join_child_into`
    let mut a = holding(&m, P, &[b"a", b"b", b"c"]);
    let b = holding(&m, P, &[]);
    assert_eq!(node_id(&b, P), m_id);
    let status = without_clones("list node into byte node", || a.join_into(b));
    assert_eq!(status, AlgebraicStatus::Identity);
    assert_eq!(node_id(&a, P), m_id);

    // The write zipper's focus join
    let mut a = holding(&m, P, &[b"a", b"b", b"c"]);
    let mut b = holding(&m, P, &[]);
    {
        let mut a_wz = a.write_zipper_at_path(P);
        let mut b_wz = b.write_zipper_at_path(P);
        let status = without_clones("focus join", || a_wz.join_into_take(&mut b_wz, false));
        assert_eq!(status, AlgebraicStatus::Identity);
    }
    assert_eq!(node_id(&a, P), m_id);
    assert_eq!(entries(&a), entries(&holding(&m, P, &[b"a", b"b", b"c"])));
}

/// The value at a node boundary lives in the parent's slot, so a shortcut on the node below must not
/// decide it.  `b` is `a` plus a value at `p`; the subtrie under `p` is the same node in both
#[test]
fn shared_subtrie_under_a_boundary_value() {
    let _serial = serial();
    let m = subtrie();
    let m_id = root_id(&m);
    // `p` in a byte node's slot, then `p` in a list node
    for (p, siblings) in [(P, &[&b"a"[..], b"b", b"c"][..]), (&b"pre"[..], &[][..])] {
        let a = holding(&m, p, siblings);
        let mut b = holding(&m, p, siblings);
        b.insert(p, 7);
        // `b` has a value at `p`, so only `a` can witness the sharing there
        assert_eq!(node_id(&a, p), m_id);
        assert_eq!(node_id(&b, p), None);

        let mut joined = b.clone();
        assert_eq!(joined.join_into(a.clone()), AlgebraicStatus::Identity, "{p:?}: b ∨ a");
        assert_eq!(entries(&joined), entries(&b));

        let mut joined = a.clone();
        assert_eq!(joined.join_into(b.clone()), AlgebraicStatus::Element, "{p:?}: a ∨ b");
        assert_eq!(joined.val_at(p), Some(&7));
        assert_eq!(entries(&joined), entries(&b));

        let restricted = a.restrict(&b);
        assert_eq!(entries(&restricted), entries(&a), "{p:?}: a <| b");
        assert_eq!(node_id(&restricted, p), m_id);

        // The value `b` has at `p` is not validated by `a`, so it goes; the subtrie stays shared
        let restricted = b.restrict(&a);
        assert_eq!(entries(&restricted), entries(&a), "{p:?}: b <| a");
        assert_eq!(node_id(&restricted, p), m_id);
    }
}

/// x <| x = x, and the result is x's own root
#[test]
fn restrict_by_itself_is_identity() {
    let _serial = serial();
    let m = subtrie();
    let mut x = holding(&m, P, &[b"a", b"b", b"c"]);
    x.insert(P, 3);
    let restricted = without_clones("x <| x", || x.restrict(&x));
    assert_eq!(entries(&restricted), entries(&x));
    let x_id = node_id(&x, b"");
    assert!(x_id.is_some(), "the result must share x's root");
    assert_eq!(node_id(&restricted, b""), x_id);
}

/// The write zipper's algebraic operations, with the focus of each operand at the same node
#[test]
fn zipper_ops_on_a_shared_focus() {
    let _serial = serial();
    let m = subtrie();
    let m_id = root_id(&m);
    let fresh = || (holding(&m, P, &[b"a", b"b", b"c"]), holding(&m, P, &[]));

    let (mut a, b) = fresh();
    let status = without_clones("join_into", || a.write_zipper_at_path(P).join_into(&b.read_zipper_at_path(P)));
    assert_eq!(status, AlgebraicStatus::Identity);
    assert_eq!(node_id(&a, P), m_id);

    let (mut a, _) = fresh();
    let status = without_clones("join_map_into", || a.write_zipper_at_path(P).join_map_into(m.clone()));
    assert_eq!(status, AlgebraicStatus::Identity);
    assert_eq!(node_id(&a, P), m_id);

    let (mut a, b) = fresh();
    let status = without_clones("meet_into", || a.write_zipper_at_path(P).meet_into(&b.read_zipper_at_path(P), false));
    assert_eq!(status, AlgebraicStatus::Identity);
    assert_eq!(node_id(&a, P), m_id);

    let (mut a, b) = fresh();
    let status = without_clones("meet_2", || a.write_zipper_at_path(b"q").meet_2(&b.read_zipper_at_path(P), &m.read_zipper()));
    assert_eq!(status, AlgebraicStatus::Element);
    assert_eq!(node_id(&a, b"q"), m_id);

    let (mut a, b) = fresh();
    let status = without_clones("restrict", || a.write_zipper_at_path(P).restrict(&b.read_zipper_at_path(P)));
    assert_eq!(status, AlgebraicStatus::Identity);
    assert_eq!(node_id(&a, P), m_id);

    let (mut a, b) = fresh();
    assert!(without_clones("restricting", || a.write_zipper_at_path(P).restricting(&b.read_zipper_at_path(P))));
    assert_eq!(node_id(&a, P), m_id);

    let (mut a, b) = fresh();
    let status = without_clones("subtract_into", || a.write_zipper_at_path(P).subtract_into(&b.read_zipper_at_path(P), false));
    assert_eq!(status, AlgebraicStatus::None);
    assert_eq!(entries(&a), entries(&holding(&PathMap::new(), P, &[b"a", b"b", b"c"])));
}
