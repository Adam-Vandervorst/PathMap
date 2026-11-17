use super::*;
use crate::alloc::{GlobalAlloc, global_alloc};
use crate::dense_byte_node::{CellByteNode, DenseByteNode};
use crate::trie_node::TrieNode;
use std::collections::{BTreeMap, BTreeSet};

type Node = TrieNodeODRc<u64, GlobalAlloc>;
type Map = PathMap<u64, GlobalAlloc>;
type Payload = ValOrChild<u64, GlobalAlloc>;
const TAGS: [usize; 5] = [
    DENSE_BYTE_NODE_TAG,
    CELL_BYTE_NODE_TAG,
    LINE_LIST_NODE_TAG,
    TINY_REF_NODE_TAG,
    EMPTY_NODE_TAG,
];

fn list(entries: Vec<(Vec<u8>, Payload)>) -> LineListNode<u64, GlobalAlloc> {
    let mut node = LineListNode::new_in(global_alloc());
    for (i, (key, payload)) in entries.into_iter().enumerate() {
        // At most two entries, sorted by key with children before values.
        unsafe {
            match i {
                0 => node.set_payload_owned::<0>(&key, payload),
                1 => node.set_payload_owned::<1>(&key, payload),
                _ => unreachable!(),
            }
        }
    }
    assert!(crate::line_list_node::validate_node(&node));
    node
}
fn child(side: u64) -> Node {
    let mut m = Map::new();
    m.set_val_at(b"c", 30 + side);
    m.set_val_at(if side == 0 { b"d" } else { b"e" }, 40 + side);
    m.root().unwrap().clone()
}
fn entries(pattern: usize, side: u64) -> Vec<(Vec<u8>, Payload)> {
    let v = |p: &[u8], n| (p.to_vec(), Payload::Val(n + 100 * side));
    let c = |p: &[u8], bare| {
        (
            p.to_vec(),
            Payload::Child(if bare { Node::new_empty() } else { child(side) }),
        )
    };
    match pattern {
        0 => vec![v(b"ab", 1), v(b"b", 2)],
        1 => vec![v(b"a", 1), c(b"ab", false)],
        2 => vec![c(b"a", false), v(b"a", 1)],
        3 => vec![c(b"ab", true), v(b"b", 2)],
        4 => vec![v(b"a", 1), v(b"ab", 2)],
        5 => vec![c(b"a", true)],
        6 => vec![c(b"a", false), c(b"b", false)],
        7 => vec![v(b"ab", 1)],
        _ => unreachable!(),
    }
}
fn byte<C: CoFree<V = u64, A = GlobalAlloc>>(
    entries: Vec<(Vec<u8>, Payload)>,
) -> ByteNode<C, GlobalAlloc> {
    let mut n = ByteNode::new_in(global_alloc());
    for (key, payload) in entries {
        if key.len() == 1 {
            n.set_payload_owned(key[0], payload);
        } else {
            n.set_child(
                key[0],
                Node::new_in(list(vec![(key[1..].to_vec(), payload)]), global_alloc()),
            );
        }
    }
    n
}
// A Tiny is a real borrowed slice inside a list key, not a map that merely
// might choose a tiny representation. Empty is the actual sentinel.
fn fixture(tag: usize, pattern: usize, side: u64) -> (Node, Vec<u8>) {
    let mut es = entries(pattern, side);
    let (node, path) = match tag {
        DENSE_BYTE_NODE_TAG => (
            Node::new_in(
                byte::<crate::dense_byte_node::OrdinaryCoFree<_, _>>(es),
                global_alloc(),
            ),
            vec![],
        ),
        CELL_BYTE_NODE_TAG => (
            Node::new_in(
                byte::<crate::dense_byte_node::CellCoFree<_, _>>(es),
                global_alloc(),
            ),
            vec![],
        ),
        LINE_LIST_NODE_TAG => (Node::new_in(list(es), global_alloc()), vec![]),
        TINY_REF_NODE_TAG => {
            es.truncate(1);
            es[0].0.insert(0, b'z');
            (Node::new_in(list(es), global_alloc()), vec![b'z'])
        }
        EMPTY_NODE_TAG => (Node::new_empty(), vec![]),
        _ => unreachable!(),
    };
    (node, path)
}
fn reference<'a>(n: &'a Node, p: &[u8]) -> TrieRefBorrowed<'a, u64, GlobalAlloc> {
    TrieRefBorrowed::new_with_key_and_path_in(n, || None, &[], p, global_alloc())
}
fn own(n: TaggedNodeRef<'_, u64, GlobalAlloc>) -> Node {
    if n.tag() == TINY_REF_NODE_TAG {
        Node::new_in(
            unsafe { n.as_tiny_unchecked() }.into_full().unwrap(),
            global_alloc(),
        )
    } else {
        n.clone_self()
    }
}
fn values(n: Option<Node>) -> BTreeMap<Vec<u8>, u64> {
    Map::new_with_root_in(n, None, global_alloc())
        .iter()
        .map(|(p, v)| (p, *v))
        .collect()
}
// Repeated removal, deliberately independent of the native recurrence.
fn expected<const SUBTRACT: bool>(
    a: &BTreeMap<Vec<u8>, u64>,
    b: &BTreeMap<Vec<u8>, u64>,
) -> BTreeMap<Vec<u8>, u64> {
    let tips = |m: &BTreeMap<Vec<u8>, u64>| -> BTreeSet<Vec<u8>> {
        m.keys()
            .filter(|p| !m.keys().any(|q| q != *p && q.starts_with(p)))
            .cloned()
            .collect()
    };
    let at = tips(a);
    let bt = tips(b);
    let protected: BTreeSet<_> = at
        .into_iter()
        .filter(|p| {
            if SUBTRACT {
                !b.contains_key(p)
            } else {
                bt.contains(p)
            }
        })
        .collect();
    let mut out: BTreeMap<_, _> = a
        .iter()
        .filter(|(p, _)| SUBTRACT || b.contains_key(*p))
        .map(|(p, v)| (p.clone(), *v))
        .collect();
    loop {
        let remove: Vec<_> = tips(&out).difference(&protected).cloned().collect();
        if remove.is_empty() {
            return out;
        }
        for p in remove {
            out.remove(&p);
        }
    }
}
fn matrix<const SUBTRACT: bool>() {
    let mut covered = BTreeSet::new();
    for lt in TAGS {
        for rt in TAGS {
            for lp in 0..8 {
                for rp in 0..8 {
                    let (l, lk) = fixture(lt, lp, 0);
                    let (r, rk) = fixture(rt, rp, 1);
                    let lr = reference(&l, &lk);
                    let rr = reference(&r, &rk);
                    let lf = lr.clone().into_focus();
                    let rf = rr.clone().into_focus();
                    let ln = lf.try_as_tagged().unwrap_or_else(|| l.as_tagged());
                    let rn = rf.try_as_tagged().unwrap_or_else(|| r.as_tagged());
                    assert_eq!(ln.tag(), lt);
                    assert_eq!(rn.tag(), rt);
                    let a = values(
                        lf.borrow()
                            .cloned()
                            .or_else(|| (!lf.is_none()).then(|| own(ln))),
                    );
                    let b = values(
                        rf.borrow()
                            .cloned()
                            .or_else(|| (!rf.is_none()).then(|| own(rn))),
                    );
                    // Call the kernel itself: sharing, singleton, disjoint-mask, and
                    // spine shortcuts cannot conceal a missing dispatch arm.
                    let (out, summary) = native_kernel::<SUBTRACT, _, _, _, _>(ln, &rr, None);
                    let out = out.map_into_option(|id| {
                        assert_eq!(id, 0);
                        Some(own(ln))
                    });
                    let out = values(out);
                    assert_eq!(
                        out,
                        expected::<SUBTRACT>(&a, &b),
                        "SUBTRACT={SUBTRACT} tags={lt}/{rt} patterns={lp}/{rp}"
                    );
                    assert_eq!(summary.live, !a.is_empty());
                    assert_eq!(summary.kept, !out.is_empty());
                    covered.insert((lt, rt));
                }
            }
        }
    }
    assert_eq!(covered.len(), 25);
}
#[test]
fn forced_native_meet_dispatch_matrix() {
    matrix::<false>();
}
#[test]
fn forced_native_subtract_dispatch_matrix() {
    matrix::<true>();
}

#[cfg(not(feature = "nightly"))]
#[test]
fn distinct_payload_and_allocator_types() {
    #[derive(Clone)]
    struct RightAlloc;
    impl Allocator for RightAlloc {}
    let mut left = Map::new();
    let mut right = PathMap::<String, RightAlloc>::new_in(RightAlloc);
    for b in 0..=255u8 {
        left.set_val_at([b], b as u64 + 1);
        left.set_val_at([b, 0], b as u64 + 1000);
        right.set_val_at([b], "interior".into());
        if b % 2 == 0 {
            right.set_val_at([b, 0], "tip".into());
        }
    }
    let meet = convex_meet(&left, &right);
    let sub = convex_subtract(&left, &right);
    assert_eq!(meet.val_count(), 256);
    assert_eq!(sub.val_count(), 256);
    for b in 0..=255u8 {
        for (path, value) in [(vec![b], b as u64 + 1), (vec![b, 0], b as u64 + 1000)] {
            assert_eq!(meet.get_val_at(&path), (b % 2 == 0).then_some(&value));
            assert_eq!(sub.get_val_at(&path), (b % 2 == 1).then_some(&value));
        }
    }
}

#[test]
fn native_spines_use_bounded_call_depth() {
    // A 128-KiB worker stack makes accidentally recursive unary handling
    // fail quickly. Construct physical spines without quadratic key inserts.
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut a = Node::new_in(list(vec![(vec![0], Payload::Val(7))]), global_alloc());
            let mut b = Node::new_in(list(vec![(vec![1], Payload::Val(9))]), global_alloc());
            for i in 0..12000 {
                if i % 2 == 0 {
                    a = Node::new_in(
                        list(vec![
                            (vec![0], Payload::Child(a)),
                            (vec![0], Payload::Val(11)),
                        ]),
                        global_alloc(),
                    );
                    b = Node::new_in(
                        list(vec![
                            (vec![0], Payload::Child(b)),
                            (vec![0], Payload::Val(12)),
                        ]),
                        global_alloc(),
                    );
                } else {
                    let mut x = DenseByteNode::new_in(global_alloc());
                    x.set_child(0, a);
                    x.set_val(0, 13);
                    let mut y = CellByteNode::new_in(global_alloc());
                    y.set_child(0, b);
                    y.set_val(0, 14);
                    a = Node::new_in(x, global_alloc());
                    b = Node::new_in(y, global_alloc());
                }
            }
            assert!(
                node_op::<false, _, _, _, _>(&a, reference(&b, &[]))
                    .0
                    .is_none()
            );
            assert!(
                node_op::<true, _, _, _, _>(&a, reference(&b, &[]))
                    .0
                    .unwrap()
                    .ptr_eq(&a)
            );
            // Teardown explicitly: the native node Drop implementations have
            // their own independent recursion limits across mixed node types.
            while let Some((_, child, _)) = spine_link(a.as_tagged()) {
                let next = child.clone();
                drop(a);
                a = next;
            }
            while let Some((_, child, _)) = spine_link(b.as_tagged()) {
                let next = child.clone();
                drop(b);
                b = next;
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
