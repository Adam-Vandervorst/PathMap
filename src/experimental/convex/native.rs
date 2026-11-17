use super::{Summary, keep_value};
use crate::{
    PathMap,
    alloc::Allocator,
    dense_byte_node::{ALL_BYTES, ByteNode, CoFree},
    line_list_node::LineListNode,
    ring::{AlgebraicResult, SELF_IDENT},
    trie_node::{
        CELL_BYTE_NODE_TAG, DENSE_BYTE_NODE_TAG, EMPTY_NODE_TAG, LINE_LIST_NODE_TAG,
        NODE_ITER_FINISHED, PayloadRef, TINY_REF_NODE_TAG, TaggedNodeRef, TrieNodeDowncast,
        TrieNodeODRc, ValOrChild,
    },
    trie_ref::TrieRefBorrowed,
    utils::{BitMask, ByteMask},
    zipper::{zipper_priv::ZipperReadOnlyPriv, *},
};
use smallvec::SmallVec;

// Stop at the first valued witness, including values above dangling children.
fn node_live<V: Clone + Send + Sync, A: Allocator>(root: &TrieNodeODRc<V, A>) -> bool {
    if root
        .as_tagged()
        .as_list()
        .is_some_and(|n| n.is_used_value_0() || n.is_used_value_1())
    {
        return true;
    }
    let mut stack: SmallVec<[_; 8]> =
        smallvec::smallvec![(root, root.as_tagged().new_iter_token())];
    while let Some((n, tok)) = stack.last_mut() {
        let (next, _, child, val) = n.as_tagged().next_items(*tok, false);
        if next == NODE_ITER_FINISHED {
            stack.pop();
            continue;
        }
        if val.is_some() {
            return true;
        }
        *tok = next;
        if let Some(child) = child {
            stack.push((child, child.as_tagged().new_iter_token()));
        }
    }
    false
}

fn ref_live_below<W: Clone + Send + Sync + Unpin, B: Allocator>(
    right: &TrieRefBorrowed<'_, W, B>,
) -> bool {
    if right.child_count() == 0 {
        return false;
    }
    let (node, key, _) = right.borrow_raw_parts();
    let mut tok = if key.is_empty() {
        node.new_iter_token()
    } else {
        node.iter_token_for_path(key)
    };
    loop {
        let (next, p, child, val) = node.next_items(tok, false);
        if next == NODE_ITER_FINISHED || !p.starts_with(key) {
            return false;
        }
        if val.is_some() || child.is_some_and(node_live) {
            return true;
        }
        tok = next;
    }
}

type NodeResult<V, A> = (Option<TrieNodeODRc<V, A>>, Summary);

fn cf_result<Cf: CoFree>(
    cf: &Cf,
    child: Option<TrieNodeODRc<Cf::V, Cf::A>>,
    keep: bool,
) -> AlgebraicResult<Cf> {
    let same_child = match (cf.rec(), &child) {
        (None, None) => true,
        (Some(a), Some(b)) => a.ptr_eq(b),
        _ => false,
    };
    if same_child && cf.has_val() == keep {
        AlgebraicResult::Identity(SELF_IDENT)
    } else if child.is_none() && !keep {
        AlgebraicResult::None
    } else {
        AlgebraicResult::Element(Cf::new(child, if keep { cf.val().cloned() } else { None }))
    }
}

fn byte_live<Cf: CoFree<A = A>, A: Allocator>(node: &ByteNode<Cf, A>, mask: ByteMask) -> bool {
    mask.iter().any(|b| {
        // The caller supplies a subset of the immutable node's mask.
        let cf = unsafe { node.get_unchecked(b) };
        cf.has_val() || cf.rec().is_some_and(node_live)
    })
}

// Dense/Dense, Dense/Cell, Cell/Dense and Cell/Cell all use this CoFree kernel,
// just as ordinary meet/join/subtract do. The right value type and allocator
// may differ; only the left payload is ever copied into the output.
fn byte_pair<const SUBTRACT: bool, L, R, A, B>(
    left: &ByteNode<L, A>,
    right: &ByteNode<R, B>,
    alloc: B,
) -> (AlgebraicResult<TrieNodeODRc<L::V, A>>, Summary)
where
    L: CoFree<A = A>,
    R: CoFree<A = B>,
    R::V: Unpin,
    A: Allocator,
    B: Allocator,
    ByteNode<L, A>: TrieNodeDowncast<L::V, A>,
{
    let common = left.mask & right.mask;
    let outside_live = byte_live(left, left.mask & !common);
    let mut total = Summary {
        live: outside_live,
        kept: SUBTRACT && outside_live,
    };
    let result = left.convex_entries(if SUBTRACT { left.mask } else { common }, |byte, l| {
        if !common.test_bit(byte) {
            return AlgebraicResult::Identity(SELF_IDENT);
        }
        let r = unsafe { right.get_unchecked(byte) };
        let (child, mut s) = match l.rec() {
            None => (None, Summary::default()),
            Some(lc) => child_pair::<SUBTRACT, _, _, _, _>(lc, r.rec()).unwrap_or_else(|| {
                let rc = r.rec().unwrap();
                node_op::<SUBTRACT, _, _, _, _>(
                    lc,
                    TrieRefBorrowed::new_with_key_and_path_in(rc, || None, &[], &[], alloc.clone()),
                )
            }),
        };
        let keep = l.has_val()
            && keep_value::<SUBTRACT>(s, r.has_val(), || r.rec().is_some_and(node_live));
        s.live |= l.has_val();
        s.kept |= keep;
        total.include(s);
        cf_result(l, child, keep)
    });
    (
        if total.kept {
            result
        } else {
            AlgebraicResult::None
        },
        total,
    )
}

// Mixed byte/compact and compressed-offset kernel. A compact right-hand node
// contributes at most two leading bytes, so meet only visits those candidates.
// Subtraction visits the left slots, reusing the disjoint entries verbatim.
fn byte_compact<const SUBTRACT: bool, L, W, A, B>(
    left: &ByteNode<L, A>,
    right: &TrieRefBorrowed<'_, W, B>,
) -> (AlgebraicResult<TrieNodeODRc<L::V, A>>, Summary)
where
    L: CoFree<A = A>,
    W: Clone + Send + Sync + Unpin,
    A: Allocator,
    B: Allocator,
    ByteNode<L, A>: TrieNodeDowncast<L::V, A>,
{
    let common = left.mask & right.child_mask();
    let outside_live = byte_live(left, left.mask & !common);
    let mut total = Summary {
        live: outside_live,
        kept: SUBTRACT && outside_live,
    };
    let result = left.convex_entries(if SUBTRACT { left.mask } else { common }, |byte, l| {
        if !common.test_bit(byte) {
            return AlgebraicResult::Identity(SELF_IDENT);
        }
        let (child, mut s, keep) = if right.aligned_node().is_some() {
            // Byte/List uses direct right slots too, including same-key
            // child/value pairs. Only an edge spanning the next node needs
            // the offset/path adaptation inside child_view or keep_at.
            let (child, s) = l.rec().map_or((None, Summary::default()), |lc| {
                node_op::<SUBTRACT, _, _, _, _>(lc, child_view(right, &[byte]))
            });
            let keep = l.has_val() && keep_at::<SUBTRACT, _, _>(right, &[byte], s);
            (child, s, keep)
        } else {
            // For an offset, resolve the byte once and share that view between
            // the child and value checks.
            let r = right.trie_ref_at_path(&[byte]);
            let (child, s) = l.rec().map_or((None, Summary::default()), |lc| {
                node_op::<SUBTRACT, _, _, _, _>(lc, r.clone())
            });
            let keep = l.has_val() && keep_value::<SUBTRACT>(s, r.is_val(), || ref_live_below(&r));
            (child, s, keep)
        };
        s.live |= l.has_val();
        s.kept |= keep;
        total.include(s);
        cf_result(l, child, keep)
    });
    (
        if total.kept {
            result
        } else {
            AlgebraicResult::None
        },
        total,
    )
}

fn byte_dispatch<const SUBTRACT: bool, L, W, A, B>(
    left: &ByteNode<L, A>,
    right: &TrieRefBorrowed<'_, W, B>,
) -> (AlgebraicResult<TrieNodeODRc<L::V, A>>, Summary)
where
    L: CoFree<A = A>,
    W: Clone + Send + Sync + Unpin,
    A: Allocator,
    B: Allocator,
    ByteNode<L, A>: TrieNodeDowncast<L::V, A>,
{
    if let Some(r) = right.aligned_node() {
        match r.tag() {
            DENSE_BYTE_NODE_TAG => {
                return byte_pair::<SUBTRACT, _, _, _, _>(
                    left,
                    unsafe { r.as_dense_unchecked() },
                    right.alloc(),
                );
            }
            CELL_BYTE_NODE_TAG => {
                return byte_pair::<SUBTRACT, _, _, _, _>(
                    left,
                    unsafe { r.as_cell_unchecked() },
                    right.alloc(),
                );
            }
            _ => {}
        }
    }
    byte_compact::<SUBTRACT, _, _, _, _>(left, right)
}

// Direct right-representation queries for the compact kernels. A query that
// crosses a child boundary uses the same native path lookup required by
// ordinary pmeet_generic; aligned local slots never go through that lookup.
fn keep_at<const SUBTRACT: bool, W: Clone + Send + Sync + Unpin, B: Allocator>(
    right: &TrieRefBorrowed<'_, W, B>,
    key: &[u8],
    s: Summary,
) -> bool {
    if SUBTRACT && s.kept {
        return true;
    }
    if !s.kept && s.live {
        return false;
    }
    if let Some(n) = right.aligned_node() {
        match n.tag() {
            DENSE_BYTE_NODE_TAG if key.len() == 1 => {
                let d = unsafe { n.as_dense_unchecked() };
                if !d.mask.test_bit(key[0]) {
                    return SUBTRACT;
                }
                let cf = unsafe { d.get_unchecked(key[0]) };
                return keep_value::<SUBTRACT>(s, cf.has_val(), || cf.rec().is_some_and(node_live));
            }
            CELL_BYTE_NODE_TAG if key.len() == 1 => {
                let d = unsafe { n.as_cell_unchecked() };
                if !d.mask.test_bit(key[0]) {
                    return SUBTRACT;
                }
                let cf = unsafe { d.get_unchecked(key[0]) };
                return keep_value::<SUBTRACT>(s, cf.has_val(), || cf.rec().is_some_and(node_live));
            }
            LINE_LIST_NODE_TAG => {
                let slots = unsafe { n.as_list_unchecked() }.convex_slots();
                let crosses_child = slots.iter().any(|(p, payload)| {
                    matches!(payload, PayloadRef::Child(_))
                        && p.len() < key.len()
                        && key.starts_with(p)
                });
                if !crosses_child {
                    let value = slots
                        .iter()
                        .any(|(p, payload)| *p == key && matches!(payload, PayloadRef::Val(_)));
                    return keep_value::<SUBTRACT>(s, value, || {
                        slots.iter().any(|(p, payload)| {
                            if !p.starts_with(key) {
                                return false;
                            }
                            match payload {
                                PayloadRef::Val(_) => p.len() > key.len(),
                                PayloadRef::Child(c) => node_live(c),
                                PayloadRef::None => false,
                            }
                        })
                    });
                }
            }
            EMPTY_NODE_TAG => return SUBTRACT,
            _ => {}
        }
    }
    let r = right.trie_ref_at_path(key);
    keep_value::<SUBTRACT>(s, r.is_val(), || ref_live_below(&r))
}

// Recursive child kernels never inspect their focus value. Borrow an aligned
// right child directly (List/List and List/byte included), without creating a
// compressed-offset view and looking the same path up again on the next call.
fn child_view<'a, W: Clone + Send + Sync + Unpin, B: Allocator>(
    right: &TrieRefBorrowed<'a, W, B>,
    key: &[u8],
) -> TrieRefBorrowed<'a, W, B> {
    let child = right.aligned_node().and_then(|n| match n.tag() {
        LINE_LIST_NODE_TAG => unsafe { n.as_list_unchecked() }
            .convex_slots()
            .into_iter()
            .find_map(|(p, payload)| {
                if p != key {
                    return None;
                }
                if let PayloadRef::Child(c) = payload {
                    Some(c)
                } else {
                    None
                }
            }),
        DENSE_BYTE_NODE_TAG if key.len() == 1 => {
            let d = unsafe { n.as_dense_unchecked() };
            if d.mask.test_bit(key[0]) {
                unsafe { d.get_unchecked(key[0]) }.rec()
            } else {
                None
            }
        }
        CELL_BYTE_NODE_TAG if key.len() == 1 => {
            let d = unsafe { n.as_cell_unchecked() };
            if d.mask.test_bit(key[0]) {
                unsafe { d.get_unchecked(key[0]) }.rec()
            } else {
                None
            }
        }
        _ => None,
    });
    match child {
        Some(c) => TrieRefBorrowed::new_with_key_and_path_in(c, || None, &[], &[], right.alloc()),
        None => right.trie_ref_at_path(key),
    }
}

// Exactly two local payload slots, using the same reconstruction helper as
// LineListNode::psubtract_dyn. Children and longer values precede their prefix
// values: a prefix value must see the final support of the other slot.
fn list_kernel<const SUBTRACT: bool, V, W, A, B>(
    left: &LineListNode<V, A>,
    right: &TrieRefBorrowed<'_, W, B>,
    mut child_result: Option<NodeResult<V, A>>,
) -> (AlgebraicResult<TrieNodeODRc<V, A>>, Summary)
where
    V: Clone + Send + Sync,
    W: Clone + Send + Sync + Unpin,
    A: Allocator,
    B: Allocator,
{
    let slots = left.convex_slots();
    let first = if matches!(slots[1].1, PayloadRef::Child(_))
        || (matches!(slots[0].1, PayloadRef::Val(_)) && slots[1].0.len() > slots[0].0.len())
    {
        1
    } else {
        0
    };
    let mut summaries = [Summary::default(); 2];
    let mut results = [AlgebraicResult::None, AlgebraicResult::None];
    for i in [first, 1 - first] {
        let (key, payload) = slots[i];
        match payload {
            PayloadRef::None => {}
            PayloadRef::Child(child) => {
                let (out, s) = child_result.take().unwrap_or_else(|| {
                    node_op::<SUBTRACT, _, _, _, _>(child, child_view(right, key))
                });
                summaries[i] = s;
                results[i] = match out {
                    None => AlgebraicResult::None,
                    Some(out) if out.ptr_eq(child) => AlgebraicResult::Identity(SELF_IDENT),
                    Some(out) => AlgebraicResult::Element(ValOrChild::Child(out)),
                };
            }
            PayloadRef::Val(_) => {
                let s = if slots[1 - i].0.starts_with(key) {
                    summaries[1 - i]
                } else {
                    Summary::default()
                };
                let keep = keep_at::<SUBTRACT, _, _>(right, key, s);
                summaries[i] = Summary {
                    live: true,
                    kept: keep,
                };
                if keep {
                    results[i] = AlgebraicResult::Identity(SELF_IDENT);
                }
            }
        }
    }
    let mut total = summaries[0];
    total.include(summaries[1]);
    (
        if total.kept {
            left.convex_rebuild(results)
        } else {
            AlgebraicResult::None
        },
        total,
    )
}

fn singleton_key<'a, V: Clone + Send + Sync, A: Allocator + 'a>(
    n: TaggedNodeRef<'a, V, A>,
) -> Option<&'a [u8]> {
    if n.as_list()
        .is_some_and(|l| l.is_used_value_0() && !l.is_used::<1>())
    {
        Some(unsafe { n.as_list_unchecked().key_unchecked::<0>() })
    } else {
        None
    }
}

fn child_pair<const SUBTRACT: bool, V, W, A, B>(
    left: &TrieNodeODRc<V, A>,
    right: Option<&TrieNodeODRc<W, B>>,
) -> Option<NodeResult<V, A>>
where
    V: Clone + Send + Sync,
    W: Clone + Send + Sync,
    A: Allocator,
    B: Allocator,
{
    let Some(right) = right else {
        let live = node_live(left);
        let kept = SUBTRACT && live;
        return Some((kept.then(|| left.clone()), Summary { live, kept }));
    };
    let l = left.as_tagged();
    let r = right.as_tagged();
    if l.shared_node_id() == r.shared_node_id() {
        let live = node_live(left);
        let kept = !SUBTRACT && live;
        return Some((kept.then(|| left.clone()), Summary { live, kept }));
    }
    if let (Some(l), Some(r)) = (singleton_key(l), singleton_key(r)) {
        let kept = (l == r) != SUBTRACT;
        return Some((kept.then(|| left.clone()), Summary { live: true, kept }));
    }
    None
}

fn node_shortcut<const SUBTRACT: bool, V, W, A, B>(
    left: &TrieNodeODRc<V, A>,
    right: &TrieRefBorrowed<'_, W, B>,
) -> Option<NodeResult<V, A>>
where
    V: Clone + Send + Sync,
    W: Clone + Send + Sync + Unpin,
    A: Allocator,
    B: Allocator,
{
    let identical = if right.child_count() != 0 {
        let (r, key, _) = right.borrow_raw_parts();
        key.is_empty() && left.as_tagged().shared_node_id() == r.shared_node_id()
    } else {
        false
    };
    if identical || (left.as_tagged().node_branches_mask(&[]) & right.child_mask()).is_empty_mask()
    {
        let live = node_live(left);
        let kept = live && if identical { !SUBTRACT } else { SUBTRACT };
        return Some((kept.then(|| left.clone()), Summary { live, kept }));
    }
    // A compact node containing one value has exactly one original tip.
    // Resolve it directly rather than allocating a postorder frame.
    if left
        .as_tagged()
        .as_list()
        .is_some_and(|n| n.is_used_value_0() && !n.is_used::<1>())
    {
        let n = left.as_tagged();
        let key = unsafe { n.as_list_unchecked().key_unchecked::<0>() };
        let kept = keep_at::<SUBTRACT, _, _>(right, key, Summary::default());
        return Some((kept.then(|| left.clone()), Summary { live: true, kept }));
    }
    None
}

// Borrow the sole recursive child without enumerating node items. List nodes
// can also hold one value; a byte spine is one CoFree with an optional value.
fn byte_link<C: CoFree<A = A>, A: Allocator>(
    n: &ByteNode<C, A>,
) -> Option<(&[u8], &TrieNodeODRc<C::V, A>, bool)> {
    if n.mask.count_bits() != 1 {
        return None;
    }
    let b = n.mask.indexed_bit::<true>(0).unwrap();
    let cf = unsafe { n.get_unchecked(b) };
    cf.rec()
        .map(|c| (&ALL_BYTES[b as usize..=b as usize], c, cf.has_val()))
}
fn spine_link<V: Clone + Send + Sync, A: Allocator>(
    n: TaggedNodeRef<'_, V, A>,
) -> Option<(&[u8], &TrieNodeODRc<V, A>, bool)> {
    match n.tag() {
        DENSE_BYTE_NODE_TAG => byte_link(unsafe { n.as_dense_unchecked() }),
        CELL_BYTE_NODE_TAG => byte_link(unsafe { n.as_cell_unchecked() }),
        LINE_LIST_NODE_TAG => {
            let slots = unsafe { n.as_list_unchecked() }.convex_slots();
            match (slots[0].1, slots[1].1) {
                (PayloadRef::Child(_), PayloadRef::Child(_)) => None,
                (PayloadRef::Child(c), other) => {
                    Some((slots[0].0, c, matches!(other, PayloadRef::Val(_))))
                }
                (other, PayloadRef::Child(c)) => {
                    Some((slots[1].0, c, matches!(other, PayloadRef::Val(_))))
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn byte_spine<const SUBTRACT: bool, L, W, A, B>(
    left: &ByteNode<L, A>,
    right: &TrieRefBorrowed<'_, W, B>,
    child_result: NodeResult<L::V, A>,
) -> (AlgebraicResult<TrieNodeODRc<L::V, A>>, Summary)
where
    L: CoFree<A = A>,
    W: Clone + Send + Sync + Unpin,
    A: Allocator,
    B: Allocator,
    ByteNode<L, A>: TrieNodeDowncast<L::V, A>,
{
    debug_assert_eq!(left.mask.count_bits(), 1);
    let (mut child, mut s) = child_result;
    let result = left.convex_entries(left.mask, |byte, l| {
        let keep = l.has_val() && keep_at::<SUBTRACT, _, _>(right, &[byte], s);
        s.live |= l.has_val();
        s.kept |= keep;
        cf_result(l, child.take(), keep)
    });
    (
        if s.kept {
            result
        } else {
            AlgebraicResult::None
        },
        s,
    )
}

// Same representation dispatch as ordinary algebra. `child_result` is present
// only while unwinding a unary spine, avoiding a native call per spine link.
fn native_kernel<const SUBTRACT: bool, V, W, A, B>(
    n: TaggedNodeRef<'_, V, A>,
    right: &TrieRefBorrowed<'_, W, B>,
    child_result: Option<NodeResult<V, A>>,
) -> (AlgebraicResult<TrieNodeODRc<V, A>>, Summary)
where
    V: Clone + Send + Sync,
    W: Clone + Send + Sync + Unpin,
    A: Allocator,
    B: Allocator,
{
    match n.tag() {
        DENSE_BYTE_NODE_TAG => {
            let l = unsafe { n.as_dense_unchecked() };
            match child_result {
                Some(c) => byte_spine::<SUBTRACT, _, _, _, _>(l, right, c),
                None => byte_dispatch::<SUBTRACT, _, _, _, _>(l, right),
            }
        }
        CELL_BYTE_NODE_TAG => {
            let l = unsafe { n.as_cell_unchecked() };
            match child_result {
                Some(c) => byte_spine::<SUBTRACT, _, _, _, _>(l, right, c),
                None => byte_dispatch::<SUBTRACT, _, _, _, _>(l, right),
            }
        }
        LINE_LIST_NODE_TAG => list_kernel::<SUBTRACT, _, _, _, _>(
            unsafe { n.as_list_unchecked() },
            right,
            child_result,
        ),
        EMPTY_NODE_TAG => (AlgebraicResult::None, Summary::default()),
        TINY_REF_NODE_TAG => {
            let tiny = unsafe { n.as_tiny_unchecked() };
            let Some(full) = tiny.into_list_node() else {
                return (AlgebraicResult::None, Summary::default());
            };
            list_kernel::<SUBTRACT, _, _, _, _>(&full, right, None)
        }
        _ => unreachable!("unsupported native node tag"),
    }
}

fn resolve<V: Clone + Send + Sync, A: Allocator>(
    left: &TrieNodeODRc<V, A>,
    result: (AlgebraicResult<TrieNodeODRc<V, A>>, Summary),
) -> NodeResult<V, A> {
    let (result, s) = result;
    let out = match result {
        AlgebraicResult::None => None,
        AlgebraicResult::Identity(id) => {
            debug_assert_eq!(id, SELF_IDENT);
            Some(left.clone())
        }
        AlgebraicResult::Element(out) => Some(out),
    };
    (out, s)
}

// An unvalued unary link needs no right-hand cursor during reconstruction.
// Keep only its original node pointer on the spine, as the ordinary algebra
// needs only a child result at this point.
fn unvalued_link<V: Clone + Send + Sync, A: Allocator>(
    left: &TrieNodeODRc<V, A>,
    result: NodeResult<V, A>,
) -> NodeResult<V, A> {
    let (child, s) = result;
    let Some(child) = child else {
        return (None, s);
    };
    let n = left.as_tagged();
    if spine_link(n).unwrap().1.ptr_eq(&child) {
        return (Some(left.clone()), s);
    }
    let result = match n.tag() {
        LINE_LIST_NODE_TAG => unsafe { n.as_list_unchecked() }.convex_rebuild([
            AlgebraicResult::Element(ValOrChild::Child(child)),
            AlgebraicResult::None,
        ]),
        DENSE_BYTE_NODE_TAG => {
            let d = unsafe { n.as_dense_unchecked() };
            let mut child = Some(child);
            d.convex_entries(d.mask, |_, cf| cf_result(cf, child.take(), false))
        }
        CELL_BYTE_NODE_TAG => {
            let d = unsafe { n.as_cell_unchecked() };
            let mut child = Some(child);
            d.convex_entries(d.mask, |_, cf| cf_result(cf, child.take(), false))
        }
        _ => unreachable!("unary link representation"),
    };
    resolve(left, (result, s))
}

fn node_op<const SUBTRACT: bool, V, W, A, B>(
    mut left: &TrieNodeODRc<V, A>,
    mut right: TrieRefBorrowed<'_, W, B>,
) -> NodeResult<V, A>
where
    V: Clone + Send + Sync,
    W: Clone + Send + Sync + Unpin,
    A: Allocator,
    B: Allocator,
{
    let mut spine = Vec::new();
    let mut valued_links = Vec::new();
    let mut result = loop {
        if let Some(done) = node_shortcut::<SUBTRACT, _, _, _, _>(left, &right) {
            break done;
        }
        if let Some((key, child, has_value)) = spine_link(left.as_tagged()) {
            let next_right = child_view(&right, key);
            if has_value {
                valued_links.push((spine.len(), right));
            }
            spine.push(left);
            left = child;
            right = next_right;
        } else {
            break resolve(
                left,
                native_kernel::<SUBTRACT, _, _, _, _>(left.as_tagged(), &right, None),
            );
        }
    };
    // If no spine link has a value, its entire support is the endpoint's.
    // Reuse or discard the whole chain without per-link reconstruction or
    // reference-count churn. Valued links still require the convex keep test.
    if valued_links.is_empty() && !spine.is_empty() {
        if result.0.is_none() {
            return result;
        }
        if result.0.as_ref().is_some_and(|out| out.ptr_eq(left)) {
            return (Some(spine[0].clone()), result.1);
        }
    }
    while let Some(left) = spine.pop() {
        if valued_links.last().is_some_and(|(i, _)| *i == spine.len()) {
            let (_, right) = valued_links.pop().unwrap();
            result = resolve(
                left,
                native_kernel::<SUBTRACT, _, _, _, _>(left.as_tagged(), &right, Some(result)),
            );
        } else {
            result = unvalued_link(left, result);
        }
    }
    result
}

fn map_op<const SUBTRACT: bool, V, W, A, B>(
    left: &PathMap<V, A>,
    right: &PathMap<W, B>,
) -> PathMap<V, A>
where
    V: Clone + Send + Sync + Unpin,
    W: Clone + Send + Sync + Unpin,
    A: Allocator,
    B: Allocator,
{
    if let (Some(l), Some(r)) = (left.root(), right.root()) {
        if l.as_tagged().shared_node_id() == r.as_tagged().shared_node_id() {
            let value = if SUBTRACT {
                (right.root_val().is_none() && left.root_val().is_some() && !node_live(l))
                    .then(|| left.root_val().unwrap().clone())
            } else {
                right.root_val().and(left.root_val()).cloned()
            };
            return PathMap::new_with_root_in(
                if SUBTRACT { None } else { Some(l.clone()) },
                value,
                left.alloc.clone(),
            );
        }
    }
    let r = right.trie_ref_at_path([]);
    let (node, s) = left.root().map_or((None, Summary::default()), |n| {
        node_op::<SUBTRACT, _, _, _, _>(n, r)
    });
    let keep_root = keep_value::<SUBTRACT>(s, right.root_val().is_some(), || {
        ref_live_below(&right.trie_ref_at_path([]))
    });
    PathMap::new_with_root_in(
        node,
        if keep_root {
            left.root_val().cloned()
        } else {
            None
        },
        left.alloc.clone(),
    )
}

/// Physical-node convex meet, with lazy copy-on-write and subtree sharing.
pub fn convex_meet<V, W, A, B>(left: &PathMap<V, A>, right: &PathMap<W, B>) -> PathMap<V, A>
where
    V: Clone + Send + Sync + Unpin,
    W: Clone + Send + Sync + Unpin,
    A: Allocator,
    B: Allocator,
{
    map_op::<false, _, _, _, _>(left, right)
}

/// Physical-node convex subtraction, preserving left payloads.
pub fn convex_subtract<V, W, A, B>(left: &PathMap<V, A>, right: &PathMap<W, B>) -> PathMap<V, A>
where
    V: Clone + Send + Sync + Unpin,
    W: Clone + Send + Sync + Unpin,
    A: Allocator,
    B: Allocator,
{
    map_op::<true, _, _, _, _>(left, right)
}

#[cfg(test)]
mod tests;
