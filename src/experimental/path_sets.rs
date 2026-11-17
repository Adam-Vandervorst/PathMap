//! Prefix extrema and divergences of **valued** paths.
//!
//! A dangling path is not a set member. Termination is not a branch: `foo`
//! and `food` have no divergence. Basis and hull retain the original values;
//! retain preserves candidate values; divergence and branches return unit-valued maps.
//!
//! All traversals use zipper movements and explicit heap stacks, never pairs
//! of keys, recursive Rust calls, repeated root lookups, or subtree `val_count`.
//! Replacing an existing output additionally pays its destruction/COW cost.
//!
//! ```
//! use pathmap::{PathMap, experimental::path_sets::{basis, hull, divergence}};
//! let mut words = PathMap::single("foo", 1);
//! words.set_val_at("food", 2);
//! assert!(basis(&words).contains("foo"));
//! assert!(!basis(&words).contains("food"));
//! assert!(hull(&words).contains("food"));
//! let points = divergence(&words, &PathMap::single("four", ()));
//! assert!(points.contains("fo"));
//! ```

use crate::{
    PathMap,
    alloc::Allocator,
    utils::{BitMask, ByteMask},
    zipper::*,
};

fn pop_byte(mask: &mut ByteMask) -> Option<u8> {
    let byte = mask.indexed_bit::<true>(0)?;
    mask.clear_bit(byte);
    Some(byte)
}

fn clear_output<V: Clone + Send + Sync, A: Allocator, Out: ZipperWriting<V, A>>(out: &mut Out) {
    out.remove_branches(false);
    out.remove_val(false);
}

struct UnaryFrame {
    remaining: ByteMask,
    live_children: usize,
}

fn unary_frame<Z: Zipper>(src: &Z, stop_at_value: bool) -> UnaryFrame {
    UnaryFrame {
        remaining: if stop_at_value && src.is_val() {
            ByteMask::EMPTY
        } else {
            src.child_mask()
        },
        live_children: 0,
    }
}

// Postorder, with a preorder cut for basis. Both zippers return to their
// entry focus, including when that focus is absent or is below the zipper root.
fn walk_unary<Z: ZipperMoving, Out: ZipperMoving>(
    src: &mut Z,
    out: &mut Out,
    stop_at_value: bool,
    mut emit: impl FnMut(&Z, &mut Out, usize),
) {
    let mut stack = vec![unary_frame(src, stop_at_value)];
    loop {
        if let Some(byte) = pop_byte(&mut stack.last_mut().unwrap().remaining) {
            src.descend_to_byte(byte);
            out.descend_to_byte(byte);
            stack.push(unary_frame(src, stop_at_value));
        } else {
            let frame = stack.pop().unwrap();
            emit(src, out, frame.live_children);
            let live = src.is_val() || frame.live_children != 0;
            let Some(parent) = stack.last_mut() else {
                break;
            };
            parent.live_children += usize::from(live);
            src.ascend(1);
            out.ascend(1);
        }
    }
}

/// Replace the output focus subtree with the prefix-minimal valued paths of
/// the input focus subtree, preserving payloads. All focuses are restored.
///
/// Runs in O(P_basis + output + value cloning), with O(h) traversal storage,
/// where P_basis counts visited byte-prefix positions. Descendants of the first
/// value on each branch are skipped, including all descendants of a root value.
pub fn zipper_basis<V, A, Z, Out>(src: &mut Z, out: &mut Out)
where
    V: Clone + Send + Sync,
    A: Allocator,
    Z: ZipperMoving + ZipperValues<V>,
    Out: ZipperWriting<V, A>,
{
    clear_output(out);
    walk_unary(src, out, true, |src, out, _| {
        if let Some(value) = src.val() {
            out.set_val(value.clone());
        }
    });
}

/// Replace the output focus subtree with the prefix-maximal valued paths of
/// the input focus subtree, preserving payloads. All focuses are restored.
///
/// Runs in O(P + output + value cloning), with O(h) traversal storage. A value
/// with only dangling descendants is retained. Each structural byte edge is
/// traversed once down and once up; descendant counts are never recomputed.
pub fn zipper_hull<V, A, Z, Out>(src: &mut Z, out: &mut Out)
where
    V: Clone + Send + Sync,
    A: Allocator,
    Z: ZipperMoving + ZipperValues<V>,
    Out: ZipperWriting<V, A>,
{
    clear_output(out);
    walk_unary(src, out, false, |src, out, live_children| {
        if live_children == 0 {
            if let Some(value) = src.val() {
                out.set_val(value.clone());
            }
        }
    });
}

/// Replace the output focus subtree with all prefixes having two different
/// next bytes leading to values in the input. A terminal is not a next byte.
/// Runs in O(P + output), with O(h) traversal storage; restores both focuses.
pub fn zipper_branches<A, Z, Out>(src: &mut Z, out: &mut Out)
where
    A: Allocator,
    Z: ZipperMoving,
    Out: ZipperWriting<(), A>,
{
    clear_output(out);
    walk_unary(src, out, false, |_, out, live_children| {
        if live_children >= 2 {
            out.set_val(());
        }
    });
}

// A one-sided fringe only needs one witness. Do not walk its remaining values.
// Distinct fringe calls cover disjoint subtrees, so this cannot cause quadratic
// rescanning. The entry focus is restored even on an early successful return.
fn has_value<Z: ZipperMoving>(src: &mut Z) -> bool {
    let initial_depth = src.depth();
    let mut stack = Vec::new();
    loop {
        if src.is_val() {
            src.ascend(src.depth() - initial_depth);
            return true;
        }
        stack.push(src.child_mask());
        loop {
            if let Some(byte) = pop_byte(stack.last_mut().unwrap()) {
                src.descend_to_byte(byte);
                break;
            }
            stack.pop();
            if stack.is_empty() {
                return false;
            }
            src.ascend(1);
        }
    }
}

struct RetainFrame {
    common: ByteMask,
    fringe: ByteMask,
    witnessed: bool,
}

impl RetainFrame {
    fn new<L: Zipper, R: Zipper>(left: &L, right: &R) -> Self {
        let right_mask = right.child_mask();
        let common = left.child_mask() & right_mask;
        Self {
            common,
            fringe: right_mask & !common,
            witnessed: right.is_val(),
        }
    }
}

/// Retain input values whose paths prefix a valued witness in `witnesses`.
/// Replace the output focus and restore all three focuses. Witness payloads
/// are ignored; output payloads come from `src`.
///
/// O(C + F + output + value cloning) time and O(h) traversal storage: C counts
/// common structural byte prefixes, and F counts the first-witness searches in
/// disjoint witness-only fringes. Bare fringes may require a full scan. Each
/// common edge is traversed once in each direction; no subtree recount is used.
/// Replacing an existing output also incurs its destruction/COW cost.
pub fn zipper_retain<V, A, L, R, Out>(src: &mut L, witnesses: &mut R, out: &mut Out)
where
    V: Clone + Send + Sync,
    A: Allocator,
    L: ZipperMoving + ZipperValues<V>,
    R: ZipperMoving,
    Out: ZipperWriting<V, A>,
{
    clear_output(out);
    if !src.is_val() && src.child_count() == 0 {
        return;
    }
    let mut stack = vec![RetainFrame::new(src, witnesses)];
    loop {
        if let Some(byte) = pop_byte(&mut stack.last_mut().unwrap().common) {
            src.descend_to_byte(byte);
            witnesses.descend_to_byte(byte);
            out.descend_to_byte(byte);
            stack.push(RetainFrame::new(src, witnesses));
        } else {
            let mut frame = stack.pop().unwrap();
            while !frame.witnessed {
                let Some(byte) = pop_byte(&mut frame.fringe) else {
                    break;
                };
                witnesses.descend_to_byte(byte);
                frame.witnessed = has_value(witnesses);
                witnesses.ascend(1);
            }
            if frame.witnessed {
                if let Some(value) = src.val() {
                    out.set_val(value.clone());
                }
            }
            let Some(parent) = stack.last_mut() else {
                break;
            };
            parent.witnessed |= frame.witnessed;
            src.ascend(1);
            witnesses.ascend(1);
            out.ascend(1);
        }
    }
}

/// Keep the valued paths of `src` that prefix a valued path in `witnesses`.
/// Preserve source payloads and allocator; dangling paths are not witnesses.
///
/// ```
/// use pathmap::{PathMap, experimental::path_sets::retain};
/// let args: PathMap<_> = [0, 2, 4, 6].into_iter().map(|x| ([x], x)).collect();
/// let graph: PathMap<_> = [[1, 1], [2, 4], [3, 9], [4, 16], [5, 25]]
///     .into_iter().map(|p| (p, ())).collect();
/// let kept = retain(&args, &graph);
/// assert_eq!(kept.iter().map(|(p, _)| p).collect::<Vec<_>>(), vec![vec![2], vec![4]]);
/// ```
pub fn retain<V, W, A, B>(src: &PathMap<V, A>, witnesses: &PathMap<W, B>) -> PathMap<V, A>
where
    V: Clone + Send + Sync + Unpin,
    W: Clone + Send + Sync + Unpin,
    A: Allocator,
    B: Allocator,
{
    let mut out = PathMap::new_in(src.alloc.clone());
    zipper_retain(
        &mut src.read_zipper(),
        &mut witnesses.read_zipper(),
        &mut out.write_zipper(),
    );
    out
}

struct BinaryFrame {
    left: ByteMask,
    right: ByteMask,
    remaining: ByteMask,
    live_left: ByteMask,
    live_right: ByteMask,
    incoming: u8,
}

impl BinaryFrame {
    fn new<L: Zipper, R: Zipper>(left: &L, right: &R, incoming: u8) -> Self {
        let left = left.child_mask();
        let right = right.child_mask();
        Self {
            left,
            right,
            remaining: left.or(&right),
            live_left: ByteMask::EMPTY,
            live_right: ByteMask::EMPTY,
            incoming,
        }
    }
}

/// Replace the output focus subtree with cross-space divergences. The inputs
/// may carry different payload types; only value presence is observed.
///
/// An output p needs a valued left path p.a.x and a valued right path p.b.y
/// with a != b. A value at p does not contribute a next byte. All three focuses
/// are restored and no input is modified.
///
/// O(C + F + output) time and O(h) traversal storage: C is the number of common
/// structural byte-prefix positions, and F is the number of positions scanned
/// to find one valued witness in each one-sided fringe subtree. Always
/// C + F = O(P_left + P_right). Dangling fringes may require a full scan; for
/// valued fringes the scan stops at the first value. These bounds count logical
/// byte prefixes, not compressed physical nodes or unique shared DAG nodes.
/// Replacing a nonempty output also costs its destruction/COW work.
pub fn zipper_divergence<A, L, R, Out>(left: &mut L, right: &mut R, out: &mut Out)
where
    A: Allocator,
    L: ZipperMoving,
    R: ZipperMoving,
    Out: ZipperWriting<(), A>,
{
    clear_output(out);
    if left.child_count() == 0 || right.child_count() == 0 {
        return;
    }
    let mut stack = vec![BinaryFrame::new(left, right, 0)];
    loop {
        let frame = stack.last_mut().unwrap();
        if let Some(byte) = pop_byte(&mut frame.remaining) {
            let in_left = frame.left.test_bit(byte);
            let in_right = frame.right.test_bit(byte);
            if in_left && in_right {
                left.descend_to_byte(byte);
                right.descend_to_byte(byte);
                out.descend_to_byte(byte);
                stack.push(BinaryFrame::new(left, right, byte));
            } else if in_left {
                left.descend_to_byte(byte);
                if has_value(left) {
                    frame.live_left.set_bit(byte);
                }
                left.ascend(1);
            } else {
                right.descend_to_byte(byte);
                if has_value(right) {
                    frame.live_right.set_bit(byte);
                }
                right.ascend(1);
            }
        } else {
            let frame = stack.pop().unwrap();
            let left_child = !frame.live_left.is_empty_mask();
            let right_child = !frame.live_right.is_empty_mask();
            if left_child && right_child && frame.live_left.or(&frame.live_right).count_bits() >= 2
            {
                out.set_val(());
            }
            let left_live = left.is_val() || left_child;
            let right_live = right.is_val() || right_child;
            let Some(parent) = stack.last_mut() else {
                break;
            };
            if left_live {
                parent.live_left.set_bit(frame.incoming);
            }
            if right_live {
                parent.live_right.set_bit(frame.incoming);
            }
            left.ascend(1);
            right.ascend(1);
            out.ascend(1);
        }
    }
}

/// Prefix-minimal valued paths, with original payloads and allocator.
pub fn basis<V: Clone + Send + Sync + Unpin, A: Allocator>(src: &PathMap<V, A>) -> PathMap<V, A> {
    let mut out = PathMap::new_in(src.alloc.clone());
    zipper_basis(&mut src.read_zipper(), &mut out.write_zipper());
    out
}

/// Prefix-maximal valued paths, with original payloads and allocator.
pub fn hull<V: Clone + Send + Sync + Unpin, A: Allocator>(src: &PathMap<V, A>) -> PathMap<V, A> {
    let mut out = PathMap::new_in(src.alloc.clone());
    zipper_hull(&mut src.read_zipper(), &mut out.write_zipper());
    out
}

/// Cross-space divergences, marked with unit, using the left allocator.
pub fn divergence<V, W, A, B>(left: &PathMap<V, A>, right: &PathMap<W, B>) -> PathMap<(), A>
where
    V: Clone + Send + Sync + Unpin,
    W: Clone + Send + Sync + Unpin,
    A: Allocator,
    B: Allocator,
{
    let mut out = PathMap::new_in(left.alloc.clone());
    zipper_divergence(
        &mut left.read_zipper(),
        &mut right.read_zipper(),
        &mut out.write_zipper(),
    );
    out
}

/// All branch points of valued paths, marked with unit.
pub fn branches<V: Clone + Send + Sync + Unpin, A: Allocator>(
    src: &PathMap<V, A>,
) -> PathMap<(), A> {
    let mut out = PathMap::new_in(src.alloc.clone());
    zipper_branches(&mut src.read_zipper(), &mut out.write_zipper());
    out
}
