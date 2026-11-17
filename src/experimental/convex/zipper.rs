use super::{Summary, keep_value};
use crate::{
    alloc::Allocator,
    utils::{BitMask, ByteMask},
    zipper::{zipper_priv::ZipperReadOnlyPriv, *},
};
use smallvec::SmallVec;

fn pop(mask: &mut ByteMask) -> Option<u8> {
    let b = mask.indexed_bit::<true>(0)?;
    mask.clear_bit(b);
    Some(b)
}

// One witness is sufficient. Fringes queried this way are disjoint.
fn zipper_live<Z: ZipperMoving>(z: &mut Z, below: bool) -> bool {
    let base = z.depth();
    if !below && z.is_val() {
        return true;
    }
    let mask = z.child_mask();
    if mask.is_empty_mask() {
        return false;
    }
    let mut stack: SmallVec<[(ByteMask, usize); 8]> = smallvec::smallvec![(mask, base)];
    loop {
        if let Some(b) = pop(&mut stack.last_mut().unwrap().0) {
            z.descend_to_byte(b);
            if !z.is_val() {
                z.descend_until();
            }
            if z.is_val() {
                z.ascend(z.depth() - base);
                return true;
            }
            stack.push((z.child_mask(), z.depth()));
        } else {
            stack.pop();
            let Some((_, parent)) = stack.last() else {
                return false;
            };
            z.ascend(z.depth() - *parent);
        }
    }
}

fn graft_values<V, A, L, O>(left: &L, out: &mut O)
where
    V: Clone + Send + Sync,
    A: Allocator,
    L: ZipperInfallibleSubtries<V, A>,
    O: ZipperWriting<V, A>,
{
    out.graft(left);
    // Explicit focus handling makes semantics independent of graft_root_vals.
    if let Some(v) = left.val() {
        out.set_val(v.clone());
    } else {
        out.remove_val(false);
    }
}

fn zipper_shortcut<const SUBTRACT: bool, V, A, L, R, O>(
    left: &mut L,
    right: &R,
    out: &mut O,
) -> Option<Summary>
where
    V: Clone + Send + Sync,
    A: Allocator,
    L: ZipperMoving + ZipperConcrete + ZipperInfallibleSubtries<V, A>,
    R: ZipperMoving + ZipperConcrete,
    O: ZipperWriting<V, A>,
{
    if let Some(id) = left.shared_node_id() {
        if Some(id) == right.shared_node_id() {
            let live = zipper_live(left, false);
            if !SUBTRACT && live {
                graft_values(left, out);
            }
            return Some(Summary {
                live,
                kept: !SUBTRACT && live,
            });
        }
    }
    if right.child_count() == 0 {
        let below = zipper_live(left, true);
        let live = left.is_val() || below;
        let kept = if SUBTRACT {
            live && (below || !right.is_val())
        } else {
            left.is_val() && right.is_val() && !below
        };
        if kept {
            if SUBTRACT {
                graft_values(left, out);
            } else {
                out.set_val(left.val().unwrap().clone());
            }
        }
        return Some(Summary { live, kept });
    }
    None
}

struct ZipFrame {
    children: ByteMask,
    summary: Summary,
    down: usize,
}

fn zipper_frame<const SUBTRACT: bool, V, A, L, R, O>(
    left: &L,
    right: &R,
    out: &mut O,
    down: usize,
) -> ZipFrame
where
    V: Clone + Send + Sync,
    A: Allocator,
    L: ZipperMoving + ZipperConcrete + ZipperInfallibleSubtries<V, A>,
    R: ZipperMoving + ZipperConcrete,
    O: ZipperWriting<V, A>,
{
    let lm = left.child_mask();
    let rm = right.child_mask();
    let mut summary = Summary::default();
    let outside = lm & !rm;
    if SUBTRACT && !outside.is_empty_mask() {
        out.graft_masked_branches(left, outside, false);
        summary.kept = zipper_live(out, true);
    }
    ZipFrame {
        children: lm & rm,
        summary,
        down,
    }
}

fn zipper_op<const SUBTRACT: bool, V, A, L, R, O>(left: &mut L, right: &mut R, out: &mut O)
where
    V: Clone + Send + Sync,
    A: Allocator,
    L: ZipperMoving + ZipperConcrete + ZipperInfallibleSubtries<V, A>,
    R: ZipperMoving + ZipperConcrete,
    O: ZipperWriting<V, A>,
{
    out.remove_branches(false);
    out.remove_val(false);
    if left
        .shared_node_id()
        .is_some_and(|id| Some(id) == right.shared_node_id())
    {
        if !SUBTRACT {
            graft_values(left, out);
        }
        return;
    }
    if SUBTRACT && (left.child_mask() & right.child_mask()).is_empty_mask() {
        if !left.is_val() || !right.is_val() || zipper_live(left, true) {
            graft_values(left, out);
        }
        return;
    }
    if zipper_shortcut::<SUBTRACT, _, _, _, _, _>(left, right, out).is_some() {
        return;
    }
    let mut frames: SmallVec<[ZipFrame; 8]> =
        smallvec::smallvec![zipper_frame::<SUBTRACT, _, _, _, _, _>(left, right, out, 0)];
    loop {
        if let Some(b) = pop(&mut frames.last_mut().unwrap().children) {
            let before = left.depth();
            left.descend_to_byte(b);
            right.descend_to_byte(b);
            out.descend_to_byte(b);
            // No candidate left value exists inside a compressed edge. The
            // right zipper can cross its own branches in one descent.
            if !left.is_val() {
                left.descend_until_observed(&mut (
                    MirrorPathObserver(right),
                    MirrorPathObserver(out),
                ));
            }
            let down = left.depth() - before;
            if let Some(s) = zipper_shortcut::<SUBTRACT, _, _, _, _, _>(left, right, out) {
                let p = &mut frames.last_mut().unwrap().summary;
                p.include(s);
                left.ascend(down);
                right.ascend(down);
                out.ascend(down);
            } else {
                frames.push(zipper_frame::<SUBTRACT, _, _, _, _, _>(
                    left, right, out, down,
                ));
            }
        } else {
            let mut f = frames.pop().unwrap();
            if left.is_val() {
                // Unmatched branches were skipped; recover original tip status
                // only when needed. First-witness probes stop at the next value.
                if !f.summary.kept && !f.summary.live {
                    f.summary.live = zipper_live(left, true);
                }
                let keep =
                    keep_value::<SUBTRACT>(f.summary, right.is_val(), || zipper_live(right, true));
                if keep {
                    out.set_val(left.val().unwrap().clone());
                    f.summary.kept = true;
                }
                f.summary.live = true;
            }
            let Some(parent) = frames.last_mut() else {
                break;
            };
            parent.summary.include(f.summary);
            left.ascend(f.down);
            right.ascend(f.down);
            out.ascend(f.down);
        }
    }
}

/// Replace the output focus with convex meet. All focuses are restored.
/// Compressed left edges are traversed as blocks, and right-only fringes need
/// only one valued witness. Payloads are cloned from the left; no Lattice bound.
pub fn zipper_convex_meet<V, A, L, R, O>(left: &mut L, right: &mut R, out: &mut O)
where
    V: Clone + Send + Sync,
    A: Allocator,
    L: ZipperMoving + ZipperConcrete + ZipperInfallibleSubtries<V, A>,
    R: ZipperMoving + ZipperConcrete,
    O: ZipperWriting<V, A>,
{
    zipper_op::<false, _, _, _, _, _>(left, right, out)
}

/// Replace the output focus with convex subtraction; preserve supporting
/// interiors even when the mask contains them. All focuses are restored.
pub fn zipper_convex_subtract<V, A, L, R, O>(left: &mut L, right: &mut R, out: &mut O)
where
    V: Clone + Send + Sync,
    A: Allocator,
    L: ZipperMoving + ZipperConcrete + ZipperInfallibleSubtries<V, A>,
    R: ZipperMoving + ZipperConcrete,
    O: ZipperWriting<V, A>,
{
    zipper_op::<true, _, _, _, _, _>(left, right, out)
}
