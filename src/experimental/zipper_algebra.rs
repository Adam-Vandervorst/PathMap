use std::borrow::Cow;

use crate::{
    alloc::{Allocator, GlobalAlloc},
    ring::{AlgebraicResult, COUNTER_IDENT, DistributiveLattice, Lattice, SELF_IDENT},
    utils::{BitMask, ByteMask},
    zipper::*,
};

pub use zipper_algebra_poly::ZipperMergeF;

/// Extension trait providing algebraic merge operations on radix-256 trie zippers.
///
/// This trait exposes high-level operations such as [`join`](Self::join),
/// [`meet`](Self::meet), and [`subtract`](Self::subtract) directly on zipper
/// instances, allowing them to be invoked in a method-oriented style:
///
/// ```ignore
/// lhs.join(&mut rhs, &mut out);
/// lhs.meet(&mut rhs, &mut out);
/// lhs.subtract(&mut rhs, &mut out);
/// ```
///
/// # Overview
///
/// All operations are implemented as *lockstep traversals* over two tries using
/// zipper navigation. They exploit the lexicographic ordering of child edges
/// (bytes `0..=255`) to efficiently merge, intersect, or subtract subtries
/// without visiting unrelated regions.
///
/// Each method delegates to a corresponding free function ([`zipper_join`],
/// [`zipper_meet`], [`zipper_subtract`]), preserving their performance
/// characteristics and semantics.
///
/// # Semantics
///
/// The provided operations correspond to common lattice and set-like behaviors:
///
/// - [`join`](Self::join): least upper bound (union-like merge),
/// - [`meet`](Self::meet): greatest lower bound (intersection),
/// - [`subtract`](Self::subtract): asymmetric difference (`lhs \ rhs`).
///
/// All operations write their result into a separate output zipper implementing
/// [`ZipperWriting`].
///
/// # Notes
///
/// - The operations are *asymmetric* with respect to the receiver (`self`) and
///   the `rhs` argument, which is particularly relevant for
///   [`subtract`](Self::subtract).
/// - The output zipper is written incrementally during traversal and must be
///   positioned consistently with the input zippers.
///
/// # See also
///
/// - [`zipper_join`]
/// - [`zipper_meet`]
/// - [`zipper_subtract`]
pub trait ZipperAlgebraExt<V: Clone + Send + Sync, A: Allocator = GlobalAlloc>:
    ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving + Sized
{
    #[inline]
    fn join<ZR, Out>(&mut self, rhs: &mut ZR, out: &mut Out)
    where
        V: Lattice,
        ZR: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        zipper_join(self, rhs, out);
    }

    #[inline]
    fn meet<ZR, Out>(&mut self, rhs: &mut ZR, out: &mut Out)
    where
        V: Lattice,
        ZR: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        zipper_meet(self, rhs, out);
    }

    #[inline]
    fn subtract<ZR, Out>(&mut self, rhs: &mut ZR, out: &mut Out)
    where
        V: DistributiveLattice,
        ZR: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        zipper_subtract(self, rhs, out);
    }
}

impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperAlgebraExt<V, A>
    for ReadZipperUntracked<'_, '_, V, A>
{
}

impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperAlgebraExt<V, A>
    for ReadZipperTracked<'_, '_, V, A>
{
}

impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperAlgebraExt<V, A>
    for ReadZipperOwned<V, A>
{
}

impl<Z, V: Clone + Send + Sync + Unpin, A: Allocator> ZipperAlgebraExt<V, A> for PrefixZipper<'_, Z> where
    Z: ZipperInfallibleSubtries<V, A> + ZipperSubtries<V, A> + ZipperConcrete + ZipperMoving
{
}

/// Performs an ordered join (least upper bound) of two radix-256 tries using zipper traversal.
///
/// This function merges two tries by simultaneously traversing them in lexicographic order,
/// exploiting the ordering of child edges (bytes `0..=255`) to avoid unnecessary descent.
///
/// # Value semantics
///
/// When both tries contain a value at the same key, they are merged using the [`Lattice`]
/// operation [`Lattice::pjoin`]. The result is interpreted as follows:
///
/// - [`AlgebraicResult::None`] → no value is written,
/// - [`AlgebraicResult::Identity`] → one of the inputs is reused (based on identity mask),
/// - [`AlgebraicResult::Element`] → the computed value is written.
///
/// If only one side contains a value, it is propagated unchanged.
///
/// # Complexity
///
/// Let:
/// - `h` be the maximum key length,
/// - `d` be the size of overlapping subtries,
/// - `f` be the size of the frontier (distinct child edges encountered).
///
/// Then:
///
/// - Best case (disjoint tries): **O(h)**
/// - Typical case: **O(h + f)**
/// - Worst case (identical structure): **O(n)**
///
/// The algorithm avoids visiting entire disjoint subtrees by grafting them directly.
///
/// # Notes
///
/// This is a stackless depth-first traversal implemented via zippers.
/// The outer loop manages ascent (unwinding), while the inner loop
/// exhausts the current node's children.
///
pub fn zipper_join<V, ZL, ZR, Out, A>(lhs: &mut ZL, rhs: &mut ZR, out: &mut Out)
where
    V: Lattice + Clone + Send + Sync,
    A: Allocator,
    ZL: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    ZR: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
{
    zipper_merge::<Join, V, ZL, ZR, Out, A>(lhs, rhs, out);
}

/// Performs an ordered join (least upper bound) of three radix-256 tries using zipper traversal.
/// That is, it performs: (`lhs` ⊔ `mid`) ⊔ `rhs`, where `⊔` = [`zipper_join`]
///
/// # See also
///
/// [`zipper_join`]
///
pub fn zipper_join3<V, ZL, ZM, ZR, Out, A>(lhs: &mut ZL, mid: &mut ZM, rhs: &mut ZR, out: &mut Out)
where
    V: Lattice + Clone + Send + Sync,
    A: Allocator,
    ZL: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    ZM: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    ZR: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
{
    zipper_merge3::<Join, V, ZL, ZM, ZR, Out, A>(lhs, mid, rhs, out);
}

/// Performs an ordered meet (greatest lower bound) of two radix-256 tries using zipper traversal.
///
/// This function intersects two tries by simultaneously traversing them in lexicographic order,
/// exploiting the ordering of child edges (bytes `0..=255`) to avoid unnecessary descent.
///
/// # Value semantics
///
/// When both tries contain a value at the same key, they are merged using the [`Lattice`]
/// operation [`Lattice::pmeet`]. The result is interpreted as follows:
///
/// - [`AlgebraicResult::None`] → no value is written,
/// - [`AlgebraicResult::Identity`] → one of the inputs is reused (based on identity mask),
/// - [`AlgebraicResult::Element`] → the computed value is written.
///
/// If a value is present on only one side, it is discarded.
///
/// # Complexity
///
/// Let:
/// - `h` be the maximum key length,
/// - `d` be the size of overlapping subtries,
/// - `f` be the size of the shared frontier (common child edges).
///
/// Then:
///
/// - Best case (disjoint tries): **O(h)**
/// - Typical case: **O(h + f)**
/// - Worst case (identical structure): **O(n)**
///
/// The algorithm avoids visiting disjoint subtrees by skipping them entirely.
///
/// # Notes
///
/// This is a stackless depth-first traversal implemented via zippers.
/// The outer loop manages ascent (unwinding), while the inner loop
/// processes only shared child edges at each node.
///
/// Unlike [`zipper_join`], this operation descends exclusively into edges
/// present in *both* tries, forming the intersection of their structures.
///
pub fn zipper_meet<V, ZL, ZR, Out, A>(lhs: &mut ZL, rhs: &mut ZR, out: &mut Out)
where
    V: Lattice + Clone + Send + Sync,
    A: Allocator,
    ZL: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    ZR: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
{
    zipper_merge::<Meet, V, ZL, ZR, Out, A>(lhs, rhs, out);
}

/// Performs an ordered meet (greater lower bound) of three radix-256 tries using zipper traversal.
/// That is, it performs: (`lhs` ⊓ `mid`) ⊓ `rhs`, where `⊓` = [`zipper_meet`]
///
/// # See also
///
/// [`zipper_meet`]
///
pub fn zipper_meet3<V, ZL, ZM, ZR, Out, A>(lhs: &mut ZL, mid: &mut ZM, rhs: &mut ZR, out: &mut Out)
where
    V: Lattice + Clone + Send + Sync,
    A: Allocator,
    ZL: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    ZM: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    ZR: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
{
    zipper_merge3::<Meet, V, ZL, ZM, ZR, Out, A>(lhs, mid, rhs, out);
}

/// Performs an ordered subtraction (set difference, `lhs \ rhs`) of two radix-256 tries
/// using zipper traversal.
///
/// This function subtracts the structure and values of `rhs` from `lhs` by simultaneously
/// traversing both tries in lexicographic order. It exploits the ordering of child edges
/// (bytes `0..=255`) to avoid unnecessary descent.
///
/// # Value semantics
///
/// Values are handled asymmetrically:
///
/// - If only `lhs` contains a value, it is preserved unchanged.
/// - If only `rhs` contains a value, it is ignored.
/// - If both tries contain a value at the same key, they are comined using the [`DistributiveLattice`]
///   operation [`DistributiveLattice::psubtract`]. The result is interpreted as follows:
///
///   - [`AlgebraicResult::None`] → no value is written,
///   - [`AlgebraicResult::Identity`] → only lhs is preserved (based on identity mask),
///   - [`AlgebraicResult::Element`] → the computed value is written.
///
/// # Complexity
///
/// Let:
/// - `h` be the maximum key length,
/// - `d` be the size of overlapping subtries,
/// - `f` be the size of the frontier (distinct child edges encountered).
///
/// Then:
///
/// - Best case (disjoint tries): **O(h)**
/// - Typical case: **O(h + f)**
/// - Worst case (identical structure): **O(n)**
///
/// The algorithm avoids visiting disjoint subtrees by grafting `lhs`-only regions
/// and skipping `rhs`-only regions entirely.
///
/// # Notes
///
/// This is a stackless depth-first traversal implemented via zippers.
/// The outer loop manages ascent (unwinding), while the inner loop
/// exhausts the current node's children.
///
/// Unlike [`zipper_join`] and [`zipper_meet`], this operation is asymmetric:
/// it preserves only the parts of `lhs` that are not overlapped by `rhs`,
/// effectively removing any shared structure or values.
///
pub fn zipper_subtract<V, ZL, ZR, Out, A>(lhs: &mut ZL, rhs: &mut ZR, out: &mut Out)
where
    V: DistributiveLattice + Clone + Send + Sync,
    A: Allocator,
    ZL: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    ZR: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
{
    zipper_merge::<Subtract, V, ZL, ZR, Out, A>(lhs, rhs, out);
}

/// Performs an ordered subtraction (set difference of three radix-256 tries using zipper traversal.
/// That is, it performs: (`lhs` \ `mid`) \ `rhs`, where `\` = [`zipper_subtract`]
///
/// # See also
///
/// [`zipper_subtract`]
///
pub fn zipper_subtract3<V, ZL, ZM, ZR, Out, A>(
    lhs: &mut ZL,
    mid: &mut ZM,
    rhs: &mut ZR,
    out: &mut Out,
) where
    V: DistributiveLattice + Clone + Send + Sync,
    A: Allocator,
    ZL: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    ZM: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    ZR: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
{
    zipper_merge3::<Subtract, V, ZL, ZM, ZR, Out, A>(lhs, mid, rhs, out);
}

trait MergePolicy<V: Clone + Send + Sync> {
    #[inline]
    fn on_left_only<Z, Out, A>(z: &mut Z, range: ByteMask, out: &mut Out)
    where
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        Self::on_single(z, 0b01, range, out);
    }

    #[inline]
    fn on_right_only<Z, Out, A>(z: &mut Z, range: ByteMask, out: &mut Out)
    where
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        Self::on_single(z, 0b10, range, out);
    }

    fn on_single<Z, Out, A>(z: &mut Z, mask: u64, range: ByteMask, out: &mut Out)
    where
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperMoving,
        Out: ZipperWriting<V, A>;

    fn descend_on_some_equal(mask: u64) -> bool;
    fn on_id<Z, Out, A>(z: &mut Z, out: &mut Out)
    where
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Out: ZipperWriting<V, A>;
}

#[inline(always)]
fn lift<'a, V: Clone>(v: Option<&'a V>) -> Option<Cow<'a, V>> {
    v.map(Cow::Borrowed)
}

#[inline(always)]
fn unlift<V: Clone>(v: Option<Cow<V>>) -> Option<V> {
    v.map(Cow::into_owned)
}
trait ValuePolicy<V: Clone> {
    fn combine_impl<'a>(l: Option<Cow<'a, V>>, r: Option<Cow<'a, V>>) -> Option<Cow<'a, V>>;
    #[inline]
    fn combine(l: Option<&V>, r: Option<&V>) -> Option<V> {
        unlift(Self::combine_impl(lift(l), lift(r)))
    }
    #[inline]
    fn combine3(l: Option<&V>, m: Option<&V>, r: Option<&V>) -> Option<V> {
        // (l op m) op r
        unlift(Self::combine_impl(
            Self::combine_impl(lift(l), lift(m)),
            lift(r),
        ))
    }
    #[inline]
    fn combine4(a: Option<&V>, b: Option<&V>, c: Option<&V>, d: Option<&V>) -> Option<V> {
        // ((a op b) op c) op d
        unlift(Self::combine_impl(
            Self::combine_impl(Self::combine_impl(lift(a), lift(b)), lift(c)),
            lift(d),
        ))
    }
    fn combine_n<'a, I>(vals: I) -> Option<V>
    where
        I: Iterator<Item = Option<Cow<'a, V>>>,
        V: 'a,
    {
        unlift(vals.fold(None, |acc, v| Self::combine_impl(acc, v)))
    }
}

fn zipper_merge<P, V, ZL, ZR, Out, A>(lhs: &mut ZL, rhs: &mut ZR, out: &mut Out)
where
    V: Clone + Send + Sync,
    P: MergePolicy<V> + ValuePolicy<V>,
    A: Allocator,
    ZL: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    ZR: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
{
    fn check_sharing<ZL, ZR>(lhs: &ZL, rhs: &ZR) -> bool
    where
        ZL: ZipperConcrete,
        ZR: ZipperConcrete,
    {
        lhs.shared_node_id()
            .is_some_and(|lsnid| rhs.shared_node_id().is_some_and(|rsnid| lsnid == rsnid))
    }
    // check for node-sharing first
    if check_sharing(lhs, rhs) {
        P::on_id(lhs, out);
        return;
    }

    // merge root values before descending
    if let Some(v) = P::combine(lhs.val(), rhs.val()) {
        out.set_val(v);
    }

    let mut k = 0;
    let mut lhs_mask = lhs.child_mask();
    let mut rhs_mask = rhs.child_mask();
    let mut lhs_next = lhs_mask.indexed_bit::<true>(0);
    let mut rhs_next = rhs_mask.indexed_bit::<true>(0);

    // At each node, the algorithm treats the sets of child edges of `lhs` and `rhs` as two sorted
    // sequences and performs a merge-like traversal:
    //
    // - If a range of edges exists only in one side, the corresponding merge policy method is
    //   called.
    // - If both sides contain the same edge, the algorithm descends into that child, recursively
    //   merging the corresponding subtries.
    // - Descent is simulated iteratively using zipper movement (`descend_to_byte` / `ascend_byte`)
    //   and an explicit depth counter (`k`).
    'ascend: loop {
        'merge_level: loop {
            match lhs_next {
                Some(lhs_byte) => match rhs_next {
                    Some(rhs_byte) if lhs_byte < rhs_byte => {
                        P::on_left_only(lhs, ByteMask::from_range(lhs_byte..rhs_byte), out);
                        lhs_next = (lhs_mask & ByteMask::from_range(rhs_byte..)).next_bit(0);
                    }
                    Some(rhs_byte) if lhs_byte > rhs_byte => {
                        P::on_right_only(rhs, ByteMask::from_range(rhs_byte..lhs_byte), out);
                        rhs_next = (rhs_mask & ByteMask::from_range(lhs_byte..)).next_bit(0);
                    }
                    Some(rhs_byte) => {
                        // equal → descend
                        out.descend_to_byte(lhs_byte);

                        lhs.descend_to_byte(lhs_byte);
                        rhs.descend_to_byte(lhs_byte);

                        // optimization - if both zippers share the node after descend, we can skip
                        // further descend and continue merging
                        if check_sharing(lhs, rhs) {
                            P::on_id(lhs, out);

                            rhs.ascend_byte();
                            rhs_next = rhs_mask.next_bit(lhs_byte);
                            lhs.ascend_byte();
                            lhs_next = lhs_mask.next_bit(lhs_byte);
                            out.ascend_byte();

                            continue 'merge_level;
                        }

                        if let Some(v) = P::combine(lhs.val(), rhs.val()) {
                            out.set_val(v);
                        }

                        lhs_mask = lhs.child_mask();
                        rhs_mask = rhs.child_mask();

                        lhs_next = lhs_mask.indexed_bit::<true>(0);
                        rhs_next = rhs_mask.indexed_bit::<true>(0);

                        k += 1;
                        continue 'merge_level;
                    }
                    None => {
                        P::on_left_only(lhs, ByteMask::from_range(lhs_byte..), out);
                        break 'merge_level;
                    }
                },
                None => match rhs_next {
                    Some(rhs_byte) => {
                        P::on_right_only(rhs, ByteMask::from_range(rhs_byte..), out);
                        break 'merge_level;
                    }
                    None => break 'merge_level,
                },
            }
        }

        // If we are at root and no deeper recursion pending, we're done
        if k == 0 {
            break 'ascend;
        }

        let byte_from = *lhs.path().last().expect("non-empty path when k > 0");

        rhs.ascend_byte();
        rhs_mask = rhs.child_mask();
        rhs_next = rhs_mask.next_bit(byte_from);

        lhs.ascend_byte();
        lhs_mask = lhs.child_mask();
        lhs_next = lhs_mask.next_bit(byte_from);

        out.ascend_byte();
        k -= 1;
    }
}

#[inline(always)]
fn cmp_swap(a: &mut Option<u8>, b: &mut Option<u8>) {
    if let Some(x) = *a {
        if let Some(y) = *b {
            if y < x {
                std::mem::swap(a, b);
            }
        }
    } else {
        std::mem::swap(a, b);
    }
}

fn zipper_merge3<P, V, ZL, ZM, ZR, Out, A>(lhs: &mut ZL, mid: &mut ZM, rhs: &mut ZR, out: &mut Out)
where
    V: Clone + Send + Sync,
    P: MergePolicy<V> + ValuePolicy<V>,
    A: Allocator,
    ZL: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    ZM: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    ZR: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
{
    const L: u8 = 0b001;
    const M: u8 = 0b010;
    const R: u8 = 0b100;
    const LM: u8 = L | M;
    const LR: u8 = L | R;
    const MR: u8 = M | R;
    const LMR: u8 = L | M | R;

    fn descend2<P, V, ZL, ZR, Out, A>(b: u8, lhs: &mut ZL, rhs: &mut ZR, out: &mut Out)
    where
        V: Clone + Send + Sync,
        P: MergePolicy<V> + ValuePolicy<V>,
        A: Allocator,
        ZL: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        ZR: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        out.descend_to_byte(b);
        lhs.descend_to_byte(b);
        rhs.descend_to_byte(b);

        zipper_merge::<P, V, ZL, ZR, Out, A>(lhs, rhs, out);

        rhs.ascend_byte();
        lhs.ascend_byte();
        out.ascend_byte();
    }

    fn all_share<ZL, ZM, ZR>(lhs: &ZL, mid: &ZM, rhs: &ZR) -> bool
    where
        ZL: ZipperConcrete,
        ZM: ZipperConcrete,
        ZR: ZipperConcrete,
    {
        lhs.shared_node_id().is_some_and(|lsnid| {
            mid.shared_node_id().is_some_and(|msnid| {
                lsnid == msnid && rhs.shared_node_id().is_some_and(|rsnid| msnid == rsnid)
            })
        })
    }

    // check for node-sharing first
    if all_share(lhs, mid, rhs) {
        P::on_id(lhs, out);
        return;
    }

    // merge root values before descending
    if let Some(v) = P::combine3(lhs.val(), mid.val(), rhs.val()) {
        out.set_val(v);
    }

    let mut k = 0;
    let mut lhs_mask = lhs.child_mask();
    let mut mid_mask = mid.child_mask();
    let mut rhs_mask = rhs.child_mask();
    let mut l = lhs_mask.indexed_bit::<true>(0);
    let mut m = mid_mask.indexed_bit::<true>(0);
    let mut r = rhs_mask.indexed_bit::<true>(0);

    'ascend: loop {
        'merge_level: loop {
            let mut a = l;
            let mut b = m;
            let mut c = r;

            cmp_swap(&mut a, &mut b);
            cmp_swap(&mut a, &mut c);

            if let Some(min) = a {
                let mut frontier = 0;
                if a == l {
                    frontier = L;
                }
                if a == m {
                    frontier |= M;
                }
                if a == r {
                    frontier |= R;
                }

                match frontier {
                    // single → graft
                    L => {
                        cmp_swap(&mut b, &mut c);
                        if let Some(next) = b {
                            P::on_single(lhs, L as u64, ByteMask::from_range(min..next), out);
                            l = (lhs_mask & ByteMask::from_range(next..)).next_bit(0);
                        } else {
                            P::on_single(lhs, L as u64, ByteMask::from_range(min..), out);
                            break 'merge_level;
                        }
                    }
                    M => {
                        cmp_swap(&mut b, &mut c);
                        if let Some(next) = b {
                            P::on_single(mid, M as u64, ByteMask::from_range(min..next), out);
                            m = (mid_mask & ByteMask::from_range(next..)).next_bit(0);
                        } else {
                            P::on_single(mid, M as u64, ByteMask::from_range(min..), out);
                            break 'merge_level;
                        }
                    }
                    R => {
                        cmp_swap(&mut b, &mut c);
                        if let Some(next) = b {
                            P::on_single(rhs, R as u64, ByteMask::from_range(min..next), out);
                            r = (rhs_mask & ByteMask::from_range(next..)).next_bit(0);
                        } else {
                            P::on_single(rhs, R as u64, ByteMask::from_range(min..), out);
                            break 'merge_level;
                        }
                    }
                    // two-way → descend 2
                    LM => {
                        if P::descend_on_some_equal(LM as u64) {
                            descend2::<P, V, ZL, ZM, Out, A>(min, lhs, mid, out);
                        }
                        l = lhs_mask.next_bit(min);
                        m = mid_mask.next_bit(min);
                    }
                    MR => {
                        if P::descend_on_some_equal(MR as u64) {
                            descend2::<P, V, ZM, ZR, Out, A>(min, mid, rhs, out);
                        }
                        m = mid_mask.next_bit(min);
                        r = rhs_mask.next_bit(min);
                    }
                    LR => {
                        if P::descend_on_some_equal(LR as u64) {
                            descend2::<P, V, ZL, ZR, Out, A>(min, lhs, rhs, out);
                        }
                        l = lhs_mask.next_bit(min);
                        r = rhs_mask.next_bit(min);
                    }
                    // full 3-way
                    LMR => {
                        out.descend_to_byte(min);

                        lhs.descend_to_byte(min);
                        mid.descend_to_byte(min);
                        rhs.descend_to_byte(min);

                        //structural sharing check
                        if all_share(lhs, mid, rhs) {
                            P::on_id(lhs, out);

                            rhs.ascend_byte();
                            r = rhs_mask.next_bit(min);
                            mid.ascend_byte();
                            m = mid_mask.next_bit(min);
                            lhs.ascend_byte();
                            l = lhs_mask.next_bit(min);
                            out.ascend_byte();

                            continue 'merge_level;
                        }

                        if let Some(val) = P::combine3(lhs.val(), mid.val(), rhs.val()) {
                            out.set_val(val);
                        }

                        lhs_mask = lhs.child_mask();
                        mid_mask = mid.child_mask();
                        rhs_mask = rhs.child_mask();

                        l = lhs_mask.indexed_bit::<true>(0);
                        m = mid_mask.indexed_bit::<true>(0);
                        r = rhs_mask.indexed_bit::<true>(0);

                        k += 1;
                        continue 'merge_level;
                    }
                    _ => unreachable!(),
                }
            } else {
                break 'merge_level;
            }
        }

        // If we are at root and no deeper recursion pending, we're done
        if k == 0 {
            break 'ascend;
        }

        let byte_from = *lhs.path().last().expect("non-empty path when k > 0");

        rhs.ascend_byte();
        rhs_mask = rhs.child_mask();
        r = rhs_mask.next_bit(byte_from);

        mid.ascend_byte();
        mid_mask = mid.child_mask();
        m = mid_mask.next_bit(byte_from);

        lhs.ascend_byte();
        lhs_mask = lhs.child_mask();
        l = lhs_mask.next_bit(byte_from);

        out.ascend_byte();
        k -= 1;
    }
}

// semi-unrolled (bitmask-driven)
// Beyond 4, the combinatorics start to creak, but k = 4 is a sweet spot:
// - still manageable (16 frontier cases)
// - still branch-predictable
// - still worth it for hot paths
fn zipper_merge4<P, V, Z0, Z1, Z2, Z3, Out, A>(
    z0: &mut Z0,
    z1: &mut Z1,
    z2: &mut Z2,
    z3: &mut Z3,
    out: &mut Out,
) where
    V: Clone + Send + Sync,
    P: MergePolicy<V> + ValuePolicy<V>,
    A: Allocator,
    Z0: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Z1: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Z2: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Z3: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
{
    fn all_share<Z0, Z1, Z2, Z3>(z0: &Z0, z1: &Z1, z2: &Z2, z3: &Z3) -> bool
    where
        Z0: ZipperConcrete,
        Z1: ZipperConcrete,
        Z2: ZipperConcrete,
        Z3: ZipperConcrete,
    {
        z0.shared_node_id().is_some_and(|snid0| {
            z1.shared_node_id().is_some_and(|snid1| {
                snid0 == snid1
                    && z2.shared_node_id().is_some_and(|snid2| {
                        snid1 == snid2 && z3.shared_node_id().is_some_and(|snid3| snid2 == snid3)
                    })
            })
        })
    }

    // check for node-sharing first
    if all_share(z0, z1, z2, z3) {
        P::on_id(z0, out);
        return;
    }

    // merge root values before descending
    if let Some(v) = P::combine4(z0.val(), z1.val(), z2.val(), z3.val()) {
        out.set_val(v);
    }

    let mut k = 0;
    // state (fully unrolled)
    let mut m0 = z0.child_mask();
    let mut m1 = z1.child_mask();
    let mut m2 = z2.child_mask();
    let mut m3 = z3.child_mask();

    let mut b0 = m0.indexed_bit::<true>(0);
    let mut b1 = m1.indexed_bit::<true>(0);
    let mut b2 = m2.indexed_bit::<true>(0);
    let mut b3 = m3.indexed_bit::<true>(0);

    'ascend: loop {
        'merge_level: loop {
            // min selection
            let mut a = b0;
            let mut b = b1;
            let mut c = b2;
            let mut d = b3;

            cmp_swap(&mut a, &mut b);
            cmp_swap(&mut a, &mut c);
            cmp_swap(&mut a, &mut d);

            if let Some(min) = a {
                let mut frontier = 0u8;
                if b0 == a {
                    frontier |= 0b0001;
                }
                if b1 == a {
                    frontier |= 0b0010;
                }
                if b2 == a {
                    frontier |= 0b0100;
                }
                if b3 == a {
                    frontier |= 0b1000;
                }

                // full match
                if frontier == 0b1111 {
                    out.descend_to_byte(min);

                    z0.descend_to_byte(min);
                    z1.descend_to_byte(min);
                    z2.descend_to_byte(min);
                    z3.descend_to_byte(min);

                    // check structural sharing
                    if all_share(z0, z1, z2, z3) {
                        P::on_id(z0, out);

                        z3.ascend_byte();
                        b3 = m3.next_bit(min);
                        z2.ascend_byte();
                        b2 = m2.next_bit(min);
                        z1.ascend_byte();
                        b1 = m1.next_bit(min);
                        z0.ascend_byte();
                        b0 = m0.next_bit(min);
                        out.ascend_byte();

                        continue 'merge_level;
                    }

                    if let Some(v) = P::combine4(z0.val(), z1.val(), z2.val(), z3.val()) {
                        out.set_val(v);
                    }

                    m0 = z0.child_mask();
                    b0 = m0.indexed_bit::<true>(0);
                    m1 = z1.child_mask();
                    b1 = m1.indexed_bit::<true>(0);
                    m2 = z2.child_mask();
                    b2 = m2.indexed_bit::<true>(0);
                    m3 = z3.child_mask();
                    b3 = m3.indexed_bit::<true>(0);

                    k += 1;
                    continue 'merge_level;
                }

                let cnt = frontier.count_ones();
                // singleton
                if cnt == 1 {
                    cmp_swap(&mut b, &mut c);
                    cmp_swap(&mut b, &mut d);

                    match frontier {
                        0b0001 => {
                            if let Some(next) = b {
                                P::on_single(z0, 0b0001, ByteMask::from_range(min..next), out);
                                b0 = (m0 & ByteMask::from_range(next..)).next_bit(0);
                            } else {
                                P::on_single(z0, 0b0001, ByteMask::from_range(min..), out);
                                break 'merge_level;
                            }
                        }
                        0b0010 => {
                            if let Some(next) = b {
                                P::on_single(z1, 0b0010, ByteMask::from_range(min..next), out);
                                b1 = (m1 & ByteMask::from_range(next..)).next_bit(0);
                            } else {
                                P::on_single(z1, 0b0010, ByteMask::from_range(min..), out);
                                break 'merge_level;
                            }
                        }
                        0b0100 => {
                            if let Some(next) = b {
                                P::on_single(z2, 0b0100, ByteMask::from_range(min..next), out);
                                b2 = (m2 & ByteMask::from_range(next..)).next_bit(0);
                            } else {
                                P::on_single(z2, 0b0100, ByteMask::from_range(min..), out);
                                break 'merge_level;
                            }
                        }
                        0b1000 => {
                            if let Some(next) = b {
                                P::on_single(z3, 0b1000, ByteMask::from_range(min..next), out);
                                b3 = (m3 & ByteMask::from_range(next..)).next_bit(0);
                            } else {
                                P::on_single(z3, 0b1000, ByteMask::from_range(min..), out);
                                break 'merge_level;
                            }
                        }
                        _ => unreachable!(),
                    };
                } else {
                    // partial overlap (2 or 3)

                    // avoid 16 match arms and duplicated logic
                    if P::descend_on_some_equal(frontier as u64) {
                        out.descend_to_byte(min);

                        if frontier & 0b0001 != 0 {
                            z0.descend_to_byte(min);
                        }
                        if frontier & 0b0010 != 0 {
                            z1.descend_to_byte(min);
                        }
                        if frontier & 0b0100 != 0 {
                            z2.descend_to_byte(min);
                        }
                        if frontier & 0b1000 != 0 {
                            z3.descend_to_byte(min);
                        }

                        // recurse on subset (still using 4-way function, but inactive ones won't match)
                        if (cnt == 2) {
                            let i = frontier.trailing_zeros();
                            let j = (frontier & !(1 << i)).trailing_zeros();
                            match (i, j) {
                                (0, 1) => {
                                    zipper_merge::<P, V, Z0, Z1, Out, A>(z0, z1, out);
                                }
                                (0, 2) => {
                                    zipper_merge::<P, V, Z0, Z2, Out, A>(z0, z2, out);
                                }
                                (0, 3) => {
                                    zipper_merge::<P, V, Z0, Z3, Out, A>(z0, z3, out);
                                }
                                (1, 2) => {
                                    zipper_merge::<P, V, Z1, Z2, Out, A>(z1, z2, out);
                                }
                                (1, 3) => {
                                    zipper_merge::<P, V, Z1, Z3, Out, A>(z1, z3, out);
                                }
                                (2, 3) => {
                                    zipper_merge::<P, V, Z2, Z3, Out, A>(z2, z3, out);
                                }
                                _ => unreachable!(),
                            }
                        } else {
                            // cnt == 3
                            let mut bits = frontier;
                            let i = bits.trailing_zeros();
                            bits &= bits - 1; // trick: it removes the lowest bit set from a bitmask
                            let j = bits.trailing_zeros();
                            bits &= bits - 1;
                            let k = bits.trailing_zeros();
                            match (i, j, k) {
                                (0, 1, 2) => {
                                    zipper_merge3::<P, V, Z0, Z1, Z2, Out, A>(z0, z1, z2, out);
                                }
                                (0, 1, 3) => {
                                    zipper_merge3::<P, V, Z0, Z1, Z3, Out, A>(z0, z1, z3, out);
                                }
                                (0, 2, 3) => {
                                    zipper_merge3::<P, V, Z0, Z2, Z3, Out, A>(z0, z2, z3, out);
                                }
                                (1, 2, 3) => {
                                    zipper_merge3::<P, V, Z1, Z2, Z3, Out, A>(z1, z2, z3, out);
                                }
                                _ => unreachable!(),
                            }
                        }

                        if frontier & 0b0001 != 0 {
                            z0.ascend_byte();
                        }
                        if frontier & 0b0010 != 0 {
                            z1.ascend_byte();
                        }
                        if frontier & 0b0100 != 0 {
                            z2.ascend_byte();
                        }
                        if frontier & 0b1000 != 0 {
                            z3.ascend_byte();
                        }

                        out.ascend_byte();
                    }
                    // then advance
                    if frontier & 0b0001 != 0 {
                        b0 = m0.next_bit(min);
                    }
                    if frontier & 0b0010 != 0 {
                        b1 = m1.next_bit(min);
                    }
                    if frontier & 0b0100 != 0 {
                        b2 = m2.next_bit(min);
                    }
                    if frontier & 0b1000 != 0 {
                        b3 = m3.next_bit(min);
                    }
                }
            } else {
                break 'merge_level;
            }
        }

        // If we are at root and no deeper recursion pending, we're done
        if k == 0 {
            break 'ascend;
        }

        let byte_from = *z0.path().last().expect("non-empty path when k > 0");

        z0.ascend_byte();
        m0 = z0.child_mask();
        b0 = m0.next_bit(byte_from);

        z1.ascend_byte();
        m1 = z1.child_mask();
        b1 = m1.next_bit(byte_from);

        z2.ascend_byte();
        m2 = z2.child_mask();
        b2 = m2.next_bit(byte_from);

        z3.ascend_byte();
        m3 = z3.child_mask();
        b3 = m3.next_bit(byte_from);

        out.ascend_byte();
        k -= 1;
    }
}

/// Performs an ordered N-way join (least upper bound) of radix-256 trie zippers.
///
/// This function merges `N` tries by traversing them simultaneously in lexicographic
/// order, using a zipper-based depth-first traversal. At each node, child edges are
/// treated as sorted streams and merged via a frontier-based strategy:
///
/// - Edges present in only one input are grafted directly,
/// - Shared edges trigger descent and recursive merging,
/// - Fully shared edges use a fast-path descent without recursion.
///
/// Values are combined using the lattice join (`∨`).
///
/// # Complexity
///
/// Let:
/// - `h` be the maximum key length,
/// - `f` be the total frontier size across levels,
/// - `n` be the size of overlapping structure.
///
/// Then:
///
/// - Best case (disjoint): **O(h)**
/// - Typical: **O(h + f)**
/// - Worst case (fully overlapping): **O(n)**
///
/// # Notes
///
/// This is the most general and least pruning-friendly variant:
/// joins preserve information, so most structure must be visited.
///
pub fn zipper_n_join<V, Z, Out, A, const N: usize>(zs: &mut [Z; N], out: &mut Out)
where
    V: Lattice + Clone + Send + Sync + Unpin,
    Z: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
    A: Allocator,
{
    zipper_merge_n_mono::<Join, _, _, _, _, _>(zs, (1 << N) - 1, out);
}

/// Performs an ordered N-way meet (greatest lower bound) of radix-256 trie zippers.
///
/// Only keys present in *all* input tries are retained. Traversal is aggressively
/// pruned: any branch missing from even one input is discarded without descent.
///
/// Values are combined using the lattice meet (`∧`) with the convention that `None ∧ x = None`.
///
/// # Complexity
///
/// Let:
/// - `h` be the maximum key length,
/// - `d` be the size of the common intersection.
///
/// Then:
///
/// - Typical: **O(h + d)**
/// - Often much smaller than join due to early annihilation of branches.
///
/// # Notes
///
/// Compared to join, meet is typically **asymptotically faster** on sparse or
/// partially overlapping inputs, since entire subtries are skipped as soon as
/// any participant is missing.
///
/// In practice, this behaves like intersecting sorted trees with short-circuiting.
///
pub fn zipper_n_meet<V, Z, Out, A, const N: usize>(zs: &mut [Z; N], out: &mut Out)
where
    V: Lattice + Clone + Send + Sync + Unpin,
    Z: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
    A: Allocator,
{
    zipper_merge_n_mono::<Meet, _, _, _, _, _>(zs, (1 << N) - 1, out);
}

/// Performs a left-associative N-way subtraction of radix-256 trie zippers.
///
/// Only the leftmost zipper contributes structure; subsequent zippers remove
/// values and subtries according to lattice subtraction semantics.
///
/// - Left-only branches are grafted directly,
/// - Right-only branches are ignored,
/// - Shared structure triggers descent when required by the policy.
///
/// Values are combined via using distributive
/// subtraction.
///
/// # Complexity
///
/// Let:
/// - `h` be the maximum key length,
/// - `l` be the size of the left-hand trie,
/// - `d` be the overlapping portion.
///
/// Then:
///
/// - Typical: **O(h + l)**
/// - Often significantly faster than join, since traversal is guided primarily
///   by the left-hand structure.
///
/// # Notes
///
/// Subtraction is **structurally biased** toward the leftmost input and benefits
/// from early pruning when right-hand operands eliminate branches.
///
/// This makes it particularly efficient for difference-like workloads,
/// where large portions of the right-hand tries can be skipped entirely.
///
pub fn zipper_n_subtract<V, Z, Out, A, const N: usize>(zs: &mut [Z; N], out: &mut Out)
where
    V: DistributiveLattice + Clone + Send + Sync + Unpin,
    Z: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
    A: Allocator,
{
    zipper_merge_n_mono::<Subtract, _, _, _, _, _>(zs, (1 << N) - 1, out);
}

// small micro-helpers
#[inline(always)]
fn for_each_bit(mut bits: u64, mut f: impl FnMut(usize)) {
    while bits != 0 {
        let i = bits.trailing_zeros() as usize;
        bits &= bits - 1;
        f(i);
    }
}

#[inline]
fn active_bits<const N: usize>(active: u64) -> impl Iterator<Item = usize> {
    (0..N).filter(move |i| (active >> i) & 1 != 0)
}

fn only_active<'a, T, const N: usize>(
    ts: &'a [T; N],
    active: u64,
) -> impl Iterator<Item = (usize, &'a T)> {
    active_bits::<N>(active).map(|i| (i, &ts[i]))
}

#[inline(always)]
fn first_active_mut<T, const N: usize>(ts: &mut [T; N], active: u64) -> &mut T {
    debug_assert_ne!(active, 0);
    let i0 = active.trailing_zeros() as usize;
    &mut ts[i0]
}

// - The function is fully monomorphized over `Z` and `N` and uses a bitmask (`active`)
//   to track participating zippers.
// - Small frontiers (`k ≤ 4`) are dispatched to specialized implementations
//   for improved performance.
// - Requires `N ≤ 64`.
fn zipper_merge_n_mono<P, V, Z, Out, A, const N: usize>(zs: &mut [Z; N], active: u64, out: &mut Out)
where
    V: Clone + Send + Sync + Unpin,
    P: MergePolicy<V> + ValuePolicy<V>,
    A: Allocator,
    Z: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
{
    debug_assert!(N > 0 && N <= 64);
    // LLVM needs to prove: `0 ≤ i < N` But i comes from: `i = bits.trailing_zeros() as usize;`` So the
    // compiler must connect: “this bitmask only contains bits < N”
    assert!(active >> N == 0);

    fn values<'a, V, Z, const N: usize>(
        zs: &'a [Z; N],
        active: u64,
    ) -> impl Iterator<Item = Option<Cow<'a, V>>>
    where
        V: Clone + 'a,
        Z: ZipperValues<V>,
    {
        only_active(zs, active).map(|(_, z)| lift(z.val()))
    }

    fn all_active_share<Z, const N: usize>(zs: &[Z; N], active: u64) -> bool
    where
        Z: ZipperConcrete,
    {
        let mut iter = only_active(zs, active).map(|(_, z)| z.shared_node_id());
        match iter.next() {
            Some(Some(first)) => iter.all(|next| next.is_some_and(|snid| snid == first)),
            _ => false,
        }
    }

    #[inline(always)]
    fn with_k<const K: usize, T, R>(
        xs: &mut [T],
        mut bits: u64,
        f: impl FnOnce([&mut T; K]) -> R,
    ) -> R {
        debug_assert!(bits.count_ones() as usize >= K);

        // collect raw pointers first (safe)
        let mut ptrs: [*mut T; K] = [std::ptr::null_mut(); K];

        let mut i = 0;
        while i < K {
            let idx = bits.trailing_zeros() as usize;
            bits &= bits - 1;
            ptrs[i] = unsafe { xs.as_mut_ptr().add(idx) };
            i += 1;
        }

        // SAFETY:
        // - indices are distinct (bitmask)
        // - derived from same slice

        // should be zero-cost after inlining
        let refs = unsafe { ptrs.map(|p| &mut *p) };

        f(refs)
    }

    // check for node-sharing first
    if all_active_share(zs, active) {
        P::on_id(first_active_mut(zs, active), out);
        return;
    }

    // combine root values
    if let Some(v) = P::combine_n(values(zs, active)) {
        out.set_val(v);
    }

    let mut bytes = [None; N];
    let mut masks = [ByteMask::EMPTY; N];
    for (i, z) in only_active(zs, active) {
        masks[i] = z.child_mask();
        bytes[i] = masks[i].indexed_bit::<true>(0);
    }

    // At each node, the algorithm:
    //
    // - Treats the child edges of all active zippers as sorted byte sequences,
    // - Computes the minimal byte `a` across all inputs,
    // - Forms the *frontier* — the subset of zippers containing `a`,
    // - Dispatches based on frontier size:
    //
    //   - **Full match (`frontier == active`)**
    //     Descends into all zippers without recursion (fast path).
    //
    //   - **Singleton (`|frontier| = 1`)**
    //     Grafts the corresponding subtrie directly into the output.
    //
    //   - **Partial overlap (`1 < |frontier| < N`)**
    //     Optionally descends into the subset, dispatching to specialized
    //     implementations for small arities (`k ≤ 4`) or recursively invoking
    //     this function on the subset.
    //
    // The traversal is performed iteratively using zipper movements
    // (`descend_to_byte` / `ascend_byte`) and an explicit depth counter,
    // avoiding recursion in the common case.
    let mut k = 0;
    debug_assert_ne!(active.count_ones(), 0);
    'ascend: loop {
        'merge_level: loop {
            let mut min = None;
            let mut frontier = 0u64;
            let mut next = None;

            for i in active_bits::<N>(active) {
                if let Some(b) = bytes[i] {
                    match min {
                        None => {
                            min = Some(b);
                            frontier = 1 << i;
                        }
                        Some(m) if b < m => {
                            next = Some(m);
                            min = Some(b);
                            frontier = 1 << i;
                        }
                        Some(m) if b == m => {
                            frontier |= 1 << i;
                        }
                        Some(m) => {
                            next = match next {
                                old @ Some(n) if n <= b => old,
                                _ => Some(b),
                            };
                        }
                    }
                }
            }

            debug_assert!(frontier <= active);

            match min {
                None => {
                    break 'merge_level;
                }
                Some(a) => {
                    // Dispatch

                    // - Case A: full match (frontier == all bits)
                    if frontier == active {
                        out.descend_to_byte(a);

                        // descend and refresh masks and indices
                        for_each_bit(active, |i| {
                            zs[i].descend_to_byte(a);
                        });

                        // check structural sharing first
                        if all_active_share(zs, active) {
                            P::on_id(first_active_mut(zs, active), out);

                            for_each_bit(active, |i| {
                                zs[i].ascend_byte();
                                bytes[i] = masks[i].next_bit(a);
                            });
                            out.ascend_byte();
                            continue 'merge_level;
                        }

                        if let Some(v) = P::combine_n(values(zs, active)) {
                            out.set_val(v);
                        }

                        for_each_bit(active, |i| {
                            masks[i] = zs[i].child_mask();
                            bytes[i] = masks[i].indexed_bit::<true>(0);
                        });

                        k += 1;
                        continue 'merge_level;
                    }

                    let cnt = frontier.count_ones();
                    // - Case B: singleton (|frontier| = 1)
                    if (cnt == 1) {
                        let i = frontier.trailing_zeros() as usize;
                        match next {
                            None => {
                                P::on_single(&mut zs[i], frontier, ByteMask::from_range(a..), out);
                                break 'merge_level;
                            }
                            Some(b) => {
                                P::on_single(&mut zs[i], frontier, ByteMask::from_range(a..b), out);
                                // advance
                                bytes[i] = (masks[i] & ByteMask::from_range(b..)).next_bit(0);
                            }
                        }
                    } else {
                        // - Case C: subset (1 < k < N)
                        if P::descend_on_some_equal(frontier) {
                            out.descend_to_byte(a);
                            match cnt {
                                2 => with_k::<2, _, _>(zs, frontier, |[lhs, rhs]| {
                                    lhs.descend_to_byte(a);
                                    rhs.descend_to_byte(a);

                                    zipper_merge::<P, _, _, _, _, _>(lhs, rhs, out);

                                    rhs.ascend_byte();
                                    lhs.ascend_byte();
                                }),
                                3 => with_k::<3, _, _>(zs, frontier, |[lhs, mid, rhs]| {
                                    lhs.descend_to_byte(a);
                                    mid.descend_to_byte(a);
                                    rhs.descend_to_byte(a);

                                    zipper_merge3::<P, _, _, _, _, _, _>(lhs, mid, rhs, out);

                                    rhs.ascend_byte();
                                    mid.ascend_byte();
                                    lhs.ascend_byte();
                                }),
                                4 => with_k::<4, _, _>(zs, frontier, |[z0, z1, z2, z3]| {
                                    z0.descend_to_byte(a);
                                    z1.descend_to_byte(a);
                                    z2.descend_to_byte(a);
                                    z3.descend_to_byte(a);

                                    zipper_merge4::<P, _, _, _, _, _, _, _>(z0, z1, z2, z3, out);

                                    z3.ascend_byte();
                                    z2.ascend_byte();
                                    z1.ascend_byte();
                                    z0.ascend_byte();
                                }),
                                _ => {
                                    // descend all active in the frontier
                                    for_each_bit(frontier, |i| zs[i].descend_to_byte(a));

                                    // recursive call with SAME array, smaller mask
                                    zipper_merge_n_mono::<P, V, Z, Out, A, N>(zs, frontier, out);

                                    //ascend
                                    for_each_bit(frontier, |i| {
                                        zs[i].ascend_byte();
                                    });
                                }
                            }

                            out.ascend_byte();
                        }

                        // advance indices
                        for_each_bit(frontier, |i| {
                            bytes[i] = masks[i].next_bit(a);
                        });
                    }
                }
            }
        }

        if (k == 0) {
            break 'ascend;
        }
        let byte_from = *first_active_mut(zs, active)
            .path()
            .last()
            .expect("non-empty path when k > 0");

        // ascend
        for_each_bit(active, |i| {
            let mut z = &mut zs[i];
            z.ascend_byte();
            masks[i] = z.child_mask();
            bytes[i] = masks[i].next_bit(byte_from);
        });

        out.ascend_byte();
        k -= 1;
    }
}

fn zipper_merge_dnf<V, Z, Out, A, const M: usize>(clauses: &mut [&mut [Z]; M], out: &mut Out)
where
    V: Lattice + Clone + Send + Sync + Unpin,
    A: Allocator,
    Z: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
    Out: ZipperWriting<V, A>,
{
    #[inline(always)]
    fn clause_mask<Z>(zs: &[Z]) -> ByteMask
    where
        Z: Zipper,
    {
        if zs.is_empty() {
            return ByteMask::EMPTY;
        };
        zs.iter()
            .try_fold(ByteMask::FULL, |mut mask, z| {
                mask &= z.child_mask();
                if mask.is_empty_mask() {
                    None
                } else {
                    Some(mask)
                }
            })
            .unwrap_or(ByteMask::EMPTY)
    }

    #[inline(always)]
    fn clause_value<V, Z>(zs: &[Z]) -> Option<V>
    where
        V: Lattice + Clone,
        Z: ZipperValues<V>,
    {
        Meet::combine_n(zs.iter().map(|z| lift(z.val())))
    }

    fn active_clauses_value<V, Z, const M: usize>(clauses: &[&mut [Z]; M], active: u64) -> Option<V>
    where
        V: Lattice + Clone,
        Z: ZipperValues<V>,
    {
        Join::combine_n(
            only_active(clauses, active).map(|(_, zs)| clause_value(zs).map(Cow::Owned)),
        )
    }

    #[inline(always)]
    fn compute_masks<Z, const M: usize>(
        clauses: &[&mut [Z]; M],
        active: u64,
        clause_masks: &mut [ByteMask; M],
    ) -> ByteMask
    where
        Z: Zipper,
    {
        let mut global = ByteMask::EMPTY;

        for (i, zs) in only_active(clauses, active) {
            let m = clause_mask(zs);

            clause_masks[i] = m;
            global |= m;
        }

        global
    }

    fn zipper_merge_dnf_branch<V, Z, Out, A, const M: usize>(
        clauses: &mut [&mut [Z]; M],
        active: u64,
        out: &mut Out,
    ) where
        V: Lattice + Clone + Send + Sync + Unpin,
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        assert!(active >> M == 0);

        // -------------------------------------------------
        // Single clause fast path
        // -------------------------------------------------
        if active.count_ones() == 1 {
            let single_clause = first_active_mut(clauses, active);
            match single_clause {
                [z0] => {
                    Meet::on_id(z0, out);
                    return;
                }
                [z0, z1] => {
                    zipper_meet(z0, z1, out);
                    return;
                }
                [z0, z1, z2] => {
                    zipper_meet3(z0, z1, z2, out);
                    return;
                }
                [z0, z1, z2, z3] => {
                    zipper_merge4::<Meet, V, Z, Z, Z, Z, Out, A>(z0, z1, z2, z3, out);
                    return;
                }
                _ => {} // do nothing special
            }
        }

        let mut clause_masks = [ByteMask::EMPTY; M];
        let mut depth = 0;

        // -------------------------------------------------
        // Emit values
        // -------------------------------------------------

        if let Some(v) = active_clauses_value(clauses, active) {
            out.set_val(v);
        }
        // -------------------------------------------------
        // Compute clause masks
        // -------------------------------------------------

        let mut global = compute_masks(clauses, active, &mut clause_masks);
        let mut next = global.indexed_bit::<true>(0);
        'descend: loop {
            // -------------------------------------------------
            // Iterate global frontier
            // -------------------------------------------------
            while let Some(byte) = next {
                out.descend_to_byte(byte);

                let mut sub_active = 0u64;

                // descend participating clauses
                for_each_bit(active, |i| {
                    if clause_masks[i].test_bit(byte) {
                        sub_active |= 1 << i;

                        for z in clauses[i].iter_mut() {
                            z.descend_to_byte(byte);
                        }
                    }
                });

                // -------------------------------------------------
                // Tail-descent fast path
                // -------------------------------------------------

                if sub_active == active {
                    depth += 1;

                    if let Some(v) = active_clauses_value(clauses, active) {
                        out.set_val(v);
                    }

                    global = compute_masks(clauses, active, &mut clause_masks);
                    next = global.indexed_bit::<true>(0);
                    continue 'descend;
                }

                // -------------------------------------------------
                // Branching recursion
                // -------------------------------------------------

                zipper_merge_dnf_branch(clauses, sub_active, out);

                // ascend
                for_each_bit(sub_active, |i| {
                    for z in clauses[i].iter_mut() {
                        z.ascend_byte();
                    }
                });

                out.ascend_byte();

                next = global.next_bit(byte);
            }

            // -------------------------------------------------
            // Ascend iterative spine
            // -------------------------------------------------
            if depth == 0 {
                break;
            }

            let byte_from = first_active_mut(clauses, active)
                .first()
                .and_then(|z| z.path().last().copied())
                .expect("non-empty path at depth > 0");

            for_each_bit(active, |i| {
                for z in clauses[i].iter_mut() {
                    z.ascend_byte();
                }
            });

            out.ascend_byte();

            depth -= 1;

            // recompute masks after ascent
            global = compute_masks(clauses, active, &mut clause_masks);
            // resume sibling traversal
            next = global.next_bit(byte_from);
        }
    }

    debug_assert!(M > 0 && M <= 64);
    zipper_merge_dnf_branch(clauses, ((1 << M) - 1), out);
}

// ==================== JOIN ====================

struct Join;
impl<V: Clone + Send + Sync> MergePolicy<V> for Join {
    #[inline]
    fn on_single<Z, Out, A>(z: &mut Z, _mask: u64, range: ByteMask, out: &mut Out)
    where
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        out.graft_masked_branches(z, range, false)
    }

    #[inline]
    fn descend_on_some_equal(_mask: u64) -> bool {
        true
    }

    #[inline]
    fn on_id<Z, Out, A>(z: &mut Z, out: &mut Out)
    where
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        if let Some(v) = z.val() {
            out.set_val(v.clone());
        }
        out.graft(z);
    }
}

impl<V: Lattice + Clone> ValuePolicy<V> for Join {
    fn combine_impl<'a>(l: Option<Cow<'a, V>>, r: Option<Cow<'a, V>>) -> Option<Cow<'a, V>> {
        if let Some(ref lv) = l {
            if let Some(ref rv) = r {
                match lv.pjoin(rv) {
                    AlgebraicResult::None => None,
                    AlgebraicResult::Identity(mask) => {
                        if mask & SELF_IDENT != 0 {
                            l
                        } else {
                            r
                        }
                    }
                    AlgebraicResult::Element(v) => Some(Cow::Owned(v)),
                }
            } else {
                l
            }
        } else {
            r
        }
    }
}

// ==================== MEET ====================

struct Meet;
impl<V: Clone + Send + Sync> MergePolicy<V> for Meet {
    #[inline(always)]
    fn on_single<Z, Out, A>(_z: &mut Z, _mask: u64, _range: ByteMask, _out: &mut Out)
    where
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
    }

    #[inline(always)]
    fn descend_on_some_equal(_mask: u64) -> bool {
        false
    }

    #[inline(always)]
    fn on_id<Z, Out, A>(z: &mut Z, out: &mut Out)
    where
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        if let Some(v) = z.val() {
            out.set_val(v.clone());
        }
        out.graft(z);
    }
}

impl<V: Lattice + Clone> ValuePolicy<V> for Meet {
    #[inline]
    fn combine_impl<'a>(l: Option<Cow<'a, V>>, r: Option<Cow<'a, V>>) -> Option<Cow<'a, V>> {
        l.and_then(|lv| r.and_then(|rv| meet_impl(lv, rv)))
    }

    fn combine3(l: Option<&V>, m: Option<&V>, r: Option<&V>) -> Option<V> {
        l.and_then(|x| {
            m.and_then(|y| {
                r.and_then(|z| {
                    unlift(meet_impl(
                        meet_impl(Cow::Borrowed(x), Cow::Borrowed(y))?,
                        Cow::Borrowed(z),
                    ))
                })
            })
        })
    }

    fn combine4(a: Option<&V>, b: Option<&V>, c: Option<&V>, d: Option<&V>) -> Option<V> {
        a.and_then(|w| {
            b.and_then(|x| {
                c.and_then(|y| {
                    d.and_then(|z| {
                        unlift(meet_impl(
                            meet_impl(
                                meet_impl(Cow::Borrowed(w), Cow::Borrowed(x))?,
                                Cow::Borrowed(y),
                            )?,
                            Cow::Borrowed(z),
                        ))
                    })
                })
            })
        })
    }

    fn combine_n<'a, I>(vals: I) -> Option<V>
    where
        I: Iterator<Item = Option<Cow<'a, V>>>,
        V: 'a,
    {
        let mut it = vals;
        let z = it.next()??;
        unlift(it.try_fold(z, |acc, v| {
            let rv = v?;
            meet_impl(acc, rv)
        }))
    }
}

#[inline]
fn meet_impl<'a, V: Lattice + Clone>(a: Cow<'a, V>, b: Cow<'a, V>) -> Option<Cow<'a, V>> {
    match a.pmeet(&b) {
        AlgebraicResult::None => None,
        AlgebraicResult::Identity(mask) => {
            if mask & SELF_IDENT != 0 {
                Some(a)
            } else {
                Some(b)
            }
        }
        AlgebraicResult::Element(v) => Some(Cow::Owned(v)),
    }
}

// ==================== SUBTRACT ====================

struct Subtract;
impl<V: Clone + Send + Sync> MergePolicy<V> for Subtract {
    #[inline]
    fn on_left_only<Z, Out, A>(z: &mut Z, range: ByteMask, out: &mut Out)
    where
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        out.graft_masked_branches(z, range, false);
    }

    #[inline]
    fn on_right_only<Z, Out, A>(_z: &mut Z, _range: ByteMask, _out: &mut Out)
    where
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
    }

    #[inline]
    fn on_single<Z, Out, A>(z: &mut Z, mask: u64, range: ByteMask, out: &mut Out)
    where
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        if mask == 1 {
            out.graft_masked_branches(z, range, false)
        }
    }

    #[inline]
    fn descend_on_some_equal(mask: u64) -> bool {
        mask & 1 != 0
    }

    #[inline]
    fn on_id<Z, Out, A>(_z: &mut Z, _out: &mut Out)
    where
        A: Allocator,
        Z: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
    }
}

impl<V: DistributiveLattice + Clone> ValuePolicy<V> for Subtract {
    fn combine_impl<'a>(l: Option<Cow<'a, V>>, r: Option<Cow<'a, V>>) -> Option<Cow<'a, V>> {
        l.and_then(|lv| {
            if let Some(rv) = r {
                subtract_impl(lv, rv)
            } else {
                // lhs-only → keep
                Some(lv)
            }
        })
    }

    fn combine_n<'a, I>(vals: I) -> Option<V>
    where
        I: Iterator<Item = Option<Cow<'a, V>>>,
        V: 'a,
    {
        let mut it = vals;
        let z = it.next()??;
        unlift(it.try_fold(z, |acc, v| match v {
            Some(rv) => subtract_impl(acc, rv),
            None => Some(acc),
        }))
    }
}

#[inline]
fn subtract_impl<'a, V: DistributiveLattice + Clone>(
    a: Cow<'a, V>,
    b: Cow<'a, V>,
) -> Option<Cow<'a, V>> {
    match a.psubtract(&b) {
        AlgebraicResult::None => None,
        AlgebraicResult::Identity(mask) => {
            if mask & SELF_IDENT != 0 {
                Some(a)
            } else {
                None
            }
        }
        AlgebraicResult::Element(v) => Some(Cow::Owned(v)),
    }
}

mod zipper_algebra_poly {
    // ==================== Machinery for zipper_merge_n ====================
    use crate as pathmap;
    use crate::PathMap;
    use crate::alloc::Allocator;
    use crate::ring::{DistributiveLattice, Lattice};
    use crate::trie_node::*;
    use crate::zipper::*;
    use pathmap_derive::PolyZipperExplicit;

    #[derive(PolyZipperExplicit)]
    #[poly_zipper_explicit(traits(ZipperMoving, ZipperValues, ZipperConcrete))]
    pub(super) enum SomeMutRefZ<'a, 'trie, 'path, V: Clone + Send + Sync + Unpin, A: Allocator> {
        RZ(&'a mut ReadZipperUntracked<'trie, 'path, V, A>),
        RZT(&'a mut ReadZipperTracked<'trie, 'path, V, A>),
        PZRZ(&'a mut PrefixZipper<'a, ReadZipperUntracked<'trie, 'path, V, A>>),
        PZRZT(&'a mut PrefixZipper<'a, ReadZipperTracked<'trie, 'path, V, A>>),
    }

    impl<V: Clone + Send + Sync + Unpin, A: Allocator> ZipperInfallibleSubtries<V, A>
        for SomeMutRefZ<'_, '_, '_, V, A>
    {
        fn make_map(&self) -> PathMap<V, A> {
            match self {
                SomeMutRefZ::RZ(inner) => inner.make_map(),
                SomeMutRefZ::RZT(inner) => inner.make_map(),
                SomeMutRefZ::PZRZ(inner) => inner.make_map(),
                SomeMutRefZ::PZRZT(inner) => inner.make_map(),
            }
        }

        fn get_trie_ref(&self) -> TrieRef<'_, V, A> {
            match self {
                SomeMutRefZ::RZ(inner) => inner.get_trie_ref(),
                SomeMutRefZ::RZT(inner) => inner.get_trie_ref(),
                SomeMutRefZ::PZRZ(inner) => inner.get_trie_ref(),
                SomeMutRefZ::PZRZT(inner) => inner.get_trie_ref(),
            }
        }

        fn get_focus(&self) -> OpaqueAbstractNodeRef<'_, V, A> {
            match self {
                SomeMutRefZ::RZ(inner) => inner.get_focus(),
                SomeMutRefZ::RZT(inner) => inner.get_focus(),
                SomeMutRefZ::PZRZ(inner) => inner.get_focus(),
                SomeMutRefZ::PZRZT(inner) => inner.get_focus(),
            }
        }

        fn get_focus_at<K: AsRef<[u8]>>(&self, path: K) -> OpaqueAbstractNodeRef<'_, V, A> {
            match self {
                SomeMutRefZ::RZ(inner) => inner.get_focus_at(path),
                SomeMutRefZ::RZT(inner) => inner.get_focus_at(path),
                SomeMutRefZ::PZRZ(inner) => inner.get_focus_at(path),
                SomeMutRefZ::PZRZT(inner) => inner.get_focus_at(path),
            }
        }

        fn try_borrow_focus(&self) -> Option<OpaqueTrieNodeRef<'_, V, A>> {
            match self {
                SomeMutRefZ::RZ(inner) => inner.try_borrow_focus(),
                SomeMutRefZ::RZT(inner) => inner.try_borrow_focus(),
                SomeMutRefZ::PZRZ(inner) => inner.try_borrow_focus(),
                SomeMutRefZ::PZRZT(inner) => inner.try_borrow_focus(),
            }
        }
    }

    pub trait ZipperMergeF<V, Out, A>
    where
        V: Clone + Send + Sync,
        A: Allocator,
        Self: Sized,
    {
        /// Performs an N-way ordered join (least upper bound) of radix-256 trie zippers using a stackless traversal.
        ///
        /// This function generalizes pairwise [`super::zipper_join`] to an arbitrary number of input tries,
        fn join_n(self, out: &mut Out)
        where
            V: Lattice,
        {
            self.merge_n::<super::Join>(out);
        }

        /// Performs an N-way ordered meet(greeatest lower bound) of radix-256 trie zippers using a stackless traversal.
        ///
        /// This function generalizes pairwise [`super::zipper_meet`] to an arbitrary number of input tries,
        fn meet_n(self, out: &mut Out)
        where
            V: Lattice,
        {
            self.merge_n::<super::Meet>(out);
        }

        /// Performs an N-way ordered subtraction (left-associative) of radix-256 trie zippers using a stackless traversal.
        ///
        /// This function generalizes pairwise [`super::zipper_subtract`] to an arbitrary number of input tries,
        fn subtract_n(self, out: &mut Out)
        where
            V: DistributiveLattice,
        {
            self.merge_n::<super::Subtract>(out);
        }

        fn merge_n<P>(self, out: &mut Out)
        where
            P: super::MergePolicy<V> + super::ValuePolicy<V>;
    }

    impl<V, Z1, Z2, Out, A> ZipperMergeF<V, Out, A> for (&mut Z1, &mut Z2)
    where
        V: Clone + Send + Sync,
        A: Allocator,
        Z1: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Z2: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        fn merge_n<P>(mut self, out: &mut Out)
        where
            P: super::MergePolicy<V> + super::ValuePolicy<V>,
        {
            super::zipper_merge::<P, _, _, _, _, _>(self.0, self.1, out);
        }
    }

    impl<V, Z1, Z2, Z3, Out, A> ZipperMergeF<V, Out, A> for (&mut Z1, &mut Z2, &mut Z3)
    where
        V: Clone + Send + Sync,
        A: Allocator,
        Z1: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Z2: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Z3: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        fn merge_n<P>(mut self, out: &mut Out)
        where
            P: super::MergePolicy<V> + super::ValuePolicy<V>,
        {
            super::zipper_merge3::<P, _, _, _, _, _, _>(self.0, self.1, self.2, out);
        }
    }

    impl<V, Z1, Z2, Z3, Z4, Out, A> ZipperMergeF<V, Out, A> for (&mut Z1, &mut Z2, &mut Z3, &mut Z4)
    where
        V: Clone + Send + Sync,
        A: Allocator,
        Z1: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Z2: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Z3: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Z4: ZipperInfallibleSubtries<V, A> + ZipperConcrete + ZipperMoving,
        Out: ZipperWriting<V, A>,
    {
        fn merge_n<P>(mut self, out: &mut Out)
        where
            P: super::MergePolicy<V> + super::ValuePolicy<V>,
        {
            super::zipper_merge4::<P, _, _, _, _, _, _, _>(self.0, self.1, self.2, self.3, out);
        }
    }

    macro_rules! impl_zipper_merge_f {
    ($($Z:ident),+) => {
        impl<'trie, 'path, V, $($Z),+, Out, A> ZipperMergeF<V, Out, A>
            for ($( &mut $Z ),+)
        where
            V: Clone + Send + Sync + Unpin + 'trie,
            A: Allocator + 'trie,
            $(
                for<'x> &'x mut $Z: Into<SomeMutRefZ<'x, 'trie, 'path, V, A>>,
            )+
            Out: ZipperWriting<V, A>,
        {
            fn merge_n<P>(mut self, out: &mut Out)
            where
                P: super::MergePolicy<V> + super::ValuePolicy<V>,
            {
                // destructure the tuple
                let ($( $Z ),+) = self;

                let mut zs = [
                    $( $Z.into() ),+
                ];

                let active: u64 = (1 << zs.len()) - 1;

                super::zipper_merge_n_mono::<P, _, SomeMutRefZ<'_, 'trie, 'path, V, A>, _, _, _>(
                    &mut zs,
                    active,
                    out,
                );
            }
        }
    };
}

    impl_zipper_merge_f!(Z1, Z2, Z3, Z4, Z5);
    impl_zipper_merge_f!(Z1, Z2, Z3, Z4, Z5, Z6);
    impl_zipper_merge_f!(Z1, Z2, Z3, Z4, Z5, Z6, Z7);
    impl_zipper_merge_f!(Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8);
    impl_zipper_merge_f!(Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9);
    impl_zipper_merge_f!(Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10);
    impl_zipper_merge_f!(Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11);
    impl_zipper_merge_f!(Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12);
    impl_zipper_merge_f!(Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13);
    impl_zipper_merge_f!(Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14);
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20,
        Z21
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20,
        Z21, Z22
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20,
        Z21, Z22, Z23
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20,
        Z21, Z22, Z23, Z24
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20,
        Z21, Z22, Z23, Z24, Z25
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20,
        Z21, Z22, Z23, Z24, Z25, Z26
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20,
        Z21, Z22, Z23, Z24, Z25, Z26, Z27
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20,
        Z21, Z22, Z23, Z24, Z25, Z26, Z27, Z28
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20,
        Z21, Z22, Z23, Z24, Z25, Z26, Z27, Z28, Z29
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20,
        Z21, Z22, Z23, Z24, Z25, Z26, Z27, Z28, Z29, Z30
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20,
        Z21, Z22, Z23, Z24, Z25, Z26, Z27, Z28, Z29, Z30, Z31
    );
    impl_zipper_merge_f!(
        Z1, Z2, Z3, Z4, Z5, Z6, Z7, Z8, Z9, Z10, Z11, Z12, Z13, Z14, Z15, Z16, Z17, Z18, Z19, Z20,
        Z21, Z22, Z23, Z24, Z25, Z26, Z27, Z28, Z29, Z30, Z31, Z32
    );

    /// Performs an N-ary zipper join by borrowing all inputs mutably
    /// and forwarding them to [`ZipperMergeF::join_n`].
    ///
    /// # Example
    /// ```ignore
    /// zipper_join_n!(z1, z2, z3 => out);
    /// ```
    ///
    /// Expands roughly to:
    /// ```ignore
    /// (&mut z1, &mut z2, &mut z3).join_n(&mut out)
    /// ```
    ///
    /// # See also
    /// [`ZipperMergeF::join_n`]
    #[macro_export]
    macro_rules! zipper_join_n {
    ( $($z:ident),+ => $out:ident ) => {{
        ( $( &mut $z ),+ ).join_n(&mut $out)
    }};
}

    /// Performs an N-ary zipper meet by borrowing all inputs mutably
    /// and forwarding them to [`ZipperMergeF::meet_n`].
    ///
    /// # Example
    /// ```ignore
    /// zipper_meet_n!(z1, z2, z3 => out);
    /// ```
    ///
    /// Expands roughly to:
    /// ```ignore
    /// (&mut z1, &mut z2, &mut z3).meet_n(&mut out)
    /// ```
    ///
    /// # See also
    /// [`ZipperMergeF::meet_n`]
    #[macro_export]
    macro_rules! zipper_meet_n {
    ( $($z:ident),+ => $out:ident ) => {{
        ( $( &mut $z ),+ ).meet_n(&mut $out)
    }};
}

    /// Performs an N-ary zipper subtract by borrowing all inputs mutably
    /// and forwarding them to [`ZipperMergeF::subtract_n`].
    ///
    /// # Example
    /// ```ignore
    /// zipper_subtract_n!(z1, z2, z3 => out);
    /// ```
    ///
    /// Expands roughly to:
    /// ```ignore
    /// (&mut z1, &mut z2, &mut z3).subtract_n(&mut out)
    /// ```
    ///
    /// # See also
    /// [`ZipperMergeF::subtract_n`]
    #[macro_export]
    macro_rules! zipper_subtract_n {
    ( $($z:ident),+ => $out:ident ) => {{
        ( $( &mut $z ),+ ).subtract_n(&mut $out)
    }};
}
}

#[cfg(test)]
mod tests {
    use crate::{
        PathMap,
        zipper::{
            ReadZipperUntracked, WriteZipperUntracked, ZipperInfallibleSubtries, ZipperMoving,
            ZipperWriting,
        },
    };
    use std::borrow::Borrow;

    type Paths = &'static [(&'static [u8], u64)];
    type BinaryTest = (Paths, Paths);
    type TernaryTest = (Paths, Paths, Paths);
    type NaryTest = [Paths; N];
    const N: usize = 6;

    fn mk_binary_test(test: &BinaryTest) -> (PathMap<u64>, PathMap<u64>) {
        (PathMap::from_iter(test.0), PathMap::from_iter(test.1))
    }

    fn mk_ternary_test(test: &TernaryTest) -> (PathMap<u64>, PathMap<u64>, PathMap<u64>) {
        (
            PathMap::from_iter(test.0),
            PathMap::from_iter(test.1),
            PathMap::from_iter(test.2),
        )
    }

    fn mk_nary_test(test: &NaryTest) -> [PathMap<u64>; N] {
        test.map(PathMap::from_iter)
    }

    fn check2<
        'x,
        T: IntoIterator<Item = &'x (&'x [u8], u64)>,
        F: for<'a> FnOnce(
            &mut ReadZipperUntracked<'a, 'x, u64>,
            &mut ReadZipperUntracked<'a, 'x, u64>,
            &mut WriteZipperUntracked<'a, 'x, u64>,
        ),
    >(
        test: &BinaryTest,
        expected: T,
        op: F,
    ) {
        let (left, right) = mk_binary_test(test);

        let mut result = PathMap::new();

        let mut lhs = left.read_zipper();
        let mut rhs = right.read_zipper();
        let mut out = result.write_zipper();

        op(&mut lhs, &mut rhs, &mut out);

        assert_trie(expected.into_iter().copied(), result);
    }

    fn check3<
        'x,
        T: IntoIterator<Item = &'x (&'x [u8], u64)>,
        F: for<'a> FnOnce(
            &mut ReadZipperUntracked<'a, 'x, u64>,
            &mut ReadZipperUntracked<'a, 'x, u64>,
            &mut ReadZipperUntracked<'a, 'x, u64>,
            &mut WriteZipperUntracked<'a, 'x, u64>,
        ),
    >(
        test: &TernaryTest,
        expected: T,
        op: F,
    ) {
        let (left, middle, right) = mk_ternary_test(test);

        let mut result = PathMap::new();

        let mut lhs = left.read_zipper();
        let mut mid = middle.read_zipper();
        let mut rhs = right.read_zipper();
        let mut out = result.write_zipper();

        op(&mut lhs, &mut mid, &mut rhs, &mut out);

        assert_trie(expected.into_iter().copied(), result);
    }

    fn checkn<
        'x,
        T: IntoIterator<Item = &'x (&'x [u8], u64)>,
        F: for<'a> FnOnce([ReadZipperUntracked<'a, 'x, u64>; N], WriteZipperUntracked<'a, 'x, u64>),
    >(
        test: &NaryTest,
        expected: T,
        op: F,
    ) {
        let path_maps = mk_nary_test(test);

        let mut result = PathMap::new();

        op(
            path_maps.each_ref().map(PathMap::read_zipper),
            result.write_zipper(),
        );

        assert_trie(expected.into_iter().copied(), result);
    }

    fn assert_trie<T: IntoIterator<Item = (P, u64)>, P: Borrow<[u8]>>(
        expected: T,
        result: PathMap<u64>,
    ) {
        let mut result_copy = result.clone();

        for (expected_path, expected_val) in expected {
            assert!(
                result.path_exists_at(expected_path.borrow()),
                "Path {:#?} does NOT exist in {result:#?}",
                expected_path.borrow()
            );
            let actual_val = result.get_val_at(expected_path.borrow()).copied();
            assert_eq!(
                actual_val,
                Some(expected_val),
                "Value at {:#?}",
                expected_path.borrow()
            );

            result_copy.remove_val_at(expected_path.borrow(), true);
        }

        assert!(
            result_copy.is_empty(),
            "Paths unaccounted for are present in the result: {result_copy:#?}"
        );
    }

    const DISJOINT_PATHS: BinaryTest = (
        &[
            (&[0x00], 0),
            (&[0x00, 0x00], 1),
            (&[0x00, 0x00, 0x00], 2),
            (&[0x00, 0x00, 0x00, 0x00], 3),
        ],
        &[
            (&[0xFF], 0),
            (&[0xFF, 0x00], 1),
            (&[0xFF, 0x00, 0x00], 2),
            (&[0xFF, 0x00, 0x00, 0x00], 3),
        ],
    );

    const DISJOINT_PATHS_3: TernaryTest = (
        &[
            (&[0x00], 0),
            (&[0x00, 0x00], 1),
            (&[0x00, 0x00, 0x00], 2),
            (&[0x00, 0x00, 0x00, 0x00], 3),
        ],
        &[
            (&[0xF0], 0),
            (&[0xF0, 0x00], 1),
            (&[0xF0, 0x00, 0x00], 2),
            (&[0xF0, 0x00, 0x00, 0x00], 3),
        ],
        &[
            (&[0xFF], 0),
            (&[0xFF, 0x00], 1),
            (&[0xFF, 0x00, 0x00], 2),
            (&[0xFF, 0x00, 0x00, 0x00], 3),
        ],
    );

    const DISJOINT_PATHS_N: NaryTest = [
        &[
            (&[0x00], 0),
            (&[0x00, 0x00], 1),
            (&[0x00, 0x00, 0x00], 2),
            (&[0x00, 0x00, 0x00, 0x00], 3),
        ],
        &[
            (&[0xC0], 0),
            (&[0xC0, 0x00], 1),
            (&[0xC0, 0x00, 0x00], 2),
            (&[0xC0, 0x00, 0x00, 0x00], 3),
        ],
        &[
            (&[0xD0], 0),
            (&[0xD0, 0x00], 1),
            (&[0xD0, 0x00, 0x00], 2),
            (&[0xD0, 0x00, 0x00, 0x00], 3),
        ],
        &[
            (&[0xE0], 0),
            (&[0xE0, 0x00], 1),
            (&[0xE0, 0x00, 0x00], 2),
            (&[0xE0, 0x00, 0x00, 0x00], 3),
        ],
        &[
            (&[0xF0], 0),
            (&[0xF0, 0x00], 1),
            (&[0xF0, 0x00, 0x00], 2),
            (&[0xF0, 0x00, 0x00, 0x00], 3),
        ],
        &[
            (&[0xFF], 0),
            (&[0xFF, 0x00], 1),
            (&[0xFF, 0x00, 0x00], 2),
            (&[0xFF, 0x00, 0x00, 0x00], 3),
        ],
    ];

    const PATHS_WITH_SHARED_PREFIX: BinaryTest = (
        &[(b"aaaaa0", 0), (b"bbbbbbbb0", 1)],
        &[(b"aaaaa1", 0), (b"bbbbb1", 1), (b"bbbbbbbb1", 2)],
    );

    const PATHS_WITH_SHARED_PREFIX_3: TernaryTest = (
        &[(b"aaaaa0", 0), (b"bbbbbbbb0", 1)],
        &[(b"aaaaa1", 0), (b"bbbbb1", 1), (b"bbbbbbbb1", 2)],
        &[(b"aaaaa2", 0), (b"bbbbb2", 1), (b"bbbbbbbb2", 2)],
    );

    const PATHS_WITH_SHARED_PREFIX_N: NaryTest = [
        &[(b"aaaaa0", 0), (b"bbbbbbbb0", 1)],
        &[(b"aaaaa1", 0), (b"bbbbb1", 1), (b"bbbbbbbb1", 2)],
        &[(b"aaaaa2", 0), (b"bbbbb2", 1), (b"bbbbbbbb2", 2)],
        &[(b"aaaaa3", 0), (b"bbbbb3", 1), (b"bbbbbbbb3", 2)],
        &[(b"aaaaa4", 0), (b"bbbbb4", 1), (b"bbbbbbbb4", 2)],
        &[(b"aaaaa5", 0), (b"bbbbb5", 1), (b"bbbbbbbb5", 2)],
    ];

    const INTERLEAVING_PATHS: BinaryTest = (
        &[(&[0], 0), (&[2], 1), (&[4], 2), (&[6], 3)],
        &[(&[1], 0), (&[3], 1), (&[5], 2), (&[7], 3)],
    );

    const INTERLEAVING_PATHS_3: TernaryTest = (
        &[(&[0], 0), (&[3], 1), (&[6], 2), (&[9], 3)],
        &[(&[1], 0), (&[4], 1), (&[7], 2), (&[10], 3)],
        &[(&[2], 0), (&[5], 1), (&[8], 2), (&[11], 3)],
    );

    const INTERLEAVING_PATHS_N: NaryTest = [
        &[(&[0], 0), (&[6], 1), (&[12], 2), (&[18], 3)],
        &[(&[1], 0), (&[7], 1), (&[13], 2), (&[19], 3)],
        &[(&[2], 0), (&[8], 1), (&[14], 2), (&[20], 3)],
        &[(&[3], 0), (&[9], 1), (&[15], 2), (&[21], 3)],
        &[(&[4], 0), (&[10], 1), (&[16], 2), (&[22], 3)],
        &[(&[5], 0), (&[11], 1), (&[17], 2), (&[23], 3)],
    ];

    const ONE_SIDED_PATHS: BinaryTest = (
        &[
            (&[0x00], 0),
            (&[0x00, 0x01], 1),
            (&[0x00, 0x01, 0x02], 2),
            (&[0x00, 0x01, 0x02, 0x03], 3),
            (&[0x01], 4),
            (&[0x01, 0x02], 5),
            (&[0x01, 0x02, 0x03], 6),
            (&[0x01, 0x02, 0x03, 0x04], 7),
            (&[0x01, 0x02, 0x03, 0x04, 0x05], 8),
            (&[0x01, 0x02, 0x03, 0x04, 0x05, 0x06], 9),
        ],
        &[
            (&[0x00], 0),
            (&[0x00, 0x01, 0x02, 0x03], 1),
            (&[0x01, 0x02, 0x03, 0x04, 0x05], 2),
        ],
    );

    const ONE_SIDED_PATHS_3: TernaryTest = (
        &[
            (&[0x00], 0),
            (&[0x00, 0x01], 1),
            (&[0x00, 0x01, 0x02], 2),
            (&[0x00, 0x01, 0x02, 0x03], 3),
            (&[0x01], 4),
            (&[0x01, 0x02], 5),
            (&[0x01, 0x02, 0x03], 6),
            (&[0x01, 0x02, 0x03, 0x04], 7),
            (&[0x01, 0x02, 0x03, 0x04, 0x05], 8),
            (&[0x01, 0x02, 0x03, 0x04, 0x05, 0x06], 9),
        ],
        &[
            (&[0x00], 0),
            (&[0x00, 0x01, 0x02, 0x03], 1),
            (&[0x01, 0x02, 0x03, 0x04, 0x05], 2),
        ],
        &[(&[0x00], 0), (&[0x00, 0x01, 0x02], 1)],
    );

    const ONE_SIDED_PATHS_N: NaryTest = [
        &[
            (&[0x00], 0),
            (&[0x00, 0x01], 1),
            (&[0x00, 0x01, 0x02], 2),
            (&[0x00, 0x01, 0x02, 0x03], 3),
            (&[0x01], 4),
            (&[0x01, 0x02], 5),
            (&[0x01, 0x02, 0x03], 6),
            (&[0x01, 0x02, 0x03, 0x04], 7),
            (&[0x01, 0x02, 0x03, 0x04, 0x05], 8),
            (&[0x01, 0x02, 0x03, 0x04, 0x05, 0x06], 9),
        ],
        &[
            (&[0x00], 0),
            (&[0x00, 0x01, 0x02, 0x03], 1),
            (&[0x01, 0x02, 0x03, 0x04, 0x05], 2),
        ],
        &[(&[0x00], 0), (&[0x00, 0x01, 0x02], 1)],
        &[(&[0x01], 4)],
        &[(&[0x01], 4), (&[0x01, 0x02], 5)],
        &[(&[0x01], 4), (&[0x01, 0x02, 0x03], 5)],
    ];

    const ALMOST_IDENTICAL_PATHS: BinaryTest = (
        &[
            (b"abcdefg", 0),
            (b"hijklmnop", 1),
            (b"qrstuwvxyz", 2),
            (b"0", 3),
            (b"1", 4),
            (b"2", 5),
            (b"3", 6),
            (b"4", 7),
            (b"5", 8),
            (b"6789", 9),
        ],
        &[
            (b"abcdefg", 0),
            (b"qrstuwvxyz", 2),
            (b"0", 3),
            (b"1", 4),
            (b"4", 7),
            (b"5", 8),
            (b"6789", 9),
        ],
    );

    const ALMOST_IDENTICAL_PATHS_3: TernaryTest = (
        &[
            (b"abcdefg", 0),
            (b"hijklmnop", 1),
            (b"qrstuwvxyz", 2),
            (b"0", 3),
            (b"1", 4),
            (b"2", 5),
            (b"3", 6),
            (b"4", 7),
            (b"5", 8),
            (b"6789", 9),
        ],
        &[
            (b"abcdefg", 0),
            (b"qrstuwvxyz", 2),
            (b"0", 3),
            (b"1", 4),
            (b"4", 7),
            (b"5", 8),
            (b"6789", 9),
        ],
        &[
            (b"abcdefg", 0),
            (b"hijklmnop", 1),
            (b"1", 4),
            (b"2", 5),
            (b"3", 6),
            (b"4", 7),
            (b"5", 8),
        ],
    );

    const ALMOST_IDENTICAL_PATHS_N: NaryTest = [
        &[
            (b"abcdefg", 0),
            (b"hijklmnop", 1),
            (b"qrstuwvxyz", 2),
            (b"0", 3),
            (b"1", 4),
            (b"2", 5),
            (b"3", 6),
            (b"4", 7),
            (b"5", 8),
            (b"6789", 9),
        ],
        &[
            (b"abcdefg", 0),
            (b"qrstuwvxyz", 2),
            (b"0", 3),
            (b"1", 4),
            (b"4", 7),
            (b"5", 8),
            (b"6789", 9),
        ],
        &[
            (b"abcdefg", 0),
            (b"hijklmnop", 1),
            (b"1", 4),
            (b"2", 5),
            (b"3", 6),
            (b"4", 7),
            (b"5", 8),
        ],
        &[
            (b"hijklmnop", 1),
            (b"1", 4),
            (b"2", 5),
            (b"3", 6),
            (b"4", 7),
            (b"5", 8),
        ],
        &[
            (b"hijklmnop", 1),
            (b"1", 4),
            (b"2", 5),
            (b"3", 6),
            (b"4", 7),
            (b"5", 8),
        ],
        &[
            (b"hijklmnop", 1),
            (b"1", 4),
            (b"2", 5),
            (b"3", 6),
            (b"4", 7),
            (b"5", 8),
        ],
    ];

    const LHS_EMPTY: BinaryTest = (&[], &[(&[1], 0), (&[2], 1)]);
    const LHS_EMPTY_3: TernaryTest = (&[], &[(&[1], 0), (&[2], 1)], &[(&[3], 0), (&[4], 1)]);
    const LHS_EMPTY_N: NaryTest = [
        &[],
        &[(&[1], 0), (&[2], 1)],
        &[(&[3], 0), (&[4], 1)],
        &[(&[5], 0)],
        &[(&[6], 0)],
        &[(&[7], 0), (&[8], 1)],
    ];

    const RHS_EMPTY: BinaryTest = (&[(&[1], 0), (&[2], 1)], &[]);
    const RHS_EMPTY_3: TernaryTest = (&[(&[1], 0), (&[2], 1)], &[(&[3], 0), (&[4], 1)], &[]);
    const RHS_EMPTY_N: NaryTest = [
        &[(&[1], 0), (&[2], 1)],
        &[(&[3], 0), (&[4], 1)],
        &[(&[5], 0)],
        &[(&[6], 0)],
        &[(&[7], 0), (&[8], 1)],
        &[],
    ];

    const MID_EMPTY: TernaryTest = (&[(&[1], 0), (&[2], 1)], &[], &[(&[3], 0), (&[4], 1)]);
    const MID_EMPTY_N: NaryTest = [
        &[(&[1], 0), (&[2], 1)],
        &[(&[3], 0), (&[4], 1)],
        &[],
        &[(&[5], 0)],
        &[(&[6], 0)],
        &[(&[7], 0), (&[8], 1)],
    ];

    const PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN: BinaryTest = (
        &[
            (&[1, 2, 3], 0),
            (&[1, 2, 3, 4], 1),
            (&[1, 2, 3, 10, 11, 12], 2),
        ],
        &[
            (&[1, 2, 3], 10),
            (&[1, 2, 3, 5], 11),
            (&[1, 2, 3, 10, 11, 0], 12),
        ],
    );

    const PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN_3: TernaryTest = (
        &[
            (&[1, 2, 3], 0),
            (&[1, 2, 3, 4], 1),
            (&[1, 2, 3, 10, 11, 12], 2),
        ],
        &[
            (&[1, 2, 3], 10),
            (&[1, 2, 3, 5], 11),
            (&[1, 2, 3, 10, 11, 0], 12),
        ],
        &[
            (&[1, 2, 3], 20),
            (&[1, 2, 3, 6], 21),
            (&[1, 2, 3, 10, 11, 1], 22),
        ],
    );

    const PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN_N: NaryTest = [
        &[
            (&[1, 2, 3], 0),
            (&[1, 2, 3, 4], 1),
            (&[1, 2, 3, 10, 11, 12], 2),
        ],
        &[
            (&[1, 2, 3], 10),
            (&[1, 2, 3, 5], 11),
            (&[1, 2, 3, 10, 11, 0], 12),
        ],
        &[
            (&[1, 2, 3], 20),
            (&[1, 2, 3, 6], 21),
            (&[1, 2, 3, 10, 11, 1], 22),
        ],
        &[
            (&[1, 2, 3], 30),
            (&[1, 2, 3, 7], 31),
            (&[1, 2, 3, 10, 11, 2], 32),
        ],
        &[
            (&[1, 2, 3], 40),
            (&[1, 2, 3, 8], 41),
            (&[1, 2, 3, 10, 11, 3], 42),
        ],
        &[
            (&[1, 2, 3], 50),
            (&[1, 2, 3, 9], 51),
            (&[1, 2, 3, 10, 11, 4], 52),
        ],
    ];

    const ZIGZAG_PATHS: BinaryTest = (
        &[
            (&[1, 1], 0),
            (&[2], 1),
            (&[2, 1], 2),
            (&[3], 3),
            (&[3, 2, 1], 4),
            (&[4], 4),
            (&[4, 3, 2, 1], 5),
        ],
        &[
            (&[1], 0),
            (&[1, 2], 1),
            (&[2, 1], 2),
            (&[3], 3),
            (&[3, 4], 4),
            (&[4, 3], 5),
        ],
    );

    const ZIGZAG_PATHS_3: TernaryTest = (
        &[
            (&[1, 1], 0),
            (&[2], 1),
            (&[2, 1], 2),
            (&[3], 3),
            (&[3, 2, 1], 4),
            (&[4], 4),
            (&[4, 3, 2, 1], 5),
        ],
        &[
            (&[1], 0),
            (&[1, 2], 1),
            (&[2, 1], 2),
            (&[3], 3),
            (&[3, 4], 4),
            (&[4, 3], 5),
        ],
        &[
            (&[1], 0),
            (&[2], 1),
            (&[2, 1], 2),
            (&[3, 2, 1, 0], 3),
            (&[4, 3, 2, 1, 0], 4),
            (&[4, 3, 2, 1], 5),
        ],
    );

    const PATHS_WITH_ROOT_VALS_AND_CHILDREN: BinaryTest =
        (&[(&[], 1), (&[1], 10)], &[(&[], 2), (&[1], 20)]);

    const PATHS_WITH_ROOT_VALS_AND_CHILDREN_3: TernaryTest = (
        &[(&[], 1), (&[1], 10)],
        &[(&[], 2), (&[1], 20)],
        &[(&[], 3), (&[1], 30)],
    );

    const PATHS_WITH_ROOT_VALS_AND_CHILDREN_N: NaryTest = [
        &[(&[], 1), (&[1], 10), (&[2], 110)],
        &[(&[], 2), (&[1], 20), (&[2], 120)],
        &[(&[], 3), (&[1], 30), (&[2], 130)],
        &[(&[], 4), (&[1], 40), (&[2], 140)],
        &[(&[], 5), (&[1], 50), (&[2], 150)],
        &[(&[], 6), (&[1], 60), (&[2], 160)],
    ];

    mod join {
        use super::*;
        use crate::experimental::zipper_algebra::{
            ZipperAlgebraExt, ZipperMergeF, zipper_join, zipper_join3,
        };
        use crate::zipper_join_n;

        #[test]
        fn test_disjoint() {
            check2(
                &DISJOINT_PATHS,
                &[DISJOINT_PATHS.0, DISJOINT_PATHS.1].concat(),
                |lhs, rhs, out| lhs.join(rhs, out),
            );
        }

        #[test]
        fn test_disjoint3() {
            check3(
                &DISJOINT_PATHS_3,
                &[DISJOINT_PATHS_3.0, DISJOINT_PATHS_3.1, DISJOINT_PATHS_3.2].concat(),
                |lhs, mid, rhs, out| zipper_join3(lhs, mid, rhs, out),
            );
        }

        #[test]
        fn test_disjoint_n() {
            checkn(
                &DISJOINT_PATHS_N,
                &[
                    DISJOINT_PATHS_N[0],
                    DISJOINT_PATHS_N[1],
                    DISJOINT_PATHS_N[2],
                    DISJOINT_PATHS_N[3],
                    DISJOINT_PATHS_N[4],
                    DISJOINT_PATHS_N[5],
                ]
                .concat(),
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_join_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_deep_shared_prefix_then_split() {
            check2(
                &PATHS_WITH_SHARED_PREFIX,
                &[PATHS_WITH_SHARED_PREFIX.0, PATHS_WITH_SHARED_PREFIX.1].concat(),
                |lhs, rhs, out| lhs.join(rhs, out),
            );
        }

        #[test]
        fn test_deep_shared_prefix_then_split3() {
            check3(
                &PATHS_WITH_SHARED_PREFIX_3,
                &[
                    PATHS_WITH_SHARED_PREFIX_3.0,
                    PATHS_WITH_SHARED_PREFIX_3.1,
                    PATHS_WITH_SHARED_PREFIX_3.2,
                ]
                .concat(),
                |lhs, mid, rhs, out| zipper_join3(lhs, mid, rhs, out),
            );
        }

        #[test]
        fn test_deep_shared_prefix_then_split_n() {
            checkn(
                &PATHS_WITH_SHARED_PREFIX_N,
                &[
                    PATHS_WITH_SHARED_PREFIX_N[0],
                    PATHS_WITH_SHARED_PREFIX_N[1],
                    PATHS_WITH_SHARED_PREFIX_N[2],
                    PATHS_WITH_SHARED_PREFIX_N[3],
                    PATHS_WITH_SHARED_PREFIX_N[4],
                    PATHS_WITH_SHARED_PREFIX_N[5],
                ]
                .concat(),
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_join_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_interleaving_paths() {
            check2(
                &INTERLEAVING_PATHS,
                &[INTERLEAVING_PATHS.0, INTERLEAVING_PATHS.1].concat(),
                |lhs, rhs, out| lhs.join(rhs, out),
            );
        }

        #[test]
        fn test_interleaving_paths3() {
            check3(
                &INTERLEAVING_PATHS_3,
                &[
                    INTERLEAVING_PATHS_3.0,
                    INTERLEAVING_PATHS_3.1,
                    INTERLEAVING_PATHS_3.2,
                ]
                .concat(),
                |lhs, mid, rhs, out| zipper_join3(lhs, mid, rhs, out),
            );
        }

        #[test]
        fn test_interleaving_paths_n() {
            checkn(
                &INTERLEAVING_PATHS_N,
                &[
                    INTERLEAVING_PATHS_N[0],
                    INTERLEAVING_PATHS_N[1],
                    INTERLEAVING_PATHS_N[2],
                    INTERLEAVING_PATHS_N[3],
                    INTERLEAVING_PATHS_N[4],
                    INTERLEAVING_PATHS_N[5],
                ]
                .concat(),
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_join_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_one_side_empty_at_many_levels() {
            check2(&ONE_SIDED_PATHS, ONE_SIDED_PATHS.0, |lhs, rhs, out| {
                lhs.join(rhs, out)
            });
        }

        #[test]
        fn test_one_side_empty_at_many_levels3() {
            check3(
                &ONE_SIDED_PATHS_3,
                ONE_SIDED_PATHS_3.0,
                |lhs, mid, rhs, out| zipper_join3(lhs, mid, rhs, out),
            );
        }

        #[test]
        fn test_one_side_empty_at_many_levels_n() {
            checkn(
                &ONE_SIDED_PATHS_N,
                ONE_SIDED_PATHS_N[0],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_join_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_almost_identical_paths() {
            check2(
                &ALMOST_IDENTICAL_PATHS,
                ALMOST_IDENTICAL_PATHS.0,
                |lhs, rhs, out| lhs.join(rhs, out),
            );
        }

        #[test]
        fn test_almost_identical_paths3() {
            check3(
                &ALMOST_IDENTICAL_PATHS_3,
                ALMOST_IDENTICAL_PATHS_3.0,
                |lhs, mid, rhs, out| zipper_join3(lhs, mid, rhs, out),
            );
        }

        #[test]
        fn test_almost_identical_paths_n() {
            checkn(
                &ALMOST_IDENTICAL_PATHS_N,
                ALMOST_IDENTICAL_PATHS_N[0],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_join_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_one_side_empty() {
            check2(&LHS_EMPTY, LHS_EMPTY.1, |lhs, rhs, out| lhs.join(rhs, out));
            check2(&RHS_EMPTY, RHS_EMPTY.0, |lhs, rhs, out| lhs.join(rhs, out));
        }

        #[test]
        fn test_one_side_empty3() {
            check3(
                &LHS_EMPTY_3,
                &[LHS_EMPTY_3.1, LHS_EMPTY_3.2].concat(),
                |lhs, mid, rhs, out| zipper_join3(lhs, mid, rhs, out),
            );
            check3(
                &MID_EMPTY,
                &[MID_EMPTY.0, MID_EMPTY.2].concat(),
                |lhs, mid, rhs, out| zipper_join3(lhs, mid, rhs, out),
            );
            check3(
                &RHS_EMPTY_3,
                &[RHS_EMPTY_3.0, RHS_EMPTY_3.1].concat(),
                |lhs, mid, rhs, out| zipper_join3(lhs, mid, rhs, out),
            );
        }

        #[test]
        fn test_one_side_empty_n() {
            checkn(
                &LHS_EMPTY_N,
                &[
                    LHS_EMPTY_N[1],
                    LHS_EMPTY_N[2],
                    LHS_EMPTY_N[3],
                    LHS_EMPTY_N[4],
                    LHS_EMPTY_N[5],
                ]
                .concat(),
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_join_n!(z0, z1, z2, z3, z4, z5 => out),
            );
            checkn(
                &MID_EMPTY_N,
                &[
                    MID_EMPTY_N[0],
                    MID_EMPTY_N[1],
                    MID_EMPTY_N[3],
                    MID_EMPTY_N[4],
                    MID_EMPTY_N[5],
                ]
                .concat(),
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_join_n!(z0, z1, z2, z3, z4, z5 => out),
            );
            checkn(
                &RHS_EMPTY_N,
                &[
                    RHS_EMPTY_N[0],
                    RHS_EMPTY_N[1],
                    RHS_EMPTY_N[2],
                    RHS_EMPTY_N[3],
                    RHS_EMPTY_N[4],
                ]
                .concat(),
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_join_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_exact_overlap_divergent_subtries() {
            let expected: Paths = &[
                (&[1, 2, 3], 0),
                (&[1, 2, 3, 4], 1),
                (&[1, 2, 3, 5], 11),
                (&[1, 2, 3, 10, 11, 0], 12),
                (&[1, 2, 3, 10, 11, 12], 2),
            ];
            check2(
                &PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN,
                expected,
                |lhs, rhs, out| lhs.join(rhs, out),
            );
        }

        #[test]
        fn test_exact_overlap_divergent_subtries3() {
            let expected: Paths = &[
                (&[1, 2, 3], 0),
                (&[1, 2, 3, 4], 1),
                (&[1, 2, 3, 5], 11),
                (&[1, 2, 3, 6], 21),
                (&[1, 2, 3, 10, 11, 0], 12),
                (&[1, 2, 3, 10, 11, 1], 22),
                (&[1, 2, 3, 10, 11, 12], 2),
            ];
            check3(
                &PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN_3,
                expected,
                |lhs, mid, rhs, out| zipper_join3(lhs, mid, rhs, out),
            );
        }

        #[test]
        fn test_exact_overlap_divergent_subtries_n() {
            let expected: Paths = &[
                (&[1, 2, 3], 0),
                (&[1, 2, 3, 4], 1),
                (&[1, 2, 3, 5], 11),
                (&[1, 2, 3, 6], 21),
                (&[1, 2, 3, 7], 31),
                (&[1, 2, 3, 8], 41),
                (&[1, 2, 3, 9], 51),
                (&[1, 2, 3, 10, 11, 0], 12),
                (&[1, 2, 3, 10, 11, 1], 22),
                (&[1, 2, 3, 10, 11, 2], 32),
                (&[1, 2, 3, 10, 11, 3], 42),
                (&[1, 2, 3, 10, 11, 4], 52),
                (&[1, 2, 3, 10, 11, 12], 2),
            ];
            checkn(
                &PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN_N,
                expected,
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_join_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_zigzag() {
            check2(
                &ZIGZAG_PATHS,
                &[ZIGZAG_PATHS.0, ZIGZAG_PATHS.1].concat(),
                |lhs, rhs, out| lhs.join(rhs, out),
            );
        }

        #[test]
        fn test_zigzag3() {
            check3(
                &ZIGZAG_PATHS_3,
                &[ZIGZAG_PATHS_3.0, ZIGZAG_PATHS_3.1, ZIGZAG_PATHS_3.2].concat(),
                |lhs, mid, rhs, out| zipper_join3(lhs, mid, rhs, out),
            );
        }

        #[test]
        fn test_root_values() {
            check2(
                &PATHS_WITH_ROOT_VALS_AND_CHILDREN,
                PATHS_WITH_ROOT_VALS_AND_CHILDREN.0,
                |lhs, rhs, out| lhs.join(rhs, out),
            );
        }

        #[test]
        fn test_root_values3() {
            check3(
                &PATHS_WITH_ROOT_VALS_AND_CHILDREN_3,
                PATHS_WITH_ROOT_VALS_AND_CHILDREN_3.0,
                |lhs, mid, rhs, out| zipper_join3(lhs, mid, rhs, out),
            );
        }

        #[test]
        fn test_root_values_n() {
            checkn(
                &PATHS_WITH_ROOT_VALS_AND_CHILDREN_N,
                PATHS_WITH_ROOT_VALS_AND_CHILDREN_N[0],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_join_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }
    }

    mod meet {
        use super::*;
        use crate::experimental::zipper_algebra::{
            ZipperAlgebraExt, ZipperMergeF, zipper_meet, zipper_meet3,
        };
        use crate::zipper_meet_n;

        #[test]
        fn test_disjoint() {
            check2(&DISJOINT_PATHS, [], |lhs, rhs, out| {
                lhs.meet(rhs, out);
            });
        }

        #[test]
        fn test_disjoint3() {
            check3(&DISJOINT_PATHS_3, [], |lhs, mid, rhs, out| {
                zipper_meet3(lhs, mid, rhs, out);
            });
        }

        #[test]
        fn test_disjoint_n() {
            checkn(
                &DISJOINT_PATHS_N,
                [],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_meet_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_deep_shared_prefix_then_split() {
            check2(&PATHS_WITH_SHARED_PREFIX, [], |lhs, rhs, out| {
                lhs.meet(rhs, out);
            });
        }

        #[test]
        fn test_deep_shared_prefix_then_split3() {
            check3(&PATHS_WITH_SHARED_PREFIX_3, [], |lhs, mid, rhs, out| {
                zipper_meet3(lhs, mid, rhs, out);
            });
        }

        #[test]
        fn test_deep_shared_prefix_then_split_n() {
            checkn(
                &PATHS_WITH_SHARED_PREFIX_N,
                [],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_meet_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_interleaving_paths() {
            check2(&INTERLEAVING_PATHS, [], |lhs, rhs, out| {
                lhs.meet(rhs, out);
            });
        }

        #[test]
        fn test_interleaving_paths3() {
            check3(&INTERLEAVING_PATHS_3, [], |lhs, mid, rhs, out| {
                zipper_meet3(lhs, mid, rhs, out);
            });
        }

        #[test]
        fn test_interleaving_paths_n() {
            checkn(
                &INTERLEAVING_PATHS_N,
                [],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_meet_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_one_side_empty_at_many_levels() {
            let expected: Paths = &[
                (&[0x00], 0),
                (&[0x00, 0x01, 0x02, 0x03], 3),
                (&[0x01, 0x02, 0x03, 0x04, 0x05], 8),
            ];
            check2(&ONE_SIDED_PATHS, expected, |lhs, rhs, out| {
                lhs.meet(rhs, out);
            });
        }

        #[test]
        fn test_one_side_empty_at_many_levels3() {
            let expected: Paths = &[(&[0x00], 0)];
            check3(&ONE_SIDED_PATHS_3, expected, |lhs, mid, rhs, out| {
                zipper_meet3(lhs, mid, rhs, out);
            });
        }

        #[test]
        fn test_one_side_empty_at_many_levels_n() {
            checkn(
                &ONE_SIDED_PATHS_N,
                [],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_meet_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_almost_identical_paths() {
            check2(
                &ALMOST_IDENTICAL_PATHS,
                ALMOST_IDENTICAL_PATHS.1,
                |lhs, rhs, out| lhs.meet(rhs, out),
            );
        }

        #[test]
        fn test_almost_identical_paths3() {
            let expected: Paths = &[(b"abcdefg", 0), (b"1", 4), (b"4", 7), (b"5", 8)];
            check3(&ALMOST_IDENTICAL_PATHS_3, expected, |lhs, mid, rhs, out| {
                zipper_meet3(lhs, mid, rhs, out);
            });
        }

        #[test]
        fn test_almost_identical_paths_n() {
            let expected: Paths = &[(b"1", 4), (b"4", 7), (b"5", 8)];
            checkn(
                &ALMOST_IDENTICAL_PATHS_N,
                expected,
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_meet_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_one_side_empty() {
            check2(&LHS_EMPTY, [], |lhs, rhs, out| lhs.meet(rhs, out));
            check2(&RHS_EMPTY, [], |lhs, rhs, out| lhs.meet(rhs, out));
        }

        #[test]
        fn test_one_side_empty3() {
            check3(&LHS_EMPTY_3, [], |lhs, mid, rhs, out| {
                zipper_meet3(lhs, mid, rhs, out)
            });
            check3(&MID_EMPTY, [], |lhs, mid, rhs, out| {
                zipper_meet3(lhs, mid, rhs, out)
            });
            check3(&RHS_EMPTY_3, [], |lhs, mid, rhs, out| {
                zipper_meet3(lhs, mid, rhs, out)
            });
        }

        #[test]
        fn test_one_side_empty_n() {
            checkn(
                &LHS_EMPTY_N,
                [],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_meet_n!(z0, z1, z2, z3, z4, z5 => out),
            );
            checkn(
                &MID_EMPTY_N,
                [],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_meet_n!(z0, z1, z2, z3, z4, z5 => out),
            );
            checkn(
                &RHS_EMPTY_N,
                [],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_meet_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_exact_overlap_divergent_subtries() {
            let expected: Paths = &[(&[1, 2, 3], 0)];
            check2(
                &PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN,
                expected,
                |lhs, rhs, out| lhs.meet(rhs, out),
            );
        }

        #[test]
        fn test_exact_overlap_divergent_subtries3() {
            let expected: Paths = &[(&[1, 2, 3], 0)];
            check3(
                &PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN_3,
                expected,
                |lhs, mid, rhs, out| zipper_meet3(lhs, mid, rhs, out),
            );
        }

        #[test]
        fn test_exact_overlap_divergent_subtries_n() {
            let expected: Paths = &[(&[1, 2, 3], 0)];
            checkn(
                &PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN_N,
                expected,
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_meet_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_zigzag() {
            let expected: Paths = &[(&[2, 1], 2), (&[3], 3)];
            check2(&ZIGZAG_PATHS, expected, |lhs, rhs, out| {
                lhs.meet(rhs, out);
            });
        }

        #[test]
        fn test_zigzag3() {
            let expected: Paths = &[(&[2, 1], 2)];
            check3(&ZIGZAG_PATHS_3, expected, |lhs, mid, rhs, out| {
                zipper_meet3(lhs, mid, rhs, out)
            });
        }

        #[test]
        fn test_root_values() {
            check2(
                &PATHS_WITH_ROOT_VALS_AND_CHILDREN,
                PATHS_WITH_ROOT_VALS_AND_CHILDREN.0,
                |lhs, rhs, out| lhs.meet(rhs, out),
            );
        }

        #[test]
        fn test_root_values3() {
            check3(
                &PATHS_WITH_ROOT_VALS_AND_CHILDREN_3,
                PATHS_WITH_ROOT_VALS_AND_CHILDREN.0,
                |lhs, mid, rhs, out| zipper_meet3(lhs, mid, rhs, out),
            );
        }

        #[test]
        fn test_root_values_n() {
            checkn(
                &PATHS_WITH_ROOT_VALS_AND_CHILDREN_N,
                PATHS_WITH_ROOT_VALS_AND_CHILDREN_N[0],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_meet_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }
    }

    mod subtract {
        use super::*;
        use crate::experimental::zipper_algebra::{
            ZipperAlgebraExt, ZipperMergeF, zipper_subtract, zipper_subtract3,
        };
        use crate::zipper_subtract_n;

        #[test]
        fn test_disjoint() {
            check2(&DISJOINT_PATHS, DISJOINT_PATHS.0, |lhs, rhs, out| {
                lhs.subtract(rhs, out);
            });
        }

        #[test]
        fn test_disjoint3() {
            check3(
                &DISJOINT_PATHS_3,
                DISJOINT_PATHS_3.0,
                |lhs, mid, rhs, out| {
                    zipper_subtract3(lhs, mid, rhs, out);
                },
            );
        }

        #[test]
        fn test_disjoint_n() {
            checkn(
                &DISJOINT_PATHS_N,
                DISJOINT_PATHS_N[0],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_subtract_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_deep_shared_prefix_then_split() {
            check2(
                &PATHS_WITH_SHARED_PREFIX,
                PATHS_WITH_SHARED_PREFIX.0,
                |lhs, rhs, out| lhs.subtract(rhs, out),
            );
        }

        #[test]
        fn test_deep_shared_prefix_then_split3() {
            check3(
                &PATHS_WITH_SHARED_PREFIX_3,
                PATHS_WITH_SHARED_PREFIX_3.0,
                |lhs, mid, rhs, out| {
                    zipper_subtract3(lhs, mid, rhs, out);
                },
            );
        }

        #[test]
        fn test_deep_shared_prefix_then_split_n() {
            checkn(
                &PATHS_WITH_SHARED_PREFIX_N,
                PATHS_WITH_SHARED_PREFIX_N[0],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_subtract_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_interleaving_paths() {
            check2(
                &INTERLEAVING_PATHS,
                INTERLEAVING_PATHS.0,
                |lhs, rhs, out| lhs.subtract(rhs, out),
            );
        }

        #[test]
        fn test_interleaving_paths3() {
            check3(
                &INTERLEAVING_PATHS_3,
                INTERLEAVING_PATHS_3.0,
                |lhs, mid, rhs, out| {
                    zipper_subtract3(lhs, mid, rhs, out);
                },
            );
        }

        #[test]
        fn test_interleaving_paths_n() {
            checkn(
                &INTERLEAVING_PATHS_N,
                INTERLEAVING_PATHS_N[0],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_subtract_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_one_side_empty_at_many_levels() {
            let expected: Paths = &[
                (&[0x00, 0x01], 1),
                (&[0x00, 0x01, 0x02], 2),
                (&[0x00, 0x01, 0x02, 0x03], 3),
                (&[0x01], 4),
                (&[0x01, 0x02], 5),
                (&[0x01, 0x02, 0x03], 6),
                (&[0x01, 0x02, 0x03, 0x04], 7),
                (&[0x01, 0x02, 0x03, 0x04, 0x05], 8),
                (&[0x01, 0x02, 0x03, 0x04, 0x05, 0x06], 9),
            ];
            check2(&ONE_SIDED_PATHS, expected, |lhs, rhs, out| {
                lhs.subtract(rhs, out)
            });
        }

        #[test]
        fn test_one_side_empty_at_many_levels3() {
            let expected: Paths = &[
                (&[0x00, 0x01], 1),
                (&[0x00, 0x01, 0x02], 2),
                (&[0x00, 0x01, 0x02, 0x03], 3),
                (&[0x01], 4),
                (&[0x01, 0x02], 5),
                (&[0x01, 0x02, 0x03], 6),
                (&[0x01, 0x02, 0x03, 0x04], 7),
                (&[0x01, 0x02, 0x03, 0x04, 0x05], 8),
                (&[0x01, 0x02, 0x03, 0x04, 0x05, 0x06], 9),
            ];
            check3(&ONE_SIDED_PATHS_3, expected, |lhs, mid, rhs, out| {
                zipper_subtract3(lhs, mid, rhs, out);
            });
        }

        #[test]
        fn test_one_side_empty_at_many_levels_n() {
            let expected: Paths = &[
                (&[0x00, 0x01], 1),
                (&[0x00, 0x01, 0x02], 2),
                (&[0x00, 0x01, 0x02, 0x03], 3),
                (&[0x01, 0x02, 0x03], 6),
                (&[0x01, 0x02, 0x03, 0x04], 7),
                (&[0x01, 0x02, 0x03, 0x04, 0x05], 8),
                (&[0x01, 0x02, 0x03, 0x04, 0x05, 0x06], 9),
            ];
            checkn(
                &ONE_SIDED_PATHS_N,
                expected,
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_subtract_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_almost_identical_paths() {
            let expected: Paths = &[(b"hijklmnop", 1), (b"2", 5), (b"3", 6)];
            check2(&ALMOST_IDENTICAL_PATHS, expected, |lhs, rhs, out| {
                lhs.subtract(rhs, out)
            });
        }

        #[test]
        fn test_almost_identical_paths3() {
            check3(&ALMOST_IDENTICAL_PATHS_3, [], |lhs, mid, rhs, out| {
                zipper_subtract3(lhs, mid, rhs, out);
            });
        }

        #[test]
        fn test_almost_identical_paths_n() {
            checkn(
                &ALMOST_IDENTICAL_PATHS_N,
                [],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_subtract_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_one_side_empty() {
            check2(&LHS_EMPTY, [], |lhs, rhs, out| lhs.subtract(rhs, out));
            check2(&RHS_EMPTY, RHS_EMPTY.0, |lhs, rhs, out| {
                lhs.subtract(rhs, out)
            });
        }

        #[test]
        fn test_one_side_empty3() {
            check3(&LHS_EMPTY_3, [], |lhs, mid, rhs, out| {
                zipper_subtract3(lhs, mid, rhs, out);
            });
            check3(&MID_EMPTY, MID_EMPTY.0, |lhs, mid, rhs, out| {
                zipper_subtract3(lhs, mid, rhs, out);
            });
            check3(&RHS_EMPTY_3, RHS_EMPTY_3.0, |lhs, mid, rhs, out| {
                zipper_subtract3(lhs, mid, rhs, out);
            });
        }

        #[test]
        fn test_one_side_empty_n() {
            checkn(
                &LHS_EMPTY_N,
                [],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_subtract_n!(z0, z1, z2, z3, z4, z5 => out),
            );
            checkn(
                &MID_EMPTY_N,
                MID_EMPTY_N[0],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_subtract_n!(z0, z1, z2, z3, z4, z5 => out),
            );
            checkn(
                &RHS_EMPTY_N,
                RHS_EMPTY_N[0],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_subtract_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_exact_overlap_divergent_subtries() {
            check2(
                &PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN,
                PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN.0,
                |lhs, rhs, out| lhs.subtract(rhs, out),
            );
        }

        #[test]
        fn test_exact_overlap_divergent_subtries3() {
            check3(
                &PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN_3,
                PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN_3.0,
                |lhs, mid, rhs, out| {
                    zipper_subtract3(lhs, mid, rhs, out);
                },
            );
        }

        #[test]
        fn test_exact_overlap_divergent_subtries_n() {
            checkn(
                &PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN_N,
                PATHS_WITH_SAME_PREFIX_DIFFERENT_CHILDREN_N[0],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_subtract_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }

        #[test]
        fn test_zigzag() {
            let expected: Paths = &[
                (&[1, 1], 0),
                (&[2], 1),
                (&[3, 2, 1], 4),
                (&[4], 4),
                (&[4, 3, 2, 1], 5),
            ];
            check2(&ZIGZAG_PATHS, expected, |lhs, rhs, out| {
                lhs.subtract(rhs, out)
            });
        }

        #[test]
        fn test_zigzag3() {
            let expected: Paths = &[(&[1, 1], 0), (&[3, 2, 1], 4), (&[4], 4)];
            check3(&ZIGZAG_PATHS_3, expected, |lhs, mid, rhs, out| {
                zipper_subtract3(lhs, mid, rhs, out);
            });
        }

        #[test]
        fn test_root_values() {
            check2(
                &PATHS_WITH_ROOT_VALS_AND_CHILDREN,
                PATHS_WITH_ROOT_VALS_AND_CHILDREN.0,
                |lhs, rhs, out| lhs.subtract(rhs, out),
            );
        }

        #[test]
        fn test_root_values3() {
            check3(
                &PATHS_WITH_ROOT_VALS_AND_CHILDREN_3,
                PATHS_WITH_ROOT_VALS_AND_CHILDREN_3.0,
                |lhs, mid, rhs, out| {
                    zipper_subtract3(lhs, mid, rhs, out);
                },
            );
        }

        #[test]
        fn test_root_values_n() {
            checkn(
                &PATHS_WITH_ROOT_VALS_AND_CHILDREN_N,
                PATHS_WITH_ROOT_VALS_AND_CHILDREN_N[0],
                |[mut z0, mut z1, mut z2, mut z3, mut z4, mut z5], mut out| zipper_subtract_n!(z0, z1, z2, z3, z4, z5 => out),
            );
        }
    }

    const FOR_MERKLEIZATION: Paths = &[
        // X
        (&[0b100000, 0b00, 0b0001], 1),
        (&[0b100000, 0b00, 0b0011], 2),
        (&[0b100000, 0b00, 0b0111], 3),
        (&[0b100000, 0b00, 0b1111], 4),
        (&[0b010000, 0b00, 0b0001], 1),
        (&[0b010000, 0b00, 0b0011], 2),
        (&[0b010000, 0b00, 0b0111], 3),
        (&[0b010000, 0b00, 0b1111], 4),
        // Y
        (&[0b001000, 0b01, 0b0001], 5),
        (&[0b001000, 0b01, 0b0011], 6),
        (&[0b001000, 0b01, 0b0111], 7),
        (&[0b001000, 0b01, 0b1111], 8),
        (&[0b000100, 0b01, 0b0001], 5),
        (&[0b000100, 0b01, 0b0011], 6),
        (&[0b000100, 0b01, 0b0111], 7),
        (&[0b000100, 0b01, 0b1111], 8),
        // Z
        (&[0b000010, 0b11, 0b0001], 9),
        (&[0b000010, 0b11, 0b0011], 10),
        (&[0b000010, 0b11, 0b0111], 11),
        (&[0b000010, 0b11, 0b1111], 12),
        (&[0b000001, 0b11, 0b0001], 9),
        (&[0b000001, 0b11, 0b0011], 10),
        (&[0b000001, 0b11, 0b0111], 11),
        (&[0b000001, 0b11, 0b1111], 12),
    ];

    #[test]
    fn test_merkleization() {
        use crate::experimental::zipper_algebra::*;
        use crate::{zipper_join_n, zipper_meet_n};

        let mut map = PathMap::from_iter(FOR_MERKLEIZATION);
        let merkelize_result = map.merkleize();
        assert!(merkelize_result.reused > 0);

        let mut r1 = map.read_zipper();
        let mut r2 = map.read_zipper();
        let mut r3 = map.read_zipper();
        let mut r4 = map.read_zipper();
        let mut r5 = map.read_zipper();
        let mut r6 = map.read_zipper();

        r1.descend_to_byte(0b000001);
        r2.descend_to_byte(0b000010);
        r3.descend_to_byte(0b000100);
        r4.descend_to_byte(0b001000);
        r5.descend_to_byte(0b010000);
        r6.descend_to_byte(0b100000);

        // this one simulates X \/ X, where X is shared
        let mut result0 = PathMap::new();
        let mut w0 = result0.write_zipper();
        zipper_join(&mut r1, &mut r2, &mut w0);
        let expected0: Paths = &[
            (&[0b11, 0b0001], 9),
            (&[0b11, 0b0011], 10),
            (&[0b11, 0b0111], 11),
            (&[0b11, 0b1111], 12),
        ];
        assert_trie(expected0.iter().copied(), result0);

        fn prefixed<V: Clone + Send + Sync + Unpin, Z: ZipperInfallibleSubtries<V>>(
            rz: &Z,
            path: &[u8],
        ) -> PathMap<V> {
            let mut res = PathMap::new();
            let mut out = res.write_zipper_at_path(path);
            out.graft(rz);
            res
        }

        let mut map1 = prefixed(&mut r3, &[0]);
        let mut map2 = prefixed(&mut r4, &[0]);
        let mut r31 = map1.read_zipper();
        let mut r32 = map1.read_zipper();
        let mut r33 = map1.read_zipper();
        let mut r41 = map2.read_zipper();
        let mut r42 = map2.read_zipper();
        let mut r43 = map2.read_zipper();

        // this one simulates X.prefixed(0) /\ X.prefixed(0) ..., where X is shared
        let mut result1 = PathMap::new();
        let mut w1 = result1.write_zipper();
        zipper_meet_n!(r31, r32, r33, r41, r42, r43 => w1);
        let expected1: Paths = &[
            (&[0b0, 0b01, 0b0001], 5),
            (&[0b0, 0b01, 0b0011], 6),
            (&[0b0, 0b01, 0b0111], 7),
            (&[0b0, 0b01, 0b1111], 8),
        ];
        assert_trie(expected1.iter().copied(), result1);

        let mut map3 = prefixed(&mut r5, &[0]);
        let mut map4 = prefixed(&mut r6, &[1]);
        let mut r51 = map3.read_zipper();
        let mut r52 = map3.read_zipper();
        let mut r53 = map3.read_zipper();
        let mut r54 = map3.read_zipper();
        let mut r61 = map4.read_zipper();
        let mut r62 = map4.read_zipper();
        let mut r63 = map4.read_zipper();

        // this one simulates X.prefixed(0) \/ X.prefixed(0) ... \/ X.prefixed(1) \/ ..., where X is shared
        let mut result2 = PathMap::new();
        let mut w2 = result2.write_zipper();
        zipper_join_n!(r51, r52, r53, r54, r61, r62, r63 => w2);
        let expected2: Paths = &[
            (&[0b0, 0b00, 0b0001], 1),
            (&[0b0, 0b00, 0b0011], 2),
            (&[0b0, 0b00, 0b0111], 3),
            (&[0b0, 0b00, 0b1111], 4),
            (&[0b1, 0b00, 0b0001], 1),
            (&[0b1, 0b00, 0b0011], 2),
            (&[0b1, 0b00, 0b0111], 3),
            (&[0b1, 0b00, 0b1111], 4),
        ];
        assert_trie(expected2.iter().copied(), result2);
    }

    mod dnf {
        use crate::experimental::zipper_algebra::{zipper_join3, zipper_meet3, zipper_merge_dnf};

        use super::*;

        const SMALL_TRIE_1: Paths = &[(&[0, 1, 2], 1), (&[0, 1, 3], 2)];
        const SMALL_TRIE_2: Paths = &[(&[0, 1], 1), (&[0, 2], 2), (&[3], 3), (&[2, 3], 4)];
        const SMALL_TRIE_3: Paths = &[(&[0, 1, 2], 1), (&[0, 1, 3], 2), (&[0, 1, 4], 3)];

        #[test]
        fn test_single_clause_multiple_zippers() {
            let mut trie1 = PathMap::from_iter(SMALL_TRIE_1);
            let mut trie2 = PathMap::from_iter(SMALL_TRIE_2);
            let mut trie3 = PathMap::from_iter(SMALL_TRIE_3);

            let mut z1 = trie1.read_zipper();
            let mut z2 = trie2.read_zipper();
            let mut z3 = trie3.read_zipper();

            let mut result = PathMap::new();
            let mut out = result.write_zipper();
            zipper_merge_dnf(&mut [&mut [&mut z1, &mut z2, &mut z3]], &mut out);

            let mut expected = PathMap::new();
            {
                z1.reset();
                z2.reset();
                z3.reset();
                zipper_meet3(&mut z1, &mut z2, &mut z3, &mut expected.write_zipper());
            }

            assert_trie(expected, result);
        }

        #[test]
        fn test_multiple_singleton_clauses() {
            let mut trie1 = PathMap::from_iter(SMALL_TRIE_1);
            let mut trie2 = PathMap::from_iter(SMALL_TRIE_2);
            let mut trie3 = PathMap::from_iter(SMALL_TRIE_3);

            let mut z1 = trie1.read_zipper();
            let mut z2 = trie2.read_zipper();
            let mut z3 = trie3.read_zipper();

            let mut result = PathMap::new();
            let mut out = result.write_zipper();
            zipper_merge_dnf(
                &mut [&mut [&mut z1], &mut [&mut z2], &mut [&mut z3]],
                &mut out,
            );

            let mut expected = PathMap::new();
            {
                z1.reset();
                z2.reset();
                z3.reset();
                zipper_join3(&mut z1, &mut z2, &mut z3, &mut expected.write_zipper());
            }

            assert_trie(expected, result);
        }

        #[test]
        fn test_partial_overlap_1() {
            let mut trie1 = PathMap::from_iter(SMALL_TRIE_1);
            let mut trie2 = PathMap::from_iter(SMALL_TRIE_2);
            let mut trie3 = PathMap::from_iter(SMALL_TRIE_3);

            let mut z2 = trie2.read_zipper();
            let mut z3 = trie3.read_zipper();

            let mut result = PathMap::new();
            let mut out = result.write_zipper();
            zipper_merge_dnf(
                &mut [
                    &mut [&mut trie1.read_zipper(), &mut z2],
                    &mut [&mut trie1.read_zipper(), &mut z3],
                ],
                &mut out,
            );
            let expected = trie1.meet(&trie2.join(&trie3));
            assert_trie(expected, result);
        }

        #[test]
        fn test_partial_overlap_2() {
            let mut trie1 = PathMap::from_iter(SMALL_TRIE_1);
            let mut trie2 = PathMap::from_iter(SMALL_TRIE_2);
            let mut trie3 = PathMap::from_iter(SMALL_TRIE_3);

            let mut z1 = trie1.read_zipper();
            let mut z2 = trie2.read_zipper();
            let mut z3 = trie3.read_zipper();

            let mut result = PathMap::new();
            let mut out = result.write_zipper();
            zipper_merge_dnf(
                &mut [
                    &mut [&mut z1, &mut trie2.read_zipper()],
                    &mut [&mut trie2.read_zipper(), &mut z3],
                ],
                &mut out,
            );
            let expected = trie2.meet(&trie1.join(&trie3));
            assert_trie(expected, result);
        }
    }
}
