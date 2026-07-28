
//GOAT, Internal discussion about the API we eventually want.
//
//It strikes me that "overlay" is *almost* join.  The main difference being the treatment of values. One
// possible direction is to embrace this and upgrade this to a full "JoinZipper" that performs a join
// on-the-fly.
//
//However, with the rearchitecture of the algebraic ops towards support for policies and subtrie algebra,
// that might make this too complicated.  In either case, I'd prefer to wait until that change fully shakes
// out before trying to mess with this zipper.  Also the algebraic traits are (and will be) defined with
// the expectations that new trie storage can be created, and thus it seems tricky to shoe-horn that into
// a zipper API.
//
//A half-step might be to change the mapping function into a "merging" function,
// e.g. `Fn(Option<&VBase>, Option<&VOverlay>) -> VOverlay`  Although this also breaks the trait contract
// with ZipperValues, etc. because we don't have a place to store the newly created value
//

use arrayvec::ArrayVec;
use fast_slice_utils::find_prefix_overlap;
use crate::utils::{BitMask, ByteMask};
use crate::zipper::{Zipper, ZipperMoving, ZipperPath, PathObserver, ZipperIteration, ZipperValues};

/// Zipper that traverses a virtual trie formed by fusing the tries of two other zippers
pub struct OverlayZipper<AV, BV, OutV, AZipper, BZipper, Mapping>
    where
        Mapping: for<'a> Fn(Option<&'a AV>, Option<&'a BV>) -> Option<&'a OutV>,
{
    a: AZipper,
    b: BZipper,
    mapping: Mapping,
    _marker: core::marker::PhantomData<(AV, BV, OutV)>,
}

fn identity_ref<'a, V>(a_val: Option<&'a V>, b_val: Option<&'a V>) -> Option<&'a V> { a_val.or(b_val) }

impl<V, AZipper, BZipper> OverlayZipper<V, V, V, AZipper, BZipper, for<'a> fn(Option<&'a V>, Option<&'a V>) -> Option<&'a V>>
    where
        AZipper: ZipperMoving,
        BZipper: ZipperMoving,
{
    /// Create a new `OverlayZipper` from two other zippers, using a default value mapping function
    ///
    /// In cases where both source zippers supply a value, the value from `AZipper` will be supplied by
    /// the `OverlayZipper`.
    pub fn new(a: AZipper, b: BZipper) -> Self {
        Self::with_mapping(a, b, identity_ref)
    }
}

impl<AV, BV, OutV, AZipper, BZipper, Mapping>
    OverlayZipper<AV, BV, OutV, AZipper, BZipper, Mapping>
    where
        AZipper: ZipperMoving,
        BZipper: ZipperMoving,
        Mapping: for<'a> Fn(Option<&'a AV>, Option<&'a BV>) -> Option<&'a OutV>,
{
    /// Create a new `OverlayZipper` from two other zippers, using a the supplied value mapping function
    pub fn with_mapping(mut a: AZipper, mut b: BZipper, mapping: Mapping) -> Self {
        a.reset();
        b.reset();
        Self {
            a, b,
            mapping,
            _marker: core::marker::PhantomData,
        }
    }
}

impl<AV, BV, OutV, AZipper, BZipper, Mapping>
    OverlayZipper<AV, BV, OutV, AZipper, BZipper, Mapping>
    where
        AZipper: ZipperMoving + ZipperPath + ZipperValues<AV>,
        BZipper: ZipperMoving + ZipperPath + ZipperValues<BV>,
        Mapping: for<'a> Fn(Option<&'a AV>, Option<&'a BV>) -> Option<&'a OutV>,
{
    fn to_sibling(&mut self, next: bool) -> bool {
        let path = self.path();
        let Some(&last) = path.last() else {
            return false;
        };
        self.ascend(1);
        let child_mask = self.child_mask();
        let maybe_child = if next {
            child_mask.next_bit(last)
        } else {
            child_mask.prev_bit(last)
        };
        let Some(child) = maybe_child else {
            self.descend_to_byte(last);
            return false;
        };
        self.descend_to_byte(child);
        true
    }
}

impl<AV, BV, OutV, AZipper, BZipper, Mapping> ZipperValues<OutV>
    for OverlayZipper<AV, BV, OutV, AZipper, BZipper, Mapping>
    where
        AZipper: ZipperValues<AV>,
        BZipper: ZipperValues<BV>,
        Mapping: for<'a> Fn(Option<&'a AV>, Option<&'a BV>) -> Option<&'a OutV>,
{
    fn val(&self) -> Option<&OutV> {
        (self.mapping)(self.a.val(), self.b.val())
    }
    fn val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&OutV> {
        (self.mapping)(self.a.val_at(&path), self.b.val_at(&path))
    }
}

impl<AV, BV, OutV, AZipper, BZipper, Mapping> Zipper
    for OverlayZipper<AV, BV, OutV, AZipper, BZipper, Mapping>
    where
        AZipper: Zipper + ZipperValues<AV>,
        BZipper: Zipper + ZipperValues<BV>,
        Mapping: for<'a> Fn(Option<&'a AV>, Option<&'a BV>) -> Option<&'a OutV>,
{
    fn path_exists(&self) -> bool {
        self.a.path_exists() || self.b.path_exists()
    }
    fn is_val(&self) -> bool {
        //NOTE: the mapping function has the ability to nullify the value, so we need ZipperValues to implement this correctly
        // self.a.is_val() || self.b.is_val()
        self.val().is_some()
    }
    fn child_count(&self) -> usize {
        self.child_mask().count_bits()
    }
    fn child_mask(&self) -> ByteMask {
        self.a.child_mask() | self.b.child_mask()
    }
}

impl<AV, BV, OutV, AZipper, BZipper, Mapping> ZipperMoving
    for OverlayZipper<AV, BV, OutV, AZipper, BZipper, Mapping>
    where
        AZipper: ZipperMoving + ZipperPath + ZipperValues<AV>,
        BZipper: ZipperMoving + ZipperPath + ZipperValues<BV>,
        Mapping: for<'a> Fn(Option<&'a AV>, Option<&'a BV>) -> Option<&'a OutV>,
{
    fn at_root(&self) -> bool {
        self.a.at_root() || self.b.at_root()
    }

    #[inline]
    fn focus_byte(&self) -> Option<u8> {
        let byte = self.a.focus_byte();
        debug_assert_eq!(byte, self.b.focus_byte());
        byte
    }

    fn reset(&mut self) {
        self.a.reset();
        self.b.reset();
    }

    fn val_count(&self) -> usize {
        todo!()
    }

    fn descend_to<P: AsRef<[u8]>>(&mut self, path: P) {
        let path = path.as_ref();
        self.a.descend_to(path);
        self.b.descend_to(path);
    }

    fn descend_to_existing<P: AsRef<[u8]>>(&mut self, path: P) -> usize {
        let path = path.as_ref();
        let depth_a = self.a.descend_to_existing(path);
        let depth_b = self.b.descend_to_existing(path);
        if depth_a > depth_b {
            self.b.descend_to(&path[depth_b..depth_a]);
            depth_a
        } else if depth_b > depth_a {
            self.a.descend_to(&path[depth_a..depth_b]);
            depth_b
        } else {
            depth_a
        }
    }

    fn descend_to_val<K: AsRef<[u8]>>(&mut self, path: K) -> usize {
        let path = path.as_ref();
        let depth_a = self.a.descend_to_val(path);
        let depth_o = self.b.descend_to_val(path);
        if depth_a < depth_o {
            if self.a.is_val() {
                self.b.ascend(depth_o - depth_a);
                depth_a
            } else {
                self.a.descend_to(&path[depth_a..depth_o]);
                depth_o
            }
        } else if depth_o < depth_a {
            if self.b.is_val() {
                self.a.ascend(depth_a - depth_o);
                depth_o
            } else {
                self.a.descend_to(&path[depth_o..depth_a]);
                depth_a
            }
        } else {
            depth_a
        }
    }

    fn descend_to_byte(&mut self, k: u8) {
        self.a.descend_to(&[k]);
        self.b.descend_to(&[k]);
    }

    fn descend_first_byte(&mut self) -> bool {
        self.descend_indexed_byte(0)
    }

    fn descend_indexed_byte(&mut self, idx: usize) -> bool {
        let child_mask = self.child_mask();
        let Some(byte) = child_mask.indexed_bit::<true>(idx) else {
            return false;
        };
        self.descend_to_byte(byte);
        true
    }

    fn descend_until<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        //Descending happens in buffer-sized chunks, so neither source can outrun what we're able
        // to capture.  As long as both sources fill a whole chunk and agree on every byte of it,
        // the chunk is committed and we go around again.  Any other outcome ends the descent and
        // is settled by the case analysis below.
        const CHUNK: usize = 48;
        let mut path_a = ArrayVec::<u8, CHUNK>::new();
        let mut path_b = ArrayVec::<u8, CHUNK>::new();

        //Total bytes committed to `obs` across all completed chunks
        let mut committed = 0usize;
        #[cfg(debug_assertions)]
        let start_depth = self.a.path().len();

        loop {
            path_a.clear();
            path_b.clear();
            let desc_a = self.a.descend_until_max_bytes(CHUNK, &mut path_a);
            let desc_b = self.b.descend_until_max_bytes(CHUNK, &mut path_b);

            if !desc_a && !desc_b {
                break;
            }
            if !desc_a && desc_b {
                if self.a.child_count() == 0 {
                    self.a.descend_to(&path_b);
                    obs.descend_to(&path_b);
                    committed += path_b.len();
                } else {
                    let ascended = self.b.ascend(path_b.len());
                    debug_assert!(ascended);
                }
                break;
            }
            if desc_a && !desc_b {
                if self.b.child_count() == 0 {
                    self.b.descend_to(&path_a);
                    obs.descend_to(&path_a);
                    committed += path_a.len();
                } else {
                    let ascended = self.a.ascend(path_a.len());
                    debug_assert!(ascended);
                }
                break;
            }

            //Both moved.  Keep the portion they agree on and rewind the rest
            let overlap = find_prefix_overlap(&path_a, &path_b);
            if path_a.len() > overlap {
                let ascended = self.a.ascend(path_a.len() - overlap);
                debug_assert!(ascended);
            }
            if path_b.len() > overlap {
                let ascended = self.b.ascend(path_b.len() - overlap);
                debug_assert!(ascended);
            }
            //Both sources must now sit at the same position: the agreed-upon prefix
            debug_assert_eq!(self.a.path(), self.b.path());
            if overlap > 0 {
                obs.descend_to(&path_a[..overlap]);
                committed += overlap;
            }

            //Only a full chunk that both sources agreed on end-to-end can be continued.  Anything
            // shorter means at least one source stopped on its own, so the descent is complete.
            if overlap < CHUNK || path_a.len() != CHUNK || path_b.len() != CHUNK {
                break;
            }
        }

        #[cfg(debug_assertions)]
        debug_assert_eq!(start_depth + committed, self.a.path().len());
        committed > 0
    }

    fn ascend(&mut self, steps: usize) -> bool {
        self.a.ascend(steps) | self.b.ascend(steps)
    }

    fn ascend_byte(&mut self) -> bool {
        self.ascend(1)
    }

    fn ascend_until(&mut self) -> bool {
        debug_assert_eq!(self.a.path(), self.b.path());
        // eprintln!("asc_until i {:?} {:?}", self.base.path(), self.overlay.path());
        let asc_a = self.a.ascend_until();
        let path_a = self.a.path();
        let depth_a = path_a.len();
        let asc_b = self.b.ascend_until();
        let path_b = self.b.path();
        let depth_b = path_b.len();
        if !(asc_b || asc_a) {
            return false;
        }
        // eprintln!("asc_until {path_a:?} {path_b:?}");
        if depth_b > depth_a {
            self.a.descend_to(&path_b[depth_a..]);
        } else if depth_a > depth_b {
            self.b.descend_to(&path_a[depth_b..]);
        }
        true
    }

    fn ascend_until_branch(&mut self) -> bool {
        let asc_a = self.a.ascend_until_branch();
        let path_a = self.a.path();
        let depth_a = path_a.len();
        let asc_b = self.b.ascend_until_branch();
        let path_b = self.b.path();
        let depth_b = path_b.len();
        if depth_b > depth_a {
            self.a.descend_to(&path_b[depth_a..]);
        } else if depth_a > depth_b {
            self.b.descend_to(&path_a[depth_b..]);
        }
        asc_a || asc_b
    }

    fn to_next_sibling_byte(&mut self) -> bool {
        self.to_sibling(true)
    }

    fn to_prev_sibling_byte(&mut self) -> bool {
        self.to_sibling(false)
    }
}

impl<AV, BV, OutV, AZipper, BZipper, Mapping> ZipperPath
    for OverlayZipper<AV, BV, OutV, AZipper, BZipper, Mapping>
    where
        AZipper: ZipperMoving + ZipperPath + ZipperValues<AV>,
        BZipper: ZipperMoving + ZipperPath + ZipperValues<BV>,
        Mapping: for<'a> Fn(Option<&'a AV>, Option<&'a BV>) -> Option<&'a OutV>,
{
    fn path(&self) -> &[u8] {
        self.a.path()
    }
}

impl<AV, BV, OutV, AZipper, BZipper, Mapping> ZipperIteration
    for OverlayZipper<AV, BV, OutV, AZipper, BZipper, Mapping>
    where
        AZipper: ZipperMoving + ZipperPath + ZipperValues<AV>,
        BZipper: ZipperMoving + ZipperPath + ZipperValues<BV>,
        Mapping: for<'a> Fn(Option<&'a AV>, Option<&'a BV>) -> Option<&'a OutV>,
{ }

crate::impl_name_only_debug!(
    impl<AV, BV, OutV, AZipper, BZipper, Mapping> core::fmt::Debug for OverlayZipper<AV, BV, OutV, AZipper, BZipper, Mapping>
        where
        Mapping: for<'a> Fn(Option<&'a AV>, Option<&'a BV>) -> Option<&'a OutV>,
);

#[cfg(test)]
mod tests {
    use crate::{
        alloc::GlobalAlloc,
        PathMap,
        zipper::{
            ReadZipperUntracked,
            zipper_iteration_tests,
            zipper_moving_tests,
            ZipperMoving,
            ZipperPath,
            OverlayZipper
        },
    };

    // #[test]
    // fn overlay_preserves_keys() {
    //     // base: ACT { "aaa" -> 1, "bbb" -> 3 }
    //     // overlay: PathMap { "aaa" -> 2, "ccc" -> 4 }
    //     // result: Overlay { "aaa" -> 2, "bbb" -> 3, "ccc" -> 4 }
    //     let keys: &[&[u8]] = &[b"a", b"aa", b"ab", b"b", b"ba", b"bb"];
    //     let trie_a = keys[..3].into_iter().map(|k| (k, ())).collect::<PathMap<()>>();
    //     let trie_b = keys[3..].into_iter().map(|k| (k, ())).collect::<PathMap<()>>();
    //     let mut oz = OverlayZipper::new(trie_a.read_zipper(), trie_b.read_zipper());
    //     assert_eq!(oz.keys(), keys);
    // }

    type Mapping = for<'a> fn(Option<&'a ()>, Option<&'a ()>) -> Option<&'a ()>;
    type OZ<'a, V, A=GlobalAlloc> = OverlayZipper<
        V, V, V,
        ReadZipperUntracked<'a, 'static, V, A>,
        ReadZipperUntracked<'a, 'static, V, A>,
        Mapping
    >;
    zipper_moving_tests::zipper_moving_tests!(overlay_zipper,
        |keys: &[&[u8]]| {
            let cutoff = keys.len() / 3 * 2;
            // eprintln!("keys={:?}", &keys);
            eprintln!("a_keys={:?}\nb_keys={:?}", &keys[..cutoff], &keys[cutoff..]);
            let a = keys[..cutoff].into_iter().map(|k| (k, ())).collect::<PathMap<()>>();
            let b = keys[cutoff..].into_iter().map(|k| (k, ())).collect::<PathMap<()>>();
            (a, b)
        },
        |trie: &mut (PathMap<()>, PathMap<()>), path: &[u8]| -> OZ<'_, ()> {
            OverlayZipper::new(
                trie.0.read_zipper_at_path(path),
                trie.1.read_zipper_at_path(path),
            )
        }
    );

    zipper_iteration_tests::zipper_iteration_tests!(overlay_zipper,
        |keys: &[&[u8]]| {
            let cutoff = keys.len() / 3 * 2;
            // eprintln!("a_keys={:?}\nb_keys={:?}", &keys[..cutoff], &keys[cutoff..]);
            let a = keys[..cutoff].into_iter().map(|k| (k, ())).collect::<PathMap<()>>();
            let b = keys[cutoff..].into_iter().map(|k| (k, ())).collect::<PathMap<()>>();
            (a, b)
        },
        |trie: &mut (PathMap<()>, PathMap<()>), path: &[u8]| -> OZ<'_, ()> {
            OverlayZipper::new(
                trie.0.read_zipper_at_path(path),
                trie.1.read_zipper_at_path(path),
            )
        }
    );

    /// The chunk size used by `OverlayZipper::descend_until`
    const CHUNK: usize = 48;

    /// Builds an overlay over two maps, each holding the single supplied path
    fn overlay_of<'a>(a_key: &[u8], b_key: &[u8],
                      a: &'a mut PathMap<()>, b: &'a mut PathMap<()>) -> OZ<'a, ()> {
        a.set_val_at(a_key, ());
        b.set_val_at(b_key, ());
        OverlayZipper::new(a.read_zipper(), b.read_zipper())
    }

    /// Both sources share a single path of `len` bytes, so `descend_until` must descend the whole
    /// thing regardless of how it lands relative to the chunk boundary
    fn assert_full_descent(len: usize) {
        let key = vec![b'x'; len];
        let (mut a, mut b) = (PathMap::new(), PathMap::new());
        let mut oz = overlay_of(&key, &key, &mut a, &mut b);

        let moved = oz.descend_until(&mut ());
        assert_eq!(moved, true, "len={len}: should have descended");
        assert_eq!(oz.path(), &key[..], "len={len}: should reach the end of the path");
    }

    #[test]
    fn overlay_descent_shorter_than_chunk() { assert_full_descent(CHUNK - 1); }

    #[test]
    fn overlay_descent_exactly_one_chunk() { assert_full_descent(CHUNK); }

    #[test]
    fn overlay_descent_one_past_chunk() { assert_full_descent(CHUNK + 1); }

    #[test]
    fn overlay_descent_spanning_several_chunks() { assert_full_descent(CHUNK * 3 + 7); }

    /// The observer must receive exactly the bytes the focus actually moved over, even when the
    /// descent spans several chunks
    #[test]
    fn overlay_observer_receives_whole_descent() {
        let key = vec![b'x'; CHUNK * 2 + 5];
        let (mut a, mut b) = (PathMap::new(), PathMap::new());
        let mut oz = overlay_of(&key, &key, &mut a, &mut b);

        let mut observed = Vec::new();
        let moved = oz.descend_until(&mut observed);
        assert_eq!(moved, true);
        assert_eq!(observed, oz.path(), "observer must match the resulting path");
        assert_eq!(observed, key);
    }

    /// When the sources diverge, the focus stops at their common prefix.  Divergence is placed on
    /// both sides of the chunk boundary to check the loop terminates at the right byte.
    fn assert_diverges_at(common_len: usize) {
        let mut key_a = vec![b'x'; common_len]; key_a.push(b'A'); key_a.extend([b'x'; 4]);
        let mut key_b = vec![b'x'; common_len]; key_b.push(b'B'); key_b.extend([b'x'; 4]);
        let (mut a, mut b) = (PathMap::new(), PathMap::new());
        let mut oz = overlay_of(&key_a, &key_b, &mut a, &mut b);

        let mut observed = Vec::new();
        let moved = oz.descend_until(&mut observed);

        assert_eq!(moved, common_len > 0, "common_len={common_len}");
        assert_eq!(oz.path(), &vec![b'x'; common_len][..],
            "common_len={common_len}: focus must stop at the common prefix");
        assert_eq!(observed, oz.path(),
            "common_len={common_len}: observer must match the resulting path");
    }

    #[test]
    fn overlay_diverges_within_first_chunk() { assert_diverges_at(CHUNK / 2); }

    #[test]
    fn overlay_diverges_at_chunk_boundary() { assert_diverges_at(CHUNK); }

    #[test]
    fn overlay_diverges_just_past_chunk_boundary() { assert_diverges_at(CHUNK + 1); }

    #[test]
    fn overlay_diverges_after_several_chunks() { assert_diverges_at(CHUNK * 2 + 3); }

    /// One source runs far past the other, spanning multiple chunks.  The shorter source is a
    /// leaf, so the overlay follows the longer one.
    #[test]
    fn overlay_one_source_much_longer() {
        let short = vec![b'x'; 4];
        let long = vec![b'x'; CHUNK * 2 + 9];
        let (mut a, mut b) = (PathMap::new(), PathMap::new());
        let mut oz = overlay_of(&short, &long, &mut a, &mut b);

        let mut observed = Vec::new();
        let moved = oz.descend_until(&mut observed);
        assert_eq!(moved, true);
        assert_eq!(observed, oz.path(), "observer must match the resulting path");
    }
}
