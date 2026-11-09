//! `OverlayZipper`: the union of two read zippers, as one read zipper.
//!
//! Construction (mirrored by `lean/PathMapModel/Sources/Overlay.lean`):
//!
//! * `a` = `map1.read_zipper_at_path(root1)`;
//! * `b` = a read zipper at **root0** over `snap0`, a clone of map0 taken right
//!   after the header (so the write zipper's edits to map0 never reach it).
//!
//! The two sources are deliberately rooted at *different* paths: that is the
//! case the crate's `overlay_sources_at_different_roots` test covers (no focus
//! byte and no sibling step at the root), and it makes the two halves of the
//! view independent of each other.
//!
//! Two sources share this file:
//!
//! * `overlay` -- `OverlayZipper::new`, the default mapping: `a`'s value where
//!   it has one, else `b`'s (`a.or(b)`).
//! * `overlay-filter` -- `OverlayZipper::with_mapping(a, b, b_unless_a)`: `b`'s
//!   value, but only where `a` has none.  A mapping that *removes* values, so
//!   locations that exist with no value (the mapping nullified it), argument
//!   order, and `descend_to_val` stepping over filtered values are all checked.
//!
//! `OverlayZipper` implements `Zipper`, `ZipperMoving`, `ZipperPath`,
//! `ZipperValues`, `ZipperValuesAt` and `ZipperIteration` -- not forking,
//! subtries, `ZipperReadOnlyValues`/`Iteration`, nor `ZipperAbsolutePath`; and
//! `val_count` is `todo!()`.  So `dump`, `make_map`, every merge,
//! `get_val_agrees` and `to_next_get_val` read `skip:<name>`, and the per-step
//! fingerprint prints `n?`.
//!
//! `ZipperAbsolutePath` is required by the harness (the fingerprint prints the
//! origin path); [`Abs`] supplies it from outside, as `root1 ++ path()`, and
//! forwards every other method unchanged.  It is a pure adapter: the overlay's
//! own `path()` is what it reports, so a wrong path still shows.

use pathmap::utils::ByteMask;
use pathmap::zipper::*;

use crate::harness::*;
use crate::sources::trailer;

/// A zipper with `ZipperAbsolutePath` added from outside: `origin_path` is the
/// given root followed by the zipper's own `path()`, refreshed after every
/// move.  Every trait method the inner zipper could override is forwarded, so
/// nothing falls back to a default the inner zipper would not have used.
pub struct Abs<Z, const F: bool> {
    z: Z,
    root: Vec<u8>,
    origin: Vec<u8>,
}

impl<Z: ZipperPath, const F: bool> Abs<Z, F> {
    pub fn new(z: Z, root: &[u8]) -> Self {
        let mut s = Self { z, root: root.to_vec(), origin: Vec::new() };
        s.sync();
        s
    }
    fn sync(&mut self) {
        self.origin.clear();
        self.origin.extend_from_slice(&self.root);
        self.origin.extend_from_slice(self.z.path());
    }
}

macro_rules! fwd_mut {
    ($self:ident, $e:expr) => {{
        let r = $e;
        $self.sync();
        r
    }};
}

impl<Z: Zipper, const F: bool> Zipper for Abs<Z, F> {
    fn path_exists(&self) -> bool { self.z.path_exists() }
    fn is_val(&self) -> bool { self.z.is_val() }
    fn child_count(&self) -> usize { self.z.child_count() }
    fn child_mask(&self) -> ByteMask { self.z.child_mask() }
}

impl<Z: ZipperPath, const F: bool> ZipperMoving for Abs<Z, F> {
    fn depth(&self) -> usize { self.z.depth() }
    fn at_root(&self) -> bool { self.z.at_root() }
    fn focus_byte(&self) -> Option<u8> { self.z.focus_byte() }
    fn reset(&mut self) { fwd_mut!(self, self.z.reset()) }
    fn val_count(&self) -> usize { self.z.val_count() }
    fn descend_to<K: AsRef<[u8]>>(&mut self, k: K) { fwd_mut!(self, self.z.descend_to(k)) }
    fn descend_to_check<K: AsRef<[u8]>>(&mut self, k: K) -> bool { fwd_mut!(self, self.z.descend_to_check(k)) }
    fn descend_to_existing<K: AsRef<[u8]>>(&mut self, k: K) -> usize { fwd_mut!(self, self.z.descend_to_existing(k)) }
    fn descend_to_val<K: AsRef<[u8]>>(&mut self, k: K) -> usize { fwd_mut!(self, self.z.descend_to_val(k)) }
    fn descend_to_byte(&mut self, k: u8) { fwd_mut!(self, self.z.descend_to_byte(k)) }
    fn descend_to_existing_byte(&mut self, k: u8) -> bool { fwd_mut!(self, self.z.descend_to_existing_byte(k)) }
    fn descend_indexed_byte(&mut self, i: usize) -> Option<u8> { fwd_mut!(self, self.z.descend_indexed_byte(i)) }
    fn descend_first_byte(&mut self) -> Option<u8> { fwd_mut!(self, self.z.descend_first_byte()) }
    fn descend_last_byte(&mut self) -> Option<u8> { fwd_mut!(self, self.z.descend_last_byte()) }
    fn descend_until(&mut self) -> bool { fwd_mut!(self, self.z.descend_until()) }
    fn descend_until_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        fwd_mut!(self, self.z.descend_until_observed(obs))
    }
    fn descend_until_max_bytes(&mut self, n: usize) -> bool { fwd_mut!(self, self.z.descend_until_max_bytes(n)) }
    fn descend_until_max_bytes_observed<Obs: PathObserver>(&mut self, n: usize, obs: &mut Obs) -> bool {
        fwd_mut!(self, self.z.descend_until_max_bytes_observed(n, obs))
    }
    fn ascend(&mut self, steps: usize) -> usize { fwd_mut!(self, self.z.ascend(steps)) }
    fn ascend_byte(&mut self) -> bool { fwd_mut!(self, self.z.ascend_byte()) }
    fn ascend_until(&mut self) -> usize { fwd_mut!(self, self.z.ascend_until()) }
    fn ascend_until_branch(&mut self) -> usize { fwd_mut!(self, self.z.ascend_until_branch()) }
    fn to_next_sibling_byte(&mut self) -> Option<u8> { fwd_mut!(self, self.z.to_next_sibling_byte()) }
    fn to_prev_sibling_byte(&mut self) -> Option<u8> { fwd_mut!(self, self.z.to_prev_sibling_byte()) }
    fn to_next_step(&mut self) -> bool { fwd_mut!(self, self.z.to_next_step()) }
    fn to_next_step_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        fwd_mut!(self, self.z.to_next_step_observed(obs))
    }
    fn to_prev_step(&mut self) -> bool { fwd_mut!(self, self.z.to_prev_step()) }
    fn to_prev_step_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        fwd_mut!(self, self.z.to_prev_step_observed(obs))
    }
}

impl<Z: ZipperPath, const F: bool> ZipperPath for Abs<Z, F> {
    fn path(&self) -> &[u8] { self.z.path() }
    fn move_to_path<K: AsRef<[u8]>>(&mut self, p: K) -> usize { fwd_mut!(self, self.z.move_to_path(p)) }
}

impl<Z: ZipperPath, const F: bool> ZipperAbsolutePath for Abs<Z, F> {
    fn origin_path(&self) -> &[u8] { &self.origin }
    fn root_prefix_path(&self) -> &[u8] { &self.root }
}

impl<Z: ZipperValues<u64>, const F: bool> ZipperValues<u64> for Abs<Z, F> {
    fn val(&self) -> Option<&u64> { self.z.val() }
}

impl<Z: ZipperValuesAt<u64>, const F: bool> ZipperValuesAt<u64> for Abs<Z, F> {
    fn val_at<K: AsRef<[u8]>>(&self, p: K) -> Option<&u64> { self.z.val_at(p) }
}

impl<Z: ZipperIteration + ZipperPath, const F: bool> ZipperIteration for Abs<Z, F> {
    fn to_next_val(&mut self) -> bool { fwd_mut!(self, self.z.to_next_val()) }
    fn to_next_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        fwd_mut!(self, self.z.to_next_val_observed(obs))
    }
    fn to_prev_val(&mut self) -> bool { fwd_mut!(self, self.z.to_prev_val()) }
    fn to_prev_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        fwd_mut!(self, self.z.to_prev_val_observed(obs))
    }
    fn descend_last_val(&mut self) -> bool { fwd_mut!(self, self.z.descend_last_val()) }
    fn descend_last_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        fwd_mut!(self, self.z.descend_last_val_observed(obs))
    }
    fn descend_last_path(&mut self) -> bool { fwd_mut!(self, self.z.descend_last_path()) }
    fn descend_last_path_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        fwd_mut!(self, self.z.descend_last_path_observed(obs))
    }
    fn descend_first_k_path(&mut self, k: usize) -> bool { fwd_mut!(self, self.z.descend_first_k_path(k)) }
    fn descend_first_k_path_observed<Obs: PathObserver>(&mut self, k: usize, obs: &mut Obs) -> bool {
        fwd_mut!(self, self.z.descend_first_k_path_observed(k, obs))
    }
    fn to_next_k_path(&mut self, k: usize) -> bool { fwd_mut!(self, self.z.to_next_k_path(k)) }
    fn to_next_k_path_observed<Obs: PathObserver>(&mut self, k: usize, obs: &mut Obs) -> bool {
        fwd_mut!(self, self.z.to_next_k_path_observed(k, obs))
    }
}

/// The overlay's read-source surface: values, movement and iteration only.
/// `F` selects the skip token (`false` = `overlay`, `true` = `overlay-filter`).
impl<Z, const F: bool> ReadSource for Abs<Z, F>
where
    Z: ZipperPath + ZipperValuesAt<u64> + ZipperIteration,
{
    const SKIP: &'static str = if F { "skip:overlay-filter" } else { "skip:overlay" };
    const VAL_COUNT: bool = false;
    fn dump_fork(&self) -> Option<String> { None }
    fn make_map_val_count(&self) -> Option<usize> { None }
    fn get_val_probe(&self, _path: &[u8]) -> Option<(Option<u64>, Option<u64>, bool)> { None }
    fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)> { None }
}

type Mapping = for<'a> fn(Option<&'a u64>, Option<&'a u64>) -> Option<&'a u64>;

/// The custom mapping of `overlay-filter`: `b`'s value where `a` has none.
fn b_unless_a<'a>(a: Option<&'a u64>, b: Option<&'a u64>) -> Option<&'a u64> {
    if a.is_some() { None } else { b }
}

fn run_with<const F: bool>(bytes: &[u8], check: bool) -> String {
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
    let Some((mut map0, map1, root0, root1)) = decode_header(&mut d) else {
        return "EMPTY\n".to_string();
    };
    let snap0 = map0.clone();
    let mut out = String::new();
    {
        let a = map1.read_zipper_at_path(&root1);
        let b = snap0.read_zipper_at_path(&root0);
        let oz = if F {
            OverlayZipper::with_mapping(a, b, b_unless_a as Mapping)
        } else {
            OverlayZipper::new(a, b)
        };
        let mut rz: Abs<_, F> = Abs::new(oz, &root1);
        let mut wz = map0.write_zipper_at_path(&root0);
        run_ops(&mut d, &mut out, &mut wz, &root0, &mut rz, &root1, check);
    }
    trailer(&mut out, &map0, &map1, &root0, &root1);
    out
}

/// `--source overlay`: the default mapping (`a.or(b)`).
pub fn run(bytes: &[u8], check: bool) -> String {
    run_with::<false>(bytes, check)
}

/// `--source overlay-filter`: the `b_unless_a` mapping.
pub fn run_filter(bytes: &[u8], check: bool) -> String {
    run_with::<true>(bytes, check)
}
