//! `DiffZipper` (`pathmap::utils::debug::DiffZipper`): a debugging zipper that
//! drives two zippers in lockstep and panics (`assert_eq!`) the moment they
//! disagree on any answer.
//!
//! Construction (mirrored by `lean/PathMapModel/Sources/Diff.lean`):
//! `DiffZipper::new(map1.read_zipper_at_path(root1),
//! map1c.read_zipper_at_path(root1), false)`, where `map1c` is `map1.clone()`.
//! Two zippers over the same trie must agree, so it must present exactly the
//! native view: map1 at root1.  A panic is a divergence (either the two native
//! zippers disagreed, or `DiffZipper` compared the wrong things).
//!
//! `DiffZipper` forwards `Zipper`, `ZipperMoving` (including `val_count`),
//! `ZipperPath`, `ZipperAbsolutePath` and `ZipperIteration`.  It does **not**
//! implement `ZipperValues` / `ZipperValuesAt`, which the harness needs, so
//! [`DiffSrc`] supplies `val`/`val_at` from outside: the value map1 holds at
//! the `DiffZipper`'s own `origin_path()` (`++ k` for `val_at`).  Those answers
//! therefore check the reported path, not a `DiffZipper` value method (there is
//! none).  Everything else is forwarded unchanged.  No forking, subtries or
//! read-only values: `dump`, `make_map`, every merge, `get_val_agrees` and
//! `to_next_get_val` read `skip:diff`.

use pathmap::utils::ByteMask;
use pathmap::utils::debug::DiffZipper;
use pathmap::zipper::*;
use pathmap::PathMap;

use crate::harness::*;
use crate::sources::trailer;

pub struct DiffSrc<'m, Z> {
    z: Z,
    map: &'m PathMap<u64>,
}

impl<'m, Z: Zipper> Zipper for DiffSrc<'m, Z> {
    fn path_exists(&self) -> bool { self.z.path_exists() }
    fn is_val(&self) -> bool { self.z.is_val() }
    fn child_count(&self) -> usize { self.z.child_count() }
    fn child_mask(&self) -> ByteMask { self.z.child_mask() }
}

impl<'m, Z: ZipperMoving> ZipperMoving for DiffSrc<'m, Z> {
    fn depth(&self) -> usize { self.z.depth() }
    fn at_root(&self) -> bool { self.z.at_root() }
    fn focus_byte(&self) -> Option<u8> { self.z.focus_byte() }
    fn reset(&mut self) { self.z.reset() }
    fn val_count(&self) -> usize { self.z.val_count() }
    fn descend_to<K: AsRef<[u8]>>(&mut self, k: K) { self.z.descend_to(k) }
    fn descend_to_check<K: AsRef<[u8]>>(&mut self, k: K) -> bool { self.z.descend_to_check(k) }
    fn descend_to_existing<K: AsRef<[u8]>>(&mut self, k: K) -> usize { self.z.descend_to_existing(k) }
    fn descend_to_val<K: AsRef<[u8]>>(&mut self, k: K) -> usize { self.z.descend_to_val(k) }
    fn descend_to_byte(&mut self, k: u8) { self.z.descend_to_byte(k) }
    fn descend_to_existing_byte(&mut self, k: u8) -> bool { self.z.descend_to_existing_byte(k) }
    fn descend_indexed_byte(&mut self, i: usize) -> Option<u8> { self.z.descend_indexed_byte(i) }
    fn descend_first_byte(&mut self) -> Option<u8> { self.z.descend_first_byte() }
    fn descend_last_byte(&mut self) -> Option<u8> { self.z.descend_last_byte() }
    fn descend_until(&mut self) -> bool { self.z.descend_until() }
    fn descend_until_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool { self.z.descend_until_observed(obs) }
    fn descend_until_max_bytes(&mut self, n: usize) -> bool { self.z.descend_until_max_bytes(n) }
    fn descend_until_max_bytes_observed<Obs: PathObserver>(&mut self, n: usize, obs: &mut Obs) -> bool {
        self.z.descend_until_max_bytes_observed(n, obs)
    }
    fn ascend(&mut self, steps: usize) -> usize { self.z.ascend(steps) }
    fn ascend_byte(&mut self) -> bool { self.z.ascend_byte() }
    fn ascend_until(&mut self) -> usize { self.z.ascend_until() }
    fn ascend_until_branch(&mut self) -> usize { self.z.ascend_until_branch() }
    fn to_next_sibling_byte(&mut self) -> Option<u8> { self.z.to_next_sibling_byte() }
    fn to_prev_sibling_byte(&mut self) -> Option<u8> { self.z.to_prev_sibling_byte() }
    fn to_next_step(&mut self) -> bool { self.z.to_next_step() }
    fn to_next_step_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool { self.z.to_next_step_observed(obs) }
    fn to_prev_step(&mut self) -> bool { self.z.to_prev_step() }
    fn to_prev_step_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool { self.z.to_prev_step_observed(obs) }
}

impl<'m, Z: ZipperPath> ZipperPath for DiffSrc<'m, Z> {
    fn path(&self) -> &[u8] { self.z.path() }
    fn move_to_path<K: AsRef<[u8]>>(&mut self, p: K) -> usize { self.z.move_to_path(p) }
}

impl<'m, Z: ZipperAbsolutePath> ZipperAbsolutePath for DiffSrc<'m, Z> {
    fn origin_path(&self) -> &[u8] { self.z.origin_path() }
    fn root_prefix_path(&self) -> &[u8] { self.z.root_prefix_path() }
}

impl<'m, Z: ZipperAbsolutePath> ZipperValues<u64> for DiffSrc<'m, Z> {
    fn val(&self) -> Option<&u64> { self.map.val_at(self.z.origin_path()) }
}

impl<'m, Z: ZipperAbsolutePath> ZipperValuesAt<u64> for DiffSrc<'m, Z> {
    fn val_at<K: AsRef<[u8]>>(&self, p: K) -> Option<&u64> {
        let mut full = self.z.origin_path().to_vec();
        full.extend_from_slice(p.as_ref());
        self.map.val_at(&full)
    }
}

impl<'m, Z: ZipperIteration> ZipperIteration for DiffSrc<'m, Z> {
    fn to_next_val(&mut self) -> bool { self.z.to_next_val() }
    fn to_next_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool { self.z.to_next_val_observed(obs) }
    fn to_prev_val(&mut self) -> bool { self.z.to_prev_val() }
    fn to_prev_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool { self.z.to_prev_val_observed(obs) }
    fn descend_last_val(&mut self) -> bool { self.z.descend_last_val() }
    fn descend_last_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool { self.z.descend_last_val_observed(obs) }
    fn descend_last_path(&mut self) -> bool { self.z.descend_last_path() }
    fn descend_last_path_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool { self.z.descend_last_path_observed(obs) }
    fn descend_first_k_path(&mut self, k: usize) -> bool { self.z.descend_first_k_path(k) }
    fn descend_first_k_path_observed<Obs: PathObserver>(&mut self, k: usize, obs: &mut Obs) -> bool {
        self.z.descend_first_k_path_observed(k, obs)
    }
    fn to_next_k_path(&mut self, k: usize) -> bool { self.z.to_next_k_path(k) }
    fn to_next_k_path_observed<Obs: PathObserver>(&mut self, k: usize, obs: &mut Obs) -> bool {
        self.z.to_next_k_path_observed(k, obs)
    }
}

impl<'m, Z> ReadSource for DiffSrc<'m, Z>
where
    Z: ZipperAbsolutePath + ZipperIteration,
{
    const SKIP: &'static str = "skip:diff";
    fn dump_fork(&self) -> Option<String> { None }
    fn make_map_val_count(&self) -> Option<usize> { None }
    fn get_val_probe(&self, _path: &[u8]) -> Option<(Option<u64>, Option<u64>, bool)> { None }
    fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)> { None }
}

pub fn run(bytes: &[u8], check: bool) -> String {
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
    let Some((mut map0, map1, root0, root1)) = decode_header(&mut d) else {
        return "EMPTY\n".to_string();
    };
    let map1c = map1.clone();
    let mut out = String::new();
    {
        let dz = DiffZipper::new(map1.read_zipper_at_path(&root1), map1c.read_zipper_at_path(&root1), false);
        let mut rz = DiffSrc { z: dz, map: &map1 };
        let mut wz = map0.write_zipper_at_path(&root0);
        run_ops(&mut d, &mut out, &mut wz, &root0, &mut rz, &root1, check);
    }
    trailer(&mut out, &map0, &map1, &root0, &root1);
    out
}
