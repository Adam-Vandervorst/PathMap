//! `ZipperHead`'s tracked zippers: `--source head`.
//!
//! The write zipper is a `WriteZipperTracked` from
//! `write_zipper_at_exclusive_path(root0)` on a head over map0, and the read
//! zipper a `ReadZipperTracked` from a head over map1.  Both are native
//! zippers handed out under the head's exclusivity tracking, so the view is
//! the native one (map1 at root1) and every operation is held to the native
//! specification (`Sources/Head.lean`).
//!
//! `ReadZipperTracked` implements the conditional (witness) forms of
//! `ZipperReadOnlyValues` / `ZipperReadOnlyIteration` rather than those traits,
//! so ops 51 and 52 run through `get_val_with_witness` /
//! `to_next_get_val_with_witness`, which must answer exactly as the
//! unconditional forms do.  It implements `ZipperReadOnlySubtries` (handing out
//! `TrieRefOwned`), so op 75 runs on both sides.
//!
//! Which head and which constructors, from the decoder position after the
//! header (`hdr`, the same number `Fuzz.header` leaves):
//!
//! * `hdr % 2`: `read_zipper_at_path` (0) or `read_zipper_at_borrowed_path` (1).
//! * `hdr / 2 % 3`: heads from `PathMap::zipper_head` (0),
//!   `PathMap::into_zipper_head(&[])` + `ZipperHeadOwned::into_map` (1), or
//!   `ZipperWriting::zipper_head` on a write zipper at the map root (2).
//! * `hdr / 6 % 2`: the write zipper is dropped (0) or handed back with
//!   `cleanup_write_zipper` (1), which prunes its root path when it is left
//!   dangling (`Source.head.finalMap0` in the model).

use pathmap::zipper::*;

use crate::harness::*;
use crate::sources::trailer;

/// [`ReadSource`] for a native read zipper that has the witness forms of the
/// read-only value traits (`ZipperReadOnlyConditionalValues`,
/// `ZipperReadOnlyConditionalIteration`) instead of the plain ones, and
/// otherwise the full native surface: subtries, forking, merges, trie refs.
#[macro_export]
macro_rules! witness_read_source {
    ($skip:expr) => {
        const SKIP: &'static str = $skip;
        $crate::trie_ref_source!();
        $crate::witness_iter_source!();
        fn dump_fork(&self) -> Option<String> {
            Some($crate::harness::dump_fork(self))
        }
        fn make_map_val_count(&self) -> Option<usize> {
            Some(self.make_map().val_count())
        }
        /// `get_val_with_witness` against `val`.  There is no witness form of
        /// `get_val_at`, so the second component is `val_at` itself.
        fn get_val_probe(&self, path: &[u8]) -> Option<(Option<u64>, Option<u64>, bool)> {
            let w = self.witness();
            let g = self.get_val_with_witness(&w).copied();
            let ga = self.val_at(path).copied();
            Some((g, ga, g == self.val().copied()))
        }
        fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)> {
            let w = self.witness();
            let got = self.to_next_get_val_with_witness(&w).copied();
            let agree = got == self.val().copied() || (got.is_none() && self.at_root());
            Some((got.is_some(), got, agree))
        }
        fn do_graft<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W) -> bool {
            wz.graft(self);
            true
        }
        fn do_graft_masked<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W, m: ::pathmap::utils::ByteMask, ru: bool) -> bool {
            wz.graft_masked_branches(self, m, ru);
            true
        }
        fn do_graft_child_maps<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W, m: ::pathmap::utils::ByteMask, ru: bool) -> bool {
            let maps: Vec<::pathmap::PathMap<u64>> = m
                .iter()
                .map(|b| {
                    // As native: a clone moved to the child (`move_to_path` for
                    // `ReadZipperOwned::clone`, see `do_meet_2`).  A fork would be
                    // `None` at a missing focus.
                    let mut c = self.clone();
                    c.move_to_path(self.path());
                    c.descend_to_byte(b);
                    c.make_map()
                })
                .collect();
            wz.graft_child_maps(m, maps, ru);
            true
        }
        fn do_meet_2<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W, path: &[u8]) -> Option<::pathmap::ring::AlgebraicStatus> {
            // `move_to_path` first: `ReadZipperOwned::clone` comes back at its
            // root, not at the focus (lean/findings/head-owned.md), and that is
            // checked by the owned source's `RCLONE` line, not here.
            let mut b = self.clone();
            b.move_to_path(self.path());
            b.descend_to(path);
            Some(wz.meet_2(self, &b))
        }
        fn do_graft_src_at<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W, p: &[u8]) -> bool {
            wz.graft_src_at(self, p);
            true
        }
        fn do_join_into<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W) -> Option<::pathmap::ring::AlgebraicStatus> {
            Some(wz.join_into(self))
        }
        fn do_join_map_into<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W) -> Option<::pathmap::ring::AlgebraicStatus> {
            Some(wz.join_map_into(self.make_map()))
        }
        fn do_meet_into<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W, prune: bool) -> Option<::pathmap::ring::AlgebraicStatus> {
            Some(wz.meet_into(self, prune))
        }
        fn do_subtract_into<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W, prune: bool) -> Option<::pathmap::ring::AlgebraicStatus> {
            Some(wz.subtract_into(self, prune))
        }
        fn do_restrict<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W) -> Option<::pathmap::ring::AlgebraicStatus> {
            Some(wz.restrict(self))
        }
        fn do_restricting<W: ::pathmap::zipper::ZipperWriting<u64>>(&self, wz: &mut W) -> Option<bool> {
            Some(wz.restricting(self))
        }
    };
}

impl<'a, 'p> ReadSource for ReadZipperTracked<'a, 'p, u64> {
    crate::witness_read_source!("skip:head");
    // Op 80 at the root: possibly a borrowed path, see `SKIP_K_PATH_BORROWED`.
    fn k_path_cold_skip(&self) -> Option<&'static str> {
        self.path().is_empty().then_some(SKIP_K_PATH_BORROWED)
    }
}

/// Run the program through zippers from two heads.
#[allow(clippy::too_many_arguments)]
fn drive<'t0, 't1, H0, H1>(
    d: &mut Dec,
    out: &mut String,
    zh0: &H0,
    zh1: &H1,
    root0: &[u8],
    root1: &[u8],
    borrowed: bool,
    cleanup: bool,
    check: bool,
) where
    H0: ZipperCreation<'t0, u64>,
    H1: ZipperCreation<'t1, u64>,
{
    // A fresh head grants any one path, so neither request can conflict.
    let mut wz = zh0.write_zipper_at_exclusive_path(root0).expect("fresh head refused a write zipper");
    if borrowed {
        let mut rz = zh1.read_zipper_at_borrowed_path(root1).expect("fresh head refused a read zipper");
        run_ops(d, out, &mut wz, root0, &mut rz, root1, check);
    } else {
        let mut rz = zh1.read_zipper_at_path(root1).expect("fresh head refused a read zipper");
        run_ops(d, out, &mut wz, root0, &mut rz, root1, check);
    }
    if cleanup {
        zh0.cleanup_write_zipper(wz);
    }
}

pub fn run(bytes: &[u8], check: bool) -> String {
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
    let Some((mut map0, mut map1, root0, root1)) = decode_header(&mut d) else {
        return "EMPTY\n".to_string();
    };
    let hdr = d.pos;
    let borrowed = hdr % 2 == 1;
    let cleanup = (hdr / 6) % 2 == 1;
    let mut out = String::new();
    match (hdr / 2) % 3 {
        0 => {
            let zh0 = map0.zipper_head();
            let zh1 = map1.zipper_head();
            drive(&mut d, &mut out, &zh0, &zh1, &root0, &root1, borrowed, cleanup, check);
        }
        1 => {
            let zh0 = std::mem::take(&mut map0).into_zipper_head([]);
            let zh1 = std::mem::take(&mut map1).into_zipper_head([]);
            drive(&mut d, &mut out, &zh0, &zh1, &root0, &root1, borrowed, cleanup, check);
            map0 = zh0.into_map();
            map1 = zh1.into_map();
        }
        _ => {
            let mut w0 = map0.write_zipper();
            let mut w1 = map1.write_zipper();
            let zh0 = w0.zipper_head();
            let zh1 = w1.zipper_head();
            drive(&mut d, &mut out, &zh0, &zh1, &root0, &root1, borrowed, cleanup, check);
        }
    }
    trailer(&mut out, &map0, &map1, &root0, &root1);
    out
}
