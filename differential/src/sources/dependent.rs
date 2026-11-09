//! `DependentProductZipperG`: a product zipper whose next factor is chosen by
//! a closure at each joint.
//!
//! The primary factor is map1 at root1.  Every time the zipper stands on a
//! leaf of its current factor (a location that exists and has no children)
//! it calls `enroll(ctx, path, n)`, where `path` is the path from root1 and
//! `n` the number of secondary factors already entered, and the closure picks
//! the next factor from a fixed set of snapshots taken right after the header
//! (so nothing aliases the live map0):
//!
//! ```text
//! n >= ctx.max_depth            -> no further factor
//! path = [] (the primary root)  -> no further factor          (strict only)
//! (n + |path| + Σ path) mod 4:
//!   0 -> map0 (snapshot) at its root
//!   1 -> map1 at its root
//!   2 -> map1 at root1 (the primary's own subtrie)
//!   3 -> no further factor
//! a factor with no children at its root -> no further factor  (strict only)
//! ```
//!
//! The two strict-only guards keep the closure away from two defects in when
//! the zipper calls it (lean/findings/dependent.md): a joint at the primary's
//! root is not entered until the first descend (D1), and a factor with nothing
//! below its root does not get the next one stacked on it until a later call
//! at the same place (D2).  Both make what the zipper presents depend on its
//! history, and both would otherwise contaminate most inputs.
//! `--source dependent-lazy` drops the guards, to replay those findings.
//!
//! The context carries the depth bound (`max_depth`) and a call counter that
//! the closure threads through but never reads, so the trie presented does not
//! depend on the order of calls.  `Sources/Dependent.lean` mirrors the choice.
//!
//! Capabilities: no `ZipperForking`, no `ZipperInfallibleSubtries` (so no merge
//! and no `make_map`: `ZipperSubtries::try_make_map` is `None` -- probed, so a
//! `Some` would diverge), no `ZipperReadOnlyIteration`, and `val_count` is
//! `unimplemented!`.  `ZipperReadOnlyValues` is served, and the probe also
//! checks `ZipperReadOnlyConditionalValues` (`get_val_with_witness`).

use pathmap::zipper::*;
use pathmap::PathMap;

use crate::harness::*;
use crate::sources::trailer;

/// The carried context: the nesting bound and a call counter.  `STRICT`
/// selects the closure (and the skip token): `dependent` or `dependent-lazy`.
#[derive(Clone, Copy, Debug)]
pub struct Ctx<const STRICT: bool> {
    pub max_depth: usize,
    pub calls: usize,
}

/// The nesting bound: at most this many secondary factors on any path.
pub const MAX_DEPTH: usize = 2;

type Rz<'a> = ReadZipperUntracked<'a, 'static, u64>;

impl<'a, F, const STRICT: bool> ReadSource for DependentProductZipperG<'a, Rz<'a>, Rz<'a>, u64, Ctx<STRICT>, F>
where
    F: Clone + for<'x> FnOnce(Ctx<STRICT>, &'x [u8], usize) -> (Ctx<STRICT>, Option<Rz<'a>>),
{
    const SKIP: &'static str = if STRICT { "skip:dependent" } else { "skip:dependent-lazy" };
    const VAL_COUNT: bool = false;
    fn dump_fork(&self) -> Option<String> {
        None
    }
    fn make_map_val_count(&self) -> Option<usize> {
        // `ZipperSubtries` is implemented but declines: no native subtries, no
        // map, no trie ref.  Probed so that a change shows up as a divergence.
        let _ = ZipperSubtries::<u64>::alloc(self);
        if ZipperSubtries::<u64>::native_subtries(self) || ZipperSubtries::<u64>::trie_ref(self).is_some() {
            return Some(usize::MAX);
        }
        // The factor bookkeeping, checked here because this probe otherwise
        // answers the skip token: a violation answers a number instead, which
        // no KNOWN entry covers.  `path_indices` are the depths at which the
        // factors on the stack begin, so they increase (factors only stack at
        // one depth through finding D2, which the strict closure avoids) and
        // none is below the focus; `focus_factor` counts the ones strictly
        // above it (a factor entered at the focus has not been moved into).
        // The doc's `path_indices().len() == focus_factor()` does not hold at
        // a joint, where the factor just entered is listed too (finding D4),
        // so only `len - focus_factor <= 1` is checked.
        let (pi, ff, depth) = (self.path_indices(), self.focus_factor(), self.depth());
        let increasing = pi.windows(2).all(|w| if STRICT { w[0] < w[1] } else { w[0] <= w[1] });
        let above = pi.iter().filter(|&&i| i < depth).count();
        if !increasing || pi.iter().any(|&i| i > depth) || ff != above || pi.len() > ff + 1 {
            return Some(usize::MAX - 1);
        }
        ZipperSubtries::<u64>::try_make_map(self).map(|m| m.val_count())
    }
    fn get_val_probe(&self, path: &[u8]) -> Option<(Option<u64>, Option<u64>, bool)> {
        let (g, ga) = (self.get_val().copied(), self.get_val_at(path).copied());
        let w = self.witness();
        let gw = self.get_val_with_witness(&w).copied();
        // Concrete-zipper queries, for coverage: neither is observable here.
        let _ = (self.is_shared(), self.shared_node_id());
        let agree = g == self.val().copied() && ga == self.val_at(path).copied() && gw == g;
        Some((g, ga, agree))
    }
    fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)> {
        None
    }
}

/// The factor choice; `Sources/Dependent.lean` `choose` mirrors it.
pub fn choose(path: &[u8], n: usize) -> usize {
    (n + path.len() + path.iter().map(|&b| b as usize).sum::<usize>()) % 4
}

/// The `enroll` closure over the snapshots (a function so the factors'
/// lifetime can be named).
fn make_enroll<'a, const STRICT: bool>(
    s0: &'a PathMap<u64>,
    s1: &'a PathMap<u64>,
    r1: &'a [u8],
) -> impl Clone + for<'x> FnOnce(Ctx<STRICT>, &'x [u8], usize) -> (Ctx<STRICT>, Option<Rz<'a>>) + 'a {
    let strict = STRICT;
    move |c: Ctx<STRICT>, path: &[u8], n: usize| {
        let next = Ctx { max_depth: c.max_depth, calls: c.calls + 1 };
        if n >= c.max_depth || (strict && path.is_empty()) {
            return (next, None);
        }
        let z = match choose(path, n) {
            0 => Some(s0.read_zipper()),
            1 => Some(s1.read_zipper()),
            2 => Some(s1.read_zipper_at_path(r1)),
            _ => None,
        };
        let z = z.filter(|z| !strict || z.child_count() > 0);
        (next, z)
    }
}

/// `--source dependent`: the strict closure (see the module docs).
pub fn run(bytes: &[u8], check: bool) -> String {
    run_with::<true>(bytes, check)
}

/// `--source dependent-lazy`: the closure without the two guards.  Diverges
/// on the two entry defects (lean/findings/dependent.md, D1 and D2); kept
/// to replay their corpus files.
pub fn run_lazy(bytes: &[u8], check: bool) -> String {
    run_with::<false>(bytes, check)
}

fn run_with<const STRICT: bool>(bytes: &[u8], check: bool) -> String {
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
    let Some((mut map0, map1, root0, root1)) = decode_header(&mut d) else {
        return "EMPTY\n".to_string();
    };
    // Snapshots for the factors, taken after the header; map1 is never written.
    let snap0: PathMap<u64> = map0.clone();
    let snap1: PathMap<u64> = map1.clone();
    let mut out = String::new();
    {
        let enroll = make_enroll::<STRICT>(&snap0, &snap1, &root1);
        let mut rz = DependentProductZipperG::new_enroll(
            map1.read_zipper_at_path(&root1),
            Ctx::<STRICT> { max_depth: MAX_DEPTH, calls: 0 },
            enroll,
        );
        rz.prepare_buffers();
        rz.reserve_buffers(64, 8);
        let mut wz = map0.write_zipper_at_path(&root0);
        run_ops(&mut d, &mut out, &mut wz, &root0, &mut rz, &root1, check);
    }
    trailer(&mut out, &map0, &map1, &root0, &root1);
    out
}
