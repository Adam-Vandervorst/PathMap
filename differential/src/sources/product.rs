//! `ProductZipper` (`--source product`) and `ProductZipperG` (`--source productg`).
//!
//! Both are built over the same three factors:
//!
//! * primary: `map1.read_zipper_at_path(r)`, where `r` is the longest prefix of
//!   root1 at which map1 has children (`[]` if none).  The header always
//!   creates root1, and a random root1 is nearly always a fresh dangling leaf,
//!   so a primary at root1 itself would almost always be empty.
//! * a `PathMap` clone of map0 taken right after the header, before any op
//!   runs (it shares structure with the live map0 the write zipper mutates);
//! * map1 itself, at its root.
//!
//! Every secondary is a root-level zipper, clear of the documented "secondary
//! factors must be at node roots" panic.  The Lean side is
//! `lean/PathMapModel/Sources/Product.lean`: one view for both zippers.
//!
//! Neither type implements forking, subtries or read-only iteration, so `dump`,
//! `make_map`, every merge and `to_next_get_val` read `skip:product[g]`.
//! `ProductZipper` only has the conditional (witness) flavour of read-only
//! values, which `get_val_agrees` uses; `ProductZipperG` has `get_val`
//! directly, but its `val_count` is `unimplemented!()`.  Both report
//! `ZipperProduct` through `source_info`.

use pathmap::zipper::*;
use pathmap::PathMap;

use crate::harness::*;
use crate::sources::trailer;

/// `ZipperProduct`, as the model's `Product.info` renders it: factor count,
/// focus factor, and the path indices strictly above the focus.  (Both types
/// also keep the start of a factor entered *at* the focus, which the trait's
/// doc says is excluded; see `lean/findings/product.md`.)
fn product_info<Z: ZipperProduct>(z: &Z) -> String {
    let depth = z.path().len();
    let above: Vec<String> = z
        .path_indices()
        .iter()
        .filter(|&&i| i < depth)
        .map(|i| i.to_string())
        .collect();
    format!("P{}:{}:{}", z.factor_count(), z.focus_factor(), above.join("."))
}

thread_local! {
    /// The factors of the running input, as (map, root) pairs, for the skip
    /// conditions below.  Set by [`run_with`] before the program runs; the
    /// `ReadSource` methods only see the zipper, which cannot answer them
    /// without moving.
    static FACTORS: std::cell::RefCell<Vec<(PathMap<u64>, Vec<u8>)>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// The model's `Product.starts`: walking `path` from the root through the
/// factors, the depth at which each later factor is entered (where the
/// existing part of the path in the current factor ends at a leaf).
fn starts(factors: &[(PathMap<u64>, Vec<u8>)], path: &[u8]) -> Vec<usize> {
    let mut out = Vec::new();
    let (mut base, mut rest) = (0usize, path);
    for (m, root) in &factors[..factors.len().saturating_sub(1)] {
        let at = |j: usize| {
            let mut p = root.clone();
            p.extend_from_slice(&rest[..j]);
            m.read_zipper_at_path(p)
        };
        let k = (0..=rest.len()).rev().find(|&j| at(j).path_exists()).unwrap_or(0);
        if at(k).child_count() != 0 {
            break;
        }
        base += k;
        rest = &rest[k..];
        out.push(base);
    }
    out
}

/// Skip token for `val_at` (crate bugs, `lean/findings/product.md`): neither
/// type's `val_at` follows a path across a joint into the next factor, and
/// `ProductZipper::val_at` panics (or reads the wrong node) with the focus
/// inside the first node of a secondary factor -- a layout matter, so for it
/// every focus at or below a joint is declined.
pub const SKIP_VAL_AT_JOINT: &str = "skip:product-val-at-joint";
/// Whole-input skip: a factor whose root has no children (an empty map1 makes
/// the primary root childless too).  Both types mishandle an empty factor
/// (`lean/findings/product.md`).  The `-full` sources run without either skip.
pub const SKIP_EMPTY_FACTOR: &str = "skip:product-empty-factor";

/// The model's `Product.valAtSkip`.
fn val_at_skip_at(in_factor: bool, focus: &[u8], path: &[u8]) -> Option<&'static str> {
    let mut full = focus.to_vec();
    full.extend_from_slice(path);
    let es = FACTORS.with(|f| starts(&f.borrow(), &full));
    let crosses = es.iter().any(|&e| focus.len() <= e && e < full.len());
    let inside = in_factor && es.iter().any(|&e| e <= focus.len());
    (crosses || inside).then_some(SKIP_VAL_AT_JOINT)
}

impl<'f, 't> ReadSource for ProductZipper<'f, 't, u64> {
    const SKIP: &'static str = "skip:product";
    fn dump_fork(&self) -> Option<String> {
        None
    }
    fn make_map_val_count(&self) -> Option<usize> {
        None
    }
    /// `ProductZipper` has no `ZipperReadOnlyValues`, only the conditional
    /// flavour: the focus value through `get_val_with_witness`, which must agree
    /// with `val`.  There is no witnessed `get_val_at`, so the second component
    /// is `val_at` (the same value the model asks for).
    fn get_val_probe(&self, path: &[u8]) -> Option<(Option<u64>, Option<u64>, bool)> {
        let w = self.witness();
        let g = self.get_val_with_witness(&w).copied();
        let ga = self.val_at(path).copied();
        Some((g, ga, g == self.val().copied()))
    }
    fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)> {
        None
    }
    fn source_info(&self) -> Option<String> {
        Some(product_info(self))
    }
    fn val_at_skip(&self, path: &[u8]) -> Option<&'static str> {
        val_at_skip_at(true, self.path(), path)
    }
}

type PzG<'a> = ProductZipperG<'a, ReadZipperUntracked<'a, 'static, u64>, ReadZipperUntracked<'a, 'static, u64>, u64>;

impl<'a> ReadSource for PzG<'a> {
    const SKIP: &'static str = "skip:productg";
    const VAL_COUNT: bool = false;
    fn dump_fork(&self) -> Option<String> {
        None
    }
    fn make_map_val_count(&self) -> Option<usize> {
        None
    }
    fn get_val_probe(&self, path: &[u8]) -> Option<(Option<u64>, Option<u64>, bool)> {
        let (g, ga) = (self.get_val().copied(), self.get_val_at(path).copied());
        let agree = g == self.val().copied() && ga == self.val_at(path).copied();
        Some((g, ga, agree))
    }
    fn to_next_get_val_probe(&mut self) -> Option<(bool, Option<u64>, bool)> {
        None
    }
    fn source_info(&self) -> Option<String> {
        Some(product_info(self))
    }
    fn val_at_skip(&self, path: &[u8]) -> Option<&'static str> {
        val_at_skip_at(false, self.path(), path)
    }
}

/// The primary's root: the longest prefix of `root1` at which `map1` has
/// children, else `[]` (the model's `Product.productRoot`).
pub fn product_root(map1: &PathMap<u64>, root1: &[u8]) -> Vec<u8> {
    (0..=root1.len())
        .rev()
        .find(|&j| map1.read_zipper_at_path(&root1[..j]).child_count() > 0)
        .map(|j| root1[..j].to_vec())
        .unwrap_or_default()
}

fn run_with(bytes: &[u8], check: bool, generic: bool, full: bool) -> String {
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
    let Some((mut map0, map1, root0, root1)) = decode_header(&mut d) else {
        return "EMPTY\n".to_string();
    };
    let snap = map0.clone();
    let r = product_root(&map1, &root1);
    if !full && (snap.read_zipper().child_count() == 0 || map1.read_zipper().child_count() == 0) {
        return format!("{SKIP_EMPTY_FACTOR}\n");
    }
    // No factors, no `val_at` skip: the `-full` sources run without any of
    // this source's skips, so every product bug reproduces through them.
    FACTORS.with(|f| {
        *f.borrow_mut() = if full {
            Vec::new()
        } else {
            vec![(map1.clone(), r.clone()), (snap.clone(), vec![]), (map1.clone(), vec![])]
        }
    });
    let mut out = String::new();
    {
        let primary = map1.read_zipper_at_path(&r);
        let secondaries = [snap.read_zipper(), map1.read_zipper()];
        let mut wz = map0.write_zipper_at_path(&root0);
        if generic {
            let mut rz: PzG = ProductZipperG::new(primary, secondaries);
            run_ops(&mut d, &mut out, &mut wz, &root0, &mut rz, &r, check);
        } else {
            let mut rz = ProductZipper::new(primary, secondaries);
            run_ops(&mut d, &mut out, &mut wz, &root0, &mut rz, &r, check);
        }
    }
    // ROOT1 is the read zipper's root, as the model prints it (the view's root).
    trailer(&mut out, &map0, &map1, &root0, &r);
    if full {
        // The skip token is the zipper type's `SKIP` (`skip:product[g]`); the
        // model derives it from the source name, which here has `-full`.
        let (from, to) = if generic {
            ("=skip:productg ", "=skip:productg-full ")
        } else {
            ("=skip:product ", "=skip:product-full ")
        };
        out = out.replace(from, to);
    }
    out
}

pub fn run(bytes: &[u8], check: bool) -> String {
    run_with(bytes, check, false, false)
}

pub fn run_g(bytes: &[u8], check: bool) -> String {
    run_with(bytes, check, true, false)
}

/// `product` without the empty-factor skip.
pub fn run_full(bytes: &[u8], check: bool) -> String {
    run_with(bytes, check, false, true)
}

/// `productg` without the empty-factor skip.
pub fn run_g_full(bytes: &[u8], check: bool) -> String {
    run_with(bytes, check, true, true)
}
