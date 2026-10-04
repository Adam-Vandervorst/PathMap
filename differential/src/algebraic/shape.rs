//! What "the same result" means.
//!
//! Two routes through the same algebraic expression are compared on the trie
//! they produce, not on the calls they made.  A trie is rendered two ways:
//!
//! * [`Shape`] — every path the trie contains, with the value at it if any.
//!   Dangling paths (structure with no value under it) are included, so this
//!   distinguishes tries that `iter()` cannot tell apart.
//! * [`Values`] — only the paths that carry values.
//!
//! The split matters because the two have different authority.  Which paths
//! carry which values is settled: every route must agree, and a disagreement
//! is a bug in one of them.  Whether a dangling path survives an operation is
//! *not* settled (see `../../SPEC_WARTS.md`), and routes legitimately built on
//! `graft` of whole subtries will keep dangling structure that routes built by
//! walking and inserting cannot.  So a divergence confined to dangling paths
//! is reported as its own class rather than lumped in with a wrong value.
//!
//! Both renderings come off a zipper, not a `PathMap`, so a lazy zipper that
//! never materialises a trie — an `OverlayZipper`, say — is comparable against
//! an eagerly built map without special-casing.

use pathmap::PathMap;
use pathmap::zipper::{ZipperMoving, ZipperPath, ZipperValues};
use std::collections::BTreeMap;

use super::value::FuzzValue;

/// Every path in a trie, in depth-first order, with the value at it if any.
pub type Shape<V> = Vec<(Vec<u8>, Option<V>)>;

/// The paths of a trie that carry values.
pub type Values<V> = BTreeMap<Vec<u8>, V>;

/// Cap on paths recorded per trie.  A generated case that needs more than this
/// is not interesting enough to be worth the comparison cost; the cap is
/// recorded in the rendering so a truncated trie can never compare equal to a
/// complete one by accident.
pub const SHAPE_CAP: usize = 8192;

/// Marker path emitted when a zipper walks out of its own root.  No real path
/// can collide with it: generated paths use a small alphabet of low bytes.
pub const ESCAPED_ROOT: &[u8] = b"<ESCAPED-ROOT>";
/// Marker path emitted when [`SHAPE_CAP`] is hit.
pub const TRUNCATED: &[u8] = b"<TRUNCATED>";

/// Depth-first walk of everything at and below the zipper's root.
///
/// The root is recorded explicitly: `to_next_step` moves before it reports, so
/// a loop driven by it alone would miss the value at the empty path.
pub fn shape_of_zipper<V: FuzzValue, Z>(z: &mut Z) -> Shape<V>
where
    Z: ZipperMoving + ZipperPath + ZipperValues<V>,
{
    z.reset();
    let mut out: Shape<V> = vec![(Vec::new(), z.val().cloned())];
    loop {
        if out.len() >= SHAPE_CAP {
            out.push((TRUNCATED.to_vec(), None));
            break;
        }
        if !z.to_next_step() {
            break;
        }
        // A depth-first step from the root can only go deeper or sideways, so
        // returning to the empty path means the zipper left its own root --
        // `lean/FINDINGS.md` #3.  Stop rather than loop forever, and say so.
        if z.path().is_empty() {
            out.push((ESCAPED_ROOT.to_vec(), None));
            break;
        }
        out.push((z.path().to_vec(), z.val().cloned()));
    }
    out
}

pub fn shape_of_map<V: FuzzValue>(m: &PathMap<V>) -> Shape<V> {
    shape_of_zipper(&mut m.read_zipper())
}

/// The value-carrying subset of a [`Shape`].
pub fn values_of_shape<V: FuzzValue>(s: &Shape<V>) -> Values<V> {
    s.iter()
        .filter_map(|(p, v)| v.clone().map(|v| (p.clone(), v)))
        .collect()
}

/// The paths of a [`Shape`], values ignored.  Used by the laws that hold only
/// up to path presence, which is how the laws that depend on join and meet being
/// different functions are checked when the value type is not a lattice.
pub fn paths_of_shape<V: FuzzValue>(s: &Shape<V>) -> Vec<Vec<u8>> {
    s.iter().map(|(p, _)| p.clone()).collect()
}

/// Render a path the way the rest of the harness does, so traces interleave.
pub fn show_path(p: &[u8]) -> String {
    if p == ESCAPED_ROOT || p == TRUNCATED {
        String::from_utf8_lossy(p).into_owned()
    } else if p.is_empty() {
        "_".to_string()
    } else {
        p.iter().map(|b| format!("{b:02x}")).collect()
    }
}

pub fn show_shape<V: FuzzValue>(s: &Shape<V>) -> String {
    s.iter()
        .map(|(p, v)| match v {
            Some(v) => format!("{}:{}", show_path(p), v.show()),
            None => format!("{}:-", show_path(p)),
        })
        .collect::<Vec<_>>()
        .join(",")
}

pub fn show_values<V: FuzzValue>(v: &Values<V>) -> String {
    v.iter()
        .map(|(p, v)| format!("{}:{}", show_path(p), v.show()))
        .collect::<Vec<_>>()
        .join(",")
}

/// First point at which two shapes differ, for the failure report.
pub fn first_shape_diff<V: FuzzValue>(a: &Shape<V>, b: &Shape<V>) -> Option<String> {
    for i in 0..a.len().max(b.len()) {
        match (a.get(i), b.get(i)) {
            (Some(x), Some(y)) if x == y => continue,
            (Some(x), Some(y)) => {
                return Some(format!(
                    "at #{i}: {}:{} vs {}:{}",
                    show_path(&x.0),
                    x.1.as_ref().map(|v| v.show()).unwrap_or("-".into()),
                    show_path(&y.0),
                    y.1.as_ref().map(|v| v.show()).unwrap_or("-".into()),
                ));
            }
            (Some(x), None) => {
                return Some(format!("at #{i}: {} vs <end>", show_path(&x.0)));
            }
            (None, Some(y)) => {
                return Some(format!("at #{i}: <end> vs {}", show_path(&y.0)));
            }
            (None, None) => break,
        }
    }
    None
}

/// First point at which two value maps differ.
pub fn first_values_diff<V: FuzzValue>(a: &Values<V>, b: &Values<V>) -> Option<String> {
    let mut keys: Vec<&Vec<u8>> = a.keys().chain(b.keys()).collect();
    keys.sort();
    keys.dedup();
    for k in keys {
        let (x, y) = (a.get(k), b.get(k));
        if x != y {
            return Some(format!(
                "at {}: {} vs {}",
                show_path(k),
                x.map(|v| v.show()).unwrap_or("-".into()),
                y.map(|v| v.show()).unwrap_or("-".into()),
            ));
        }
    }
    None
}
