//! `PrefixZipper`: a source zipper's trie presented under an extra prefix.
//!
//! `PrefixZipper::new(P, src)` presents the trie `src` reads (from its root,
//! including the root value) as if it sat at the absolute path `P`;
//! `set_root_prefix_path(P[..k])` / `with_origin(P[..k])` make the first `k`
//! bytes of `P` the zipper's `root_prefix_path`, so the rest of `P` is part of
//! its own `path`.  The view is therefore "map1's subtrie at the source root,
//! moved under `P`", rooted at `P[..k]`:
//!
//! * every location along `P` exists (a prefix path exists iff the source's
//!   root does, and the header always creates the source's root), carries no
//!   value, and has exactly one child, the next byte of `P`;
//! * the source's root value is the value at `P` itself;
//! * leaving `P` (a byte that is not the next prefix byte) leaves the trie.
//!
//! [`config`] derives `P`, the source root and `k` from the two header roots,
//! so the wire format is unchanged.  `Sources/Prefix.lean` computes the same
//! configuration and view.
//!
//! `PrefixZipper` has the native read zipper's whole trait surface (forking,
//! subtries, read-only values and iteration), so it is a full merge source.

use pathmap::zipper::*;

use crate::full_read_source;
use crate::harness::*;
use crate::sources::trailer;

/// The `PrefixZipper` construction for one input.
pub struct Config {
    /// The prefix `P` the source's trie is presented under.
    pub prefix: Vec<u8>,
    /// Where the wrapped read zipper over map1 is rooted (root1 or `[]`).
    pub source_root: Vec<u8>,
    /// `P[..k]` is the zipper's `root_prefix_path`.
    pub k: usize,
    /// Set the root prefix with `with_origin` rather than `set_root_prefix_path`.
    pub with_origin: bool,
}

/// Derive the configuration from the two header roots (`prefixConfig` in
/// `Sources/Prefix.lean`).  `h` mixes both roots; its low bits pick the
/// prefix among: the empty prefix (the crate's own tests use `b""`), root0,
/// `[2, 1] ++ root0` (a longer prefix), and root1 (with the source at root1
/// this is the identity: the native view below root1).
pub fn config(root0: &[u8], root1: &[u8]) -> Config {
    let h = root0
        .iter()
        .chain(root1.iter())
        .fold(root0.len() * 4 + root1.len(), |a, &b| a * 5 + b as usize + 1);
    let prefix = match h % 4 {
        0 => vec![],
        1 => root0.to_vec(),
        2 => [&[2u8, 1][..], root0].concat(),
        _ => root1.to_vec(),
    };
    let source_root = if (h / 4) % 2 == 0 { root1.to_vec() } else { vec![] };
    let k = (h / 8) % (prefix.len() + 1);
    let with_origin = (h / 8 / (prefix.len() + 1)) % 2 == 1;
    Config { prefix, source_root, k, with_origin }
}

/// Merges skip unless the focus is in the source (at or below `P`).
///
/// KNOWN CRATE BUG (`lean/findings/prefix.md`, "merge from the prefix stem"):
/// `get_focus`/`get_focus_at` delegate to the source zipper, which sits at its
/// own root while the focus is inside the prefix, so `graft`, `join_into`,
/// `meet_into`, ... read the source's root node instead of "rest of the prefix,
/// then the source", and a focus that has left the prefix reads the whole
/// source instead of nothing.  It corrupts map0 for the rest of the run, so
/// those merges are skipped (`Source.prefix.mergeAt` mirrors this).  Fixed
/// upstream by 1e95979, which this branch does not have.
fn merge_at<Z>(z: &PrefixZipper<'_, Z>) -> bool {
    z.prefix_path_below_focus() == Some(&[][..])
}

impl<'pre, 'a, 'p> ReadSource for PrefixZipper<'pre, ReadZipperUntracked<'a, 'p, u64>> {
    full_read_source!("skip:prefix", |z| merge_at(z));
}

pub fn run(bytes: &[u8], check: bool) -> String {
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
    let Some((mut map0, map1, root0, root1)) = decode_header(&mut d) else {
        return "EMPTY\n".to_string();
    };
    let cfg = config(&root0, &root1);
    // `ROOT1` in the trailer is the read zipper's root, as in the model.
    let root = cfg.prefix[..cfg.k].to_vec();
    let mut out = String::new();
    {
        let src = map1.read_zipper_at_path(&cfg.source_root);
        let mut rz = PrefixZipper::new(cfg.prefix.clone(), src);
        if cfg.with_origin {
            rz = rz.with_origin(&root).expect("root is a prefix of P");
        } else {
            rz.set_root_prefix_path(&root).expect("root is a prefix of P");
        }
        let mut wz = map0.write_zipper_at_path(&root0);
        run_ops(&mut d, &mut out, &mut wz, &root0, &mut rz, &root, check);
    }
    trailer(&mut out, &map0, &map1, &root0, &root);
    out
}
