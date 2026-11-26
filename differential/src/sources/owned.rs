//! The owned zippers: `--source owned`.
//!
//! The write zipper is `map0.into_write_zipper(root0)` (a `WriteZipperOwned`)
//! and the read zipper `map1.into_read_zipper(root1)` (a `ReadZipperOwned`),
//! or its `clone()`.  Both are native zippers that own their map, so the view
//! is the native one and the model is unchanged (`Sources/Owned.lean`); what
//! is new is the ownership plumbing, which extra lines after `ROOT1` check:
//!
//! * `ITER0` — `IntoIterator for WriteZipperOwned` (`OwnedZipperIter`) on a
//!   clone reset to its root: every value below the root, depth-first, paths
//!   relative to it (at most 64).
//! * `ITERF` — the same from a clone moved to `wz`'s focus: the iterator starts
//!   at the focus, so it yields the values at or after it in depth-first order.
//! * `W2R` — the fingerprint of the write zipper, or of the `ReadZipperOwned`
//!   `WriteZipperOwned::into_read_zipper` turns it into (same root and focus).
//! * `RCLONE` / `WCLONE` — the fingerprint of a `clone()` of each zipper, taken
//!   with the original off its root (`rz` after `reset` + `descend_last_path`,
//!   `wz` wherever the program left it).  A clone is the same zipper.  Last,
//!   because the clones lose their focus (a known defect) and an input is
//!   classified by its first differing line.
//! * `MAP0` comes from `into_map()` on whichever of the two is left.
//!
//! Variants, from the decoder position after the header (`hdr`): `hdr % 2`
//! makes `rz` the clone of a fresh owned read zipper; `hdr / 2 % 2` goes
//! through `into_read_zipper` before `into_map`.
//!
//! The trailer lines join their fields with `;` and `/`, never spaces, `,` or
//! `:`, so `differential.py`'s shape rules cannot mistake a divergence there
//! for a known class.

use core::fmt::Write as _;
use pathmap::zipper::*;

use crate::harness::*;
use crate::sources::trailer;

impl ReadSource for ReadZipperOwned<u64> {
    crate::witness_read_source!("skip:owned");
}

/// A fingerprint as one token.
fn fp<Z: ZipperMoving + ZipperPath + ZipperValues<u64> + ZipperAbsolutePath>(z: &Z, root: &[u8]) -> String {
    fingerprint(z, root).replace(' ', ";")
}

/// At most 64 `(path, value)` pairs from an owned write zipper's iterator.
fn iter_pairs(z: WriteZipperOwned<u64>) -> String {
    let v: Vec<String> = z.into_iter().take(DUMP_CAP).map(|(k, v)| format!("{}={v}", hex_path(&k))).collect();
    if v.is_empty() { "-".to_string() } else { v.join("/") }
}

pub fn run(bytes: &[u8], check: bool) -> String {
    let Some(mut d) = Dec::new(bytes) else { return "EMPTY\n".to_string(); };
    let Some((map0, map1, root0, root1)) = decode_header(&mut d) else {
        return "EMPTY\n".to_string();
    };
    let hdr = d.pos;
    let mut out = String::new();
    let mut wz = map0.into_write_zipper(&root0);
    let rz0 = map1.clone().into_read_zipper(&root1);
    let mut rz = if hdr % 2 == 1 { rz0.clone() } else { rz0 };
    run_ops(&mut d, &mut out, &mut wz, &root0, &mut rz, &root1, check);

    // The source's own lines go after the standard trailer (`MAP0`..`ROOT1`),
    // so `MAP0` (from `into_map`) is compared even on an input whose clone
    // line differs, and the clone lines come last of all: a clone that loses
    // its focus is a known defect, and an input is classified by its first
    // differing line.
    let mut extra = String::new();
    let wclone = fp(&wz.clone(), &root0);
    let mut c = wz.clone();
    c.reset();
    let _ = writeln!(extra, "ITER0 {}", iter_pairs(c));
    let mut c = wz.clone();
    c.move_to_path(wz.path());
    let _ = writeln!(extra, "ITERF {}", iter_pairs(c));
    let map0 = if (hdr / 2) % 2 == 1 {
        let r = wz.into_read_zipper();
        let _ = writeln!(extra, "W2R {}", fp(&r, &root0));
        r.into_map()
    } else {
        let _ = writeln!(extra, "W2R {}", fp(&wz, &root0));
        wz.into_map()
    };
    rz.reset();
    rz.descend_last_path();
    let _ = writeln!(extra, "RCLONE {}", fp(&rz.clone(), &root1));
    let _ = writeln!(extra, "WCLONE {wclone}");
    trailer(&mut out, &map0, &map1, &root0, &root1);
    out.push_str(&extra);
    out
}
