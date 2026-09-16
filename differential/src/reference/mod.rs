//! An executable reference model of the `pathmap` trie and zipper API: a Rust
//! transcription of the Lean 4 specification in `lean/PathMapModel/`.
//!
//! See `lean/README.md` for the reasoning behind the specification and
//! `lean/FINDINGS.md` for what it found.  Every item names the `pathmap` item it
//! specifies, and the file layout mirrors the Lean one one-for-one, so drift
//! between the two is visible as a diff rather than hidden inside a module:
//!
//! | Lean                     | here            |
//! |--------------------------|-----------------|
//! | `Basic.lean`             | `basic.rs`      |
//! | `PathMap.lean`           | `pathmap.rs`    |
//! | `Zipper.lean`            | `zipper.rs`     |
//! | `Write.lean`             | `write.rs`      |
//! | `Map.lean`               | `map.rs`        |
//! | `Spec.lean` §2           | `laws.rs`       |
//! | `Check.lean`             | `check.rs`      |
//! | `Fuzz.lean`              | `fuzz.rs`       |
//!
//! It lives in the `differential` crate rather than in `pathmap/src/` because
//! nothing in the library may depend on it: it is a testing oracle, not a data
//! structure, and keeping it out of the crate proper is what makes "the model
//! shares no code with the implementation" a fact about the build rather than a
//! promise in a comment.
//!
//! # This is not a trie, and that is the point
//!
//! A trie is a prefix tree, which `pathmap` implements with four node types and
//! a great deal of care.  The model is a flat `BTreeMap<Vec<u8>, Option<V>>` of
//! whole paths.  It is not a prefix tree and does not try to be.
//!
//! That is deliberate.  This is a *specification*, and what it specifies is the
//! meaning a trie carries, not the trie.  A model shaped like the implementation
//! would inherit the implementation's structure, and then a bug in how that
//! structure is handled — a node type promoted wrongly, a child index off by
//! one, an empty node where a real one was expected — could be present in both
//! and cancel out.  Findings 14, 15 and 16 are bugs of exactly that kind, and
//! they are visible only because the model has no nodes to get wrong.
//!
//! # The model must never reach into the crate
//!
//! No file in this directory may `use pathmap::...`; not `utils::ByteMask`, not
//! `ring::AlgebraicStatus`, not a helper.  Shared code is shared risk.  In the
//! archive this was enforced by the build — the model was its own cargo example
//! target, which did not depend on `pathmap` at all — and it now lives beside
//! [`crate::harness`], which does.  So the rule is checked instead, by the
//! `model_does_not_touch_the_crate` test below, which reads these files and
//! fails if any of them names the crate.
//!
//! The comparison between model and crate belongs in the harness and in
//! `bin/in_process.rs`, not here.
//!
//! # Why `BTreeMap<Vec<u8>, Option<V>>`
//!
//! The Lean model keeps a list of `(Path, Option V)` pairs held canonical by
//! hand: sorted by the lexicographic path order, duplicate-free, prefix-closed,
//! and containing the empty path.  Rust's `Ord for Vec<u8>` **is** that order —
//! `[] < [0] < [0,0] < [0,255] < [1]` — which is the order a depth-first
//! traversal of a radix trie visits paths in.  So a `BTreeMap` discharges
//! "sorted" and "duplicate-free" structurally, its iteration order is depth-first
//! order for free, and every "the least existing path after the focus such
//! that ..." in the specification becomes a range query.  Prefix-closure and the
//! presence of the root remain the model's own responsibility;
//! `PathMap::mk` establishes them and [`laws::prefix_closed`] checks
//! them.
//!
//! Structural equality of two canonical maps is therefore observational
//! equality, which is what lets the model decide `AlgebraicStatus::Identity`
//! against `Element` (see `PathMap::beq_t`).
//!
//! # Deviations from the Lean model
//!
//! * The Lean model is purely functional: every operation returns a new `Zip`.
//!   Here the mutating operations take `&mut self` and return only what the
//!   corresponding `pathmap` method returns, so the trace front end can call the
//!   two side by side.  Where a law needs the prior state, it clones.
//! * `Zip` owns its `PathMap` (as in Lean, where a read zipper holds a snapshot
//!   and a write zipper holds the live map).  Operations that read one zipper
//!   and write another take the source by reference.
//! * The proved theorems of `Spec.lean` §1 have no counterpart: they are proofs,
//!   not tests.  The checkable laws of §2 are in [`laws`].
//! * `V: Clone` is required throughout; the Lean model is generic over any `V`.
//!
//! # The three front ends
//!
//! | binary | drives |
//! |---|---|
//! | `lean/.lake/build/bin/pathmap-oracle` | the Lean model (`lean/PathMapModel/Fuzz.lean`) |
//! | `target/release/pathmap_trace`        | the real crate ([`crate::harness`]) |
//! | `target/release/reference`            | the Rust model in this directory |
//!
//! `lean/differential.py` diffs any two of them.  Model-against-model —
//! `--model` — is the acceptance test for this port: the two are independent
//! transcriptions of the same specification in different languages, so a diff
//! means one of them is wrong and nothing about the crate is in question.
//!
//! Once that holds, `target/release/in_process` drops the pipes: it runs
//! [`fuzz::run`] and [`crate::harness::run`] on the same bytes in one process
//! and compares the traces in memory.

// The model is a specification: it defines the whole API surface whether or not
// any particular front end happens to call each item.  `laws` and `map` are
// reached only from `check.rs`, under `cfg(test)`.
#![allow(dead_code)]

pub mod basic;
pub mod pathmap;
pub mod zipper;
pub mod write;
pub mod map;
pub mod laws;

#[cfg(test)]
mod check;

pub mod fuzz;

#[cfg(test)]
mod tests {
    /// The model may not name the crate it is a model of.
    ///
    /// In the archive this was a property of the build: `examples/reference/`
    /// was its own cargo target and `pathmap` was not in scope for it at all.
    /// Here the model sits in a crate that does depend on `pathmap`, so the
    /// invariant has to be asserted rather than obtained for free — otherwise a
    /// single `use pathmap::utils::ByteMask` would quietly make the model share
    /// the implementation's bugs, and the differential would agree for the wrong
    /// reason.
    #[test]
    fn model_does_not_touch_the_crate() {
        // Spelled in halves so this file, which is itself part of the model
        // directory and is scanned like the rest, does not match its own needle.
        let crate_path = ["path", "map::"].concat();
        let extern_crate = ["extern crate ", "pathmap"].concat();
        let own_map = ["crate::reference::path", "map"].concat();
        let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/reference");
        let mut offenders = Vec::new();
        for entry in std::fs::read_dir(&dir).expect("src/reference must exist") {
            let path = entry.expect("readable dir entry").path();
            if path.extension().and_then(|e| e.to_str()) != Some("rs") {
                continue;
            }
            let src = std::fs::read_to_string(&path).expect("readable model file");
            for (n, line) in src.lines().enumerate() {
                // Doc comments talk *about* the crate; code may not name it.
                let code = line.trim_start();
                if code.starts_with("//") {
                    continue;
                }
                // The model's *own* map module is also called `pathmap`, so
                // strip its path before looking for the crate's.
                let code = code.replace(&own_map, "");
                if code.contains(&crate_path) || code.contains(&extern_crate) {
                    offenders.push(format!("{}:{}: {}", path.display(), n + 1, line.trim()));
                }
            }
        }
        assert!(
            offenders.is_empty(),
            "the reference model must not reach into the crate it models:\n{}",
            offenders.join("\n")
        );
    }
}
