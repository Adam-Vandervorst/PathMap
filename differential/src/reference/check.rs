//! `Check.lean` — the checks, plus a randomised sweep with no Lean counterpart.
//!
//! `Check.lean`'s `#guard`s are evaluated by the Lean compiler on every build;
//! here they are `#[test]`s, which is why the example carries `test = true`.

// ===========================================================================
// Check.lean — build-time checks
// ===========================================================================

#[cfg(test)]
mod tests {
    //! Two kinds of check, transcribed from `lean/PathMapModel/Check.lean`, where
    //! they are `#guard`s evaluated by the Lean compiler on every build:
    //!
    //! * **Regression fixtures** transcribed from `pathmap`'s own unit tests
    //!   (`src/write_zipper.rs`).  These pin the model to observed crate behaviour
    //!   for the operations whose semantics are hardest to read off the source —
    //!   pruning and `drop_head`.
    //! * **Law checks**: the metamorphic properties from [`crate::reference::laws`],
    //!   evaluated over a battery of maps chosen to cover branch points,
    //!   single-child runs, values at interior nodes, dangling paths, and the
    //!   empty map.

    use crate::reference::basic::U64Ops;
    use crate::reference::laws::*;
    use crate::reference::map;
    use crate::reference::pathmap::PathMap;
    use crate::reference::zipper::Zip;

    type T = PathMap<u64>;
    const OPS: U64Ops = U64Ops;

    /// Build a map from a list of path/value pairs.
    fn mk(entries: &[(&[u8], u64)]) -> T {
        let mut t = PathMap::empty();
        for (p, v) in entries {
            t.set_val(p, *v);
        }
        t
    }

    fn zip_at(t: &T, root: &[u8], path: &[u8]) -> Zip<u64> {
        Zip::at_path(t.clone(), root, path)
    }

    // -- fixtures -----------------------------------------------------------

    /// Branching at the root and at depth 1, with a value at an interior node.
    fn f_branch() -> T {
        mk(&[(&[], 0), (&[0], 1), (&[0, 0], 2), (&[0, 1], 3), (&[1], 4)])
    }
    /// A single-child run: the shape `descend_until` / `ascend_until` care about.
    fn f_run() -> T {
        mk(&[(&[0, 0, 0, 0], 7)])
    }
    /// Overlapping prefixes without a root value.
    fn f_side() -> T {
        mk(&[(&[0, 0], 9), (&[0, 2], 8), (&[2], 7)])
    }
    /// The empty map.
    fn f_empty() -> T {
        PathMap::empty()
    }
    /// A dangling path: `[0,1,2]` exists but carries no value.
    fn f_dangle() -> T {
        let mut t = mk(&[(&[0], 5)]);
        t.add_path(&[0, 1, 2]);
        t
    }
    /// Two values under a shared 2-byte prefix, plus a deeper third.
    fn f_deep() -> T {
        mk(&[(&[1, 1, 0], 1), (&[1, 1, 1], 2), (&[1, 1, 1, 3], 3)])
    }

    fn fixtures() -> Vec<T> {
        vec![f_branch(), f_run(), f_side(), f_empty(), f_dangle(), f_deep()]
    }

    /// Focus positions worth probing in each fixture.
    fn probes() -> Vec<Vec<u8>> {
        vec![
            vec![],
            vec![0],
            vec![1],
            vec![0, 0],
            vec![0, 1],
            vec![1, 1],
            vec![0, 1, 2],
            vec![3],
        ]
    }

    fn all_zips() -> Vec<Zip<u64>> {
        let mut zs = Vec::new();
        for t in fixtures() {
            for p in probes() {
                zs.push(Zip::at_path(t.clone(), &[], &p));
            }
        }
        zs
    }

    // -- regression fixtures from `src/write_zipper.rs` ----------------------

    /// `write_zipper_prune_path_test2`, first phase: removing the value at
    /// `[0,0,1,0,0]` and pruning removes exactly 3 bytes, back to the branch at
    /// `[0,0]`.
    #[test]
    fn prune_path_test2() {
        let t = mk(&[(&[0], 0), (&[0, 0, 0], 0), (&[0, 0, 1, 0, 0], 0)]);
        let mut z = zip_at(&t, &[], &[0, 0, 1, 0, 0]);
        z.remove_val(false);
        assert!(z.path_exists(), "remove_val(false) leaves the location dangling");
        assert_eq!(z.prune_path(), 3);
        assert!(!z.path_exists());
        assert_eq!(zip_at(&t, &[], &[0, 0]).child_count(), 2);
    }

    /// Same test, later phase: a chain with every value removed prunes all the
    /// way to the map root (7 bytes), and the root itself survives.
    #[test]
    fn prune_path_test2b() {
        let mut t = mk(&[(&[0, 0, 0, 1, 2, 3, 4], 0)]);
        t.remove_val(&[0, 0, 0, 1, 2, 3, 4]);

        let mut z = zip_at(&t, &[], &[0, 0, 0, 1, 2, 3, 4]);
        assert_eq!(z.prune_path(), 7);
        z.reset();
        assert!(z.path_exists(), "the map root always survives");

        // Pruning is a no-op above the dangling tip (the location still has a
        // child) and below it (the location does not exist).
        assert_eq!(zip_at(&t, &[], &[0, 0, 0, 1, 2, 3]).prune_path(), 0);
        assert_eq!(zip_at(&t, &[], &[0, 0, 0, 1, 2, 3, 4, 5]).prune_path(), 0);
    }

    /// Pruning *does* rise above the zipper's root, contradicting the doc comment
    /// on `ZipperWriting::prune_path`.  A zipper rooted at `[0,0]` looking at the
    /// dangling tip of the same chain prunes all 7 bytes, back to the map root —
    /// not the 5 that lie below its own root.  Verified against pathmap 0.3.1.
    #[test]
    fn prune_path_rises_above_zipper_root() {
        let mut t = mk(&[(&[0, 0, 0, 1, 2, 3, 4], 0)]);
        t.remove_val(&[0, 0, 0, 1, 2, 3, 4]);
        let mut z = zip_at(&t, &[0, 0], &[0, 1, 2, 3, 4]);
        assert_eq!(z.prune_path(), 7);
        assert!(z.trie.is_empty_map());
    }

    /// `write_zipper_drop_head_test3`: `[[0,0],[0,1],[1,0],[1,1]]` with
    /// `join_k_path_into(1)` collapses to 2 values.
    #[test]
    fn drop_head_test3() {
        let t = mk(&[(&[0, 0], 0), (&[0, 1], 1), (&[1, 0], 2), (&[1, 1], 3)]);
        let mut z = zip_at(&t, &[], &[]);
        z.join_k_path_into(&OPS, 1, true);
        assert_eq!(z.val_count(), 2);
    }

    /// `write_zipper_drop_head_test6`: dropping 4 bytes from paths that are at
    /// most 4 long annihilates everything, because values at depth exactly `k`
    /// are lost.
    #[test]
    fn drop_head_test6() {
        let t = mk(&[
            (&[193, 191, 193, 193, 191], 0),
            (&[193, 191, 193, 194, 12, 28], 1),
            (&[193, 191, 193, 194, 18, 9], 2),
            (&[193, 191, 194, 193, 191], 3),
            (&[193, 191, 194, 194, 12, 28], 4),
            (&[193, 191, 194, 194, 15, 47], 5),
            (&[193, 191, 194, 194, 18, 9], 6),
        ]);
        let mut z = zip_at(&t, &[], &[193, 191]);
        assert!(!z.join_k_path_into(&OPS, 4, true));
        assert_eq!(z.val_count(), 0);
    }

    /// `write_zipper_drop_head_test1`: under the root `123:`, dropping 4 bytes
    /// rewrites `abc:Bob` to `Bob` and `dog:Bob:Fido` to `Bob:Fido`.
    #[test]
    fn drop_head_test1() {
        let t = mk(&[(b"123:abc:Bob", 0), (b"123:dog:Bob:Fido", 1)]);
        let mut z = zip_at(&t, b"123:", &[]);
        z.join_k_path_into(&OPS, 4, true);
        let r = z.trie;
        assert_eq!(r.val_at(b"123:Bob"), Some(&0));
        assert_eq!(r.val_at(b"123:Bob:Fido"), Some(&1));
        assert_eq!(r.val_count(&[]), 2);
    }

    // -- structural invariants over every fixture ---------------------------

    #[test]
    fn structural_invariants() {
        for t in fixtures() {
            assert!(vals_exist(&t));
            assert!(prefix_closed(&t));
            assert!(val_count_agrees(&t));
            for p in probes() {
                assert!(child_mask_agrees(&t, &p));
            }
        }
    }

    // -- zipper law checks --------------------------------------------------

    #[test]
    fn zipper_laws() {
        for z in all_zips() {
            assert!(remove_val_leaves_path(&z));
            assert!(create_path_idempotent(&z));
            assert!(create_then_prune(&OPS, &z));
            assert!(descend_indexed_lands(&z));
            assert!(sibling_round_trip(&z));
            assert!(descend_until_observed_exact(&z));
            assert!(ascend_until_accounts(&z));
            assert!(to_next_val_monotone(&z));
            assert!(set_val_then_val(&OPS, &z, 42));
            assert!(take_then_graft(&OPS, &z));
            assert!(join_empty_identity(&OPS, &z));
            assert!(join_self_identity(&OPS, &z));
            assert!(remove_branches_keeps_val(&OPS, &z));
            assert!(remove_unmasked_full_mask(&OPS, &z));
            assert!(remove_unmasked_empty_mask(&OPS, &z));
            for p in probes() {
                assert!(descend_to_existing_lands(&z, &p));
            }
            for pre in [&[0u8][..], &[0, 1][..], &[2, 2][..]] {
                assert!(drop_head_undoes_insert_prefix(&OPS, &z, pre));
            }
        }
    }

    #[test]
    fn graft_laws() {
        let zs = all_zips();
        for z in &zs {
            for w in &zs {
                assert!(graft_then_make_map(&OPS, z, w));
            }
        }
        for s in fixtures() {
            for (a, b) in [
                (&[0u8][..], &[9u8][..]),
                (&[1][..], &[2][..]),
                (&[0, 0][..], &[1, 1][..]),
            ] {
                assert!(grafted_copies_independent(&OPS, &s, a, b, &[3, 7], 999));
            }
        }
    }

    // -- algebraic law checks -----------------------------------------------

    #[test]
    fn algebraic_laws() {
        let fs = fixtures();
        for a in &fs {
            assert!(join_idem(&OPS, a));
            assert!(meet_idem_on_vals(&OPS, a));
            assert!(meet_idem(&OPS, a));
            assert!(meet_pruned_idem(&OPS, a));
            assert!(sub_self_empty_vals(&OPS, a));
            assert!(restrict_self(&OPS, a));
            for b in &fs {
                assert!(join_comm_on_paths(&OPS, a, b));
                assert!(meet_comm_on_paths(&OPS, a, b));
                for c in &fs {
                    assert!(join_assoc(&OPS, a, b, c));
                }
            }
        }
    }

    // -- naive oracles ------------------------------------------------------
    //
    // `PathMap::join` / `meet` / `sub` are defined in terms of `ValOps`, which was
    // transcribed from `src/ring.rs` — so a defect in the crate's `Option<V>`
    // lattice impls could have been copied into the model, after which the
    // differential would agree and report nothing.
    //
    // These oracles are written from set theory instead: they say which *keys*
    // survive without consulting `ValOps`, `PathMap`, or anything else the model
    // shares with the crate.  They are deliberately naive and quadratic.  Where
    // they and the real definitions agree, the shared-derivation risk is excluded
    // for that operation.
    //
    // `U64Ops::psub` annihilates exactly when the two values are equal, which is
    // the one fact about the value type these need.

    fn keys(t: &T) -> Vec<Vec<u8>> {
        t.vals().map(|(k, _)| k.clone()).collect()
    }

    fn sorted_dedup(mut v: Vec<Vec<u8>>) -> Vec<Vec<u8>> {
        v.sort();
        v.dedup();
        v
    }

    /// Keys of `a` and `b` together: what `join` must produce.
    fn join_keys_oracle(a: &T, b: &T) -> Vec<Vec<u8>> {
        let mut v = keys(a);
        v.extend(keys(b));
        sorted_dedup(v)
    }

    /// Keys in both: what `meet` must produce.
    fn meet_keys_oracle(a: &T, b: &T) -> Vec<Vec<u8>> {
        sorted_dedup(keys(a).into_iter().filter(|k| b.val_at(k).is_some()).collect())
    }

    /// Keys of `a` whose value `b` does not annihilate: what `sub` must produce.
    /// For `u64`, `psubtract` annihilates exactly on equal values.
    fn sub_keys_oracle(a: &T, b: &T) -> Vec<Vec<u8>> {
        sorted_dedup(
            a.vals()
                .filter(|(k, av)| b.val_at(k) != Some(av))
                .map(|(k, _)| k.clone())
                .collect(),
        )
    }

    /// `restrict` against the `BTreeSet` oracle from
    /// `tests/pathmap_algebra_differential.rs`: a path of `a` survives when some
    /// prefix of it — the empty prefix and the path itself both count — carries a
    /// value in `b`.
    fn restrict_oracle(a: &T, b: &T) -> Vec<Vec<u8>> {
        a.vals()
            .filter(|(p, _)| (0..=p.len()).any(|i| b.val_at(&p[..i]).is_some()))
            .map(|(p, _)| p.clone())
            .collect()
    }

    #[test]
    fn naive_oracles_agree() {
        let fs = fixtures();
        for a in &fs {
            for b in &fs {
                assert_eq!(keys(&PathMap::join(&OPS, a, b)), join_keys_oracle(a, b));
                assert_eq!(keys(&PathMap::meet(&OPS, a, b)), meet_keys_oracle(a, b));
                assert_eq!(keys(&PathMap::sub(&OPS, a, b)), sub_keys_oracle(a, b));
                assert_eq!(keys(&map::restrict(a, b)), restrict_oracle(a, b));
            }
        }
    }

    /// The minimal shapes from `restrict_matches_btreeset_oracle`, which caught a
    /// real `prestrict` bug: a location that both carries a value and branches.
    #[test]
    fn restrict_minimal_shapes() {
        let shapes: Vec<Vec<(&[u8], u64)>> = vec![
            vec![(&[0, 1], 0), (&[0, 1, 2], 1)],
            vec![(&[0, 1], 0), (&[0, 1, 2], 1), (&[0, 1, 3], 2)],
            vec![(&[0], 0), (&[0, 1], 1), (&[0, 1, 2], 2)],
            vec![(&[0], 0), (&[0, 1, 2], 1), (&[0, 1, 3], 2)],
            vec![(&[0], 0), (&[0, 1], 1), (&[0, 1, 2], 2), (&[0, 1, 3], 3), (&[9, 9], 4)],
        ];
        for es in shapes {
            assert!(restrict_self(&OPS, &mk(&es)));
        }
    }
}

#[cfg(test)]
mod fuzz_tests {
    //! Randomised self-consistency, over far more states than the fixture
    //! battery reaches.
    //!
    //! The fixtures in [`crate::reference::check::tests`] are the ones the Lean `#guard`s use: 6
    //! maps × 8 probes.  They were chosen to cover the interesting *shapes*, but
    //! they are still 48 states, and a range query with an off-by-one in it can
    //! easily survive all 48.  So this walks random operation sequences, and
    //! after every step asserts
    //!
    //! * the map is still canonical — the one invariant `BTreeMap` does not
    //!   enforce for us, and the one every constructor here is responsible for;
    //! * every law from [`crate::reference::laws`] that applies to a single state.
    //!
    //! What this cannot catch is a *faithful-looking but wrong* transcription
    //! that is internally consistent — a mis-ordered `AlgebraicStatus::merge`,
    //! say.  Only a differential against the Lean model or the crate finds those.

    use crate::reference::basic::U64Ops;
    use crate::reference::laws::*;
    use crate::reference::pathmap::PathMap;
    use crate::reference::zipper::Zip;

    const OPS: U64Ops = U64Ops;

    /// splitmix64 — a deterministic PRNG, so a failure is reproducible from the
    /// seed alone and the test pulls in no dependency.
    struct Rng(u64);

    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9E3779B97F4A7C15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xBF58476D1CE4E5B9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
            z ^ (z >> 31)
        }
        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
        /// A short path over a 3-letter alphabet, so the generated maps share
        /// prefixes heavily — that is where branch points, dangling chains and
        /// single-child runs live.
        fn path(&mut self, max: u64) -> Vec<u8> {
            let n = self.below(max + 1);
            (0..n).map(|_| self.below(3) as u8).collect()
        }
    }

    /// Every law that is a predicate on one zipper state.
    fn check_state(z: &Zip<u64>) {
        assert!(z.trie.is_canonical(), "not canonical: {:?}", z.trie.entries.keys());
        assert!(vals_exist(&z.trie));
        assert!(prefix_closed(&z.trie));
        assert!(val_count_agrees(&z.trie));
        assert!(child_mask_agrees(&z.trie, &z.focus()));
        assert!(remove_val_leaves_path(z));
        assert!(create_path_idempotent(z));
        // Not universal: `prune_path` reaches above the zipper root, so a
        // dangling ancestor is swept up along with the created chain.
        if create_then_prune_applies(z) {
            assert!(create_then_prune(&OPS, z));
        }
        assert!(descend_indexed_lands(z));
        assert!(sibling_round_trip(z));
        assert!(descend_until_observed_exact(z));
        assert!(ascend_until_accounts(z));
        assert!(to_next_val_monotone(z));
        assert!(set_val_then_val(&OPS, z, 42));
        assert!(take_then_graft(&OPS, z));
        assert!(join_empty_identity(&OPS, z));
        assert!(join_self_identity(&OPS, z));
        assert!(remove_branches_keeps_val(&OPS, z));
        assert!(remove_unmasked_full_mask(&OPS, z));
        assert!(remove_unmasked_empty_mask(&OPS, z));
        assert!(drop_head_undoes_insert_prefix(&OPS, z, &[0, 1]));
        assert!(join_idem(&OPS, &z.trie));
        assert!(meet_idem_on_vals(&OPS, &z.trie));
        assert!(sub_self_empty_vals(&OPS, &z.trie));
        // Not universal: a dangling path with no valued ancestor is dropped by
        // `restrict`.  See `restrict_self`.
        if restrict_self_applies(&z.trie) {
            assert!(restrict_self(&OPS, &z.trie));
        }
    }

    #[test]
    fn random_programs_keep_every_law() {
        for seed in 0..256u64 {
            let mut r = Rng(seed.wrapping_mul(0x2545F4914F6CDD1D) | 1);
            let root = r.path(2);
            let mut z = Zip::at(PathMap::empty(), &root);
            // A source zipper over an independently seeded map, for the binary
            // operations.
            let mut src_map = PathMap::empty();
            for _ in 0..r.below(6) {
                src_map.set_val(&r.path(4), r.below(4));
            }
            let src = Zip::at_path(src_map, &[], &r.path(2));

            for _ in 0..40 {
                let k = r.path(3);
                match r.below(18) {
                    0 => {
                        z.set_val(r.below(4));
                    }
                    1 => {
                        z.remove_val(r.below(2) == 1);
                    }
                    2 => {
                        z.create_path();
                    }
                    3 => {
                        z.prune_path();
                    }
                    4 => {
                        z.remove_branches(r.below(2) == 1);
                    }
                    5 => {
                        z.descend_to(&k);
                    }
                    6 => {
                        z.ascend(r.below(3) as usize);
                    }
                    7 => {
                        z.ascend_until();
                    }
                    8 => {
                        z.descend_until();
                    }
                    9 => {
                        z.to_next_val();
                    }
                    10 => {
                        z.graft(&src);
                    }
                    11 => {
                        z.join_into(&OPS, &src);
                    }
                    12 => {
                        z.meet_into(&OPS, &src, r.below(2) == 1);
                    }
                    13 => {
                        z.subtract_into(&OPS, &src, r.below(2) == 1);
                    }
                    14 => {
                        z.restrict(&OPS, &src);
                    }
                    15 => {
                        z.insert_prefix(&k);
                    }
                    16 => {
                        z.join_k_path_into(&OPS, 1 + r.below(2) as usize, r.below(2) == 1);
                    }
                    _ => {
                        z.take_map(r.below(2) == 1);
                    }
                }
                check_state(&z);
                // The zipper must never leave the subtree it was created in.
                assert!(z.focus().starts_with(&root), "escaped its root");
            }
        }
    }
}
