/// Regression test for psubtract_dyn bug on LineListNode.
///
/// LineListNode::subtract_from_slot_contents (line_list_node.rs:1159)
/// panics when `other` has a child subtree at a key where `self` has
/// a value, because it assumes `node_get_val(onward_key)` returns Some.
///
/// This is triggered when `other` is a node produced by join_into
/// (pjoin_dyn internally) that has children at a path prefix where the
/// original node stored a value at the exact key.
#[cfg(test)]
mod tests {
    use crate::PathMap;
    use crate::ring::*;
    use crate::zipper::ZipperWriting;

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct V(u32);

    impl Lattice for V {
        fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> {
            if self.0 == other.0 { AlgebraicResult::Identity(SELF_IDENT) }
            else { AlgebraicResult::Element(V(self.0.max(other.0))) }
        }
        fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> {
            if self.0 == other.0 { AlgebraicResult::Identity(SELF_IDENT) }
            else { AlgebraicResult::Element(V(self.0.min(other.0))) }
        }
    }

    impl DistributiveLattice for V {
        fn psubtract(&self, other: &Self) -> AlgebraicResult<Self> {
            if self.0 <= other.0 { AlgebraicResult::None }
            else { AlgebraicResult::Identity(SELF_IDENT) }
        }
    }

    /// Reproduces the crash using only public PathMap API.
    ///
    /// Build two maps with string keys at different steps, join them
    /// (creating a synthetic node via pjoin_dyn internally), then
    /// subtract the joined result from a third map.  At n=200 with
    /// keys "k_0", "k_1", etc., the internal trie structure creates
    /// LineListNodes whose compressed keys hit the buggy code path.
    #[test]
    fn psubtract_dyn_linelistnode_crash() {
        let n = 200u32;

        // Build 8 maps with keys "k_{j*step}" for step 1..8
        let maps: Vec<PathMap<V>> = (0..8).map(|i| {
            let mut m = PathMap::<V>::new();
            let step = (i + 1) as u32;
            for j in 0..n {
                let k = j * step;
                m.set_val_at(format!("k_{}", k).as_bytes(), V(k));
            }
            m
        }).collect();

        // Chain of operations using only public zipper API:
        // ((((A|B) & C) | D) & E) | F) & G) \ H
        let mut r = maps[0].clone();
        r.write_zipper().join_into(&maps[1].read_zipper());       // A | B
        r.write_zipper().meet_into(&maps[2].read_zipper(), true); // & C
        r.write_zipper().join_into(&maps[3].read_zipper());       // | D
        r.write_zipper().meet_into(&maps[4].read_zipper(), true); // & E
        r.write_zipper().join_into(&maps[5].read_zipper());       // | F
        r.write_zipper().meet_into(&maps[6].read_zipper(), true); // & G
        r.write_zipper().subtract_into(&maps[7].read_zipper(), true); // \ H

        // If we get here without panicking, the bug is fixed.
        // Sanity check: result should be non-empty.
        let mut rz = r.read_zipper();
        let mut count = 0;
        use crate::zipper::ZipperIteration;
        while rz.to_next_val() { count += 1; }
        assert!(count > 0);
    }
}
