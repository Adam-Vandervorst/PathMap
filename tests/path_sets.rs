use pathmap::{
    PathMap,
    experimental::path_sets::*,
    utils::{BitMask, ByteMask},
    zipper::*,
};
use std::{cell::Cell, collections::BTreeSet};

type Space = BTreeSet<Vec<u8>>;
fn map(s: &Space) -> PathMap<()> {
    let mut m = PathMap::new();
    for p in s {
        m.set_val_at(p, ());
    }
    m
}
fn keys<V: Clone + Send + Sync + Unpin>(m: &PathMap<V>) -> Space {
    m.iter().map(|(p, _)| p).collect()
}
fn assert_value_supported<V: Clone + Send + Sync + Unpin>(m: &PathMap<V>) {
    let mut z = m.read_zipper();
    loop {
        assert!(
            z.at_root() || z.child_count() != 0 || z.is_val(),
            "output has a dangling tip"
        );
        if !z.to_next_step() {
            break;
        }
    }
}

fn oracle(a: &Space, b: &Space) -> Space {
    a.iter()
        .flat_map(|p| {
            b.iter().filter_map(move |q| {
                let n = p.iter().zip(q).take_while(|(x, y)| x == y).count();
                (n < p.len().min(q.len())).then(|| p[..n].to_vec())
            })
        })
        .collect()
}
fn spaces() -> Vec<Space> {
    let ps = [
        vec![],
        vec![0],
        vec![1],
        vec![0, 0],
        vec![0, 1],
        vec![1, 0],
        vec![1, 1],
    ];
    // Keep roots, a chain, and a fork in the exhaustive Miri matrix.
    #[cfg(miri)]
    let ps = &ps[..4];
    (0..1usize << ps.len())
        .map(|mask| {
            ps.iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, p)| p.clone())
                .collect()
        })
        .collect()
}

#[test]
fn exhaustive_binary_spaces() {
    let spaces = spaces();
    let maps: Vec<_> = spaces.iter().map(map).collect();
    for (a, ma) in spaces.iter().zip(&maps) {
        let min: Space = a
            .iter()
            .filter(|p| !a.iter().any(|q| q != *p && p.starts_with(q)))
            .cloned()
            .collect();
        let max: Space = a
            .iter()
            .filter(|p| !a.iter().any(|q| q != *p && q.starts_with(p)))
            .cloned()
            .collect();
        assert_value_supported(&basis(ma));
        assert_value_supported(&hull(ma));
        assert_value_supported(&branches(ma));
        assert_eq!(keys(&basis(ma)), min);
        assert_eq!(keys(&hull(ma)), max);
        assert_eq!(keys(&branches(ma)), oracle(a, a));
        for (b, mb) in spaces.iter().zip(&maps) {
            assert_eq!(keys(&divergence(ma, mb)), oracle(a, b), "{a:?}, {b:?}");
            let expected = a
                .iter()
                .filter(|p| b.iter().any(|q| q.starts_with(p)))
                .cloned()
                .collect();
            let retained = retain(ma, mb);
            assert_eq!(keys(&retained), expected, "retain {a:?}, {b:?}");
            assert_value_supported(&retained);
        }
    }
}

#[test]
fn values_dangling_paths_and_termination() {
    let mut a = PathMap::new();
    for (p, v) in [("foo", 10), ("food", 20), ("four", 30)] {
        a.set_val_at(p, v);
    }
    a.write_zipper_at_path(b"food/empty").create_path();
    a.write_zipper_at_path(b"x/empty").create_path();
    assert_eq!(
        basis(&a).iter().map(|(p, v)| (p, *v)).collect::<Vec<_>>(),
        vec![(b"foo".to_vec(), 10), (b"four".to_vec(), 30)]
    );
    assert_eq!(
        hull(&a).iter().map(|(p, v)| (p, *v)).collect::<Vec<_>>(),
        vec![(b"food".to_vec(), 20), (b"four".to_vec(), 30)]
    );
    assert_eq!(keys(&branches(&a)), [b"fo".to_vec()].into());
    let b = PathMap::single("foo", "different payload type");
    assert!(divergence(&b, &PathMap::single("food", ())).is_empty());
    let mut bare = PathMap::<()>::new();
    bare.write_zipper_at_path(b"four").create_path();
    assert!(divergence(&a, &bare).is_empty());
    assert!(basis(&bare).is_empty());
    assert!(hull(&bare).is_empty());
    assert!(branches(&bare).is_empty());
    a.set_val_at([], 99);
    assert_eq!(
        basis(&a).iter().map(|(p, v)| (p, *v)).collect::<Vec<_>>(),
        vec![(vec![], 99)]
    );
}

#[test]
fn focus_relative_replacement_and_restoration() {
    let mut a = PathMap::new();
    a.set_val_at("left/aa", 1);
    a.set_val_at("left/ab", 2);
    a.set_val_at("outside", 3);
    let b = PathMap::single("right/b", ());
    let mut out = PathMap::single("keep", ());
    out.set_val_at("dest/stale", ());
    let mut l = a.read_zipper();
    l.descend_to("left/");
    let mut r = b.read_zipper();
    r.descend_to("right/");
    {
        let mut o = out.write_zipper();
        o.descend_to("dest/");
        zipper_divergence(&mut l, &mut r, &mut o);
        assert_eq!(l.path(), b"left/");
        assert_eq!(r.path(), b"right/");
        assert_eq!(o.path(), b"dest/");
    }
    assert_eq!(keys(&out), [b"dest/".to_vec(), b"keep".to_vec()].into());
    let mut result = PathMap::single("keep", 7);
    result.set_val_at("dest/stale", 8);
    {
        let mut o = result.write_zipper_at_path(b"dest/");
        zipper_hull(&mut l, &mut o);
        assert_eq!(l.path(), b"left/");
        assert!(o.at_root());
    }
    assert_eq!(
        keys(&result),
        [b"dest/aa".to_vec(), b"dest/ab".to_vec(), b"keep".to_vec()].into()
    );
    l.descend_to("absent");
    {
        let mut o = result.write_zipper_at_path(b"dest/");
        zipper_basis(&mut l, &mut o);
        assert_eq!(l.path(), b"left/absent");
        assert!(o.at_root());
    }
    assert_eq!(keys(&result), [b"keep".to_vec()].into());
}

#[test]
fn deep_compressed_stem_and_all_bytes() {
    // Match the core long-key test's dense-only depth limit: those nodes
    // expand every byte and use recursive teardown.
    let depth = if cfg!(miri) {
        97
    } else if cfg!(feature = "all_dense_nodes") {
        2048
    } else {
        20_000
    };
    let stem = vec![42; depth];
    let mut p = stem.clone();
    p.push(0);
    let mut q = stem.clone();
    q.push(255);
    let a = PathMap::single(&p, ());
    let b = PathMap::single(&q, ());
    assert_eq!(keys(&divergence(&a, &b)), [stem].into());
    let mut dense = PathMap::new();
    for byte in 0..=255u8 {
        dense.set_val_at([byte], byte);
    }
    assert_eq!(keys(&branches(&dense)), [vec![]].into());
    assert_eq!(keys(&basis(&dense)), keys(&dense));
    assert_eq!(keys(&hull(&dense)), keys(&dense));
}

// A virtual binary trie with exact movement counts. It can describe 2^h values
// without allocating them, and panics if an algorithm requests val_count.
struct Counted {
    path: Vec<u8>,
    height: usize,
    offset: u8,
    root_value: bool,
    leaf_values: bool,
    moves: usize,
    masks: Cell<usize>,
}
impl Counted {
    fn new(height: usize) -> Self {
        Self {
            path: vec![],
            height,
            offset: 0,
            root_value: false,
            leaf_values: true,
            moves: 0,
            masks: Cell::new(0),
        }
    }
}
impl Zipper for Counted {
    fn path_exists(&self) -> bool {
        self.path.len() <= self.height
    }
    fn is_val(&self) -> bool {
        (self.root_value && self.path.is_empty())
            || (self.leaf_values && self.path.len() == self.height)
    }
    fn child_count(&self) -> usize {
        if self.path.len() < self.height { 2 } else { 0 }
    }
    fn child_mask(&self) -> ByteMask {
        self.masks.set(self.masks.get() + 1);
        let mut m = ByteMask::EMPTY;
        if self.child_count() != 0 {
            m.set_bit(self.offset);
            m.set_bit(self.offset + 1);
        }
        m
    }
}
impl ZipperValues<()> for Counted {
    fn val(&self) -> Option<&()> {
        self.is_val().then_some(&())
    }
}
impl ZipperMoving for Counted {
    fn depth(&self) -> usize {
        self.path.len()
    }
    fn focus_byte(&self) -> Option<u8> {
        self.path.last().copied()
    }
    fn val_count(&self) -> usize {
        panic!("subtree recount would break the bound")
    }
    fn descend_to<K: AsRef<[u8]>>(&mut self, k: K) {
        self.moves += k.as_ref().len();
        self.path.extend_from_slice(k.as_ref());
    }
    fn ascend(&mut self, steps: usize) -> usize {
        let n = steps.min(self.path.len());
        self.moves += n;
        self.path.truncate(self.path.len() - n);
        n
    }
    fn ascend_until(&mut self) -> usize {
        self.ascend(1)
    }
    fn ascend_until_branch(&mut self) -> usize {
        self.ascend(1)
    }
}

#[test]
fn linear_work_and_basis_cutoff() {
    let max_height = if cfg!(miri) { 4 } else { 9 };
    for h in 2..=max_height {
        let n = (1 << (h + 1)) - 1;
        let mut a = Counted::new(h);
        let mut out = PathMap::new();
        zipper_hull(&mut a, &mut out.write_zipper());
        assert_eq!(a.moves, 2 * (n - 1));
        assert_eq!(a.masks.get(), n);
        assert_eq!(out.val_count(), 1 << h);
        let mut a = Counted::new(h);
        let mut b = Counted::new(h);
        zipper_divergence(&mut a, &mut b, &mut out.write_zipper());
        assert_eq!(a.moves + b.moves, 4 * (n - 1));
        assert_eq!(out.val_count(), (1 << h) - 1);
        assert_eq!(a.depth() + b.depth(), 0);
        let mut a = Counted::new(h);
        let mut b = Counted::new(h);
        zipper_retain(&mut a, &mut b, &mut out.write_zipper());
        assert_eq!(a.moves + b.moves, 4 * (n - 1));
        assert_eq!(a.masks.get(), n);
        assert_eq!(b.masks.get(), n);
        assert_eq!(a.depth() + b.depth(), 0);
        assert_eq!(out.val_count(), 1 << h);
    }
    let mut a = Counted::new(1_000_000);
    a.root_value = true;
    let mut out = PathMap::new();
    zipper_basis(&mut a, &mut out.write_zipper());
    assert_eq!(a.moves, 0);
    assert_eq!(a.masks.get(), 0);
    assert!(out.contains([]));
}

#[test]
fn disjoint_fringe_stops_at_first_value_and_empty_annihilates() {
    let mut a = Counted::new(30);
    let mut b = Counted::new(30);
    b.offset = 2;
    let mut out = PathMap::new();
    zipper_divergence(&mut a, &mut b, &mut out.write_zipper());
    assert_eq!(keys(&out), [vec![]].into());
    assert!(a.moves + b.moves <= 8 * 30);
    let mut empty = Counted::new(0);
    empty.leaf_values = false;
    let mut enormous = Counted::new(1_000_000);
    zipper_divergence(&mut enormous, &mut empty, &mut out.write_zipper());
    assert_eq!(enormous.moves, 0);
    assert!(out.is_empty());
    let mut bare = Counted::new(8);
    bare.leaf_values = false;
    let mut actual = Counted::new(8);
    zipper_divergence(&mut bare, &mut actual, &mut out.write_zipper());
    assert!(out.is_empty());
    assert_eq!(bare.moves + actual.moves, 4 * ((1 << 9) - 2));
}

#[test]
fn retain_focus_payloads_and_bare_witnesses() {
    let mut a = PathMap::new();
    for (p, v) in [("left/", 1), ("left/a", 2), ("left/ab", 3), ("left/b", 4)] {
        a.set_val_at(p, v);
    }
    let mut b = PathMap::single("right/abc", "witness".to_owned());
    b.write_zipper_at_path(b"right/b/c").create_path();
    let mut out = PathMap::single("keep", 9);
    out.set_val_at("dest/stale", 10);
    let mut left = a.read_zipper();
    let mut right = b.read_zipper();
    left.descend_to("left/");
    right.descend_to("right/");
    {
        let mut dest = out.write_zipper();
        dest.descend_to("dest/");
        zipper_retain(&mut left, &mut right, &mut dest);
        assert_eq!(left.path(), b"left/");
        assert_eq!(right.path(), b"right/");
        assert_eq!(dest.path(), b"dest/");
    }
    assert_eq!(
        out.iter().map(|(p, v)| (p, *v)).collect::<Vec<_>>(),
        vec![
            (b"dest/".to_vec(), 1),
            (b"dest/a".to_vec(), 2),
            (b"dest/ab".to_vec(), 3),
            (b"keep".to_vec(), 9)
        ]
    );
    right.descend_to("b");
    zipper_retain(
        &mut left,
        &mut right,
        &mut out.write_zipper_at_path(b"dest/"),
    );
    assert_eq!(keys(&out), [b"keep".to_vec()].into());
    assert_eq!(right.path(), b"right/b");
}

#[test]
fn retain_fringe_witness_and_empty_shortcuts() {
    let mut arg = Counted::new(0);
    let mut witnesses = Counted::new(30);
    let mut out = PathMap::new();
    zipper_retain(&mut arg, &mut witnesses, &mut out.write_zipper());
    assert_eq!(arg.moves, 0);
    assert_eq!(witnesses.moves, 60);
    assert_eq!(witnesses.depth(), 0);
    assert_eq!(keys(&out), [vec![]].into());
    let mut bare = Counted::new(8);
    bare.leaf_values = false;
    zipper_retain(&mut arg, &mut bare, &mut out.write_zipper());
    assert_eq!(bare.moves, 2 * ((1 << 9) - 2));
    assert_eq!(bare.depth(), 0);
    assert!(out.is_empty());
    arg.leaf_values = false;
    let mut huge = Counted::new(1_000_000);
    zipper_retain(&mut arg, &mut huge, &mut out.write_zipper());
    assert_eq!(huge.moves, 0);
    assert!(out.is_empty());
}
