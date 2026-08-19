#![allow(unused)]

use divan::{Divan, Bencher, black_box};
use pasture_core::{
    containers::{BorrowedBuffer, VectorBuffer},
    layout::attributes::POSITION_3D,
    nalgebra::Vector3,
    nalgebra::Point3,
    math::AABB
};
use pasture_core::containers::BorrowedBufferExt;
use pasture_core::meta::Metadata;
use pasture_io::base::{PointReader, SeekToPoint};
use pasture_io::las::LASReader;
use pathmap::PathMap;
use pathmap::utils::BitMask;
use pathmap::zipper::{ReadZipperUntracked, WriteZipperUntracked, Zipper, ZipperMoving, ZipperReadOnlyValues, ZipperWriting};

fn main() {
    let divan = Divan::from_args().sample_count(3);

    divan.main();
}

#[divan::bench(args = ["build", "query", "knn"])]
fn run(bencher: Bencher, stage: &str) {
    let data_dir = match std::env::var("BENCH_DATA_DIR") {
        Ok(val) => std::path::PathBuf::from(val),
        Err(_) => std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benches"),
    };
    let file_path = data_dir.join("lion_takanawa.copc.laz");
    let mut reader = LASReader::from_path(file_path, false).expect("read file");
    let point_count: usize = reader.point_count().expect("point count meta data");
    let bbox: AABB<f64> = reader.las_metadata().bounds().expect("bbox meta data");
    let points: VectorBuffer = reader.read(point_count).expect("read all points");

    if points.point_layout().has_attribute(&POSITION_3D) {
        let positions = points.view_attribute::<Vector3<f64>>(&POSITION_3D);
        let mut rbbox = AABB::from_min_max(Point3::origin(), Point3::origin());
        positions.clone().into_iter().for_each(|point| rbbox = AABB::extend_with_point(&rbbox, &point.into()));
        // yuck, probably due to rounding, the real bbox does not coincide with the meta data bbox

        // change both occurrences of `BTMOctree` to `Octree` for the reference implementation 
        if stage == "build" { return bencher.bench_local(|| {
            let mut tree = BTMOctree::new(rbbox);
            positions.clone().into_iter().for_each(|point| tree.insert(point.into()));
            tree
        }) }
        let mut tree = BTMOctree::new(rbbox);
        positions.into_iter().for_each(|point| tree.insert(point.into()));

        let first_octant = Octree::child(&tree.bounds, 0);
        if stage == "query" { return bencher.bench_local(|| {
            let mut contained = 0;
            tree.range_query(first_octant, &mut |_| { contained += 1; true });
            assert_eq!(contained, 40641)
        }) }
        if stage == "knn" { return bencher.bench_local(|| {
            let k = 10;
            let topk = tree.knn(first_octant.center(), k);
            let reference = vec![&[-4.07, 1.09, -1.99], &[-4.12, 1.2, -1.87], &[-4.12, 1.2, -1.87], &[-4.09, 1.08, -2.0100000000000002], &[-4.09, 1.08, -2.0100000000000002], &[-4.12, 1.19, -1.87], &[-4.09, 1.08, -2.0], &[-4.1, 1.08, -2.0100000000000002], &[-4.09, 1.08, -1.99], &[-4.13, 1.17, -1.8900000000000001]];
            for (top, rtop) in topk.iter().zip(reference.iter()) { for (co, rco) in top.iter().zip(rtop.iter()) { assert_eq!(co, rco) } } 
            topk
        }) }
    } else {
        panic!("Point cloud files has no positions!");
    }
}


const LEAF_CAPACITY: usize = 8;
const MAX_DEPTH: usize = 12;

enum Node {
    Leaf { points: Vec<Point3<f64>> },
    Branch { children: [Option<Box<Node>>; 8] },
}

impl Default for Node {
    fn default() -> Self {
        Node::Leaf {
            points: Vec::with_capacity(LEAF_CAPACITY),
        }
    }
}

struct Octree {
    root: Node,
    bounds: AABB<f64>,
}

impl Octree {
    fn new(bounds: AABB<f64>) -> Self {
        Self {
            root: Node::default(),
            bounds,
        }
    }

    pub fn insert(&mut self, p: Point3<f64>) {
        if !self.bounds.contains(&p) {
            panic!("Point {:?} is outside the tree bounds {:?}", p, self.bounds);
        }
        Self::insert_rec(&mut self.root, p, self.bounds, 0);
    }

    fn insert_rec(node: &mut Node, p: Point3<f64>, bounds: AABB<f64>, depth: usize) {
        match node {
            Node::Leaf { points } => {
                if points.len() < LEAF_CAPACITY || depth >= MAX_DEPTH {
                    points.push(p);
                } else {
                    // Split the leaf.
                    let mut new_children: [Option<Box<Node>>; 8] = Default::default();
                    // Re‑insert existing points into children.
                    for &old_p in points.iter() {
                        let idx = Self::child_index(bounds.center(), old_p);
                        let child_bounds = Self::child(&bounds, idx);
                        new_children[idx].get_or_insert_with(|| Box::new(Node::default()));
                        Self::insert_rec(
                            new_children[idx].as_mut().unwrap(),
                            old_p,
                            child_bounds,
                            depth + 1,
                        );
                    }
                    // Clear points and convert to branch.
                    *node = Node::Branch { children: new_children };
                    // Insert the new point.
                    Self::insert_rec(node, p, bounds, depth);
                }
            }
            Node::Branch { children } => {
                let idx = Self::child_index(bounds.center(), p);
                let child_bounds = Self::child(&bounds, idx);
                children[idx].get_or_insert_with(|| Box::new(Node::default()));
                Self::insert_rec(
                    children[idx].as_mut().unwrap(),
                    p,
                    child_bounds,
                    depth + 1,
                );
            }
        }
    }

    #[inline]
    fn child_index(c: Point3<f64>, p: Point3<f64>) -> usize {
        ((p.x >= c.x) as usize)
            | (((p.y >= c.y) as usize) << 1)
            | (((p.z >= c.z) as usize) << 2)
    }

    /// Bounding box of the `index`th child octant.
    /// Octant bit pattern: x >> 0, y >> 1, z >> 2 (LSB is x).
    fn child(bx: &AABB<f64>, index: usize) -> AABB<f64> {
        let c = bx.center();
        let (min, max) = (
            Point3::new(
                if index & 1 == 0 { bx.min().x } else { c.x },
                if index & 2 == 0 { bx.min().y } else { c.y },
                if index & 4 == 0 { bx.min().z } else { c.z },
            ),
            Point3::new(
                if index & 1 == 0 { c.x } else { bx.max().x },
                if index & 2 == 0 { c.y } else { bx.max().y },
                if index & 4 == 0 { c.z } else { bx.max().z },
            ),
        );
        AABB::from_min_max(min, max)
    }

    /// Range query: collects points whose cells intersect `query` and are themselves inside.
    pub fn range_query<F : FnMut(Point3<f64>) -> bool>(&self, query: AABB<f64>, mut f: &mut F) -> bool {
        Self::query_rec(&self.root, self.bounds, &query, &mut f)
    }

    fn query_rec<F : FnMut(Point3<f64>) -> bool>(node: &Node, bounds: AABB<f64>, query: &AABB<f64>, f: &mut F) -> bool {
        if !bounds.intersects(query) {
            return true;
        }
        match node {
            Node::Leaf { points } => {
                for &p in points {
                    if query.contains(&p) {
                        if !f(p) { return false }
                    }
                }
            }
            Node::Branch { children } => {
                for idx in 0..8 {
                    if let Some(child) = &children[idx] {
                        let child_bounds = Self::child(&bounds, idx);
                        if !Self::query_rec(child, child_bounds, query, f) { return false }
                    }
                }
            }
        }
        true
    }

    #[inline]
    fn d2(s: Point3<f64>, o: Point3<f64>) -> f64 {
        let dx = s.x - o.x;
        let dy = s.y - o.y;
        let dz = s.z - o.z;
        dx * dx + dy * dy + dz * dz
    }

    fn boundary_d2(bbox: &AABB<f64>, p: Point3<f64>) -> f64 {
        let dx = if p.x < bbox.min().x { bbox.min().x - p.x }
        else if p.x > bbox.max().x { p.x - bbox.max().x }
        else { 0.0 };
        let dy = if p.y < bbox.min().y { bbox.min().y - p.y }
        else if p.y > bbox.max().y { p.y - bbox.max().y }
        else { 0.0 };
        let dz = if p.z < bbox.min().z { bbox.min().z - p.z }
        else if p.z > bbox.max().z { p.z - bbox.max().z }
        else { 0.0 };
        dx * dx + dy * dy + dz * dz
    }

    /// k‑nearest‑neighbour search (Euclidean) using best‑first traversal.
    pub fn knn(&self, query: Point3<f64>, k: usize) -> Vec<Point3<f64>> {
        if k == 0 {
            return Vec::new();
        }
        let mut best: Vec<(f64, Point3<f64>)> = Vec::with_capacity(k);
        Self::knn_rec(&self.root, self.bounds, query, k, &mut best);
        // Sort ascending before returning.
        best.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
        best.into_iter().map(|(_, p)| p).collect()
    }

    fn knn_rec(node: &Node, bounds: AABB<f64>, query: Point3<f64>, k: usize, best: &mut Vec<(f64, Point3<f64>)>) {
        // Prune if this branch cannot contain a closer point than current worst.
        let worst_dist = if best.len() == k {
            best.last().unwrap().0
        } else {
            f64::INFINITY
        };
        let box_dist = Self::boundary_d2(&bounds, query);
        if box_dist > worst_dist {
            return; // Entire node too far away.
        }

        match node {
            Node::Leaf { points } => {
                for &p in points {
                    let d2 = Self::d2(p, query);
                    Self::try_add_candidate(best, k, d2, p);
                }
            }
            Node::Branch { children } => {
                // Compute distance for each existing child and visit nearest first.
                // Collect (dist2, idx)
                let mut order: Vec<(f64, usize)> = Vec::with_capacity(8);
                for idx in 0..8 {
                    if children[idx].is_some() {
                        let child_bounds = Self::child(&bounds, idx);
                        order.push((Self::boundary_d2(&child_bounds, query), idx));
                    }
                }
                order.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
                for &(_, idx) in &order {
                    let child_bounds = Self::child(&bounds, idx);
                    let child = children[idx].as_ref().unwrap();
                    Self::knn_rec(child, child_bounds, query, k, best);
                }
            }
        }
    }

    #[inline]
    fn try_add_candidate(best: &mut Vec<(f64, Point3<f64>)>, k: usize, dist2: f64, p: Point3<f64>) {
        // Insert while keeping `best` sorted descending (worst at end).
        let pos = best.binary_search_by(|a| a.0.partial_cmp(&dist2).unwrap_or(std::cmp::Ordering::Equal));
        let insert_idx = match pos {
            Ok(i) | Err(i) => i,
        };
        best.insert(insert_idx, (dist2, p));
        if best.len() > k {
            best.pop(); // Remove farthest.
        }
    }
}

// note, this is a close copy of the above on purpose
// if we wanted to be fancy, we could do an 72-tree instead of an 8-tree which would suit the BTM very well
struct BTMOctree {
    root: PathMap<Vec<Point3<f64>>>,
    bounds: AABB<f64>,
}

impl BTMOctree {
    fn new(bounds: AABB<f64>) -> Self {
        Self {
            root: PathMap::default(),
            bounds,
        }
    }

    pub fn insert(&mut self, p: Point3<f64>) {
        if !self.bounds.contains(&p) {
            panic!("Point {:?} is outside the tree bounds {:?}", p, self.bounds);
        }
        let mut wz = self.root.write_zipper();
        Self::insert_rec(&mut wz, p, self.bounds, 0);
    }

    fn insert_rec(wz: &mut WriteZipperUntracked<Vec<Point3<f64>>>, p: Point3<f64>, bounds: AABB<f64>, depth: usize) {
        if let Some(points) = wz.get_val_mut() {
            if points.len() < LEAF_CAPACITY || depth >= MAX_DEPTH {
                points.push(p);
            } else {
                let ps = wz.remove_val(true).unwrap();
                for &old_p in ps.iter() {
                    let idx = Octree::child_index(bounds.center(), old_p);
                    let child_bounds = Octree::child(&bounds, idx);
                    wz.descend_to_byte(idx as u8);
                    Self::insert_rec(wz, old_p, child_bounds, depth + 1);
                    wz.ascend_byte();
                }

                Self::insert_rec(wz, p, bounds, depth);
            }
        } else {
            if depth >= MAX_DEPTH || wz.child_count() == 0 {
                if wz.is_val() { wz.get_val_mut().unwrap().push(p); }
                else { wz.set_val(vec![p]); }
                // wz.get_val_or_set_mut_with(|| vec![]).push(p);
            } else {
                let idx = Octree::child_index(bounds.center(), p);
                let child_bounds = Octree::child(&bounds, idx);
                wz.descend_to_byte(idx as u8);
                Self::insert_rec(wz, p, child_bounds, depth + 1);
                wz.ascend_byte();
            }
        }
    }

    /// Range query: collects points whose cells intersect `query` and are themselves inside.
    pub fn range_query<F : FnMut(Point3<f64>) -> bool>(&self, query: AABB<f64>, mut f: &mut F) -> bool {
        let mut rz = self.root.read_zipper();
        Self::query_rec(&mut rz, self.bounds, &query, &mut f)
    }

    fn query_rec<F : FnMut(Point3<f64>) -> bool>(rz: &mut ReadZipperUntracked<Vec<Point3<f64>>>, bounds: AABB<f64>, query: &AABB<f64>, f: &mut F) -> bool {
        if !bounds.intersects(query) {
            return true;
        }
        if let Some(points) = rz.get_val() {
            for &p in points {
                if query.contains(&p) {
                    if !f(p) { return false }
                }
            }
        }

        for idx in rz.child_mask().iter() {
            let child_bounds = Octree::child(&bounds, idx as usize);
            rz.descend_to_byte(idx);
            if !Self::query_rec(rz, child_bounds, query, f) { return false }
            rz.ascend_byte();
        }

        true
    }

    /// k‑nearest‑neighbour search (Euclidean) using best‑first traversal.
    pub fn knn(&self, query: Point3<f64>, k: usize) -> Vec<Point3<f64>> {
        if k == 0 {
            return Vec::new();
        }
        let mut best: Vec<(f64, Point3<f64>)> = Vec::with_capacity(k);
        let mut rz = self.root.read_zipper();
        Self::knn_rec(&mut rz, self.bounds, query, k, &mut best);
        // Sort ascending before returning.
        best.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
        best.into_iter().map(|(_, p)| p).collect()
    }

    fn knn_rec(rz: &mut ReadZipperUntracked<Vec<Point3<f64>>>, bounds: AABB<f64>, query: Point3<f64>, k: usize, best: &mut Vec<(f64, Point3<f64>)>) {
        // Prune if this branch cannot contain a closer point than current worst.
        let worst_dist = if best.len() == k {
            best.last().unwrap().0
        } else {
            f64::INFINITY
        };
        let box_dist = Octree::boundary_d2(&bounds, query);
        if box_dist > worst_dist {
            return; // Entire node too far away.
        }

        if let Some(points) = rz.get_val() {
            for &p in points {
                let d2 = Octree::d2(p, query);
                Octree::try_add_candidate(best, k, d2, p);
            }
        }

        // Compute distance for each existing child and visit nearest first.
        // Collect (dist2, idx)
        let mut order: Vec<(f64, u8)> = Vec::with_capacity(8);
        rz.child_mask().iter().for_each(|idx| {
            let child_bounds = Octree::child(&bounds, idx as usize);
            order.push((Octree::boundary_d2(&child_bounds, query), idx));
        });

        order.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
        for &(_, idx) in &order {
            let child_bounds = Octree::child(&bounds, idx as usize);
            rz.descend_to_byte(idx);
            Self::knn_rec(rz, child_bounds, query, k, best);
            rz.ascend_byte();
        }
    }
}