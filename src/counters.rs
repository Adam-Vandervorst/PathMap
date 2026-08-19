use crate::PathMap;
use crate::zipper::*;
use crate::trie_node::{TaggedNodeRef, TrieNode};

/// Example usage of counters
///
/// ```
/// # let mut map: pathmap::PathMap<usize> = pathmap::PathMap::new();
/// # map.set_val_at(b"example", 0);
/// pathmap::counters::print_traversal::<usize, _>(&map.read_zipper());
/// let counters = pathmap::counters::Counters::count_ocupancy(&map);
/// counters.print_histogram_by_depth();
/// counters.print_run_length_histogram();
/// counters.print_list_node_stats();
/// ```
pub struct Counters {
    total_nodes_by_depth: Vec<usize>,
    total_child_items_by_depth: Vec<usize>,
    max_child_items_by_depth: Vec<usize>,

    /// Counts the number of each node type at a given depth
    total_dense_byte_nodes_by_depth: Vec<usize>,
    total_list_nodes_by_depth: Vec<usize>,

    /// List-node-specific counters
    total_slot0_length_by_depth: Vec<usize>,
    slot1_occupancy_count_by_depth: Vec<usize>,
    total_slot1_length_by_depth: Vec<usize>,
    list_node_single_byte_keys_by_depth: Vec<usize>,

    /// Counts the runs of distance (in bytes) that end at each byte depth
    /// [run_length][ending_byte_depth]
    run_length_histogram_by_ending_byte_depth: Vec<Vec<usize>>,
    cur_run_start_depth: usize,
}
impl Counters {
    pub const fn new() -> Self {
        Self {
            total_nodes_by_depth: vec![],
            total_child_items_by_depth: vec![],
            max_child_items_by_depth: vec![],
            total_dense_byte_nodes_by_depth: vec![],
            total_list_nodes_by_depth: vec![],
            total_slot0_length_by_depth: vec![],
            slot1_occupancy_count_by_depth: vec![],
            total_slot1_length_by_depth: vec![],
            list_node_single_byte_keys_by_depth: vec![],
            run_length_histogram_by_ending_byte_depth: vec![],
            cur_run_start_depth: 0,
        }
    }
    pub fn total_nodes(&self) -> usize {
        let mut total = 0;
        self.total_nodes_by_depth.iter().for_each(|cnt| total += cnt);
        total
    }
    pub fn total_child_items(&self) -> usize {
        let mut total = 0;
        self.total_child_items_by_depth.iter().for_each(|cnt| total += cnt);
        total
    }
    pub fn print_histogram_by_depth(&self) {
        println!("\n\ttotal_nodes\ttot_child_cnt\tavg_branch\tmax_child_items\tdense_nodes\tlist_nodes");
        for depth in 0..self.total_nodes_by_depth.len() {
            println!("{depth}\t{}\t\t{}\t\t{:1.4}\t\t{}\t\t{}\t\t{}",
                self.total_nodes_by_depth[depth],
                self.total_child_items_by_depth[depth],
                self.total_child_items_by_depth[depth] as f32 / self.total_nodes_by_depth[depth] as f32,
                self.max_child_items_by_depth[depth],
                self.total_dense_byte_nodes_by_depth[depth],
                self.total_list_nodes_by_depth[depth],
            );
        }
        println!("TOTAL nodes: {}, items: {}, avg children-per-node: {}", self.total_nodes(), self.total_child_items(), self.total_child_items() as f32 / self.total_nodes() as f32);
    }
    pub fn print_run_length_histogram(&self) {
        println!("run_len\trun_cnt\trun_end_mean_depth");
        for (run_length, depths) in self.run_length_histogram_by_ending_byte_depth.iter().enumerate() {
            let total = depths.iter().fold(0, |mut sum, cnt| {sum += cnt; sum});
            let depth_sum = depths.iter().enumerate().fold(0, |mut sum, (depth, cnt)| {sum += cnt*(depth+1); sum});
            println!("{run_length}\t{total}\t{}", depth_sum as f32 / total as f32);
        }
    }
    pub fn print_list_node_stats(&self) {
        println!("\n\ttotal_nodes\tlist_node_cnt\tlist_node_rto\tavg_slot0_len\tslot1_cnt\tslot1_used_rto\tavg_slot1_len\tone_byte_keys\tone_byte_rto");
        for depth in 0..self.total_nodes_by_depth.len() {
            println!("{depth}\t{}\t\t{}\t\t{:2.1}%\t\t{:1.4}\t\t{}\t\t{:2.1}%\t\t{:1.4}\t\t{}\t\t{:2.1}%",
                self.total_nodes_by_depth[depth],
                self.total_list_nodes_by_depth[depth],
                self.total_list_nodes_by_depth[depth] as f32 / self.total_nodes_by_depth[depth] as f32 * 100.0,
                self.total_slot0_length_by_depth[depth] as f32 / self.total_list_nodes_by_depth[depth] as f32,
                self.slot1_occupancy_count_by_depth[depth],
                self.slot1_occupancy_count_by_depth[depth] as f32 / self.total_list_nodes_by_depth[depth] as f32 * 100.0,
                self.total_slot1_length_by_depth[depth] as f32 / self.slot1_occupancy_count_by_depth[depth] as f32,
                self.list_node_single_byte_keys_by_depth[depth],
                self.list_node_single_byte_keys_by_depth[depth] as f32 / self.total_list_nodes_by_depth[depth] as f32 * 100.0,
            );
        }
    }
    pub fn count_ocupancy<V: Clone + Send + Sync + Unpin>(map: &PathMap<V>) -> Self {
        let mut counters = Counters::new();

        counters.count_node(map.root().unwrap().as_tagged(), 0);

        let mut zipper = map.read_zipper();
        while zipper.to_next_step() {
            let depth = zipper.path().len();

            counters.run_counter_update(depth);
            if let Some(focus_node) = zipper.get_focus().try_as_tagged() {
                counters.count_node(focus_node, depth);
            } else {
                counters.end_run(depth-1);
            }
        }

        counters
    }
    fn count_node<V: Clone + Send + Sync, A : crate::alloc::Allocator>(&mut self, node: TaggedNodeRef<V, A>, depth: usize) {
        if let Some(dbn) = node.as_dense() {
            if dbn.item_count() != 1 {
                self.end_run(depth);
            }
            self.increment_common_counters(node, depth);
            self.total_dense_byte_nodes_by_depth[depth] += 1;
        }
        if let Some(lln) = node.as_list() {
            if lln.item_count() != 1 {
                self.end_run(depth);
            }
            self.increment_common_counters(node, depth);
            self.total_list_nodes_by_depth[depth] += 1;

            let (key0, key1) = lln.get_both_keys();
            self.total_slot0_length_by_depth[depth] += key0.len();
            if key1.len() > 0 {
                self.slot1_occupancy_count_by_depth[depth] += 1;
                self.total_slot1_length_by_depth[depth] += key1.len();
            }
            if key0.len() == 1 || key1.len() == 1 {
                self.list_node_single_byte_keys_by_depth[depth] += 1;
            }
        }
    }
    fn resize_all_historgrams(&mut self, depth: usize) {
        if self.total_nodes_by_depth.len() <= depth {
            self.total_nodes_by_depth.resize(depth+1, 0);
            self.total_child_items_by_depth.resize(depth+1, 0);
            self.max_child_items_by_depth.resize(depth+1, 0);
            self.total_dense_byte_nodes_by_depth.resize(depth+1, 0);
            self.total_list_nodes_by_depth.resize(depth+1, 0);
            self.total_slot0_length_by_depth.resize(depth+1, 0);
            self.slot1_occupancy_count_by_depth.resize(depth+1, 0);
            self.total_slot1_length_by_depth.resize(depth+1, 0);
            self.list_node_single_byte_keys_by_depth.resize(depth+1, 0);
        }
    }
    fn increment_common_counters<V: Clone + Send + Sync, A : crate::alloc::Allocator>(&mut self, node: TaggedNodeRef<V, A>, depth: usize) {
        self.resize_all_historgrams(depth);
        let child_item_count = node.item_count();
        self.total_nodes_by_depth[depth] += 1;
        self.total_child_items_by_depth[depth] += child_item_count;
        if self.max_child_items_by_depth[depth] < child_item_count {
            self.max_child_items_by_depth[depth] = child_item_count;
        }
    }
    fn end_run(&mut self, depth: usize) {
        if depth > self.cur_run_start_depth {
            let cur_run_length = depth - self.cur_run_start_depth;
            self.push_run(cur_run_length, depth-1);
        }
        self.cur_run_start_depth = depth;
    }
    fn run_counter_update(&mut self, depth: usize) {
        if self.cur_run_start_depth > depth {
            self.cur_run_start_depth = depth;
        }
    }
    fn push_run(&mut self, cur_run_length: usize, byte_depth: usize) {
        if self.run_length_histogram_by_ending_byte_depth.len() <= cur_run_length {
            self.run_length_histogram_by_ending_byte_depth.resize(cur_run_length+1, vec![]);
        }
        if self.run_length_histogram_by_ending_byte_depth[cur_run_length].len() <= byte_depth {
            self.run_length_histogram_by_ending_byte_depth[cur_run_length].resize(byte_depth+1, 0);
        }
        self.run_length_histogram_by_ending_byte_depth[cur_run_length][byte_depth] += 1;
    }
}

pub fn print_traversal<'a, V: 'a + Clone + Unpin, Z: ZipperIteration + Clone>(zipper: &Z) {
    let mut zipper = zipper.clone();

    println!("{:?}", zipper.path());
    while zipper.to_next_val() {
        println!("{:?}", zipper.path());
    }
}

/// Copy-on-write write-path counters
///
/// Every structural write goes through `TrieNodeODRc::make_unique`, which either finds the node
/// unshared (cheap) or clones it (the copy-on-write cost).  These counters expose that split, so
/// a workload's write amplification can be measured directly:
///
/// ```
/// # use pathmap::PathMap;
/// pathmap::counters::reset_cow_counters();
/// let mut map: PathMap<usize> = PathMap::new();
/// map.set_val_at(b"hello", 42);
/// let shared = map.clone();
/// map.set_val_at(b"help", 43); // writing while `shared` aliases the trie forces clones
/// let counters = pathmap::counters::cow_counters();
/// assert!(counters.cow_clones >= 1);
/// assert!(counters.cow_clones <= counters.make_unique_calls);
/// # drop(shared);
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CowCounters {
    /// Number of times a write required a unique reference to a node
    pub make_unique_calls: usize,
    /// How many of those calls found the node shared and cloned it
    pub cow_clones: usize,
}

static MAKE_UNIQUE_CALLS: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);
static COW_CLONES: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(0);

/// Returns a snapshot of the counters accumulated since the last [reset_cow_counters]
pub fn cow_counters() -> CowCounters {
    use core::sync::atomic::Ordering::Relaxed;
    CowCounters {
        make_unique_calls: MAKE_UNIQUE_CALLS.load(Relaxed),
        cow_clones: COW_CLONES.load(Relaxed),
    }
}

/// Resets the copy-on-write counters to zero
pub fn reset_cow_counters() {
    use core::sync::atomic::Ordering::Relaxed;
    MAKE_UNIQUE_CALLS.store(0, Relaxed);
    COW_CLONES.store(0, Relaxed);
}

/// Internal. Records one `make_unique` call and whether it had to clone
pub(crate) fn record_make_unique(cloned: bool) {
    use core::sync::atomic::Ordering::Relaxed;
    MAKE_UNIQUE_CALLS.fetch_add(1, Relaxed);
    if cloned {
        COW_CLONES.fetch_add(1, Relaxed);
    }
}

/// The key-byte capacity of a single [LineListNode](crate::line_list_node), and the resulting node size
pub const LIST_NODE_KEY_BYTES: usize = crate::line_list_node::KEY_BYTES_CNT;
/// The size in bytes of a single `LineListNode`, derived from [LIST_NODE_KEY_BYTES]
pub const LIST_NODE_SIZE: usize = crate::line_list_node::LINE_LIST_NODE_SIZE;

/// Memory attribution for a trie, broken down by node type
///
/// Walks physical (deduplicated) nodes, so structurally shared subtries are counted once. Use it to
/// decide where layout work pays: the split between list-node and dense-node bytes varies enormously
/// with key shape, and is what determines whether a given optimization is worth anything.
#[derive(Clone, Default, Debug)]
pub struct MemProfile {
    pub list_nodes: usize,
    pub list_bytes: usize,
    pub dense_nodes: usize,
    pub dense_items: usize,
    pub dense_cap: usize,
    pub dense_bytes: usize,
    pub cell_nodes: usize,
    pub cell_items: usize,
    pub cell_bytes: usize,
    pub klen_hist: Vec<usize>,
    pub val_slots: usize,
    pub child_slots: usize,
    pub both_slots: usize,
    pub key_bytes_used: usize,
    pub at_cap: usize,
    pub empty_nodes: usize,
    pub dangling_slots: usize,
    pub node_klen_hist: Vec<usize>,
    pub allval_nodes: usize,
    pub allval_klen_hist: Vec<usize>,
}
impl MemProfile {
    fn merge(mut self, o: Self) -> Self {
        self.list_nodes += o.list_nodes; self.list_bytes += o.list_bytes;
        self.dense_nodes += o.dense_nodes; self.dense_items += o.dense_items; self.dense_bytes += o.dense_bytes; self.dense_cap += o.dense_cap;
        self.cell_nodes += o.cell_nodes; self.cell_items += o.cell_items; self.cell_bytes += o.cell_bytes;
        self.val_slots += o.val_slots; self.child_slots += o.child_slots;
        self.both_slots += o.both_slots; self.key_bytes_used += o.key_bytes_used; self.at_cap += o.at_cap;
        if self.klen_hist.len() < o.klen_hist.len() { self.klen_hist.resize(o.klen_hist.len(), 0); }
        for (i, c) in o.klen_hist.iter().enumerate() { self.klen_hist[i] += c; }
        if self.node_klen_hist.len() < o.node_klen_hist.len() { self.node_klen_hist.resize(o.node_klen_hist.len(), 0); }
        for (i, c) in o.node_klen_hist.iter().enumerate() { self.node_klen_hist[i] += c; }
        if self.allval_klen_hist.len() < o.allval_klen_hist.len() { self.allval_klen_hist.resize(o.allval_klen_hist.len(), 0); }
        for (i, c) in o.allval_klen_hist.iter().enumerate() { self.allval_klen_hist[i] += c; }
        self.allval_nodes += o.allval_nodes;
        self.empty_nodes += o.empty_nodes; self.dangling_slots += o.dangling_slots;
        self
    }
    pub fn total_bytes(&self) -> usize { self.list_bytes + self.dense_bytes + self.cell_bytes }
    pub fn report_list_slots(&self) {
        let tot: usize = self.klen_hist.iter().sum();
        println!("  list slot key-length histogram ({} slots, {} value-slots, {} child-slots):", tot, self.val_slots, self.child_slots);
        let mut acc = 0;
        for (len, cnt) in self.klen_hist.iter().enumerate() {
            if *cnt == 0 { continue }
            acc += cnt;
            println!("     len {:>2}: {:>9}  ({:4.1}%)  cum {:4.1}%", len, cnt, *cnt as f64/tot as f64*100.0, acc as f64/tot as f64*100.0);
        }
        println!("  nodes with both slots used: {}   total key bytes used per node avg: {:.1} of {}",
            self.both_slots, self.key_bytes_used as f64 / self.list_nodes.max(1) as f64, crate::line_list_node::KEY_BYTES_CNT);
        let tn: usize = self.node_klen_hist.iter().sum();
        let mut cum = 0usize; let mut cum_av = 0usize;
        println!("  per-NODE total key bytes (cumulative fit):");
        for (len, cnt) in self.node_klen_hist.iter().enumerate() {
            cum += cnt; cum_av += self.allval_klen_hist[len];
            if [6usize,10,14,18,22,26,34,42,50,58,84].contains(&len) {
                println!("     <= {:>2} bytes: {:5.1}% of all list nodes | {:5.1}% of the {} leaf-only nodes",
                    len, cum as f64/tn as f64*100.0, cum_av as f64/self.allval_nodes.max(1) as f64*100.0, self.allval_nodes);
            }
        }
        println!("  leaf-only nodes (no child slot): {} of {} ({:4.1}%)", self.allval_nodes, self.list_nodes, self.allval_nodes as f64/self.list_nodes.max(1) as f64*100.0);
        println!("  nodes at the key cap (key0+key1 >= {}): {}", crate::line_list_node::KEY_BYTES_CNT, self.at_cap);
    }
    pub fn report(&self, label: &str, vals: usize) {
        let t = self.total_bytes() as f64;
        println!("--- {label} ---");
        println!("  values                {vals}");
        println!("  list  nodes {:>9}  bytes {:>11}  ({:4.1}% of trie)", self.list_nodes, self.list_bytes, self.list_bytes as f64/t*100.0);
        println!("  dense nodes {:>9}  bytes {:>11}  ({:4.1}% of trie)  items {}  avg {:.1}/node",
            self.dense_nodes, self.dense_bytes, self.dense_bytes as f64/t*100.0, self.dense_items,
            self.dense_items as f64 / self.dense_nodes.max(1) as f64);
        println!("  dense slots: len {} cap {} ({:.1}% over-allocated)", self.dense_items, self.dense_cap, (self.dense_cap as f64/self.dense_items.max(1) as f64 - 1.0)*100.0);
        println!("  cell  nodes {:>9}  bytes {:>11}  ({:4.1}% of trie)  items {}", self.cell_nodes, self.cell_bytes, self.cell_bytes as f64/t*100.0, self.cell_items);
        println!("  empty (allocated) nodes {}   dangling sentinel slots {}", self.empty_nodes, self.dangling_slots);
        println!("  TOTAL bytes {:>9}   = {:.1} bytes/value", self.total_bytes(), t / vals.max(1) as f64);
    }
}

/// Builds a [MemProfile] for `map`.  See the type docs
pub fn memory_profile<V: Clone + Send + Sync + Unpin + 'static>(map: &PathMap<V>) -> MemProfile {
    use crate::trie_node::traverse_physical;
    use crate::alloc::GlobalAlloc;
    let cf = core::mem::size_of::<crate::dense_byte_node::OrdinaryCoFree<V, GlobalAlloc>>();
    let cellcf = core::mem::size_of::<crate::dense_byte_node::CellCoFree<V, GlobalAlloc>>();
    let list_sz = core::mem::size_of::<crate::line_list_node::LineListNode<V, GlobalAlloc>>();
    let dense_sz = core::mem::size_of::<crate::dense_byte_node::DenseByteNode<V, GlobalAlloc>>();
    let cell_sz = core::mem::size_of::<crate::dense_byte_node::CellByteNode<V, GlobalAlloc>>();
    let Some(root) = map.root() else { return MemProfile::default() };
    traverse_physical(root, move |node, ctx: MemProfile| {
        let mut c = ctx;
        if node.item_count() == 0 { c.empty_nodes += 1; }
        if let Some(l) = node.as_list() {
            c.list_nodes += 1; c.list_bytes += list_sz;
            //A slot whose child link is the empty sentinel is a dangling path: the path exists but
            //carries no value and leads nowhere
            if l.is_used_child_0() && unsafe{ l.child_in_slot::<0>() }.is_empty() { c.dangling_slots += 1 }
            if l.is_used_child_1() && unsafe{ l.child_in_slot::<1>() }.is_empty() { c.dangling_slots += 1 }
            let (k0, k1) = l.get_both_keys();
            if c.klen_hist.len() < crate::line_list_node::KEY_BYTES_CNT + 1 { c.klen_hist.resize(crate::line_list_node::KEY_BYTES_CNT + 1, 0); }
            c.klen_hist[k0.len()] += 1;
            if k1.len() > 0 { c.klen_hist[k1.len()] += 1; c.both_slots += 1; }
            c.key_bytes_used += k0.len() + k1.len();
            if k0.len() + k1.len() >= crate::line_list_node::KEY_BYTES_CNT { c.at_cap += 1; }
            let ktot = k0.len() + k1.len();
            if c.node_klen_hist.len() < 2*crate::line_list_node::KEY_BYTES_CNT + 2 { c.node_klen_hist.resize(2*crate::line_list_node::KEY_BYTES_CNT + 2, 0); c.allval_klen_hist.resize(2*crate::line_list_node::KEY_BYTES_CNT + 2, 0); }
            c.node_klen_hist[ktot] += 1;
            let has_child = l.is_used_child_0() || l.is_used_child_1();
            if !has_child { c.allval_nodes += 1; c.allval_klen_hist[ktot] += 1; }
            if l.is_used_value_0() { c.val_slots += 1 } else if l.is_used_child_0() { c.child_slots += 1 }
            if l.is_used_value_1() { c.val_slots += 1 } else if l.is_used_child_1() { c.child_slots += 1 }
        }
        else if let Some(d) = node.as_dense() {
            c.dense_nodes += 1; c.dense_items += d.slot_count(); c.dense_cap += d.slot_capacity(); c.dense_bytes += dense_sz + d.slot_capacity()*cf;
        } else if node.tag() == crate::trie_node::CELL_BYTE_NODE_TAG {
            let n = node.item_count();
            // each CellCoFree additionally owns a boxed OrdinaryCoFree
            c.cell_nodes += 1; c.cell_items += n; c.cell_bytes += cell_sz + n*(cellcf + cf);
        }
        c
    }, |a, b| a.merge(b))
}

#[cfg(test)]
mod tests {
    use super::{cow_counters, reset_cow_counters};
    use crate::PathMap;

    #[test]
    fn cow_counters_split_unshared_and_shared_writes() {
        reset_cow_counters();

        // Writes into an unshared trie never clone: every make_unique call finds a unique node.
        let mut map: PathMap<usize> = PathMap::new();
        for (i, key) in [&b"romane"[..], b"romanus", b"romulus", b"rubens"].iter().enumerate() {
            map.set_val_at(key, i);
        }
        let unshared = cow_counters();
        assert!(unshared.make_unique_calls > 0, "writes must route through make_unique");
        assert_eq!(unshared.cow_clones, 0, "an unshared trie must never clone on write");

        // Once another handle aliases the trie, a write must clone every shared node on its path.
        let shared_handle = map.clone();
        map.set_val_at(b"romanes", 4);
        let shared = cow_counters();
        assert!(shared.cow_clones >= 1, "writing an aliased trie must record at least one clone");
        assert!(shared.cow_clones <= shared.make_unique_calls);
        assert_eq!(shared_handle.get_val_at(b"romane"), Some(&0), "the aliased handle is unaffected");
        assert_eq!(shared_handle.get_val_at(b"romanes"), None);

        // After the aliasing handle is gone, fresh writes stop cloning.
        drop(shared_handle);
        map.set_val_at(b"ruber", 5);
        let reunified = cow_counters();
        assert_eq!(
            reunified.cow_clones, shared.cow_clones,
            "writes after the alias is dropped must not clone (the path was already un-shared by the previous write, and sole ownership needs no copies)"
        );

        reset_cow_counters();
        let zeroed = cow_counters();
        assert_eq!((zeroed.make_unique_calls, zeroed.cow_clones), (0, 0));
    }
}
