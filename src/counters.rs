
use crate::trie_map::BytesTrieMap;
use crate::zipper::{Zipper, ReadZipper};
use crate::trie_node::ValOrChildRef;

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

    /// Counts the runs of distance (in bytes) that end at each byte depth
    /// [run_length][ending_byte_depth]
    run_length_histogram_by_ending_byte_depth: Vec<Vec<usize>>,
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
            run_length_histogram_by_ending_byte_depth: vec![],
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
        println!("\n\ttotal_nodes\ttot_child_cnt\tavg_branch\tmax_child_items");
        for depth in 0..self.total_nodes_by_depth.len() {
            println!("{depth}\t{}\t\t{}\t\t{:1.4}\t\t{}",
                self.total_nodes_by_depth[depth],
                self.total_child_items_by_depth[depth],
                self.total_child_items_by_depth[depth] as f32 / self.total_nodes_by_depth[depth] as f32,
                self.max_child_items_by_depth[depth]);
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
    pub fn count_ocupancy<V: Clone>(map: &BytesTrieMap<V>) -> Self {
        let mut counters = Counters::new();
        let mut depth = 0;
        let mut cur_run_length = 0;
        let mut byte_depth = 0;
        let mut byte_depth_stack: Vec<usize> = vec![0];
        let mut prefixes: Vec<Vec<u8>> = vec![vec![]];

        counters.count_node(map.root().borrow().item_count(), 0);

        let mut zipper = map.read_zipper();
        

        //GOAT, old implementation using TrieNode::boxed_node_iter()
        // let mut btnis = vec![map.root().borrow().boxed_node_iter()];
        // loop {
        //     match btnis.last_mut() {
        //         None => { break }
        //         Some(last) => {
        //             match last.next() {
        //                 None => {
        //                     depth -= 1;
        //                     byte_depth -= byte_depth_stack.pop().unwrap();
        //                     cur_run_length = 0;
        //                     prefixes.pop();
        //                     btnis.pop();
        //                 }
        //                 Some((bytes, item)) => {
        //                     //let mut cur_prefix: Vec<u8> = prefixes.last().unwrap().clone();
        //                     //cur_prefix.extend(bytes);

        //                     match item {
        //                         ValOrChildRef::Val(_val) => {

        //                             counters.push_run(cur_run_length + bytes.len(), byte_depth + bytes.len());

        //                             //return Some((cur_prefix, val))
        //                         },
        //                         ValOrChildRef::Child(child) => {
        //                             depth += 1;
        //                             counters.count_node(child.item_count(), depth);

        //                             byte_depth += bytes.len();
        //                             byte_depth_stack.push(bytes.len());

        //                             if child.item_count() > 1 {
        //                                 counters.push_run(cur_run_length + bytes.len(), byte_depth);
        //                                 cur_run_length = 0;
        //                             } else {
        //                                 cur_run_length += bytes.len();
        //                             }

        //                             //prefixes.push(cur_prefix);
        //                             btnis.push(child.boxed_node_iter())
        //                         }
        //                     }
        //                 }
        //             }
        //         }
        //     }
        // }
        counters
    }
    fn count_node(&mut self, child_item_count: usize, depth: usize) {
        if self.total_nodes_by_depth.len() <= depth {
            self.total_nodes_by_depth.resize(depth+1, 0);
            self.total_child_items_by_depth.resize(depth+1, 0);
            self.max_child_items_by_depth.resize(depth+1, 0);
        }
        self.total_nodes_by_depth[depth] += 1;
        self.total_child_items_by_depth[depth] += child_item_count;
        if self.max_child_items_by_depth[depth] < child_item_count {
            self.max_child_items_by_depth[depth] = child_item_count;
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

pub fn print_traversal<V: Clone>(zipper: &ReadZipper<V>) {
    let mut zipper = zipper.clone();

    println!("{:?}", zipper.path());
    while let Some(_v) = zipper.to_next_val() {
        println!("{:?}", zipper.path());
    }
}