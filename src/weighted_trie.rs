use core::cell::UnsafeCell;
use std::collections::BinaryHeap;
use std::cmp::Reverse;
use crate::alloc::{Allocator, GlobalAlloc};
use crate::trie_map::PathMap;
use crate::ring::{Lattice, AlgebraicResult};

/// Weight structure for individual nodes
#[derive(Debug, Clone, PartialEq)]
pub struct NodeWeight {
    /// Number of times this exact node/pattern occurred
    pub local_count: u64,
    /// Aggregate occurrences below this node (sum of descendants)
    pub subtree_count: u64,
    /// Running sum of achieved compression gains when a feature rooted here was accepted
    pub compress_gain_sum: f64,
}

impl Default for NodeWeight {
    fn default() -> Self {
        Self {
            local_count: 0,
            subtree_count: 0,
            compress_gain_sum: 0.0,
        }
    }
}

/// Weight semiring operations
impl NodeWeight {
    /// Union operation: w = w1 + w2
    pub fn union(&self, other: &Self) -> Self {
        Self {
            local_count: self.local_count + other.local_count,
            subtree_count: self.subtree_count + other.subtree_count,
            compress_gain_sum: self.compress_gain_sum + other.compress_gain_sum,
        }
    }
    
    /// Intersection operation: w = min(w1, w2)
    pub fn intersection_min(&self, other: &Self) -> Self {
        Self {
            local_count: self.local_count.min(other.local_count),
            subtree_count: self.subtree_count.min(other.subtree_count),
            compress_gain_sum: self.compress_gain_sum.min(other.compress_gain_sum),
        }
    }
    
    /// Intersection operation: w = w1 * w2 (alternative semantics)
    pub fn intersection_mult(&self, other: &Self) -> Self {
        Self {
            local_count: self.local_count * other.local_count,
            subtree_count: self.subtree_count * other.subtree_count,
            compress_gain_sum: self.compress_gain_sum * other.compress_gain_sum,
        }
    }
    
    /// Calculate composite weight (can be customized based on use case)
    pub fn composite_weight(&self) -> f64 {
        (self.subtree_count as f64) + self.compress_gain_sum
    }
}

/// Entry for top-k tracking
#[derive(Debug, Clone, PartialEq)]
pub struct TopKEntry {
    pub path: Vec<u8>,
    pub weight: NodeWeight,
    pub composite_score: f64,
}

impl Eq for TopKEntry {}

impl PartialOrd for TopKEntry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TopKEntry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // For correct ordering in TopKTracker, we want normal comparison
        // The min-heap behavior is handled by the Reverse wrapper
        self.composite_score.partial_cmp(&other.composite_score)
            .unwrap_or(std::cmp::Ordering::Equal)
    }
}

/// Top-K tracker with fixed size
#[derive(Debug, Clone)]
pub struct TopKTracker {
    k: usize,
    heap: BinaryHeap<Reverse<TopKEntry>>,
}

impl TopKTracker {
    pub fn new(k: usize) -> Self {
        Self {
            k,
            heap: BinaryHeap::with_capacity(k + 1),
        }
    }
    
    /// Add an entry, maintaining only the k heaviest
    pub fn add_entry(&mut self, entry: TopKEntry) {
        self.heap.push(Reverse(entry));
        
        // If we exceed k, remove the lightest entry
        if self.heap.len() > self.k {
            self.heap.pop();
        }
    }
    
    /// Get the current top-k entries (heaviest first)
    pub fn get_topk(&self) -> Vec<TopKEntry> {
        let mut entries: Vec<_> = self.heap.iter().map(|r| r.0.clone()).collect();
        entries.sort_by(|a, b| b.composite_score.partial_cmp(&a.composite_score).unwrap_or(std::cmp::Ordering::Equal));
        entries
    }
    
    /// Check if an entry would be in top-k
    pub fn would_be_included(&self, composite_score: f64) -> bool {
        if self.heap.len() < self.k {
            return true;
        }
        
        // Check against the smallest (lightest) entry
        if let Some(Reverse(lightest)) = self.heap.peek() {
            composite_score > lightest.composite_score
        } else {
            true
        }
    }
}

/// A weighted version of PathMap with node-level weight tracking
pub struct WeightedTriemap<
    V: Clone + Send + Sync,
    A: Allocator = GlobalAlloc,
> {
    /// The underlying PathMap for structure and values
    pub(crate) inner: PathMap<V, A>,
    /// Weight information mapped by path
    pub(crate) weights: PathMap<NodeWeight, A>,
    /// Top-k tracker for heaviest children
    pub(crate) topk: UnsafeCell<TopKTracker>,
    /// Allocator
    pub(crate) alloc: A,
}

unsafe impl<V: Clone + Send + Sync, A: Allocator> Send for WeightedTriemap<V, A> {}
unsafe impl<V: Clone + Send + Sync, A: Allocator> Sync for WeightedTriemap<V, A> {}

impl<V: Clone + Send + Sync + Unpin> WeightedTriemap<V, GlobalAlloc> {
    /// Creates a new empty weighted triemap with default k=10
    pub fn new() -> Self {
        Self::new_with_k(10)
    }
    
    /// Creates a new empty weighted triemap with specified k for top-k tracking
    pub fn new_with_k(k: usize) -> Self {
        Self {
            inner: PathMap::new(),
            weights: PathMap::new(),
            topk: UnsafeCell::new(TopKTracker::new(k)),
            alloc: GlobalAlloc::default(),
        }
    }
}

impl<V: Clone + Send + Sync + Unpin, A: Allocator> WeightedTriemap<V, A> {
    /// Creates a new empty weighted triemap with specified allocator and k
    pub fn new_with_k_in(k: usize, alloc: A) -> Self {
        Self {
            inner: PathMap::new_in(alloc.clone()),
            weights: PathMap::new_in(alloc.clone()),
            topk: UnsafeCell::new(TopKTracker::new(k)),
            alloc,
        }
    }
    
    /// Set a value at the given path and update weights
    pub fn set_val_at<P: AsRef<[u8]>>(&mut self, path: P, val: V) {
        let path_bytes = path.as_ref();
        
        // Set the value in the inner map
        self.inner.set_val_at(path_bytes, val);
        
        // Update local count for this exact path
        let current_weight = self.weights.get_val_at(path_bytes).cloned().unwrap_or_default();
        let new_weight = NodeWeight {
            local_count: current_weight.local_count + 1,
            subtree_count: current_weight.subtree_count + 1, // Will be updated by propagate_subtree_counts
            compress_gain_sum: current_weight.compress_gain_sum,
        };
        self.weights.set_val_at(path_bytes, new_weight.clone());
        
        // Update top-k tracker
        let entry = TopKEntry {
            path: path_bytes.to_vec(),
            weight: new_weight.clone(),
            composite_score: new_weight.composite_weight(),
        };
        
        unsafe {
            (*self.topk.get()).add_entry(entry);
        }
        
        // Propagate subtree count updates to ancestors
        self.propagate_subtree_counts(path_bytes);
    }
    
    /// Get a value at the given path
    pub fn get<P: AsRef<[u8]>>(&self, path: P) -> Option<&V> {
        self.inner.get_val_at(path)
    }
    
    /// Get weight information for a path
    pub fn get_weight<P: AsRef<[u8]>>(&self, path: P) -> Option<&NodeWeight> {
        self.weights.get_val_at(path)
    }
    
    /// Get the current top-k heaviest entries
    pub fn get_topk(&self) -> Vec<TopKEntry> {
        unsafe {
            (*self.topk.get()).get_topk()
        }
    }
    
    /// Propagate subtree count changes up the tree
    fn propagate_subtree_counts(&mut self, path: &[u8]) {
        // Update all ancestor paths
        for prefix_len in (0..path.len()).rev() {
            let prefix = &path[..prefix_len];
            
            let current_weight = self.weights.get_val_at(prefix).cloned().unwrap_or_default();
            let new_weight = NodeWeight {
                local_count: current_weight.local_count,
                subtree_count: current_weight.subtree_count + 1,
                compress_gain_sum: current_weight.compress_gain_sum,
            };
            self.weights.set_val_at(prefix, new_weight);
        }
    }
    
    /// Add compression gain to a specific path
    pub fn add_compression_gain<P: AsRef<[u8]>>(&mut self, path: P, gain: f64) {
        let path_bytes = path.as_ref();
        let current_weight = self.weights.get_val_at(path_bytes).cloned().unwrap_or_default();
        let new_weight = NodeWeight {
            local_count: current_weight.local_count,
            subtree_count: current_weight.subtree_count,
            compress_gain_sum: current_weight.compress_gain_sum + gain,
        };
        self.weights.set_val_at(path_bytes, new_weight.clone());
        
        // Update top-k if this path would still be included
        let composite_score = new_weight.composite_weight();
        let topk_ref = unsafe { &mut *self.topk.get() };
        if topk_ref.would_be_included(composite_score) {
            let entry = TopKEntry {
                path: path_bytes.to_vec(),
                weight: new_weight,
                composite_score,
            };
            topk_ref.add_entry(entry);
        }
    }
}

impl<V: Clone + Send + Sync + Unpin> Default for WeightedTriemap<V, GlobalAlloc> {
    fn default() -> Self {
        Self::new()
    }
}

/// Implement lattice operations for weight combination
impl Lattice for NodeWeight {
    fn pjoin(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized {
        AlgebraicResult::Element(self.union(other))
    }
    
    fn pmeet(&self, other: &Self) -> AlgebraicResult<Self> where Self: Sized {
        AlgebraicResult::Element(self.intersection_min(other))
    }
}

impl<V: Clone + Send + Sync + Unpin, A: Allocator> WeightedTriemap<V, A> {
    /// Union operation: combine two weighted triemaps
    pub fn union_with(&mut self, _other: &Self) {
        // Union the inner maps
        // Note: This is a simplified approach. Full implementation would need
        // to properly handle the PathMap union operations
        
        // For now, we iterate over the other map and add values
        // In a full implementation, this would use PathMap's built-in union operations
        todo!("Implement union operation using PathMap's ring operations")
    }
    
    /// Intersection operation: find common elements with combined weights
    pub fn intersection_with(&mut self, _other: &Self) {
        // Similar to union, this would use PathMap's intersection operations
        todo!("Implement intersection operation using PathMap's ring operations")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_node_weight_operations() {
        let w1 = NodeWeight {
            local_count: 5,
            subtree_count: 15,
            compress_gain_sum: 2.5,
        };
        
        let w2 = NodeWeight {
            local_count: 3,
            subtree_count: 10,
            compress_gain_sum: 1.8,
        };
        
        let union = w1.union(&w2);
        assert_eq!(union.local_count, 8);
        assert_eq!(union.subtree_count, 25);
        assert_eq!(union.compress_gain_sum, 4.3);
        
        let intersection = w1.intersection_min(&w2);
        assert_eq!(intersection.local_count, 3);
        assert_eq!(intersection.subtree_count, 10);
        assert_eq!(intersection.compress_gain_sum, 1.8);
    }
    
    #[test]
    fn test_weighted_triemap_basic() {
        let mut wtm = WeightedTriemap::new();
        
        wtm.set_val_at("test", "value1".to_string());
        wtm.set_val_at("test", "value2".to_string()); // Should increment count
        
        let weight = wtm.get_weight("test").unwrap();
        assert_eq!(weight.local_count, 2);
        assert_eq!(weight.subtree_count, 2);
        
        let topk = wtm.get_topk();
        assert!(!topk.is_empty());
    }
    
    #[test]
    fn test_topk_tracker() {
        let mut tracker = TopKTracker::new(3);
        
        tracker.add_entry(TopKEntry {
            path: b"path1".to_vec(),
            weight: NodeWeight::default(),
            composite_score: 10.0,
        });
        
        tracker.add_entry(TopKEntry {
            path: b"path2".to_vec(),
            weight: NodeWeight::default(),
            composite_score: 5.0,
        });
        
        tracker.add_entry(TopKEntry {
            path: b"path3".to_vec(),
            weight: NodeWeight::default(),
            composite_score: 15.0,
        });
        
        tracker.add_entry(TopKEntry {
            path: b"path4".to_vec(),
            weight: NodeWeight::default(),
            composite_score: 3.0,
        });
        
        let topk = tracker.get_topk();
        assert_eq!(topk.len(), 3);
        assert_eq!(topk[0].composite_score, 15.0); // Heaviest first
        assert_eq!(topk[1].composite_score, 10.0);
        assert_eq!(topk[2].composite_score, 5.0);
    }
    
    #[test]
    fn test_sexpr_counting() {
        let mut wtm = WeightedTriemap::new();
        
        // S-Expression Pfade als Strings 
        let expr1 = "(first_name John)";
        let expr2 = "(last_name Smith)";
        let expr3 = "(age 25)";
        let expr4 = "(first_name John)"; // Duplikat!
        let expr5 = "(first_name John)"; // Noch ein Duplikat!
        
        // Füge S-Expressions hinzu mit einfachen String-Werten
        wtm.set_val_at(expr1, "john_entry".to_string());
        wtm.set_val_at(expr2, "smith_entry".to_string());
        wtm.set_val_at(expr3, "age_entry".to_string());
        wtm.set_val_at(expr4, "john_entry_duplicate".to_string()); // Überschreibt, aber Count geht hoch
        wtm.set_val_at(expr5, "john_entry_third".to_string());     // Nochmal!
        
        // Prüfe local_counts
        let weight1 = wtm.get_weight(expr1).unwrap();
        let weight2 = wtm.get_weight(expr2).unwrap();
        let weight3 = wtm.get_weight(expr3).unwrap();
        
        println!("Weight for '{}': local_count={}, subtree_count={}", 
                expr1, weight1.local_count, weight1.subtree_count);
        println!("Weight for '{}': local_count={}, subtree_count={}", 
                expr2, weight2.local_count, weight2.subtree_count);
        println!("Weight for '{}': local_count={}, subtree_count={}", 
                expr3, weight3.local_count, weight3.subtree_count);
        
        // "(first_name John)" wurde 3x hinzugefügt
        assert_eq!(weight1.local_count, 3);
        
        // Die anderen nur 1x
        assert_eq!(weight2.local_count, 1);
        assert_eq!(weight3.local_count, 1);
        
        // Prüfe dass der letzte Wert gespeichert wurde
        assert_eq!(wtm.get(expr1).unwrap(), "john_entry_third");
        assert_eq!(wtm.get(expr2).unwrap(), "smith_entry");
        assert_eq!(wtm.get(expr3).unwrap(), "age_entry");
        
        // Prüfe TopK - sollte "(first_name John)" an der Spitze haben
        let topk = wtm.get_topk();
        assert!(!topk.is_empty());
        
        // Finde den Eintrag mit der höchsten local_count
        let heaviest = topk.iter().max_by_key(|entry| entry.weight.local_count).unwrap();
        assert_eq!(heaviest.path, expr1.as_bytes());
        assert_eq!(heaviest.weight.local_count, 3);
    }
    
    #[test]
    fn test_complex_sexpr_patterns() {
        let mut wtm = WeightedTriemap::new();
        
        // Komplexere S-Expressions
        let expressions = vec![
            "(person (name John) (age 25))",
            "(person (name Jane) (age 30))", 
            "(person (name John) (age 25))",  // Exaktes Duplikat
            "(animal (type dog) (name Rex))",
            "(person (name Bob) (age 40))",
            "(person (name John) (age 25))",  // Noch ein Duplikat
            "(animal (type cat) (name Fluffy))",
            "(person (name Jane) (age 30))",  // Duplikat von Jane
        ];
        
        // Füge alle Expressions hinzu
        for (i, expr) in expressions.iter().enumerate() {
            wtm.set_val_at(*expr, format!("entry_{}", i));
        }
        
        // Prüfe Counts
        let john_weight = wtm.get_weight("(person (name John) (age 25))").unwrap();
        let jane_weight = wtm.get_weight("(person (name Jane) (age 30))").unwrap();
        let rex_weight = wtm.get_weight("(animal (type dog) (name Rex))").unwrap();
        let bob_weight = wtm.get_weight("(person (name Bob) (age 40))").unwrap();
        
        assert_eq!(john_weight.local_count, 3);  // 3x John
        assert_eq!(jane_weight.local_count, 2);  // 2x Jane  
        assert_eq!(rex_weight.local_count, 1);   // 1x Rex
        assert_eq!(bob_weight.local_count, 1);   // 1x Bob
        
        println!("John appears {} times", john_weight.local_count);
        println!("Jane appears {} times", jane_weight.local_count);
        println!("Rex appears {} times", rex_weight.local_count);
        println!("Bob appears {} times", bob_weight.local_count);
        
        // TopK sollte John und Jane enthalten
        let topk = wtm.get_topk();
        let top_counts: Vec<u64> = topk.iter().map(|e| e.weight.local_count).collect();
        
        // John (3x) und Jane (2x) sollten in den Top-Entries sein
        assert!(top_counts.contains(&3));
        assert!(top_counts.contains(&2));
    }
}
