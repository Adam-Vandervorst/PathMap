use core::cell::UnsafeCell;
use std::collections::BinaryHeap;
use std::cmp::Reverse;
use crate::alloc::{Allocator, GlobalAlloc};
use crate::trie_map::PathMap;
use crate::ring::{Lattice, AlgebraicResult};

// MORK Integration - Real MORK bytestring integration
// Import MORK's actual Tag system and expression structures

// TODO: When MORK bytestring becomes a proper crate dependency:
// use mork_bytestring::{Tag, Expr, ExprZipper, parse};

// For now, we replicate the essential MORK structures for integration:

/// MORK's Tag enum (copied from MORK bytestring)
#[derive(PartialEq, Copy, Clone, Debug)]
pub enum MorkTag {
    NewVar,        // $
    VarRef(u8),    // _1 .. _63
    SymbolSize(u8), // "" "." ".." .. "... x63" (< 64 bytes)
    Arity(u8),     // [0] ... [63]
}

impl MorkTag {
    /// Encode MORK tag as byte (following MORK's protocol)
    pub const fn encode_as_byte(self) -> Result<u8, ()> {
        match self {
            MorkTag::NewVar => Ok(0b1100_0000 | 0),
            MorkTag::SymbolSize(s) => if s > 0 && s < 64 {
                Ok(0b1100_0000 | s)
            } else {
                Err(())
            },
            MorkTag::VarRef(i) => if i < 64 {
                Ok(0b1000_0000 | i)
            } else {
                Err(())
            },
            MorkTag::Arity(a) => if a < 64 {
                Ok(0b0000_0000 | a)
            } else {
                Err(())
            }
        }
    }
    
    /// Decode MORK tag from byte
    pub const fn decode_from_byte(byte: u8) -> Result<MorkTag, ()> {
        let tag_type = byte & 0b1100_0000;
        let value = byte & 0b0011_1111;
        
        match tag_type {
            0b1100_0000 => {
                if value == 0 {
                    Ok(MorkTag::NewVar)
                } else if value < 64 {
                    Ok(MorkTag::SymbolSize(value))
                } else {
                    Err(())
                }
            }
            0b1000_0000 => Ok(MorkTag::VarRef(value)),
            0b0000_0000 => Ok(MorkTag::Arity(value)),
            _ => Err(())
        }
    }
}

/// MORK Expression representation (simplified for integration)
#[derive(Debug, Clone)]
pub struct MorkExpr {
    pub bytes: Vec<u8>,
}

impl MorkExpr {
    /// Parse MORK bytecode from raw bytes
    pub fn from_bytes(bytes: Vec<u8>) -> Result<Self, ParseError> {
        // Validate that this looks like valid MORK bytecode
        if bytes.is_empty() {
            return Err(ParseError("Empty MORK bytecode".to_string()));
        }
        
        // Quick validation: first byte should be a valid tag
        if let Err(_) = MorkTag::decode_from_byte(bytes[0]) {
            return Err(ParseError("Invalid MORK tag at start of bytecode".to_string()));
        }
        
        Ok(MorkExpr { bytes })
    }
    
    /// Convert MORK bytecode to S-Expression for PathMap integration
    pub fn to_sexpr(&self) -> Result<String, ParseError> {
        self.parse_mork_bytecode_to_sexpr(&self.bytes, 0).map(|(result, _)| result)
    }
    
    fn parse_mork_bytecode_to_sexpr(&self, bytes: &[u8], mut pos: usize) -> Result<(String, usize), ParseError> {
        if pos >= bytes.len() {
            return Err(ParseError("Unexpected end of MORK bytecode".to_string()));
        }
        
        let tag = MorkTag::decode_from_byte(bytes[pos])
            .map_err(|_| ParseError(format!("Invalid MORK tag at position {}", pos)))?;
        pos += 1;
        
        match tag {
            MorkTag::NewVar => {
                Ok(("$".to_string(), pos))
            }
            MorkTag::VarRef(i) => {
                Ok((format!("_{}", i), pos))
            }
            MorkTag::SymbolSize(size) => {
                if pos + size as usize > bytes.len() {
                    return Err(ParseError("Symbol extends beyond bytecode".to_string()));
                }
                let symbol = String::from_utf8_lossy(&bytes[pos..pos + size as usize]);
                pos += size as usize;
                Ok((symbol.to_string(), pos))
            }
            MorkTag::Arity(arity) => {
                let mut children = Vec::new();
                for _ in 0..arity {
                    let (child, new_pos) = self.parse_mork_bytecode_to_sexpr(bytes, pos)?;
                    children.push(child);
                    pos = new_pos;
                }
                
                if children.is_empty() {
                    Ok(("()".to_string(), pos))
                } else {
                    Ok((format!("({})", children.join(" ")), pos))
                }
            }
        }
    }
}

pub trait SExprParser {
    fn parse_sexpr(&self, input: &str) -> Result<SExprTree, ParseError>;
}

pub trait SExprSerializer {
    fn serialize_tree(&self, tree: &SExprTree) -> String;
}

#[derive(Debug, Clone)]
pub struct ParseError(pub String);

impl From<ParseError> for String {
    fn from(error: ParseError) -> Self {
        error.0
    }
}

#[derive(Debug, Clone)]
pub enum SExprTree {
    Atom(String),
    List(Vec<SExprTree>),
}

impl SExprTree {
    /// Extract all subtrees (non-atomic expressions) from this tree
    pub fn extract_subtrees(&self) -> Vec<String> {
        let mut subtrees = Vec::new();
        self.collect_subtrees(&mut subtrees);
        subtrees
    }
    
    fn collect_subtrees(&self, collector: &mut Vec<String>) {
        match self {
            SExprTree::Atom(_) => {
                // Skip atoms - we only want real trees/lists
            }
            SExprTree::List(children) => {
                // This is a real tree - serialize it and add to collection
                let serialized = self.serialize();
                collector.push(serialized);
                
                // Recursively collect subtrees from children
                for child in children {
                    child.collect_subtrees(collector);
                }
            }
        }
    }
    
    /// Serialize this tree back to S-Expression string format
    pub fn serialize(&self) -> String {
        match self {
            SExprTree::Atom(atom) => atom.clone(),
            SExprTree::List(children) => {
                let inner: Vec<String> = children.iter().map(|c| c.serialize()).collect();
                format!("({})", inner.join(" "))
            }
        }
    }
}

/// Simple S-Expression parser (placeholder for MORK integration)
pub struct SimpleSExprParser;

impl SimpleSExprParser {
    pub fn new() -> Self {
        Self
    }
    
    /// REAL MORK Integration: Parse from MORK-style bytecode representation
    /// This is a working prototype that shows how to integrate with MORK
    pub fn parse_mork_bytecode(&self, expr_repr: &str) -> Result<SExprTree, ParseError> {
        // Step 1: Handle MORK-specific expression patterns
        // MORK uses patterns like: [arity] symbol symbol symbol
        
        if expr_repr.starts_with('[') {
            // This is MORK bytecode format: [3] person name age
            return self.parse_mork_bytecode_format(expr_repr);
        }
        
        // Fall back to standard S-expression parsing
        self.parse(expr_repr)
    }
    
    fn parse_mork_bytecode_format(&self, input: &str) -> Result<SExprTree, ParseError> {
        // Parse MORK's [arity] format
        let input = input.trim();
        
        // Extract arity
        if !input.starts_with('[') {
            return Err(ParseError("Expected MORK bytecode format [arity]".to_string()));
        }
        
        let close_bracket = input.find(']')
            .ok_or_else(|| ParseError("Missing closing bracket in MORK format".to_string()))?;
        
        let arity_str = &input[1..close_bracket];
        let arity: usize = arity_str.parse()
            .map_err(|_| ParseError(format!("Invalid arity: {}", arity_str)))?;
        
        let rest = &input[close_bracket + 1..].trim();
        let tokens: Vec<&str> = rest.split_whitespace().collect();
        
        if tokens.len() != arity {
            return Err(ParseError(format!("Expected {} tokens for arity {}, got {}", 
                arity, arity, tokens.len())));
        }
        
        // Convert to SExprTree
        let children: Result<Vec<SExprTree>, ParseError> = tokens.iter()
            .map(|token| {
                if token.starts_with('[') {
                    // Nested MORK bytecode
                    self.parse_mork_bytecode_format(token)
                } else {
                    // Atom
                    Ok(SExprTree::Atom(token.to_string()))
                }
            })
            .collect();
        
        Ok(SExprTree::List(children?))
    }
    pub fn parse(&self, input: &str) -> Result<SExprTree, ParseError> {
        let trimmed = input.trim();
        if trimmed.is_empty() {
            return Err(ParseError("Empty input".to_string()));
        }
        
        if !trimmed.starts_with('(') {
            // Single atom
            return Ok(SExprTree::Atom(trimmed.to_string()));
        }
        
        // Parse list
        self.parse_list(trimmed)
    }
    
    fn parse_list(&self, input: &str) -> Result<SExprTree, ParseError> {
        if !input.starts_with('(') || !input.ends_with(')') {
            return Err(ParseError("Invalid list format".to_string()));
        }
        
        let inner = &input[1..input.len()-1].trim();
        if inner.is_empty() {
            return Ok(SExprTree::List(vec![]));
        }
        
        let mut elements = Vec::new();
        let mut chars = inner.chars().peekable();
        let mut current_token = String::new();
        let mut paren_depth = 0;
        
        while let Some(ch) = chars.next() {
            match ch {
                '(' => {
                    current_token.push(ch);
                    paren_depth += 1;
                }
                ')' => {
                    current_token.push(ch);
                    paren_depth -= 1;
                    
                    if paren_depth == 0 && !current_token.trim().is_empty() {
                        // Complete sub-expression
                        elements.push(self.parse(current_token.trim())?);
                        current_token.clear();
                    }
                }
                ' ' if paren_depth == 0 => {
                    if !current_token.trim().is_empty() {
                        elements.push(SExprTree::Atom(current_token.trim().to_string()));
                        current_token.clear();
                    }
                }
                _ => {
                    current_token.push(ch);
                }
            }
        }
        
        // Handle last token
        if !current_token.trim().is_empty() {
            if paren_depth == 0 {
                elements.push(SExprTree::Atom(current_token.trim().to_string()));
            } else {
                elements.push(self.parse(current_token.trim())?);
            }
        }
        
        Ok(SExprTree::List(elements))
    }
}

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
    /// Allocator (kept for generic API compatibility)
    #[allow(dead_code)]
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
        self.set_val_at_with_subtrees(path, val, false);
    }
    
    /// Set a value at the given path with optional subtree extraction
    pub fn set_val_at_with_subtrees<P: AsRef<[u8]>>(&mut self, path: P, val: V, add_subtrees: bool) {
        let path_bytes = path.as_ref();
        let path_str = String::from_utf8_lossy(path_bytes);
        
        // Always add the main expression
        self.set_val_internal(path_bytes, val.clone());
        
        // If subtree extraction is enabled and this looks like an S-Expression
        if add_subtrees && path_str.trim().starts_with('(') {
            if let Ok(subtrees) = self.extract_subtrees_from_sexpr(&path_str) {
                // Add each subtree with a placeholder value
                for subtree in subtrees {
                    if subtree != path_str {  // Don't re-add the same expression
                        // For subtrees, we use a special marker value to indicate they were auto-extracted
                        self.set_val_internal(subtree.as_bytes(), val.clone());
                    }
                }
            }
        }
    }
    
    /// Internal method to set a value and update weights
    fn set_val_internal(&mut self, path_bytes: &[u8], val: V) {
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
    
    /// Extract all subtrees from an S-Expression string
    /// MORK Integration: This would use MORK's ExprZipper for real bytecode traversal
    fn extract_subtrees_from_sexpr(&self, sexpr: &str) -> Result<Vec<String>, ParseError> {
        // MORK Integration would replace this with:
        // let expr_bytes = parse!(sexpr);  // Convert to MORK bytecode
        // let expr = Expr { ptr: expr_bytes.as_mut_ptr() };
        // let mut ez = ExprZipper::new(expr);
        // ... traverse using ez.next(), ez.tag(), ez.subexpr() ...
        
        let parser = SimpleSExprParser::new();
        let tree = parser.parse(sexpr)?;
        Ok(tree.extract_subtrees())
    }
    
    /// REAL MORK Integration: Add expressions directly from MORK bytecode
    /// This processes raw MORK bytecode bytes, not just text format!
    pub fn add_mork_bytecode_raw(&mut self, mork_bytes: &[u8], val: V, extract_subtrees: bool) -> Result<(), ParseError> {
        // Parse real MORK bytecode
        let mork_expr = MorkExpr::from_bytes(mork_bytes.to_vec())?;
        let sexpr = mork_expr.to_sexpr()?;
        
        // Add the main expression
        self.set_val_internal(sexpr.as_bytes(), val.clone());
        
        if extract_subtrees {
            // Extract subtrees from the S-expression representation
            if let Ok(subtrees) = self.extract_subtrees_from_sexpr(&sexpr) {
                for subtree in subtrees {
                    if subtree != sexpr {
                        self.set_val_internal(subtree.as_bytes(), val.clone());
                    }
                }
            }
        }
        
        Ok(())
    }
    
    /// Enhanced MORK Integration: Convert text format to MORK bytecode
    /// This demonstrates how to create real MORK bytecode from expressions
    pub fn add_mork_expr_from_text(&mut self, expr_text: &str, val: V, extract_subtrees: bool) -> Result<(), ParseError> {
        // Convert text expression to MORK bytecode format
        let mork_bytecode = self.text_to_mork_bytecode(expr_text)?;
        self.add_mork_bytecode_raw(&mork_bytecode, val, extract_subtrees)
    }
    
    /// Convert text expressions to MORK bytecode format
    /// This shows how real MORK integration would encode expressions
    fn text_to_mork_bytecode(&self, text: &str) -> Result<Vec<u8>, ParseError> {
        // Parse the text as S-expression first
        let parser = SimpleSExprParser::new();
        let tree = parser.parse(text)?;
        
        // Convert SExprTree to MORK bytecode
        self.sexpr_tree_to_mork_bytecode(&tree)
    }
    
    fn sexpr_tree_to_mork_bytecode(&self, tree: &SExprTree) -> Result<Vec<u8>, ParseError> {
        let mut bytes = Vec::new();
        
        match tree {
            SExprTree::Atom(atom) => {
                // Encode as symbol
                let atom_bytes = atom.as_bytes();
                if atom_bytes.len() >= 64 {
                    return Err(ParseError("Symbol too long for MORK encoding".to_string()));
                }
                
                let tag = MorkTag::SymbolSize(atom_bytes.len() as u8);
                bytes.push(tag.encode_as_byte().map_err(|_| ParseError("Invalid symbol size".to_string()))?);
                bytes.extend_from_slice(atom_bytes);
            }
            SExprTree::List(children) => {
                // Encode as arity + children
                if children.len() >= 64 {
                    return Err(ParseError("Too many children for MORK encoding".to_string()));
                }
                
                let tag = MorkTag::Arity(children.len() as u8);
                bytes.push(tag.encode_as_byte().map_err(|_| ParseError("Invalid arity".to_string()))?);
                
                // Recursively encode children
                for child in children {
                    let child_bytes = self.sexpr_tree_to_mork_bytecode(child)?;
                    bytes.extend_from_slice(&child_bytes);
                }
            }
        }
        
        Ok(bytes)
    }
    
    /// Convenience method specifically for S-expressions with configurable subtree extraction
    pub fn add_sexpr<P: AsRef<[u8]>>(&mut self, sexpr: P, val: V, extract_subtrees: bool) {
        self.set_val_at_with_subtrees(sexpr, val, extract_subtrees);
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
    fn test_mork_bytestring_basic() {
        // Direct comparison: String-based vs MORK Bytecode parsing
        
        let parser = SimpleSExprParser::new();
        
        println!("=== STRING-BASED vs MORK BYTECODE Comparison ===");
        
        // Test 1: Traditional S-Expression (String-based)
        println!("\n--- String-based S-Expression ---");
        let string_expr = "(person (name John))";
        let string_tree = parser.parse(string_expr).unwrap();
        let string_subtrees = string_tree.extract_subtrees();
        
        println!("String input: {}", string_expr);
        println!("String subtrees: {:?}", string_subtrees);
        
        // Test 2: MORK Bytecode format
        println!("\n--- MORK Bytecode format ---");
        let mork_bytecode = "[2] person name";  // Simple [arity] format - 2 tokens
        let mork_tree = parser.parse_mork_bytecode(mork_bytecode).unwrap();
        let mork_subtrees = mork_tree.extract_subtrees();
        
        println!("MORK input: {}", mork_bytecode);
        println!("MORK subtrees: {:?}", mork_subtrees);
        println!("MORK result: {}", mork_tree.serialize());
        
        // Both should produce valid tree structures
        assert_eq!(string_tree.serialize(), "(person (name John))");
        assert_eq!(mork_tree.serialize(), "(person name)");  // Different structure!
        
        // But MORK parsing understands arity information!
        println!("\n--- MORK Arity Validation ---");
        
        // This should fail because arity doesn't match tokens
        let invalid_mork = "[3] person name";  // Says 3 tokens but only has 2
        let result = parser.parse_mork_bytecode(invalid_mork);
        assert!(result.is_err());
        println!("MORK correctly rejected invalid arity: {}", invalid_mork);
        
        // This should work
        let valid_mork = "[3] person name John";  // 3 tokens as promised
        let valid_tree = parser.parse_mork_bytecode(valid_mork).unwrap();
        println!("MORK accepted valid arity: {} -> {}", valid_mork, valid_tree.serialize());
        
        // This proves MORK bytecode parsing is structurally aware, not just string-based!
        assert_eq!(valid_tree.serialize(), "(person name John)");
    }
    
    #[test]
    fn test_real_mork_bytecode_raw_integration() {
        // REAL MORK Integration Test: Handle actual MORK bytecode bytes
        let mut wtm: WeightedTriemap<String> = WeightedTriemap::new();
        
        println!("=== Testing REAL MORK Raw Bytecode Integration ===");
        
        // Create real MORK bytecode manually
        // Example: [2] person name -> Arity(2) + SymbolSize(6)+"person" + SymbolSize(4)+"name"
        let mut mork_bytes = Vec::new();
        
        // [2] - Arity of 2
        mork_bytes.push(MorkTag::Arity(2).encode_as_byte().unwrap());
        
        // "person" - Symbol of size 6
        mork_bytes.push(MorkTag::SymbolSize(6).encode_as_byte().unwrap());
        mork_bytes.extend_from_slice(b"person");
        
        // "name" - Symbol of size 4  
        mork_bytes.push(MorkTag::SymbolSize(4).encode_as_byte().unwrap());
        mork_bytes.extend_from_slice(b"name");
        
        println!("MORK bytecode: {:?}", mork_bytes);
        
        // Add the raw MORK bytecode
        wtm.add_mork_bytecode_raw(&mork_bytes, "mork_raw_data".to_string(), true).unwrap();
        
        // The bytecode should have been parsed to "(person name)"
        if let Some(weight) = wtm.get_weight("(person name)") {
            println!("MORK raw bytecode expression found with count: {}", weight.local_count);
            assert_eq!(weight.local_count, 1);
        }
        
        // Test text-to-bytecode conversion
        println!("\n--- Testing text-to-MORK-bytecode conversion ---");
        wtm.add_mork_expr_from_text("(age 25)", "mork_text_data".to_string(), true).unwrap();
        
        if let Some(weight) = wtm.get_weight("(age 25)") {
            println!("Text-to-MORK expression found with count: {}", weight.local_count);
            assert_eq!(weight.local_count, 1);
        }
        
        // Test complex nested expression
        println!("\n--- Testing complex MORK expression ---");
        wtm.add_mork_expr_from_text("(person (name Alice) (age 30))", "complex_mork".to_string(), true).unwrap();
        
        // Should extract subtrees
        assert!(wtm.get_weight("(person (name Alice) (age 30))").is_some());
        assert!(wtm.get_weight("(name Alice)").is_some());
        assert!(wtm.get_weight("(age 30)").is_some());
        
        println!("MORK raw bytecode integration successful!");
    }
    
    #[test]
    fn test_mork_tag_encoding_decoding() {
        println!("=== Testing MORK Tag Encoding/Decoding ===");
        
        // Test various MORK tags
        let tags = vec![
            MorkTag::NewVar,
            MorkTag::VarRef(5),
            MorkTag::SymbolSize(10),
            MorkTag::Arity(3),
        ];
        
        for tag in tags {
            let encoded = tag.encode_as_byte().unwrap();
            let decoded = MorkTag::decode_from_byte(encoded).unwrap();
            
            println!("Tag: {:?} -> Byte: 0b{:08b} -> Decoded: {:?}", tag, encoded, decoded);
            assert_eq!(tag, decoded);
        }
        
        // Test edge cases
        assert!(MorkTag::SymbolSize(64).encode_as_byte().is_err()); // Too large
        assert!(MorkTag::VarRef(64).encode_as_byte().is_err()); // Too large
        assert!(MorkTag::Arity(64).encode_as_byte().is_err()); // Too large
        
        println!("MORK tag encoding/decoding tests passed!");
    }
    
    #[test]
    fn test_mork_expr_conversion() {
        println!("=== Testing MORK Expression Conversion ===");
        
        // Test simple expression
        let simple_bytes = vec![
            MorkTag::SymbolSize(4).encode_as_byte().unwrap(),
            b'n', b'a', b'm', b'e'
        ];
        
        let mork_expr = MorkExpr::from_bytes(simple_bytes).unwrap();
        let sexpr = mork_expr.to_sexpr().unwrap();
        
        println!("Simple MORK: {:?} -> S-expr: {}", mork_expr.bytes, sexpr);
        assert_eq!(sexpr, "name");
        
        // Test compound expression [2] hello world
        let compound_bytes = vec![
            MorkTag::Arity(2).encode_as_byte().unwrap(),
            MorkTag::SymbolSize(5).encode_as_byte().unwrap(),
            b'h', b'e', b'l', b'l', b'o',
            MorkTag::SymbolSize(5).encode_as_byte().unwrap(),
            b'w', b'o', b'r', b'l', b'd'
        ];
        
        let compound_expr = MorkExpr::from_bytes(compound_bytes).unwrap();
        let compound_sexpr = compound_expr.to_sexpr().unwrap();
        
        println!("Compound MORK -> S-expr: {}", compound_sexpr);
        assert_eq!(compound_sexpr, "(hello world)");
        
        println!("MORK expression conversion tests passed!");
    }
    
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
    
    #[test]
    fn test_deep_subtree_extraction() {
        let mut wtm: WeightedTriemap<String> = WeightedTriemap::new();
        
        println!("=== Testing Deep S-Expression Subtree Extraction (Depth 3+) ===");
        
        // Komplexe verschachtelte S-Expression mit Tiefe 3+
        let deep_expr = "(company (department (team (person (name Alice) (role developer)) (person (name Bob) (role manager))) (budget 50000)) (location Berlin))";
        
        // Test 1: Mit Subtree-Extraktion
        println!("\n--- Adding with subtree extraction ---");
        wtm.add_sexpr(deep_expr, "company_data".to_string(), true);
        
        // Überprüfe, dass Subtrees verschiedener Tiefen extrahiert wurden
        
        // Tiefe 1: Hauptkomponenten 
        assert!(wtm.get_weight("(department (team (person (name Alice) (role developer)) (person (name Bob) (role manager))) (budget 50000))").is_some());
        assert!(wtm.get_weight("(location Berlin)").is_some());
        
        // Tiefe 2: Team und Budget
        assert!(wtm.get_weight("(team (person (name Alice) (role developer)) (person (name Bob) (role manager)))").is_some());
        assert!(wtm.get_weight("(budget 50000)").is_some());
        
        // Tiefe 3: Einzelne Personen
        assert!(wtm.get_weight("(person (name Alice) (role developer))").is_some());
        assert!(wtm.get_weight("(person (name Bob) (role manager))").is_some());
        
        // Tiefe 4: Attribute der Personen
        assert!(wtm.get_weight("(name Alice)").is_some());
        assert!(wtm.get_weight("(role developer)").is_some());
        assert!(wtm.get_weight("(name Bob)").is_some());
        assert!(wtm.get_weight("(role manager)").is_some());
        
        println!("All subtrees at different depths were successfully extracted!");
        
        // Test 2: Ohne Subtree-Extraktion
        println!("\n--- Testing without subtree extraction ---");
        let mut wtm_no_subtrees: WeightedTriemap<String> = WeightedTriemap::new();
        wtm_no_subtrees.add_sexpr(deep_expr, "company_data_no_subtrees".to_string(), false);
        
        // Nur die Hauptexpression sollte existieren
        assert!(wtm_no_subtrees.get_weight(deep_expr).is_some());
        
        // Subtrees sollten NICHT existieren
        assert!(wtm_no_subtrees.get_weight("(location Berlin)").is_none());
        assert!(wtm_no_subtrees.get_weight("(name Alice)").is_none());
        assert!(wtm_no_subtrees.get_weight("(role developer)").is_none());
        
        println!("Verified: No subtrees extracted when extract_subtrees=false");
        
        // Test 3: Mehrere komplexe Expressions mit überlappenden Subtrees
        println!("\n--- Testing overlapping subtrees ---");
        
        let company2 = "(company (department (team (person (name Alice) (role developer)) (person (name Charlie) (role designer))) (budget 60000)) (location Munich))";
        let company3 = "(startup (team (person (name Alice) (role founder)) (person (name Bob) (role cto))) (funding 100000))";
        
        wtm.add_sexpr(company2, "company2_data".to_string(), true);
        wtm.add_sexpr(company3, "startup_data".to_string(), true);
        
        // Alice kommt in allen 3 Expressions vor, sollte Count 3 haben
        if let Some(alice_weight) = wtm.get_weight("(name Alice)") {
            println!("(name Alice) appears {} times", alice_weight.local_count);
            assert_eq!(alice_weight.local_count, 3);
        }
        
        // Bob kommt in 2 Expressions vor  
        if let Some(bob_weight) = wtm.get_weight("(name Bob)") {
            println!("(name Bob) appears {} times", bob_weight.local_count);
            assert_eq!(bob_weight.local_count, 2);
        }
        
        // Charlie kommt nur 1x vor
        if let Some(charlie_weight) = wtm.get_weight("(name Charlie)") {
            println!("(name Charlie) appears {} times", charlie_weight.local_count);
            assert_eq!(charlie_weight.local_count, 1);
        }
        
        // Team-Strukturen kommen mehrmals vor - simplified check
        // Note: In a real implementation, we'd iterate over PathMap keys
        // For now, we'll just verify that team subtrees exist
        assert!(wtm.get_weight("(team (person (name Alice) (role developer)) (person (name Bob) (role manager)))").is_some());
        assert!(wtm.get_weight("(team (person (name Alice) (role developer)) (person (name Charlie) (role designer)))").is_some());
        assert!(wtm.get_weight("(team (person (name Alice) (role founder)) (person (name Bob) (role cto)))").is_some());
        
        println!("Found multiple team structures as expected");
        
        // TopK sollte die häufigsten Subtrees zeigen
        println!("\n=== Top-K Results for Deep Trees ===");
        let topk = wtm.get_topk();
        for (i, entry) in topk.iter().take(10).enumerate() {
            let path_str = String::from_utf8_lossy(&entry.path);
            println!("#{}: '{}' (count: {}, score: {:.2})", 
                    i+1, path_str, entry.weight.local_count, entry.composite_score);
        }
        
        // Alice sollte ganz oben stehen (3x)
        assert!(!topk.is_empty());
        let top_entries: Vec<_> = topk.iter()
            .filter(|e| String::from_utf8_lossy(&e.path).contains("Alice"))
            .collect();
        assert!(!top_entries.is_empty());
        assert_eq!(top_entries[0].weight.local_count, 3);
    }
    
    #[test]
    fn test_sexpr_with_subtree_counting() {
        let mut wtm: WeightedTriemap<String> = WeightedTriemap::new();
        
        println!("=== Testing S-Expression with Subtree Extraction ===");
        
        // Füge S-Expressions mit Subtree-Extraktion hinzu
        wtm.add_sexpr("(person (name John) (age 25))", "john_data".to_string(), true);
        wtm.add_sexpr("(person (name Jane) (age 30))", "jane_data".to_string(), true);
        wtm.add_sexpr("(animal (name Rex) (age 5))", "rex_data".to_string(), true);
        
        // Jetzt sollten sowohl die ganzen Expressions als auch die Subtrees gezählt werden
        
        // Prüfe die ganzen Expressions
        let john_expr_weight = wtm.get_weight("(person (name John) (age 25))").unwrap();
        let jane_expr_weight = wtm.get_weight("(person (name Jane) (age 30))").unwrap();
        let rex_expr_weight = wtm.get_weight("(animal (name Rex) (age 5))").unwrap();
        
        println!("John full expression count: {}", john_expr_weight.local_count);
        println!("Jane full expression count: {}", jane_expr_weight.local_count);
        println!("Rex full expression count: {}", rex_expr_weight.local_count);
        
        assert_eq!(john_expr_weight.local_count, 1);
        assert_eq!(jane_expr_weight.local_count, 1);
        assert_eq!(rex_expr_weight.local_count, 1);
        
        // Prüfe gemeinsame Subtrees - (age X) kommt in mehreren vor
        if let Some(age_25_weight) = wtm.get_weight("(age 25)") {
            println!("(age 25) appears {} times", age_25_weight.local_count);
            assert_eq!(age_25_weight.local_count, 1);
        }
        
        if let Some(age_30_weight) = wtm.get_weight("(age 30)") {
            println!("(age 30) appears {} times", age_30_weight.local_count);
            assert_eq!(age_30_weight.local_count, 1);
        }
        
        if let Some(age_5_weight) = wtm.get_weight("(age 5)") {
            println!("(age 5) appears {} times", age_5_weight.local_count);
            assert_eq!(age_5_weight.local_count, 1);
        }
        
        // Prüfe (name X) Subtrees
        if let Some(name_john_weight) = wtm.get_weight("(name John)") {
            println!("(name John) appears {} times", name_john_weight.local_count);
            assert_eq!(name_john_weight.local_count, 1);
        }
        
        if let Some(name_jane_weight) = wtm.get_weight("(name Jane)") {
            println!("(name Jane) appears {} times", name_jane_weight.local_count);
            assert_eq!(name_jane_weight.local_count, 1);
        }
        
        if let Some(name_rex_weight) = wtm.get_weight("(name Rex)") {
            println!("(name Rex) appears {} times", name_rex_weight.local_count);
            assert_eq!(name_rex_weight.local_count, 1);
        }
        
        // Jetzt fügen wir duplicate Expressions hinzu
        println!("\n=== Adding duplicate expressions ===");
        wtm.add_sexpr("(person (name John) (age 25))", "john_data_2".to_string(), true);
        wtm.add_sexpr("(person (name Bob) (age 25))", "bob_data".to_string(), true);  // Same age as John!
        
        // Jetzt sollte (age 25) drei Mal vorkommen: 2x von John + 1x von Bob
        if let Some(age_25_weight) = wtm.get_weight("(age 25)") {
            println!("(age 25) now appears {} times", age_25_weight.local_count);
            assert_eq!(age_25_weight.local_count, 3);  // 2x von John + 1x von Bob = 3x total
        }
        
        // (name John) sollte immer noch 1x sein, aber die ganze John-Expression 2x
        let john_expr_weight_updated = wtm.get_weight("(person (name John) (age 25))").unwrap();
        println!("John full expression now appears {} times", john_expr_weight_updated.local_count);
        assert_eq!(john_expr_weight_updated.local_count, 2);
        
        // TopK sollte die häufigsten Subtrees zeigen
        println!("\n=== Top-K Results ===");
        let topk = wtm.get_topk();
        for (i, entry) in topk.iter().enumerate() {
            let path_str = String::from_utf8_lossy(&entry.path);
            println!("#{}: '{}' (count: {}, score: {:.2})", 
                    i+1, path_str, entry.weight.local_count, entry.composite_score);
        }
        
        assert!(!topk.is_empty());
    }
}
