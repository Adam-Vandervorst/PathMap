
use core::mem::MaybeUninit;
use core::fmt::{Debug, Formatter};
use std::collections::HashMap;

use crate::trie_node::*;
use crate::ring::*;
use crate::line_list_node::{LineListNode, ValOrChildUnion, validate_node};
use crate::dense_byte_node::DenseByteNode;

/// A borrowed reference to a payload with a key stored elsewhere, contained in 16 Bytes
#[derive(Clone)]
pub struct TinyRefNode<'a, V> {
    /// bit 7 = used
    /// bit 6 = is_child
    /// bit 5 to bit 0 = key_len
    header: u8,
    key_bytes: [MaybeUninit<u8>; 7],
    payload: &'a ValOrChildUnion<V>
}

impl<V> Debug for TinyRefNode<'_, V> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "TinyRefNode")
    }
}

impl<'a, V: Clone> TinyRefNode<'a, V> {

    pub fn new(is_child: bool, key: &[u8], payload: &'a ValOrChildUnion<V>) -> Self {
        let mut new_node = Self {
            header: Self::header(is_child, key.len()),
            key_bytes: [MaybeUninit::uninit(); 7],
            payload
        };
        unsafe{ core::ptr::copy_nonoverlapping(key.as_ptr(), new_node.key_bytes.as_mut_ptr().cast(), key.len()); }
        new_node
    }

    /// Turn the TinyRefNode into a LineListNode by cloning the payload
    pub fn into_full(&self) -> Option<LineListNode<V>> {
        self.clone_payload().map(|payload| {
            let mut new_node = LineListNode::new();
            unsafe{ new_node.set_payload_owned::<0>(self.key(), payload); }
            debug_assert!(validate_node(&new_node));
            new_node
        })
    }

    /// Clones the payload from self
    fn clone_payload(&self) -> Option<ValOrChild<V>> {
        if self.node_is_empty() {
            return None;
        } else {
            match self.is_child_ptr() {
                true => {
                    let child = unsafe{ &*self.payload.child }.clone();
                    Some(ValOrChild::Child(child))
                },
                false => {
                    let val = unsafe{ &**self.payload.val }.clone();
                    Some(ValOrChild::Val(val))
                }
            }
        }
    }
    fn header(is_child: bool, key_len: usize) -> u8 {
        debug_assert!(key_len <= 7);
        if is_child {
            ((1 << 7) | (1 << 6) | key_len) as u8
        } else {
            ((1 << 7) | key_len) as u8
        }
    }
    fn is_child_ptr(&self) -> bool {
        self.header & (1 << 6) > 0
    }
    fn is_used_child(&self) -> bool {
        self.header & ((1 << 7) | (1 << 6)) == ((1 << 7) | (1 << 6))
    }
    fn is_used_val(&self) -> bool {
        self.header & ((1 << 7) | (1 << 6)) == (1 << 7)
    }
    fn key_len(&self) -> usize {
        (self.header & 0x3f) as usize
    }
    fn key(&self) -> &[u8] {
        unsafe{ core::slice::from_raw_parts(self.key_bytes.as_ptr().cast(), self.key_len()) }
    }
}

//GOAT, this implementation is swiss cheese (full of holes for the non-Americans).  This node type will
// never support mutability, but it may need more support to enable the full range of use cases
impl<'a, V: Clone> TrieNode<V> for TinyRefNode<'a, V> {
    fn node_contains_partial_key(&self, key: &[u8]) -> bool {
        if self.key().starts_with(key) {
            true
        } else {
            false
        }
    }
    fn node_get_child(&self, key: &[u8]) -> Option<(usize, &dyn TrieNode<V>)> {
        if self.is_used_child() {
            let node_key = self.key();
            let key_len = node_key.len();
            if key.len() >= key_len {
                if node_key == &key[..key_len] {
                    let child = unsafe{ &*self.payload.child }.borrow();
                    return Some((key_len, child))
                }
            }
        }
        None
    }
    fn node_get_child_and_val_mut(&mut self, _key: &[u8]) -> Option<(usize, Option<&mut V>, Option<&mut TrieNodeODRc<V>>)> { unreachable!() }
    fn node_get_child_mut(&mut self, _key: &[u8]) -> Option<(usize, &mut TrieNodeODRc<V>)> { unreachable!() }
    fn node_replace_child(&mut self, _key: &[u8], _new_node: TrieNodeODRc<V>) -> &mut dyn TrieNode<V> { unreachable!() }
    fn node_contains_val(&self, key: &[u8]) -> bool {
        if self.is_used_val() {
            let node_key = self.key();
            if node_key == key {
                return true;
            }
        }
        false
    }
    fn node_get_val(&self, key: &[u8]) -> Option<&V> {
        if self.is_used_val() {
            let node_key = self.key();
            if node_key == key {
                let val = unsafe{ &**self.payload.val };
                return Some(val);
            }
        }
        None
    }
    fn node_remove_val(&mut self, _key: &[u8]) -> Option<V> { unreachable!() }
    fn node_get_val_mut(&mut self, _key: &[u8]) -> Option<&mut V> { unreachable!() }
    fn node_set_val(&mut self, key: &[u8], val: V) -> Result<(Option<V>, bool), TrieNodeODRc<V>> {
        let mut replacement_node = self.into_full().unwrap();
        replacement_node.node_set_val(key, val).unwrap_or_else(|_| panic!());
        Err(TrieNodeODRc::new(replacement_node))
    }
    fn node_set_branch(&mut self, key: &[u8], new_node: TrieNodeODRc<V>) -> Result<bool, TrieNodeODRc<V>> {
        let mut replacement_node = self.into_full().unwrap();
        replacement_node.node_set_branch(key, new_node).unwrap_or_else(|_| panic!());
        Err(TrieNodeODRc::new(replacement_node))
    }
    fn node_remove_all_branches(&mut self, _key: &[u8]) -> bool { unreachable!() }
    fn node_remove_unmasked_branches(&mut self, _key: &[u8], _mask: [u64; 4]) { unreachable!() }
    fn node_is_empty(&self) -> bool {
        self.header & (1 << 7) == 0
    }
    fn new_iter_token(&self) -> u128 { unreachable!() }
    fn iter_token_for_path(&self, _key: &[u8]) -> (u128, &[u8]) { unreachable!() }
    fn next_items(&self, _token: u128) -> (u128, &'a[u8], Option<&TrieNodeODRc<V>>, Option<&V>) { unreachable!() }
    fn node_val_count(&self, _cache: &mut HashMap<*const dyn TrieNode<V>, usize>) -> usize {
        panic!();
    }
    #[cfg(feature = "counters")]
    fn item_count(&self) -> usize {
        panic!();
    }
    fn node_first_val_depth_along_key(&self, key: &[u8]) -> Option<usize> {
        debug_assert!(key.len() > 0);
        let node_key = self.key();
        if self.is_used_val() && key.starts_with(node_key) {
            Some(node_key.len() - 1)
        } else {
            None
        }
    }
    fn nth_child_from_key(&self, _key: &[u8], _n: usize) -> (Option<u8>, Option<&dyn TrieNode<V>>) {
        panic!();
    }
    fn first_child_from_key(&self, _key: &[u8]) -> (Option<&[u8]>, Option<&dyn TrieNode<V>>) {
        panic!();
    }
    fn count_branches(&self, _key: &[u8]) -> usize {
        panic!();
    }
    fn node_branches_mask(&self, _key: &[u8]) -> [u64; 4] {
        panic!();
    }
    fn is_leaf(&self, _key: &[u8]) -> bool {
        panic!();
    }
    fn prior_branch_key(&self, _key: &[u8]) -> &[u8] {
        panic!();
    }
    fn get_sibling_of_child(&self, _key: &[u8], _next: bool) -> (Option<u8>, Option<&dyn TrieNode<V>>) {
        panic!();
    }
    fn get_node_at_key(&self, key: &[u8]) -> AbstractNodeRef<V> {

        //Zero-length key means borrow this node
        if key.len() == 0 {
            return AbstractNodeRef::BorrowedDyn(self)
        }

        //Exact match with a path to a child node means return that node
        let node_key = self.key();
        if self.is_used_child() && node_key == key {
            return AbstractNodeRef::BorrowedRc(unsafe{ &*self.payload.child })
        }

        //Otherwise check to see if we need to make a sub-node.
        if node_key.len() > key.len() && node_key.starts_with(key) {
            let new_key = &node_key[key.len()..];
            let ref_node = TinyRefNode::new(self.is_child_ptr(), new_key, self.payload);
            return AbstractNodeRef::BorrowedTiny(ref_node)
        }

        //The key must specify a path the node doesn't contains
        AbstractNodeRef::None
    }
    fn take_node_at_key(&mut self, _key: &[u8]) -> Option<TrieNodeODRc<V>> { unreachable!() }
    fn join_dyn(&self, other: &dyn TrieNode<V>) -> TrieNodeODRc<V> where V: Lattice {
        //GOAT, I can streamline this quite a lot, but for now I'll just up-convert to a ListNode to test
        // the basic premise of the TinyRefNode
        self.into_full().unwrap().join_dyn(other)
    }
    fn join_into_dyn(&mut self, mut _other: TrieNodeODRc<V>) where V: Lattice { unreachable!() }
    fn drop_head_dyn(&mut self, _byte_cnt: usize) -> Option<TrieNodeODRc<V>> where V: Lattice { unreachable!() }
    fn meet_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> where V: Lattice {
        //GOAT, is this worth bespoke code to save some cycles?
        self.into_full().unwrap().meet_dyn(other)
    }
    fn psubtract_dyn(&self, other: &dyn TrieNode<V>) -> (bool, Option<TrieNodeODRc<V>>) where V: PartialDistributiveLattice {
        //GOAT, is this worth bespoke code to save some cycles?
        self.into_full().unwrap().psubtract_dyn(other)
    }
    fn prestrict_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> {
        //GOAT, is this worth bespoke code to save some cycles?
        self.into_full().unwrap().prestrict_dyn(other)
    }
    fn as_dense(&self) -> Option<&DenseByteNode<V>> {
        None
    }
    fn as_dense_mut(&mut self) -> Option<&mut DenseByteNode<V>> {
        None
    }
    fn as_list(&self) -> Option<&LineListNode<V>> {
        None
    }
    fn as_list_mut(&mut self) -> Option<&mut LineListNode<V>> {
        None
    }
    fn as_tagged(&self) -> TaggedNodeRef<V> {
        panic!();
    }
    fn clone_self(&self) -> TrieNodeODRc<V> {
        TrieNodeODRc::new(self.clone())
    }
}

#[test]
fn test_tiny_node() {
    //First confirm TinyRefNode is 16 bytes
    assert_eq!(std::mem::size_of::<TinyRefNode::<()>>(), 16);

}
