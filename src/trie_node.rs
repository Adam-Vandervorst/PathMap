
use std::sync::Arc;
use std::collections::HashMap;
use dyn_clone::*;

use crate::dense_byte_node::*;
use crate::line_list_node::LineListNode;
use crate::empty_node::EmptyNode;
use crate::ring::*;
use crate::tiny_node::TinyRefNode;

/// The abstract interface to all nodes, from which tries are built
///
/// TrieNodes are small tries that can be stitched together into larger tries.  Within a TrieNode, value
/// and onward link locations are defined by key paths.  There are a few conventions and caveats to this
/// iterface:
///
/// 1. A TrieNode will never have a value or an onward link at a zero-length key.  A value associated with
/// the path to the root of a TrieNode must be stored in the parent node.
pub trait TrieNode<V>: TrieNodeDowncast<V> + DynClone + core::fmt::Debug + Send + Sync {

    /// Returns `true` if the node contains a key that begins with `key`, irrespective of whether the key
    /// specifies a child, value, or both
    ///
    /// This method should never be called with a zero-length key.  If the `key` arg is longer than the
    /// keys contained within the node, this method should return `false`
    fn node_contains_partial_key(&self, key: &[u8]) -> bool;

    /// Returns the child node that matches `key` along with the number of `key` characters matched.
    /// Returns `None` if no child node matches the key, even if there is a value with that prefix
    fn node_get_child(&self, key: &[u8]) -> Option<(usize, &dyn TrieNode<V>)>;

    //GOAT, Do we actually need this method?  Originally the thinking was that needed to borrow both the
    // value and the onward link from a node at the same path.  This is needed because it's impossible to
    // split the borrows to different parts of the same node.  However, the Zippers are implemented to keep a
    // key path rather than a node and value pointer at the focus, and therefore this method is never used.
    /// Similar behavior to `node_get_child`, but operates across a mutable reference and returns both the 
    /// value and onward link associated with a given path
    ///
    /// Unlike `node_get_child`, if the key matches a value but not an onward link, this method will return
    /// `Some(byte_cnt, Some(val), None)`
    fn node_get_child_and_val_mut<'a>(&'a mut self, key: &[u8]) -> Option<(usize, Option<&'a mut V>, Option<&'a mut TrieNodeODRc<V>>)>;

    /// Same behavior as `node_get_child`, but operates across a mutable reference
    fn node_get_child_mut(&mut self, key: &[u8]) -> Option<(usize, &mut TrieNodeODRc<V>)>;

    //GOAT, Probably can be removed
    /// Replaces a child-node at `key` with the node provided, returning a `&mut` reference to the newly
    /// added child node
    ///
    /// Unlike [node_get_child], this method requires an exact key and not just a prefix, in order to
    /// maintain tree integrity.  This method is not intended as a general-purpose "set" operation, and
    /// may panic if the node does not already contain a child node at the specified key.
    ///
    /// QUESTION: Does this method have a strong purpose, or can it be superseded by node_set_branch?
    fn node_replace_child(&mut self, key: &[u8], new_node: TrieNodeODRc<V>) -> &mut dyn TrieNode<V>;

    /// Returns `true` if the node contains a value at the specified key, otherwise returns `false`
    ///
    /// NOTE: just as with [Self::node_get_val], this method will return `false` if key is longer than
    /// the exact key contained within this node
    fn node_contains_val(&self, key: &[u8]) -> bool;

    /// Returns the value that matches `key` if it contained within the node
    ///
    /// NOTE: this method will return `None` if key is longer than the exact key contained within this
    /// node, even if there is a valid value at the leading subset of `key`
    fn node_get_val<'a>(&'a self, key: &[u8]) -> Option<&'a V>;

    /// Mutable version of [node_get_val]
    fn node_get_val_mut(&mut self, key: &[u8]) -> Option<&mut V>;

    /// Sets the value specified by `key` to the object V
    ///
    /// Returns `Ok((None, _))` if a new value was added where there was no previous value, returns
    /// `Ok((Some(v), false))` with the old value if the value was replaced.  The returned `bool` is a
    /// "sub_node_created" flag that will be `true` if `key` now specifies a different subnode; `false`
    /// if key still specifies a branch within the node.
    ///
    /// If this method returns Err(node), then the node was upgraded, and the new node must be
    /// substituted into the context formerly ocupied by this this node, and this node must be dropped.
    fn node_set_val(&mut self, key: &[u8], val: V) -> Result<(Option<V>, bool), TrieNodeODRc<V>>;

    /// Deletes the value specified by `key`
    ///
    /// Returns `Some(val)` with the value that was removed, otherwise returns `None`
    ///
    /// WARNING: This method may leave the node empty
    fn node_remove_val(&mut self, key: &[u8]) -> Option<V>;

    //GOAT-Deprecated-Update  deprecating `update` interface in favor of WriteZipper
    // /// Returns a mutable reference to the value, creating it using `default_f` if it doesn't already
    // /// exist
    // ///
    // /// If this method returns Err(node), then the node was upgraded, and the new node must be
    // /// substituted into the context formerly ocupied by this this node, and this node must be dropped.
    // /// Then the new node may be re-borrowed.
    // //GOAT, consider a boxless version of this that takes a regular &dyn Fn() instead of FnOnce
    // //Or maybe two versions, one that takes an &dyn Fn, and another that takes a V
    // fn node_update_val(&mut self, key: &[u8], default_f: Box<dyn FnOnce()->V + '_>) -> Result<&mut V, TrieNodeODRc<V>>;

    /// Sets the downstream branch from the specified `key`.  Does not affect the value at the `key`
    ///
    /// Returns `Ok(sub_node_created)`, which will be `true` if `key` now specifies a different subnode;
    /// and `false` if key still specifies a branch within the node.
    ///
    /// If this method returns Err(node), then the `self` node was upgraded, and the new node must be
    /// substituted into the context formerly ocupied by this this node, and this node must be dropped.
    fn node_set_branch(&mut self, key: &[u8], new_node: TrieNodeODRc<V>) -> Result<bool, TrieNodeODRc<V>>;

    /// Removes the downstream branch from the specified `key`.  Does not affect the value at the `key`
    ///
    /// Returns `true` if a value was sucessfully removed from the node; returns `false` if the node did not
    /// contain a branch at the specified key
    ///
    /// WARNING: This method may leave the node empty.  If eager pruning of branches is desired then the
    /// node should subsequently be checked to see if it is empty
    fn node_remove_all_branches(&mut self, key: &[u8]) -> bool;

    /// Uses a 256-bit mask to filter down children and values from the specified `key`.  Does not affect
    /// the value at the `key`
    ///
    /// WARNING: This method may leave the node empty.  If eager pruning of branches is desired then the
    /// node should subsequently be checked to see if it is empty
    fn node_remove_unmasked_branches(&mut self, key: &[u8], mask: [u64; 4]);

    /// Returns `true` if the node contains no children nor values, otherwise false
    fn node_is_empty(&self) -> bool;

    /// Generates a new iter token, to iterate the children and values contained within this node
    fn new_iter_token(&self) -> u128;

    /// Generates an iter token that can be passed to [Self::next_items] to continue iteration from the
    /// specified path
    ///
    /// Returns `(new_token, complete_node_key)`
    fn iter_token_for_path(&self, key: &[u8]) -> (u128, &[u8]);

    /// Steps to the next existing path within the node, in a depth-first order
    ///
    /// Returns `(next_token, path, child_node, value)`
    /// - `next_token` is the value to pass to a subsequent call of this method.  Returns
    ///   [NODE_ITER_FINISHED] when there are no more sub-paths
    /// - `path` is relative to the start of `node`
    /// - `child_node` an onward node link, of `None`
    /// - `value` that exists at the path, or `None`
    fn next_items(&self, token: u128) -> (u128, &[u8], Option<&TrieNodeODRc<V>>, Option<&V>);

    /// Returns the total number of leaves contained within the whole subtree defined by the node
    fn node_val_count(&self, cache: &mut HashMap<*const dyn TrieNode<V>, usize>) -> usize;

    #[cfg(feature = "counters")]
    /// Returns the number of internal items (onward links and values) within the node.  In the case where
    /// a child node and a value have the same internal path it should be counted as two items
    fn item_count(&self) -> usize;

    /// Returns the depth (byte count) of the first value encountered along the specified key
    ///
    /// For example, if the node contains a value at "he" and another value at "hello", this method should
    /// return `Some(1)` for the key "hello", because the "he" value is encountered first.  Returns `None`
    /// if no value is contained within the node along the specified `key`.
    ///
    /// If this method returns `Some(n)`, then `node_get_val(&key[..=n])` must return a non-None result.
    ///
    /// This method will never be called with a zero-length key.
    fn node_first_val_depth_along_key(&self, key: &[u8]) -> Option<usize>;

    /// Returns the nth descending child path from the branch specified by `key` within this node, as the
    /// prefix leading to that new path and optionally a new node
    ///
    /// This method returns (None, _) if `n >= self.count_branches()`.
    /// This method returns (Some(_), None) if the child path is is contained within the same node.
    /// This method returns (Some(_), Some(_)) if the child path is is contained within a different node.
    ///
    /// NOTE: onward paths that lead to values are still part of the enumeration
    /// NOTE: Unlike some other trait methods, method may be called with a zero-length key
    fn nth_child_from_key(&self, key: &[u8], n: usize) -> (Option<u8>, Option<&dyn TrieNode<V>>);

    /// Behaves similarly to [Self::nth_child_from_key(0)] with the difference being that the returned
    /// prefix should be an entire path to the onward link or to the next branch
    fn first_child_from_key(&self, key: &[u8]) -> (Option<&[u8]>, Option<&dyn TrieNode<V>>);

    /// Returns the number of onward (child) paths within a node from a specified key
    ///
    /// If the node doesn't contain the key, this method returns 0.
    /// If the key identifies a value but no onward path within the node, this method returns 0.
    /// If the key identifies a partial path within the node, this method returns 1.
    ///
    /// WARNING: This method does not recurse, so an onward child link's children will not be
    ///   considered.  Therefore, it is necessary to call this method on the referenced node and
    ///   not the parent.
    /// NOTE: Unlike some other trait methods, method may be called with a zero-length key
    fn count_branches(&self, key: &[u8]) -> usize;

    /// Returns 256-bit mask, indicating which children exist from the branch specified by `key`
    fn node_branches_mask(&self, key: &[u8]) -> [u64; 4];

    /// Returns `true` if the key specifies a leaf within the node from which it is impossible to
    /// descend further, otherwise returns `false`
    ///
    /// NOTE: Returns `true` if the key specifies an invalid path, because an invalid path has no
    ///   onward paths branching from it.
    /// NOTE: The reason this is not the same as `node.count_branches() == 0` is because [Self::count_branches]
    ///   counts only internal children, and treats values and onward links equivalently.  Therefore
    ///   some keys that specify onward links will be reported as having a `count_branches` of 0, but
    ///   `is_leaf` will not be true.
    fn is_leaf(&self, key: &[u8]) -> bool;

    /// Returns the key of the prior upstream branch, within the node
    ///
    /// This method will never be called with a zero-length key.
    /// Returns &[] if `key` is descended from the root and therefore has no upstream branch.
    /// Returns &[] if `key` does not exist within the node.
    fn prior_branch_key(&self, key: &[u8]) -> &[u8];

    /// Returns the child of this node that is immediately before or after the child identified by `key`
    ///
    /// Returns None if the found child node is already the first or last child, or if `key` does not
    /// identify any contained subnode
    ///
    /// If 'next == true` then the returned child will be immediately after to the node found by
    /// `key`, otherwise it will be immedtely before
    ///
    /// NOTE: This method will never be called with a zero-length key
    fn get_sibling_of_child(&self, key: &[u8], next: bool) -> (Option<u8>, Option<&dyn TrieNode<V>>);

    /// Returns a new node which is a clone or reference to the portion of the node rooted at `key`, or
    /// `None` if `key` does not specify a path within the node
    ///
    /// If `key.len() == 0` this method will return a reference to or a clone of the node.
    fn get_node_at_key(&self, key: &[u8]) -> AbstractNodeRef<V>;

    /// Returns a node which is the the portion of the node rooted at `key`, or `None` if `key` does
    /// not specify a path within the node
    ///
    /// This method should never be called with `key.len() == 0`
    fn take_node_at_key(&mut self, key: &[u8]) -> Option<TrieNodeODRc<V>>;

    /// Allows for the implementation of the Lattice trait on different node implementations, and
    /// the logic to promote nodes to other node types
    fn join_dyn(&self, other: &dyn TrieNode<V>) -> TrieNodeODRc<V> where V: Lattice;

    /// Allows for the implementation of the Lattice trait on different node implementations, and
    /// the logic to promote nodes to other node types
    fn join_into_dyn(&mut self, other: TrieNodeODRc<V>) where V: Lattice;

    /// Returns a node composed of the children of `self`, `byte_cnt` bytes downstream, all joined together,
    /// or `None` if the node has no children at that depth
    ///
    /// After this method, `self` will be invalid and/ or empty, and should be replaced with the result.
    ///
    /// QUESTION: Is there a value to a "copying" version of drop_head?  It has higher overheads but could
    /// be safely implemented by the [crate::zipper::ReadZipper].
    fn drop_head_dyn(&mut self, byte_cnt: usize) -> Option<TrieNodeODRc<V>> where V: Lattice;

    /// Allows for the implementation of the Lattice trait on different node implementations, and
    /// the logic to promote nodes to other node types.
    fn meet_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> where V: Lattice;

    /// Allows for the implementation of the PartialDistributiveLattice algebraic operations
    ///
    /// If this method returns `(false, None)`, it means the original value should be "annihilated",
    ///   e.g. complete subtraction, with nothing left behind
    /// If it returns `(true, _)` it means the original value of the slot should be maintained, unmodified.
    /// If it returns `(false, Some(_))` then a new node was created
    fn psubtract_dyn(&self, other: &dyn TrieNode<V>) -> (bool, Option<TrieNodeODRc<V>>) where V: PartialDistributiveLattice;

    /// Allows for the implementation of the PartialQuantale algebraic operations
    fn prestrict_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>>;

    /// Returns a clone of the node in its own Rc
    fn clone_self(&self) -> TrieNodeODRc<V>;
}

/// Implements methods to get the concrete type from a dynamic TrieNode
pub trait TrieNodeDowncast<V> {
    /// Returns a [TaggedNodeRef] referencing this node
    fn as_tagged(&self) -> TaggedNodeRef<V>;

    /// Returns a [TaggedNodeRefMut] referencing this node
    fn as_tagged_mut(&mut self) -> TaggedNodeRefMut<V>;

    /// Migrates the contents of the node into a new CellByteNode.  After this method, `self` will be empty
    fn convert_to_cell_node(&mut self) -> TrieNodeODRc<V>;
}

/// Special sentinel token value indicating iteration of a node has not been initialized
pub const NODE_ITER_INVALID: u128 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF;

/// Special sentinel token value indicating iteration of a node has concluded
pub const NODE_ITER_FINISHED: u128 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE;

#[derive(Clone)]
pub(crate) enum ValOrChild<V> {
    Val(V),
    Child(TrieNodeODRc<V>)
}

impl<V> core::fmt::Debug for ValOrChild<V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::Val(_v) => write!(f, "ValOrChild::Val"), //Don't want to restrict the impl to V: Debug
            Self::Child(c) => write!(f, "ValOrChild::Child{{ {c:?} }}"),
        }
    }
}

impl<V> ValOrChild<V> {
    pub fn into_child(self) -> TrieNodeODRc<V> {
        match self {
            Self::Child(child) => child,
            _ => panic!()
        }
    }
    pub fn into_val(self) -> V {
        match self {
            Self::Val(val) => val,
            _ => panic!()
        }
    }
}

pub enum AbstractNodeRef<'a, V> {
    None,
    BorrowedDyn(&'a dyn TrieNode<V>),
    BorrowedRc(&'a TrieNodeODRc<V>),
    BorrowedTiny(TinyRefNode<'a, V>),
    OwnedRc(TrieNodeODRc<V>)
}

impl<'a, V> core::fmt::Debug for AbstractNodeRef<'a, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::None => write!(f, "AbstractNodeRef::None"),
            Self::BorrowedDyn(_) => write!(f, "AbstractNodeRef::BorrowedDyn"),
            Self::BorrowedRc(_) => write!(f, "AbstractNodeRef::BorrowedRc"),
            Self::BorrowedTiny(_) => write!(f, "AbstractNodeRef::BorrowedTiny"),
            Self::OwnedRc(_) => write!(f, "AbstractNodeRef::OwnedRc"),
        }
    }
}

impl<'a, V: Clone + Send + Sync> AbstractNodeRef<'a, V> {
    pub fn is_none(&self) -> bool {
        matches!(self, AbstractNodeRef::None)
    }
    pub fn borrow(&self) -> &dyn TrieNode<V> {
        match self {
            AbstractNodeRef::None => panic!(),
            AbstractNodeRef::BorrowedDyn(node) => *node,
            AbstractNodeRef::BorrowedRc(rc) => rc.borrow(),
            AbstractNodeRef::BorrowedTiny(tiny) => tiny,
            AbstractNodeRef::OwnedRc(rc) => rc.borrow()
        }
    }
    pub fn try_borrow(&self) -> Option<&dyn TrieNode<V>> {
        match self {
            AbstractNodeRef::None => None,
            AbstractNodeRef::BorrowedDyn(node) => Some(*node),
            AbstractNodeRef::BorrowedRc(rc) => Some(rc.borrow()),
            AbstractNodeRef::BorrowedTiny(tiny) => Some(tiny),
            AbstractNodeRef::OwnedRc(rc) => Some(rc.borrow())
        }
    }
    pub fn into_option(self) -> Option<TrieNodeODRc<V>> {
        match self {
            AbstractNodeRef::None => None,
            AbstractNodeRef::BorrowedDyn(node) => Some(node.clone_self()),
            AbstractNodeRef::BorrowedRc(rc) => Some(rc.clone()),
            AbstractNodeRef::BorrowedTiny(tiny) => tiny.into_full().map(|list_node| TrieNodeODRc::new(list_node)),
            AbstractNodeRef::OwnedRc(rc) => Some(rc)
        }
    }
}

/// A reference to a node with a concrete type
#[derive(Clone, Copy)]
pub enum TaggedNodeRef<'a, V> {
    DenseByteNode(&'a DenseByteNode<V>),
    LineListNode(&'a LineListNode<V>),
    CellByteNode(&'a CellByteNode<V>),
    EmptyNode(&'a EmptyNode<V>),
}

/// A mutable reference to a node with a concrete type
pub enum TaggedNodeRefMut<'a, V> {
    DenseByteNode(&'a mut DenseByteNode<V>),
    LineListNode(&'a mut LineListNode<V>),
    CellByteNode(&'a mut CellByteNode<V>),
}

impl<V: Clone + Send + Sync> core::fmt::Debug for TaggedNodeRef<'_, V> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::DenseByteNode(node) => write!(f, "{node:?}"), //Don't want to restrict the impl to V: Debug
            Self::LineListNode(node) => write!(f, "{node:?}"),
            Self::CellByteNode(node) => write!(f, "{node:?}"),
            Self::EmptyNode(node) => write!(f, "{node:?}"),
        }
    }
}

impl<'a, V: Clone + Send + Sync> TaggedNodeRef<'a, V> {
    pub fn borrow(&self) -> &dyn TrieNode<V> {
        match self {
            Self::DenseByteNode(node) => *node as &dyn TrieNode<V>,
            Self::LineListNode(node) => *node as &dyn TrieNode<V>,
            Self::CellByteNode(node) => *node as &dyn TrieNode<V>,
            Self::EmptyNode(node) => *node as &dyn TrieNode<V>,
        }
    }
    pub fn node_contains_partial_key(&self, key: &[u8]) -> bool {
        match self {
            Self::DenseByteNode(node) => node.node_contains_partial_key(key),
            Self::LineListNode(node) => node.node_contains_partial_key(key),
            Self::CellByteNode(node) => node.node_contains_partial_key(key),
            Self::EmptyNode(_) => false
        }
    }
    #[inline(always)]
    pub fn node_get_child(&self, key: &[u8]) -> Option<(usize, &'a dyn TrieNode<V>)> {
        match self {
            Self::DenseByteNode(node) => node.node_get_child(key),
            Self::LineListNode(node) => node.node_get_child(key),
            Self::CellByteNode(node) => node.node_get_child(key),
            Self::EmptyNode(_) => None,
        }
    }

    // fn node_get_child_and_val_mut<'a>(&'a mut self, key: &[u8]) -> Option<(usize, Option<&'a mut V>, Option<&'a mut TrieNodeODRc<V>>)>;

    // fn node_get_child_mut(&mut self, key: &[u8]) -> Option<(usize, &mut TrieNodeODRc<V>)>;

    // fn node_replace_child(&mut self, key: &[u8], new_node: TrieNodeODRc<V>) -> &mut dyn TrieNode<V>;

    pub fn node_contains_val(&self, key: &[u8]) -> bool {
        match self {
            Self::DenseByteNode(node) => node.node_contains_val(key),
            Self::LineListNode(node) => node.node_contains_val(key),
            Self::CellByteNode(node) => node.node_contains_val(key),
            Self::EmptyNode(_) => false,
        }
    }
    pub fn node_get_val(&self, key: &[u8]) -> Option<&'a V> {
        match self {
            Self::DenseByteNode(node) => node.node_get_val(key),
            Self::LineListNode(node) => node.node_get_val(key),
            Self::CellByteNode(node) => node.node_get_val(key),
            Self::EmptyNode(_) => None,
        }
    }

    // fn node_get_val_mut(&mut self, key: &[u8]) -> Option<&mut V>;

    // fn node_set_val(&mut self, key: &[u8], val: V) -> Result<(Option<V>, bool), TrieNodeODRc<V>>;

    // fn node_remove_val(&mut self, key: &[u8]) -> Option<V>;

    // fn node_set_branch(&mut self, key: &[u8], new_node: TrieNodeODRc<V>) -> Result<bool, TrieNodeODRc<V>>;

    // fn node_remove_all_branches(&mut self, key: &[u8]) -> bool;

    // fn node_remove_unmasked_branches(&mut self, key: &[u8], mask: [u64; 4]);

    // fn node_is_empty(&self) -> bool;

    #[inline(always)]
    pub fn new_iter_token(&self) -> u128 {
        match self {
            Self::DenseByteNode(node) => node.new_iter_token(),
            Self::LineListNode(node) => node.new_iter_token(),
            Self::CellByteNode(node) => node.new_iter_token(),
            Self::EmptyNode(node) => node.new_iter_token(),
        }
    }
    #[inline(always)]
    pub fn iter_token_for_path(&self, key: &[u8]) -> (u128, &[u8]) {
        match self {
            Self::DenseByteNode(node) => node.iter_token_for_path(key),
            Self::LineListNode(node) => node.iter_token_for_path(key),
            Self::CellByteNode(node) => node.iter_token_for_path(key),
            Self::EmptyNode(node) => node.iter_token_for_path(key),
        }
    }
    #[inline(always)]
    pub fn next_items(&self, token: u128) -> (u128, &'a[u8], Option<&'a TrieNodeODRc<V>>, Option<&'a V>) {
        match self {
            Self::DenseByteNode(node) => node.next_items(token),
            Self::LineListNode(node) => node.next_items(token),
            Self::CellByteNode(node) => node.next_items(token),
            Self::EmptyNode(node) => node.next_items(token),
        }
    }

    // fn node_val_count(&self, cache: &mut HashMap<*const dyn TrieNode<V>, usize>) -> usize;

    // #[cfg(feature = "counters")]
    // fn item_count(&self) -> usize;

    // fn node_first_val_depth_along_key(&self, key: &[u8]) -> Option<usize>;

    pub fn nth_child_from_key(&self, key: &[u8], n: usize) -> (Option<u8>, Option<&'a dyn TrieNode<V>>) {
        match self {
            Self::DenseByteNode(node) => node.nth_child_from_key(key, n),
            Self::LineListNode(node) => node.nth_child_from_key(key, n),
            Self::CellByteNode(node) => node.nth_child_from_key(key, n),
            Self::EmptyNode(node) => node.nth_child_from_key(key, n),
        }
    }
    pub fn first_child_from_key(&self, key: &[u8]) -> (Option<&'a [u8]>, Option<&'a dyn TrieNode<V>>) {
        match self {
            Self::DenseByteNode(node) => node.first_child_from_key(key),
            Self::LineListNode(node) => node.first_child_from_key(key),
            Self::CellByteNode(node) => node.first_child_from_key(key),
            Self::EmptyNode(node) => node.first_child_from_key(key),
        }
    }
    #[inline(always)]
    pub fn count_branches(&self, key: &[u8]) -> usize {
        match self {
            Self::DenseByteNode(node) => node.count_branches(key),
            Self::LineListNode(node) => node.count_branches(key),
            Self::CellByteNode(node) => node.count_branches(key),
            Self::EmptyNode(node) => node.count_branches(key),
        }
    }
    #[inline(always)]
    pub fn node_branches_mask(&self, key: &[u8]) -> [u64; 4] {
        match self {
            Self::DenseByteNode(node) => node.node_branches_mask(key),
            Self::LineListNode(node) => node.node_branches_mask(key),
            Self::CellByteNode(node) => node.node_branches_mask(key),
            Self::EmptyNode(node) => node.node_branches_mask(key),
        }
    }
    #[inline(always)]
    pub fn is_leaf(&self, key: &[u8]) -> bool {
        match self {
            Self::DenseByteNode(node) => node.is_leaf(key),
            Self::LineListNode(node) => node.is_leaf(key),
            Self::CellByteNode(node) => node.is_leaf(key),
            Self::EmptyNode(node) => node.is_leaf(key),
        }
    }
    pub fn prior_branch_key(&self, key: &[u8]) -> &[u8] {
        match self {
            Self::DenseByteNode(node) => node.prior_branch_key(key),
            Self::LineListNode(node) => node.prior_branch_key(key),
            Self::CellByteNode(node) => node.prior_branch_key(key),
            Self::EmptyNode(node) => node.prior_branch_key(key),
        }
    }
    pub fn get_sibling_of_child(&self, key: &[u8], next: bool) -> (Option<u8>, Option<&'a dyn TrieNode<V>>) {
        match self {
            Self::DenseByteNode(node) => node.get_sibling_of_child(key, next),
            Self::LineListNode(node) => node.get_sibling_of_child(key, next),
            Self::CellByteNode(node) => node.get_sibling_of_child(key, next),
            Self::EmptyNode(node) => node.get_sibling_of_child(key, next),
        }
    }
    pub fn get_node_at_key(&self, key: &[u8]) -> AbstractNodeRef<V> {
        match self {
            Self::DenseByteNode(node) => node.get_node_at_key(key),
            Self::LineListNode(node) => node.get_node_at_key(key),
            Self::CellByteNode(node) => node.get_node_at_key(key),
            Self::EmptyNode(node) => node.get_node_at_key(key),
        }
    }

    // fn take_node_at_key(&mut self, key: &[u8]) -> Option<TrieNodeODRc<V>>;

    // fn join_dyn(&self, other: &dyn TrieNode<V>) -> TrieNodeODRc<V> where V: Lattice;

    // fn join_into_dyn(&mut self, other: TrieNodeODRc<V>) where V: Lattice;

    // fn drop_head_dyn(&mut self, byte_cnt: usize) -> Option<TrieNodeODRc<V>> where V: Lattice;

    // fn meet_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>> where V: Lattice;

    // fn psubtract_dyn(&self, other: &dyn TrieNode<V>) -> (bool, Option<TrieNodeODRc<V>>) where V: PartialDistributiveLattice;

    // fn prestrict_dyn(&self, other: &dyn TrieNode<V>) -> Option<TrieNodeODRc<V>>;

    #[inline(always)]
    pub fn as_dense(&self) -> Option<&'a DenseByteNode<V>> {
        match self {
            Self::DenseByteNode(node) => Some(node),
            Self::LineListNode(_) => None,
            Self::CellByteNode(_) => None,
            Self::EmptyNode(_) => None,
        }
    }

    // fn as_dense_mut(&mut self) -> Option<&mut DenseByteNode<V>>;

    #[inline(always)]
    pub fn as_list(&self) -> Option<&'a LineListNode<V>> {
        match self {
            Self::DenseByteNode(_) => None,
            Self::LineListNode(node) => Some(node),
            Self::CellByteNode(_) => None,
            Self::EmptyNode(_) => None,
        }
    }

    // fn as_list_mut(&mut self) -> Option<&mut LineListNode<V>>;

    // fn as_tagged(&self) -> TaggedNodeRef<V>;

    // fn clone_self(&self) -> TrieNodeODRc<V>;
}

impl<'a, V: Clone + Send + Sync> TaggedNodeRefMut<'a, V> {
    #[inline(always)]
    pub fn into_dense(self) -> Option<&'a mut DenseByteNode<V>> {
        match self {
            Self::DenseByteNode(node) => Some(node),
            Self::LineListNode(_) => None,
            Self::CellByteNode(_) => None,
        }
    }
    #[inline(always)]
    pub fn into_list(self) -> Option<&'a mut LineListNode<V>> {
        match self {
            Self::LineListNode(node) => Some(node),
            Self::DenseByteNode(_) => None,
            Self::CellByteNode(_) => None,
        }
    }
    #[inline(always)]
    pub fn into_cell_node(self) -> Option<&'a mut CellByteNode<V>> {
        match self {
            Self::CellByteNode(node) => Some(node),
            Self::DenseByteNode(_) => None,
            Self::LineListNode(_) => None,
        }
    }
}

/// Returns the count of values in the subtrie descending from the node, caching shared subtries
pub(crate) fn val_count_below_root<V>(node: &dyn TrieNode<V>) -> usize {
    let mut cache = std::collections::HashMap::new();
    node.node_val_count(&mut cache)
}

pub(crate) fn val_count_below_node<V>(node: &TrieNodeODRc<V>, cache: &mut HashMap<*const dyn TrieNode<V>, usize>) -> usize {
    if Arc::strong_count(node.as_arc()) > 1 {
        let ptr = Arc::as_ptr(node.as_arc());
        match cache.get(&ptr) {
            Some(cached) => *cached,
            None => {
                let val = node.borrow().node_val_count(cache);
                cache.insert(ptr, val);
                val
            },
        }
    } else {
        node.borrow().node_val_count(cache)
    }
}

/// Ensures that the node at the specified path exists, and is a [DenseByteNode]
///
/// Returns `(false, node)` if the node already existed (regardless of whether or not it was upgraded),
/// and returns `(true, node)` if the node was created.
///
/// NOTE: I was originally thinking this code could be shared between the PathMap::zipper_head impl and
/// the WriteZipper::zipper_head impl.  But unfortunately the WriteZipper version is too intertwined with
/// the logic to keep the zipper in a coherent state.  So maybe this function should just be integrated
/// into PathMap::zipper_head.
pub(crate) fn prepare_exclusive_write_path<'a, V: Clone + Send + Sync>(root_node: &'a mut TrieNodeODRc<V>, path: &[u8]) -> &'a mut TrieNodeODRc<V> {
    if path.len() == 0 {
        //If `path.len() == 0` then we know this node is either the root of an existing WriteZipper or
        // the root of a Map, so we know it's safe to write to it from another thread
        root_node
    } else {
        let (mut remaining_key, mut node) = node_along_path_mut(root_node, path, true);
        debug_assert!(remaining_key.len() > 0);

        //See if we need to make an intermediary parent node
        if remaining_key.len() > 1 {
            let intermediate_key = &remaining_key[..remaining_key.len()-1];
            let node_ref = node.make_mut();
            let new_parent = match node_ref.take_node_at_key(intermediate_key) {
                Some(downward_node) => downward_node,
                None => TrieNodeODRc::new(CellByteNode::new())
            };
            let result = node_ref.node_set_branch(intermediate_key, new_parent);
            match result {
                Ok(_) => { },
                Err(replacement_node) => { *node = replacement_node; }
            }
            let (new_remaining_key, child_node) = node_along_path_mut(node, remaining_key, true);
            debug_assert_eq!(new_remaining_key, &remaining_key[remaining_key.len()-1..]);
            remaining_key = new_remaining_key;
            node = child_node;
        }

        debug_assert_eq!(remaining_key.len(), 1);
        make_cell_node(node);
        let cell_node = node.make_mut().as_tagged_mut().into_cell_node().unwrap();
        let (child, val) = cell_node.prepare_cf(remaining_key[0]);
        //GOAT, gotta use the val for the zipper's root value
        child
    }
}

/// Internal function to walk a mut TrieNodeODRc<V> ref along a path
///
/// If `stop_early` is `true`, this function will return the parent node of the path and will never return
/// a zero-length continuation path.  If `stop_early` is `false`, the returned continuation path may be
/// zero-length and the returned node will represent as much of the path as is possible.
#[inline]
pub(crate) fn node_along_path_mut<'a, 'k, V>(start_node: &'a mut TrieNodeODRc<V>, path: &'k [u8], stop_early: bool) -> (&'k [u8], &'a mut TrieNodeODRc<V>) {
    let mut key = path;
    let mut node = start_node;

    //Step until we get to the end of the key or find a leaf node
    let mut node_ptr: *mut TrieNodeODRc<V> = node; //Work-around for lack of polonius
    if key.len() > 0 {
        while let Some((consumed_byte_cnt, next_node)) = node.make_mut().node_get_child_mut(key) {
            if consumed_byte_cnt < key.len() || !stop_early {
                node = next_node;
                node_ptr = node;
                key = &key[consumed_byte_cnt..];
                if key.len() == 0 {
                    break;
                }
            } else {
                break;
            };
        }
    }

    //SAFETY: Polonius is ok with this code.  All mutable borrows of the current version of the
    //  `node` &mut ref have ended by this point
    node = unsafe{ &mut *node_ptr };
    (key, node)
}

/// Ensures the node is a CellByteNode
///
/// Returns `true` if the node was upgraded and `false` if it already was a CellByteNode
pub(crate) fn make_cell_node<V: Clone + Send + Sync>(node: &mut TrieNodeODRc<V>) -> bool {
    match node.borrow().as_tagged() {
        TaggedNodeRef::CellByteNode(_) => false,
        _ => {
            let replacement = node.make_mut().convert_to_cell_node();
            *node = replacement;
            true
        },
    }
}

//TODO: Make a Macro to generate OpaqueDynBoxes and ODRc (OpaqueDynRc) and an Arc version
//GOAT: the `pub(crate)` visibility inside the `opaque_dyn_rc_trie_node` module come from the visibility of
// the trait it is derived on.  In this case, `TrieNode`
pub(crate) use opaque_dyn_rc_trie_node::TrieNodeODRc;
mod opaque_dyn_rc_trie_node {
    use super::TrieNode;

    //TODO_FUTURE: make a type alias within the trait to refer to this type, as soon as
    // https://github.com/rust-lang/rust/issues/29661 is addressed

    #[derive(Clone)]
    #[repr(transparent)]
    pub struct TrieNodeODRc<V>(std::sync::Arc<dyn TrieNode<V> + 'static>);

    impl<V> TrieNodeODRc<V> {
        #[inline]
        pub(crate) fn new<'odb, T>(obj: T) -> Self
            where T: 'odb + TrieNode<V>,
            V: 'odb
        {
            let inner: std::rc::Rc<dyn TrieNode<V>> = std::rc::Rc::new(obj);
            //SAFETY NOTE: The key to making this abstraction safe is the bound on this method,
            // such that it's impossible to create this wrapper around a concrete type unless the
            // same lifetime can bound both the trait's type parameter and the type itself
            unsafe { Self(core::mem::transmute(inner)) }
        }
        #[inline]
        pub(crate) fn new_from_rc<'odb>(rc: std::rc::Rc<dyn TrieNode<V> + 'odb>) -> Self
            where V: 'odb
        {
            let inner = rc as std::rc::Rc<dyn TrieNode<V>>;
            //SAFETY NOTE: The key to making this abstraction safe is the bound on this method,
            // such that it's impossible to create this wrapper around a concrete type unless the
            // same lifetime can bound both the trait's type parameter and the type itself
            unsafe { Self(core::mem::transmute(inner)) }
        }
        #[inline]
        pub(crate) fn as_arc(&self) -> &std::sync::Arc<dyn TrieNode<V>> {
            &self.0
        }
        #[inline]
        pub(crate) fn borrow(&self) -> &dyn TrieNode<V> {
            &*self.0
        }
        /// Returns `true` if both internal Rc ptrs point to the same object
        #[inline]
        pub fn ptr_eq(&self, other: &Self) -> bool {
            std::sync::Arc::ptr_eq(self.as_arc(), other.as_arc())
        }
        //GOAT, make this contingent on a dyn_clone compile-time feature
        #[inline]
        pub(crate) fn make_mut(&mut self) -> &mut (dyn TrieNode<V> + 'static) {
            dyn_clone::arc_make_mut(&mut self.0) as &mut dyn TrieNode<V>
        }
    }

    impl<V> core::fmt::Debug for TrieNodeODRc<V>
        where for<'a> &'a dyn TrieNode<V>: core::fmt::Debug
    {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            core::fmt::Debug::fmt(&self.0, f)
        }
    }

    //GOAT, make this impl contingent on a "DefaultT" argument to the macro
    type DefaultT<V> = super::EmptyNode<V>;
    impl<V> Default for TrieNodeODRc<V> where DefaultT<V>: Default + TrieNode<V> {
        fn default() -> Self {
            Self::new(DefaultT::<V>::default())
        }
    }

    impl<'odb, V> From<std::rc::Rc<dyn TrieNode<V> + 'odb>> for TrieNodeODRc<V>
        where V: 'odb
    {
        fn from(rc: std::rc::Rc<dyn TrieNode<V> + 'odb>) -> Self {
            Self::new_from_rc(rc)
        }
    }
}

//NOTE: This resembles the Lattice trait impl, but we want to return option instead of allocating a
// an empty node to return a reference to
impl<V: Lattice + Clone> TrieNodeODRc<V> {
    #[inline]
    pub fn join(&self, other: &Self) -> Self {
        if self.ptr_eq(other) {
            self.clone()
        } else {
            let node = self.borrow();
            if !node.node_is_empty() {
                node.join_dyn(other.borrow())
            } else {
                other.clone()
            }
        }
    }
    #[inline]
    pub fn join_into(&mut self, other: Self) {
        if !self.ptr_eq(&other) {
            self.make_mut().join_into_dyn(other)
        }
    }
    #[inline]
    pub fn meet(&self, other: &Self) -> Option<Self> {
        if self.ptr_eq(other) {
            Some(self.clone())
        } else {
            self.borrow().meet_dyn(other.borrow())
        }
    }
}

//See above, pseudo-impl for PartialDistributiveLattice trait
impl<V: PartialDistributiveLattice + Clone> TrieNodeODRc<V> {
    pub fn psubtract(&self, other: &Self) -> Option<Self> {
        if self.ptr_eq(other) {
            None
        } else {
            match self.borrow().psubtract_dyn(other.borrow()) {
                (false, None) => None,
                (false, Some(new_node)) => Some(new_node),
                (true, _) => Some(self.clone()),
            }
        }
    }
}

impl <V: Clone> PartialQuantale for TrieNodeODRc<V> {
    fn prestrict(&self, other: &Self) -> Option<Self> where Self: Sized {
        self.borrow().prestrict_dyn(other.borrow())
    }
}

//See above, pseudo-impl for DistributiveLattice trait
impl<V: PartialDistributiveLattice + Clone + Send + Sync> TrieNodeODRc<V> {
    pub fn subtract(&self, other: &Self) -> Self {
        if self.ptr_eq(other) {
            TrieNodeODRc::new(EmptyNode::new())
        } else {
            match self.borrow().psubtract_dyn(other.borrow()) {
                (false, None) => TrieNodeODRc::new(EmptyNode::new()),
                (false, Some(new_node)) => new_node,
                (true, _) => self.clone(),
            }
        }
    }
}

impl<V: Lattice + Clone> Lattice for Option<TrieNodeODRc<V>> {
    fn join(&self, other: &Option<TrieNodeODRc<V>>) -> Option<TrieNodeODRc<V>> {
        match self {
            None => { match other {
                None => { None }
                Some(r) => { Some(r.clone()) }
            } }
            Some(l) => match other {
                None => { Some(l.clone()) }
                Some(r) => { Some(l.join(r)) }
            }
        }
    }
    /// GOAT, maybe the default impl is fine
    // fn join_into(&mut self, other: Self) {
    //     match self {
    //         None => { match other {
    //             None => { }
    //             Some(r) => { *self = Some(r) }
    //         } }
    //         Some(l) => match other {
    //             None => { }
    //             Some(r) => { l.join_into(r) }
    //         }
    //     }
    // }
    fn meet(&self, other: &Option<TrieNodeODRc<V>>) -> Option<TrieNodeODRc<V>> {
        match self {
            None => { None }
            Some(l) => {
                match other {
                    None => { None }
                    Some(r) => l.meet(r)
                }
            }
        }
    }
    fn bottom() -> Self {
        None
    }
}

impl<V: Lattice + Clone> LatticeRef for Option<&TrieNodeODRc<V>> {
    type T = Option<TrieNodeODRc<V>>;
    fn join(&self, other: &Option<&TrieNodeODRc<V>>) -> Option<TrieNodeODRc<V>> {
        match self {
            None => { match other {
                None => { None }
                Some(r) => { Some((*r).clone()) }
            } }
            Some(l) => match other {
                None => { Some((*l).clone()) }
                Some(r) => { Some(l.join(r)) }
            }
        }
    }
    fn meet(&self, other: &Option<&TrieNodeODRc<V>>) -> Option<TrieNodeODRc<V>> {
        match self {
            None => { None }
            Some(l) => {
                match other {
                    None => { None }
                    Some(r) => l.meet(r)
                }
            }
        }
    }
}

impl<V: PartialDistributiveLattice + Clone> PartialDistributiveLattice for Option<TrieNodeODRc<V>> {
    fn psubtract(&self, other: &Self) -> Option<Self> {
        match self {
            None => { None }
            Some(s) => { match other {
                None => { Some(Some(s.clone())) }
                Some(o) => { Some(s.psubtract(o)) }
            } }
        }
    }
}

impl<V: PartialDistributiveLattice + Clone> PartialDistributiveLatticeRef for Option<&TrieNodeODRc<V>> {
    type T = Option<TrieNodeODRc<V>>;
    fn psubtract(&self, other: &Self) -> Option<Self::T> {
        match self {
            None => { None }
            Some(s) => { match other {
                None => { Some(Some((*s).clone())) }
                Some(o) => { Some(s.psubtract(o)) }
            } }
        }
    }
}

impl<V: PartialDistributiveLattice + Clone> DistributiveLattice for Option<TrieNodeODRc<V>> {
    fn subtract(&self, other: &Self) -> Self {
        match self {
            None => { None }
            Some(s) => { match other {
                None => { Some(s.clone()) }
                Some(o) => { s.psubtract(o) }
            } }
        }
    }
}
