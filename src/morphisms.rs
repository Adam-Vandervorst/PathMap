//! Functionality for applying various morphisms to [PathMap] and [Zipper](crate::zipper::Zipper)s
//!
//! Morphisms are a generalization of the [fold](std::iter::Iterator::fold) pattern, but for a trie or
//! sub-trie, as opposed to a list / sequence.  Similarly they rely on results being aggregated into
//! intermediate structures that are themselves joined together to produce a result.
//!
//! ### Supported Morphisms:
//!
//! #### Catamorphism
//!
//! Process a trie from the leaves towards the root.  This algorithm proceeds in a depth-first order,
//! working from the leaves upward calling a closure on each path in the trie.  A summary "accumulator"
//! type `W` is used to represent the information about the trie and carry it upwards to the next invocation
//! of the closure.
//!
//! The word "catamorphism" comes from the Greek for "down", because the root is considered the bottom
//! of the trie.  This is confusing because elsewhere we use the convention that `descend_` "deeper"
//! into the trie means moving further from the root while `ascend` moves closer to the root.  The docs
//! will stick to this convention in-spite of the Greek meaning.
//!
//! **NOTE**: The traversal order, while depth-first, is subtly different from the order of
//! [ZipperIteration::to_next_val](crate::zipper::ZipperIteration::to_next_val) and
//! [ZipperIteration::to_next_step](crate::zipper::ZipperIteration::to_next_step).  The
//! [ZipperIteration](crate::zipper::ZipperIteration) methods visit values first before descending to the
//! branches below, while the `cata` methods call the `mapper` on the deepest values first, before
//! returning to higher levels where `collapse` is called.
//!
//! #### Anamorphism
//!
//! Generate a trie from the root.  Conceptually it is the inverse of catamorphism.  This algorithm proceeds
//! from a starting point corresponding to a root of a trie, and generates branches and leaves recursively.
//!
//! ### Jumping Morphisms and the `jump` closure
//!
//! Ordinary morphism methods conceptually operate on a trie of bytes.  Therefore they execute the `alg`
//! closure for all non-leaf path positions, regardless of the existence of values.
//!
//! By contrast, `_jumping` methods conceptually operate on a trie of values.  That means the `alg` closure
//! is only called at "forking" path positions from which multiple downstream branches descend, and also for
//! the root.  There is an additional `jump` closure passed to these methods that can process an entire
//! substring from the path.
//!
//! In general, `jumping` methods will perform substantially better, so you should use them if your `alg`
//! closure simply passes the intermediate structure upwards when there is only one child branch.
//!
//! ### Side-Effecting vs Factored Iteration
//!
//! Many methods come (or will come) with a `_side_effect` and an ordinary or `factored` flavor.  The
//! algorithm is identical in both variants but the one to use depends on your situation.
//!
//! The `_side_effect` flavor of the methods will exhaustively traverse the entire trie, irrespective of
//! structural sharing within the trie.  So a subtrie that is included `n` times will be visited `n` times.
//! They take [`FnMut`] closure arguments, meaning the closures can produce side-effects, and making these
//! methods useful for things like serialization, etc.
//!
//! The ordinary `factored` flavor takes sharing into account, and thus will only visit each shared subtrie
//! once.  The methods take [`Fn`] closure arguments and they may cache and re-use intermediate results.
//! This means the intermediate result type must implement [`Clone`].
//!
//! In general, the ordinary methods should be preferred unless sife-effects are necessary, because many
//! operations produce structural sharing so the ordinary `factored` methods will likely be more efficient.
//!
use gxhash::HashMap;
use core::convert::Infallible;
use reusing_vec::ReusingQueue;

use crate::utils::*;
use crate::trie_map::BytesTrieMap;
use crate::trie_node::TrieNodeODRc;
use crate::zipper;
use crate::zipper::*;

/// Provides methods to perform a catamorphism on types that can reference or contain a trie
pub trait Catamorphism<V> {
    /// Applies a catamorphism to the trie descending from the zipper's root, running the `alg_f` at every
    /// step (at every byte)
    ///
    /// ## Arguments to `alg_f`:
    /// `(child_mask: &`[`ByteMask`]`, children: &mut [W], value: Option<&V>, path: &[u8]`
    ///
    /// - `child_mask`: A [`ByteMask`] indicating the corresponding byte for each downstream branche in
    /// `children`.
    ///
    /// - `children`: A slice containing all the `W` values from previous invocations of `alg_f` for
    /// downstream branches.
    ///
    /// - `value`: A value associated with a given path in the trie, or `None` if the trie has no value at
    /// that path.
    ///
    /// - `path`: The [`origin_path`](ZipperAbsolutePath::origin_path) for the invocation.  The `alg_f` will
    /// be run exactly once for each unique path in the trie.
    ///
    /// ## Behavior
    ///
    /// The focus position of the zipper will be ignored and it will be immediately reset to the root.
    fn into_cata_side_effect<W, AlgF>(self, mut alg_f: AlgF) -> W
        where
        AlgF: FnMut(&ByteMask, &mut [W], Option<&V>, &[u8]) -> W,
        Self: Sized
    {
        self.into_cata_side_effect_fallible(|mask, children, val, path| -> Result<W, Infallible> {
            Ok(alg_f(mask, children, val, path))
        }).unwrap()
    }

    /// Allows the closure to return an error, stopping traversal immediately
    ///
    /// See [Catamorphism::into_cata_side_effect]
    fn into_cata_side_effect_fallible<W, Err, AlgF>(self, alg_f: AlgF) -> Result<W, Err>
        where AlgF: FnMut(&ByteMask, &mut [W], Option<&V>, &[u8]) -> Result<W, Err>;

    /// Applies a "jumping" catamorphism to the trie
    ///
    /// A "jumping" catamorphism is a form of catamorphism where the `alg_f` "jumps over" (isn't called for)
    /// path bytes in the trie where there isn't either a `value` or a branch where `children.len() > 1`.
    ///
    /// ## Arguments to `alg_f`:
    /// `(child_mask: &`[`ByteMask`]`, children: &mut [W], jumped_byte_cnt: usize, value: Option<&V>, path: &[u8]`
    ///
    /// - `jumped_byte_cnt`: The number of bytes before the `alg_f` will be called again.  The "jumped" substring
    /// is equal to `path[path.len()-jumped_byte_cnt..]`
    ///
    /// See [into_cata_side_effect](Catamorphism::into_cata_side_effect) for explanation of other arguments and
    /// behavior
    fn into_cata_jumping_side_effect<W, AlgF>(self, mut alg_f: AlgF) -> W
        where
        AlgF: FnMut(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> W,
        Self: Sized
    {
        self.into_cata_jumping_side_effect_fallible(|mask, children, jumped_cnt, val, path| -> Result<W, Infallible> {
            Ok(alg_f(mask, children, jumped_cnt, val, path))
        }).unwrap()
    }

    /// Allows the closure to return an error, stopping traversal immediately
    ///
    /// See [Catamorphism::into_cata_jumping_side_effect]
    fn into_cata_jumping_side_effect_fallible<W, Err, AlgF>(self, alg_f: AlgF) -> Result<W, Err>
        where AlgF: FnMut(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> Result<W, Err>;

    /// Applies a catamorphism to the trie descending from the zipper's root, running the `alg_f` at every
    /// step (at every byte)
    ///
    /// The arguments are the same as `into_cata_side_effect`, and this function will re-use
    /// previous calculations, if the mapping for the node was previously computed.
    /// This happens when the nodes are shared in different parts of the trie.
    ///
    /// XXX(igor): the last argument to AlgF (path) makes caching invalid
    /// since the user can calculate values of W depending on path.
    ///
    /// We're leaving this for testing purposes, but we should not expose this outside.
    fn into_cata_cached<W, AlgF>(self, alg_f: AlgF) -> W
        where
            W: Clone,
            AlgF: Fn(&ByteMask, &mut [W], Option<&V>, &[u8]) -> W,
        Self: Sized
    {
        self.into_cata_cached_fallible(|mask, children, val, path| -> Result<W, Infallible> {
            Ok(alg_f(mask, children, val, path))
        }).unwrap()
    }

    /// Allows the closure to return an error, stopping traversal immediately
    ///
    /// See [Catamorphism::into_cata_cached]
    fn into_cata_cached_fallible<W, E, AlgF>(self, alg_f: AlgF) -> Result<W, E>
        where
            W: Clone,
            AlgF: Fn(&ByteMask, &mut [W], Option<&V>, &[u8]) -> Result<W, E>;

    /// Applies a "jumping" catamorphism to the trie
    ///
    /// A "jumping" catamorphism is a form of catamorphism where the `alg_f` "jumps over" (isn't called for)
    /// path bytes in the trie where there isn't either a `value` or a branch where `children.len() > 1`.
    ///
    /// The arguments are the same as `into_cata_jumping_side_effect`, and this function will re-use
    /// previous calculations, if the mapping for the node was previously computed.
    /// This happens when the nodes are shared in different parts of the trie.
    ///
    /// XXX(igor): the last argument to AlgF (path) makes caching invalid
    /// since the user can calculate values of W depending on path.
    ///
    /// We're leaving this for testing purposes, but we should not expose this outside.
    fn into_cata_jumping_cached<W, AlgF>(self, alg_f: AlgF) -> W
        where
            W: Clone,
            AlgF: Fn(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> W,
        Self: Sized
    {
        self.into_cata_jumping_cached_fallible(|mask, children, jumped_cnt, val, path| -> Result<W, Infallible> {
            Ok(alg_f(mask, children, jumped_cnt, val, path))
        }).unwrap()
    }

    /// Allows the closure to return an error, stopping traversal immediately
    ///
    /// See [Catamorphism::into_cata_jumping_cached]
    fn into_cata_jumping_cached_fallible<W, E, AlgF>(self, alg_f: AlgF) -> Result<W, E>
        where
            W: Clone,
            AlgF: Fn(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> Result<W, E>;
}

/// A compatibility shim to provide a 3-function catamorphism API
///
/// ## Args
/// - `map_f`: `mapper(v: &V, path: &[u8]) -> W`
/// Maps value `v` at a leaf `path` into an intermediate result
///
/// - `collapse_f`: `collapse(v: &V, w: W, path: &[u8]) -> W`
/// Folds value `v` at a non-leaf `path` with the aggregated results from the trie below `path`
///
/// - `alg_f`: `alg(mask: ByteMask, children: &mut [W], path: &[u8]) -> W`
/// Aggregates the results from the child branches, `children`, descending from `path` into a single result
pub struct SplitCata;

impl SplitCata {
    pub fn new<'a, V, W, MapF, CollapseF, AlgF>(mut map_f: MapF, mut collapse_f: CollapseF, alg_f: AlgF) -> impl FnMut(&ByteMask, &mut [W], Option<&V>, &[u8]) -> W + 'a
        where
        MapF: FnMut(&V, &[u8]) -> W + 'a,
        CollapseF: FnMut(&V, W, &[u8]) -> W + 'a,
        AlgF: Fn(&ByteMask, &mut [W], &[u8]) -> W + 'a,
    {
        move |mask, children, val, path| -> W {
            // println!("STEPPING path=\"{path:?}\", mask={mask:?}, children_cnt={}, val={}", children.len(), val.is_some());
            if children.len() == 0 {
                return match val {
                    Some(val) => map_f(val, path),
                    None => {
                        // This degenerate case can only occur at the root
                        debug_assert_eq!(path.len(), 0);
                        alg_f(mask, children, path)
                    }
                }
            }
            let w = alg_f(mask, children, path);
            match val {
                Some(val) => collapse_f(val, w, path),
                None => w
            }
        }
    }
}

/// A compatibility shim to provide a 4-function "jumping" catamorphism API
///
/// - `jump_f`: `FnMut(sub_path: &[u8], w: W, path: &[u8]) -> W`
/// Elevates a result `w` descending from the relative path, `sub_path` to the current position at `path`
///
/// See [`SplitCata`] for a description of additional args
pub struct SplitCataJumping;

impl SplitCataJumping {
    pub fn new<'a, V, W, MapF, CollapseF, AlgF, JumpF>(mut map_f: MapF, mut collapse_f: CollapseF, mut alg_f: AlgF, mut jump_f: JumpF) -> impl FnMut(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> W + 'a
        where
        //TODO GOAT!!: It would be nice to get rid of this Default bound on all morphism Ws.  In this case, the plan
        // for doing that would be to create a new type called a TakableSlice.  It would be able to deref
        // into a regular mutable slice of `T` so it would work just like an ordinary slice.  Additionally
        // there would be special `take(idx: usize)` methods. it would have an additional bitmask to keep
        // track of which elements have already been taken.  So each element would be backed by a MaybeUninit,
        // and taking an element twice would be a panic.  There would be an additional `try_take` method to
        // avoid the panic.
        //Additionally, if `T: Default`, the `take` method would become the ordinary mem::take, and would always
        // succeed, therefore the abstraction would have minimal cost
        //Creating a new TakableSlice would be very cheap as it could be transmuted from an existing slice of T.
        // The tricky part is making sure Drop does the right thing, dropping the elements that were taken, and
        // not double-dropping the ones that weren't.  For this reason, I think the right solution would be to
        // require a `TakableSlice` be borrowed from a `TakableVec`, and then making sure the `TakableVec`
        // methods like `clear` do the right thing.
        //When all this work is done, this object probably deserves a stand-alone crate.
        W: Default,
        MapF: FnMut(&V, &[u8]) -> W + 'a,
        CollapseF: FnMut(&V, W, &[u8]) -> W + 'a,
        AlgF: FnMut(&ByteMask, &mut [W], &[u8]) -> W + 'a,
        JumpF: FnMut(&[u8], W, &[u8]) -> W + 'a,
    {
        move |mask, children, jump_len, val, path| -> W {
            // println!("JUMPING  path=\"{path:?}\", mask={mask:?}, jump_len={jump_len}, children_cnt={}, val={}", children.len(), val.is_some());
            let w = if children.len() == 0 {
                match val {
                    Some(val) => map_f(val, path),
                    None => {
                        // This degenerate case can only occur at the root
                        debug_assert_eq!(path.len(), 0);
                        alg_f(mask, children, path)
                    }
                }
            } else {
                let w = if children.len() > 1 {
                    alg_f(mask, children, path)
                } else {
                    core::mem::take(&mut children[0])
                };
                match val {
                    Some(val) => collapse_f(val, w, path),
                    None => w
                }
            };
            debug_assert!(jump_len <= path.len());
            let jump_dst_path = &path[..(path.len() - jump_len)];
            let stem = &path[(path.len() - jump_len)..];
            let w = if jump_len > 0 && jump_dst_path.len() > 0 || jump_len > 1 {
                jump_f(stem, w, jump_dst_path)
            } else {
                w
            };
            //If we jumped all the way to the root, run the alg one last time on the root to match the old behavior
            if jump_dst_path.len() == 0 && stem.len() > 0 {
                let mut temp_mask = ByteMask::EMPTY;
                temp_mask.set_bit(stem[0]);
                let mut temp_children = [w];
                alg_f(&temp_mask, &mut temp_children[..], &[])
            } else {
                w
            }
        }
    }
}

impl<'a, Z, V: 'a> Catamorphism<V> for Z where Z: Zipper + ZipperReadOnly<'a, V> + ZipperAbsolutePath {
    fn into_cata_side_effect_fallible<W, Err, AlgF>(self, mut alg_f: AlgF) -> Result<W, Err>
        where AlgF: FnMut(&ByteMask, &mut [W], Option<&V>, &[u8]) -> Result<W, Err>,
    {
        cata_side_effect_body::<Self, V, W, Err, _, false>(self, |mask, children, jump_len, val, path| {
            debug_assert!(jump_len == 0);
            alg_f(mask, children, val, path)
        })
    }
    fn into_cata_jumping_side_effect_fallible<W, Err, AlgF>(self, alg_f: AlgF) -> Result<W, Err>
        where AlgF: FnMut(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> Result<W, Err>
    {
        cata_side_effect_body::<Self, V, W, Err, AlgF, true>(self, alg_f)
    }
    fn into_cata_cached_fallible<W, E, AlgF>(self, alg_f: AlgF) -> Result<W, E>
        where
            W: Clone,
            AlgF: Fn(&ByteMask, &mut [W], Option<&V>, &[u8]) -> Result<W, E>
    {
        into_cata_cached_body::<Self, V, W, E, _, DoCache, false>(self, |mask, children, jump_len, val, path| {
            debug_assert!(jump_len == 0);
            alg_f(mask, children, val, path)
        })
    }
    fn into_cata_jumping_cached_fallible<W, E, AlgF>(self, alg_f: AlgF) -> Result<W, E>
        where
            W: Clone,
            AlgF: Fn(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> Result<W, E>
    {
        into_cata_cached_body::<Self, V, W, E, _, DoCache, true>(self, alg_f)
    }
}

impl<V: 'static + Clone + Send + Sync + Unpin> Catamorphism<V> for BytesTrieMap<V> {
    fn into_cata_side_effect_fallible<W, Err, AlgF>(self, mut alg_f: AlgF) -> Result<W, Err>
        where AlgF: FnMut(&ByteMask, &mut [W], Option<&V>, &[u8]) -> Result<W, Err>
    {
        let rz = self.into_read_zipper(&[]);
        cata_side_effect_body::<ReadZipperOwned<V>, V, W, Err, _, false>(rz, |mask, children, jump_len, val, path| {
            debug_assert!(jump_len == 0);
            alg_f(mask, children, val, path)
        })
    }
    fn into_cata_jumping_side_effect_fallible<W, Err, AlgF>(self, alg_f: AlgF) -> Result<W, Err>
        where AlgF: FnMut(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> Result<W, Err>
    {
        let rz = self.into_read_zipper(&[]);
        cata_side_effect_body::<ReadZipperOwned<V>, V, W, Err, AlgF, true>(rz, alg_f)
    }
    fn into_cata_cached_fallible<W, E, AlgF>(self, alg_f: AlgF) -> Result<W, E>
        where
            W: Clone,
            AlgF: Fn(&ByteMask, &mut [W], Option<&V>, &[u8]) -> Result<W, E>
    {
        let rz = self.into_read_zipper(&[]);
        into_cata_cached_body::<ReadZipperOwned<V>, V, W, E, _, DoCache, false>(rz,
            |mask, children, jump_len, val, path| {
                debug_assert!(jump_len == 0);
                alg_f(mask, children, val, path)
            }
        )
    }
    fn into_cata_jumping_cached_fallible<W, E, AlgF>(self, alg_f: AlgF) -> Result<W, E>
        where
            W: Clone,
            AlgF: Fn(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> Result<W, E>
    {
        let rz = self.into_read_zipper(&[]);
        into_cata_cached_body::<ReadZipperOwned<V>, V, W, E, _, DoCache, true>(rz, alg_f)
    }
}

#[inline]
fn cata_side_effect_body<'a, Z, V: 'a, W, Err, AlgF, const JUMPING: bool>(mut z: Z, mut alg_f: AlgF) -> Result<W, Err>
    where
    Z: Zipper + ZipperReadOnly<'a, V> + ZipperAbsolutePath,
    AlgF: FnMut(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> Result<W, Err>
{
    //`stack` holds a "frame" at each forking point above the zipper position.  No frames exist for values
    let mut stack = Vec::<StackFrame>::with_capacity(12);
    let mut children = Vec::<W>::new();
    let mut frame_idx = 0;

    z.reset();
    z.prepare_buffers();
    //Push a stack frame for the root, and start on the first branch off the root
    stack.push(StackFrame::from(&z));
    if !z.descend_first_byte() {
        //Empty trie is a special case
        return alg_f(&ByteMask::EMPTY, &mut [], 0, z.value(), z.origin_path().unwrap())
    }

    loop {
        //Descend to the next forking point, or leaf
        let mut is_leaf = false;
        while z.child_count() < 2 {
            if !z.descend_until() {
                is_leaf = true;
                break;
            }
        }

        if is_leaf {
            //Ascend back to the last fork point from this leaf
            let cur_w = ascend_to_fork::<Z, V, W, Err, AlgF, JUMPING>(&mut z, &mut alg_f, &mut [])?;
            children.push(cur_w);
            stack[frame_idx].child_idx += 1;

            //Keep ascending until we get to a branch that we haven't fully explored
            debug_assert!(stack[frame_idx].child_idx <= stack[frame_idx].child_cnt);
            while stack[frame_idx].child_idx == stack[frame_idx].child_cnt {

                if frame_idx == 0 {
                    //See if we need to run the aggregate function on the root before returning
                    let stack_frame = &mut stack[0];
                    let val = z.value();
                    let child_mask = ByteMask::from(z.child_mask());
                    debug_assert_eq!(stack_frame.child_idx, stack_frame.child_cnt);
                    debug_assert_eq!(stack_frame.child_cnt as usize, children.len());
                    let w = if stack_frame.child_cnt != 1 || val.is_some() || !JUMPING {
                        alg_f(&child_mask, &mut children, 0, val, z.origin_path().unwrap())?
                    } else {
                        children.pop().unwrap()
                    };
                    return Ok(w)
                } else {
                    // Ascend the rest of the way back up to the branch
                    debug_assert_eq!(stack[frame_idx].child_idx, stack[frame_idx].child_cnt);
                    let child_start = children.len() - stack[frame_idx].child_cnt as usize;
                    let children2 = &mut children[child_start..];
                    let cur_w = ascend_to_fork::<Z, V, W, Err, AlgF, JUMPING>(&mut z, &mut alg_f, children2)?;
                    children.truncate(child_start);
                    frame_idx -= 1;

                    //Merge the result into the stack frame
                    children.push(cur_w);
                    stack[frame_idx].child_idx += 1;
                }
            }

            //Position to descend the next child branch
            let descended = z.descend_indexed_branch(stack[frame_idx].child_idx as usize);
            debug_assert!(descended);
        } else {
            //Push a new stack frame for this branch
            Stack::push_state_raw(&mut stack, &mut frame_idx, &z);

            //Descend the first child branch
            z.descend_first_byte();
        }
    }
}

#[inline(always)]
fn ascend_to_fork<'a, Z, V: 'a, W, Err, AlgF, const JUMPING: bool>(z: &mut Z, 
        alg_f: &mut AlgF, children: &mut [W]
) -> Result<W, Err>
    where
    Z: Zipper + ZipperReadOnly<'a, V> + ZipperAbsolutePath,
    AlgF: FnMut(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> Result<W, Err>
{
    let mut w;
    let mut child_mask = ByteMask::from(z.child_mask());
    let mut children = &mut children[..];
    if JUMPING {
        //This loop runs until we got to a fork or the root.  We will take a spin through the loop
        // for each value we encounter along the way while ascending
        loop {
            let old_path_len = z.origin_path().unwrap().len();
            let old_val = z.get_value();
            let ascended = z.ascend_until();
            debug_assert!(ascended);

            let origin_path = unsafe{ z.origin_path_assert_len(old_path_len) };
            let jump_len = if z.child_count() != 1 || z.is_value() {
                old_path_len - (z.origin_path().unwrap().len()+1)
            } else {
                old_path_len - z.origin_path().unwrap().len()
            };

            w = alg_f(&child_mask, children, jump_len, old_val, origin_path)?;

            if z.child_count() != 1 || z.at_root() {
                return Ok(w)
            }

            children = core::array::from_mut(&mut w);

            // SAFETY: We will never over-read the path buffer because we only get here after we ascended
            let byte = *unsafe{ z.origin_path_assert_len(old_path_len-jump_len) }.last().unwrap();
            child_mask = ByteMask::EMPTY;
            child_mask.set_bit(byte);
        }
    } else {
        //This loop runs at each byte step as we ascend
        loop {
            let origin_path = z.origin_path().unwrap();
            let byte = origin_path.last().copied().unwrap_or(0);
            let val = z.value();
            w = alg_f(&child_mask, children, 0, val, origin_path)?;

            let ascended = z.ascend_byte();
            debug_assert!(ascended);

            if z.child_count() != 1 || z.at_root() {
                return Ok(w)
            }

            children = core::array::from_mut(&mut w);
            child_mask = ByteMask::EMPTY;
            child_mask.set_bit(byte);
        }
    }
}

pub type FocusAddr = usize;

/// Get the address of zipper's focus node, if it points at the root of the node.
/// When zipper is focused inside of the node, return `None`.
#[inline]
pub fn shared_addr<'a, V, Z>(zipper: &Z) -> Option<FocusAddr>
    where V: 'a, Z: Zipper + zipper_priv::ZipperReadOnlyPriv<'a, V>,
{
    let (node, key, value) = zipper.borrow_raw_parts();
    if !zipper.is_shared() || !key.is_empty() || value.is_some() {
        // TODO(igorm): Currently values associated with a nodes that can be shared
        // are stored outside of the node. This means one focus address can
        // correspond to two different points which have different values.
        // Therefore, we can't cache nodes that have values themselves.
        // Relevant discussion:
        // https://github.com/Adam-Vandervorst/PathMap/pull/8#discussion_r2005555762
        // https://github.com/Adam-Vandervorst/PathMap/blob/cleanup_to_release/pathmap-book/src/A.0001_map_root_values.md
        // https://discord.com/channels/@me/1215835387432271922/1352463443541754068
        return None
    }
    let addr = (node as *const dyn crate::trie_node::TrieNode<V>).addr();
    Some(addr)
    // FocusAddr(addr, key.into())
}

/// Internal structure to hold temporary info used inside morphism apply methods
struct StackFrame {
    child_idx: u16,
    child_cnt: u16,
    child_addr: Option<usize>,
}

impl StackFrame {
    /// Allocates a new StackFrame
    fn from<'a, V, Z>(zipper: &Z) -> Self
        where V: 'a, Z: Zipper + zipper_priv::ZipperReadOnlyPriv<'a, V>,
    {
        let mut stack_frame = StackFrame {
            child_cnt: 0,
            child_idx: 0,
            child_addr: None,
        };
        stack_frame.reset(zipper);
        stack_frame
    }

    /// Resets a StackFrame to the state needed to iterate a new forking point
    fn reset<'a, V, Z>(&mut self, zipper: &Z)
        where V: 'a, Z: Zipper + zipper_priv::ZipperReadOnlyPriv<'a, V>,
    {
        self.child_cnt = zipper.child_count() as u16;
        self.child_idx = 0;
    }

    // fn push_val(&mut self, w: W) {
    //     debug_assert!(self.child_idx < self.child_cnt,
    //         "we're trying to push a value for a non-existent child");
    //     self.children.push(w);
    //     self.child_idx += 1;
    // }
    //GOAT, unused for the time being.
    // fn push_none(&mut self) {
    //     self.child_idx += 1;
    //     debug_assert!(self.remaining_children_mask > 0); //If this assert trips, then it means we're trying to push a value for a non-existent child
    //     let index = self.remaining_children_mask.trailing_zeros();
    //     self.remaining_children_mask ^= 1u64 << index;
    //     self.child_mask.0[self.mask_word_idx] ^= 1u64 << index;
    //     self.advance_word_idx();
    // }
}

struct Stack {
    stack: Vec<StackFrame>,
    position: usize,
}

impl Stack {
    pub fn new() -> Self {
        Self {
            stack: Vec::with_capacity(12),
            position: !0,
        }
    }
    /// Return the reference to the top stack frame
    #[inline]
    pub fn last_mut(&mut self) -> Option<&mut StackFrame> {
        let idx = self.position;
        self.stack.get_mut(idx)
    }

    /// Return the reference to the top stack frame
    /// and decrease stack pointer. Doesn't free the stack frame.
    #[inline]
    pub fn pop_mut(&mut self) -> Option<&mut StackFrame> {
        if self.position == !0 {
            return None;
        }
        let idx = self.position;
        self.position = self.position.wrapping_sub(1);
        self.stack.get_mut(idx)
    }

    /// Push stack state for current zipper position
    ///
    /// This function re-uses allocations for stack frames,
    /// to avoid allocator thrashing.
    pub fn push_state<'a, V: 'a, Z>(&mut self, z: &Z)
        where Z: Zipper + zipper_priv::ZipperReadOnlyPriv<'a, V>,
    {
        Self::push_state_raw(&mut self.stack, &mut self.position, z);
    }

    pub fn push_state_raw<'a, V: 'a, Z>(
        stack: &mut Vec<StackFrame>,
        position: &mut usize,
        zipper: &Z)
        where Z: Zipper + zipper_priv::ZipperReadOnlyPriv<'a, V>,
    {
        *position = position.wrapping_add(1);
        assert!(*position <= stack.len(),
            "stack invariant: position <= len");
        if *position == stack.len() {
            stack.push(StackFrame::from(zipper));
        } else {
            stack[*position].reset(zipper);
        }
    }
}

pub(crate) fn new_map_from_ana_jumping<'a, V, WZ, W, CoAlgF, I>(wz: &mut WZ, w: W, mut coalg_f: CoAlgF)
where
    V: 'static + Clone + Send + Sync + Unpin,
    W: Default,
    I: IntoIterator<Item=W>,
    WZ: ZipperWriting<V> + zipper::ZipperMoving,
    CoAlgF: Copy + FnMut(W, &[u8]) -> (&'a [u8], ByteMask, I, Option<V>),
{
    let (prefix, bm, ws, mv) = coalg_f(w, wz.path());
    let prefix_len = prefix.len();

    wz.descend_to(&prefix[..]);
    if let Some(v) = mv { wz.set_value(v); }
    for (b, w) in bm.iter().zip(ws) {
        wz.descend_to_byte(b);
        new_map_from_ana_jumping(wz, w, coalg_f);
        wz.ascend_byte();
    }
    wz.ascend(prefix_len);
}

/// A trait to dictate if and how the value should be cached.
///
/// The reason this trait exists is to allow a single function to work with and
/// without caching, and avoid polluting every public interface with `W: Clone`.
///
/// This is not intended to be a public interface.
trait CacheStrategy<W> {
    /// Enable/disable the caching
    const CACHING: bool;

    /// Implement `Clone`, so that we can put/get values from cache
    fn clone(_x: &W) -> W;

    /// Insert a value to cache
    #[inline(always)]
    fn insert(cache: &mut HashMap<FocusAddr, W>, addr: Option<FocusAddr>, cur_w: &W) {
        // Do nothing if caching is disabled
        if !Self::CACHING {
            return;
        }
        if let Some(addr) = addr {
            cache.insert(addr, Self::clone(cur_w));
        }
    }

    /// Get a value from cache
    #[inline(always)]
    fn get(cache: &HashMap<FocusAddr, W>, addr: Option<FocusAddr>) -> Option<W> {
        // Do nothing if caching is disabled
        if !Self::CACHING {
            return None;
        }
        addr.and_then(|addr| cache.get(&addr).map(Self::clone))
    }
}

/// Cache is disabled
#[allow(dead_code)] // this is unused for now, but can be used in side_effecting
struct NoCache;

impl<W> CacheStrategy<W> for NoCache {
    const CACHING: bool = false;
    fn clone(_w: &W) -> W {
        unreachable!("`NoCache::clone` must not be called, since `CACHING` is disabled")
    }
}

/// Cache is enabled for `W: Clone`
struct DoCache;

impl<W: Clone> CacheStrategy<W> for DoCache {
    const CACHING: bool = true;
    fn clone(w: &W) -> W { w.clone() }
}

fn into_cata_cached_body<'a, Z, V: 'a, W, E, AlgF, Cache, const JUMPING: bool>(
    mut zipper: Z, mut alg_f: AlgF
) -> Result<W, E>
    where
    Cache: CacheStrategy<W>,
    Z: Zipper+ ZipperReadOnly<'a, V> + ZipperAbsolutePath,
    AlgF: FnMut(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> Result<W, E>
{
    use gxhash::HashMapExt;

    zipper.reset();
    zipper.prepare_buffers();

    let mut stack = Stack::new();
    let mut children = Vec::<W>::new();
    let mut cache = HashMap::<FocusAddr, W>::new();
    stack.push_state(&zipper);
    'outer: loop {
        let frame_mut = stack.last_mut()
            .expect("into_cata stack is emptied before we returned to root");
        // This branch represents the body of the for loop.
        if frame_mut.child_idx < frame_mut.child_cnt {
            zipper.descend_indexed_branch(frame_mut.child_idx as usize);
            frame_mut.child_idx += 1;
            frame_mut.child_addr = shared_addr(&zipper);

            // Read and reuse value from cache, if exists
            if let Some(cache) = Cache::get(&cache, frame_mut.child_addr) {
                // DO NOT modify the W from cache
                children.push(cache);
                zipper.ascend_byte();
                continue 'outer;
            }

            // Descend until leaf or branch
            let mut is_leaf = false;
            'descend: while zipper.child_count() < 2 {
                if !zipper.descend_until() {
                    is_leaf = true;
                    break 'descend;
                }
            }

            if is_leaf {
                // If we encounter a leaf, ascend immediately.
                // This branch will preserve the current stack frame.
                let cur_w = ascend_to_fork::<Z, V, W, E, AlgF, JUMPING>(
                    &mut zipper, &mut alg_f, &mut [])?;
                // Put value to cache (1)
                Cache::insert(&mut cache, frame_mut.child_addr, &cur_w);
                children.push(cur_w);
                continue 'outer;
            }

            // Enter one recursion step
            stack.push_state(&zipper);
            continue 'outer;
        }

        // This branch represents the rest of the function after the loop
        let frame_idx = stack.position;
        let StackFrame { child_cnt, .. } = stack.pop_mut()
            .expect("we just checked that stack is not empty, pop must return Some");
        let child_start = children.len() - *child_cnt as usize;
        let children2 = &mut children[child_start..];

        if frame_idx == 0 {
            // Final branch
            debug_assert!(zipper.at_root(), "must be at root when cata is done");
            let value = zipper.value();
            let child_mask = ByteMask::from(zipper.child_mask());
            return if JUMPING && *child_cnt == 1 && value.is_none() {
                Ok(children.pop().unwrap())
            } else {
                alg_f(&child_mask, children2, 0, value, zipper.path())
            };
        }

        let cur_w = ascend_to_fork::<Z, V, W, E, AlgF, JUMPING>(
            &mut zipper, &mut alg_f, children2)?;
        children.truncate(child_start);

        // Exit one recursion step
        let frame_mut = stack.last_mut()
            .expect("when we're not at root, expect parent stack");
        // Put value to cache (2) after recursion
        Cache::insert(&mut cache, frame_mut.child_addr, &cur_w);
        children.push(cur_w);
    }
}

// This is a naive implementation of caching/jumping cata
// The code is left in for reference/readability, since the unrolled version
// is very hard to read. It took several days to debug the unrolled version.
#[cfg(any())] // this is equivalent to "always disabled"
fn into_cata_jumping_naive<'a, Z, V: 'a, W, E, AlgF, Cache, const JUMPING: bool>(
    z: &mut Z, alg_f: &mut AlgF
) -> Result<W, E>
    where
    Cache: CacheStrategy<W>, Z: Zipper<V> + ZipperReadOnly<'a, V> + ZipperAbsolutePath,
    AlgF: FnMut (&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> Result<W, E>
{
    let child_mask = ByteMask::from(z.child_mask());
    let child_count = child_mask.count_bits();
    let mut children = Vec::<W>::with_capacity(child_count);
    let mut cache = HashMap::<FocusAddr, W>::new();
    let path = z.path().to_vec();
    for ii in 0..child_count {
        z.descend_indexed_branch(ii);
        let child_addr = shared_addr(z);
        // Read and reuse value from cache, if exists
        if let Some(cached) = Cache::get(&cache, child_addr) {
            // DO NOT modify the W from cache
            children.push(cached);
            z.ascend_byte();
        }
        let mut is_leaf = false;

        // Descend until leaf or branch
        'descend: while z.child_count() < 2 {
            if !z.descend_until() {
                is_leaf = true;
                break 'descend;
            }
        }

        let w = if is_leaf {
            // If we encounter a leaf, ascend immediately
            // This branch will preserve the current stack frame.
            ascend_to_fork::<Z, V, W, E, AlgF, JUMPING>(z, alg_f, &mut [][..])?
        } else {
            // Enter one recursion step
            into_cata_jumping_naive::<Z, V, W, E, AlgF, Cache, JUMPING>(z, alg_f)?
        };
        assert!(path == z.path(), "we didn't return to the original path");
        // Put value to cache (1), (2)
        Cache::insert(&mut cache, child_addr, &w);
        children.push(w);
    }

    if z.at_root() {
        // Final branch
        let value = z.value();
        if JUMPING && children.len() == 1 && value.is_none() {
            Ok(children.pop().unwrap())
        } else {
            alg_f(&child_mask, &mut children, 0, value, z.path())
        }
    } else {
        // Exit one recursion step
        ascend_to_fork::<Z, V, W, E, AlgF, JUMPING>(z, alg_f, &mut children)
    }
}

/// Internal function to generate a new root trie node from an anamorphism
pub(crate) fn new_map_from_ana<V, W, AlgF>(w: W, mut alg_f: AlgF) -> BytesTrieMap<V>
    where
    V: 'static + Clone + Send + Sync + Unpin,
    W: Default,
    AlgF: FnMut(W, &mut Option<V>, &mut TrieBuilder<V, W>, &[u8])
{
    let mut stack = Vec::<(TrieBuilder<V, W>, usize)>::with_capacity(12);
    let mut frame_idx = 0;

    let mut new_map = BytesTrieMap::new();
    let mut z = new_map.write_zipper();
    let mut val = None;

    //The root is a special case
    stack.push((TrieBuilder::<V, W>::new(), 0));
    alg_f(w, &mut val, &mut stack[frame_idx].0, z.path());
    stack[frame_idx].0.finalize();
    if let Some(val) = core::mem::take(&mut val) {
        z.set_value(val);
    }
    loop {
        //Should we descend?
        if let Some(w_or_node) = stack[frame_idx].0.take_next() {
            //TODO Optimization Opportunity: There is likely a 2x speedup in here, that can be achieved by
            // setting all the children at the same time.  The reason is that the current behavior will create
            // a smaller node (ListNode), and then upgrade it if necessary.  But if we know in advance what
            // the node needs to hold, we could allocate the correct node right off the bat.
            //
            // I'm going to hold off on implementing this until the explicit path API is fully settled,
            // since ideally we'd call a WriteZipper method to set multiple downstream paths, but we'd want
            // some assurances those paths would actually be created, and not pruned because they're empty.
            //
            //I'm thinking this needs to take the form of a TrieNode trait method that looks something like:
            // `fn set_children_and_values(child_mask, val_mask, branches: &[??], vals: &[V])` or possibly
            // a node creation method.  Since this is designed to be used by anamorphism (trie construction)
            // perhaps we don't actually need the downstream nodes at all, and can fill them in later.
            //
            //BEWARE: This change needs to be accompanied by another change to allow an existing node's path
            // to be augmented, or the above change could be a performance step backwards.  Specifically,
            // consider a ListNode that is created with only one child, based on a mask.  Then, if the zipper
            // descends and tries to create the rest of a path, it would be a disaster if that took the form
            // of another node, as opposed to just putting the rest of the path into the existing node.

            let child_path_byte = stack[frame_idx].0.taken_child_byte();
            z.descend_to_byte(child_path_byte);
            let mut child_path_len = 1;

            if let Some(child_path_remains) = stack[frame_idx].0.taken_child_remaining_path(child_path_byte) {
                z.descend_to(child_path_remains);
                child_path_len += child_path_remains.len();
            }

            match w_or_node {
                // Recursive path with more Ws
                WOrNode::W(w) => {
                    debug_assert!(frame_idx < stack.len());
                    frame_idx += 1;
                    if frame_idx == stack.len() {
                        stack.push((TrieBuilder::<V, W>::new(), child_path_len));
                    } else {
                        stack[frame_idx].0.reset();
                        stack[frame_idx].1 = child_path_len;
                    }

                    //Run the alg if we just descended
                    alg_f(w, &mut val, &mut stack[frame_idx].0, z.path());
                    stack[frame_idx].0.finalize();
                    if let Some(val) = core::mem::take(&mut val) {
                        z.set_value(val);
                    }
                },
                // Path from a graft, we shouldn't descend
                WOrNode::Node(node) => {
                    z.core().graft_internal(Some(node));
                    z.ascend(child_path_len);
                }
            }
        } else {
            //If not, we should ascend
            if frame_idx == 0 {
                break
            }
            z.ascend(stack[frame_idx].1);
            stack[frame_idx].0.reset();
            frame_idx -= 1;
        }
    }
    drop(z);
    new_map
}

/// A [Vec]-like struct for assembling all the downstream branches from a path in the trie
//GOAT, Ideally I would skip the `val` argument to the anamorphism closure, and add a `set_val` method
// to TrieBuilder.  I'm a little on the fence about it, however, because it increases the size of the
// TrieBuilder by an `Option<V>`, which is stored for every stack frame, as opposed to just the one place
// it's needed.  However, this change opens up the possibility to embed the WriteZipper into the TrieBuilder,
// which can make some operations a bit more efficient.
//
//GOAT, If we exposed an interface that allowed values to be set in bulk, (e.g. with a mask), we could
// plumb it straight through to a node interface
pub struct TrieBuilder<V, W> {
    child_mask: [u64; 4],
    cur_mask_word: usize,
    child_paths: ReusingQueue<Vec<u8>>,
    child_structs: ReusingQueue<WOrNode<V, W>>,
}

/// Internal structure 
enum WOrNode<V, W> {
    W(W),
    Node(TrieNodeODRc<V>)
}

impl<V, W: Default> Default for WOrNode<V, W> {
    fn default() -> Self {
        //GOAT, the default impl here is mainly to facilitate core::mem::take, therefore, the default
        // should be the cheapest thing to create.  At some point that will be a TrieNodeODRc pointing
        // at a static empty node, but that's currently not implemented yet.
        // Alternatively we could use a MaybeUninit.
        Self::W(W::default())
    }
}

impl<V: Clone + Send + Sync, W: Default> TrieBuilder<V, W> {
    /// Internal method to make a new empty `TrieBuilder`
    fn new() -> Self {
        Self {
            child_mask: [0u64; 4],
            cur_mask_word: 0,
            child_paths: ReusingQueue::new(),
            child_structs: ReusingQueue::new() }
    }
    /// Internal method.  Clears a builder without freeing its memory
    fn reset(&mut self) {
        self.child_mask = [0u64; 4];
        self.cur_mask_word = 0;
        self.child_structs.clear();
        self.child_paths.clear();
    }
    /// Internal method.  Called after the user code has run to fill the builder, but before we start to empty it
    fn finalize(&mut self) {
        self.cur_mask_word = 0;
        while self.cur_mask_word < 4 && self.child_mask[self.cur_mask_word] == 0 {
            self.cur_mask_word += 1;
        }
    }
    /// Internal method to get the next child from the builder in the push order.  Used by the anamorphism
    fn take_next(&mut self) -> Option<WOrNode<V, W>> {
        self.child_structs.pop_front().map(|element| core::mem::take(element))
    }
    /// Internal method.  After [Self::take_next] returns `Some`, this method will return the first byte of the
    /// associated path.
    fn taken_child_byte(&mut self) -> u8 {
        let least_component = self.child_mask[self.cur_mask_word].trailing_zeros() as u8;
        debug_assert!(least_component < 64);
        let byte = (self.cur_mask_word * 64) as u8 + least_component;
        self.child_mask[self.cur_mask_word] ^= 1u64 << least_component;
        while self.cur_mask_word < 4 && self.child_mask[self.cur_mask_word] == 0 {
            self.cur_mask_word += 1;
        }
        byte
    }
    /// Internal method.  After [Self::take_next] returns `Some`, this method will return the associated path
    /// beyond the first byte, or `None` if the path is only 1-byte long
    fn taken_child_remaining_path(&mut self, byte: u8) -> Option<&[u8]> {
        if self.child_paths.get(0).map(|path| path[0]) != Some(byte) {
            None
        } else {
            self.child_paths.pop_front().map(|v| &v.as_slice()[1..])
        }
    }
    /// Returns the number of children that have been pushed to the `TrieBuilder`, so far
    pub fn len(&self) -> usize {
        self.child_structs.len()
    }
    /// Simultaneously sets all child branches with single-byte path continuations
    ///
    /// Panics if existing children have already been set / pushed, or if the number of bits set in `mask`
    /// doesn't match `children.len()`.
    pub fn set_child_mask<C: AsMut<[W]>>(&mut self, mask: [u64; 4], mut children: C) {
        if self.child_structs.len() != 0 {
            panic!("set_mask called over existing children")
        }
        let children = children.as_mut();
        debug_assert_eq!(mask.iter().fold(0, |sum, word| sum + word.count_ones() as usize), children.len());
        if children.len() == 0 {
            return
        }
        self.child_structs.clear();
        for child in children {
            self.child_structs.push_val(WOrNode::W(core::mem::take(child)));
        }
        debug_assert_eq!(self.cur_mask_word, 0);
        while mask[self.cur_mask_word] == 0 {
            self.cur_mask_word += 1;
        }
        self.child_mask = mask;
    }
    /// Pushes a new child branch into the `TrieBuilder` with the specified `byte`
    ///
    /// Panics if `byte <=` the first byte of any previosuly pushed paths.
    pub fn push_byte(&mut self, byte: u8, w: W) {
        let mask_word = (byte / 64) as usize;
        if mask_word < self.cur_mask_word {
            panic!("children must be pushed in sorted order")
        }
        self.cur_mask_word = mask_word;
        let mask_delta = 1u64 << (byte % 64);
        if self.child_mask[mask_word] >= mask_delta {
            panic!("children must be pushed in sorted order and each initial byte must be unique")
        }
        self.child_mask[mask_word] |= mask_delta;

        //Push the `W`
        self.child_structs.push_val(WOrNode::W(w));
    }
    /// Pushes a new child branch into the `TrieBuilder` with the specified `sub_path`
    ///
    /// Panics if `sub_path` fails to meet any of the following conditions:
    /// - `sub_path.len() > 0`.
    /// - `sub_path` must not begin with the same byte as any previously-pushed path.
    /// - `sub_path` must alphabetically sort after all previously pushed paths.
    ///
    /// For example, pushing `b"horse"` and then `b"hour"` is wrong.  Instead you should push `b"ho"`, and
    /// push the remaining parts of the path from the triggered closures downstream.
    //
    //TODO, could make a `push_unchecked` method to turn these these checks from `assert!` to `debug_assert`.
    // Not sure if it would make any difference.  Feels unlikely, but might be worth a try after we've implemented
    // the other speedup ideas
    pub fn push(&mut self, sub_path: &[u8], w: W) {
        assert!(sub_path.len() > 0);

        //Push the remaining path
        if sub_path.len() > 1 {
            let child_path = self.child_paths.push_mut();
            child_path.clear();
            child_path.extend(sub_path);
        }

        self.push_byte(sub_path[0], w);
    }
    /// Behaves like [push](Self::push), but will tolerate inputs in any order, and inputs and with
    /// overlapping initial bytes
    ///
    /// DISCUSSION: This method is handy when you are generating paths composed of data types that can't be
    /// cleanly separated at byte boundaries; for example UTF-8 encoded `char`s.  This method saves you the
    /// extra work of handling the case where different structures encode with the same initial byte, and of
    /// concerning yourself with partial encoding generally.
    ///
    /// This method is much higher overhead than the ordinary `push` method, and also it introduces
    /// some ambiguity in the order in which the closure is run for the children.  Specifically it means that
    /// the same path location in the trie may be visited multiple times, and you cannot rely on closure
    /// execution proceeding in a strictly depth-first order.  Furthermore, the closure order may not match
    /// the traversal order of the completed trie.
    ///
    /// NOTE: Because a given location may be visited multiple times, values set by later-running closures
    /// will overwrite a value set by an earlier closure running at the same path.
    ///
    /// NOTE: If you push twice to an identical path within the same closure execution, the second push will
    /// overwrite the first.
    ///
    /// NOTE: use of this method will preclude any automatic multi-threading of the anamorphism on downstream
    /// paths.
    pub fn tolerant_push(&mut self, sub_path: &[u8], w: W) {
        let byte = match sub_path.get(0) {
            Some(byte) => byte,
            None => return
        };

        //Find the index in the `child_structs` vec based on the initial byte
        let mask_word = (byte / 64) as usize;
        let byte_remainder = byte % 64;
        let mut byte_index = 0;
        for i in 0..mask_word {
            byte_index += self.child_mask[i].count_ones();
        }
        if byte_remainder > 0 {
            byte_index += (self.child_mask[mask_word] & 0xFFFFFFFFFFFFFFFF >> (64-byte_remainder)).count_ones();
        }

        let mask_delta = 1u64 << (byte % 64);
        let collision = self.child_mask[mask_word] & mask_delta > 0;
        self.child_mask[mask_word] |= mask_delta;

//GOAT, my thinking on the data structure changes
//For the paths, we should go back to storing the whole path, and use the first byte for association.  No need
// to keep the index association
//For the W array, we ought to just push the Ws in, in the order we want.  Since we always iterate the W vec
//If we want to support direct-push of values, we ought to have a separate value mask
//There should be two value vecs.  One for direct values of the current node, and one for values associated
// with downstream children / paths.  (we could even piggy-back the downstream value on the path)

//GOAT, THE W vec should have the string pairs hanging off each element.  So the W vec is `Vec<(W, Vec<(Vec<u8>, W)>)>`
//GOAT, Actually the W needs to be an Option<W>, and at that point, we may as well split the 

//GOAT options:
// 1. Make one vec that holds length-1 children, and another that holds lenth > 1,
//     

//GOAT!!! Vec<(Option<W>, Vec<(Vec<u8>, W)>)>
//GOAT!!! ReusingQueue<SmallVec<(Vec<u8>, W)>>

        //GOAT, we need to reset self.cur_mask_word, scanning the whole child_mask, because any child byte may have been added
        // self.cur_mask_word = mask_word;
    }
    /// Returns the child mask from the `TrieBuilder`, representing paths that have been pushed so far
    pub fn child_mask(&self) -> [u64; 4] {
        self.child_mask
    }
    /// Grafts the subtrie below the focus of the `read_zipper` at the specified `byte`
    ///
    /// WARNING: This method is incompatible with [Self::set_child_mask] and must follow the same
    /// rules as [Self::push_byte]
    pub fn graft_at_byte<Z: ZipperAccess<V>>(&mut self, byte: u8, read_zipper: &Z) {
        let mask_word = (byte / 64) as usize;
        if mask_word < self.cur_mask_word {
            panic!("children must be pushed in sorted order")
        }
        self.cur_mask_word = mask_word;
        let mask_delta = 1u64 << (byte % 64);
        if self.child_mask[mask_word] >= mask_delta {
            panic!("children must be pushed in sorted order and each initial byte must be unique")
        }
        self.child_mask[mask_word] |= mask_delta;

        //Clone the read_zipper's focus and push it
        let node = read_zipper.get_focus().into_option();
        self.child_structs.push_val(WOrNode::Node(node.unwrap())); //GOAT!! Currently we panic if the read_zipper is at an nonexistent path
    }
    //GOAT, feature removed.  See below
    // /// Returns an [`Iterator`] type to iterate over the `(sub_path, w)` pairs that have been pushed
    // pub fn iter(&self) -> TrieBuilderIter<'_, W> {
    //     self.into_iter()
    // }
}

//GOAT, the IntoIterator impl is obnoxious because I don't have a contiguous buffer that holds the path anymore
// It's unnecessary anyway, so I'm just going to chuck it
//
// impl<'a, W> IntoIterator for &'a TrieBuilder<W> {
//     type Item = (&'a[u8], &'a W);
//     type IntoIter = TrieBuilderIter<'a, W>;

//     fn into_iter(self) -> Self::IntoIter {
//         TrieBuilderIter {
//             cb: self,
//             cur_mask: self.child_mask[0],
//             mask_word: 0,
//             i: 0
//         }
//     }
// }

// /// An [`Iterator`] type for a [`TrieBuilder`]
// pub struct TrieBuilderIter<'a, W> {
//     cb: &'a TrieBuilder<W>,
//     cur_mask: u64,
//     mask_word: usize,
//     i: usize,
// }

// impl<'a, W> Iterator for TrieBuilderIter<'a, W> {
//     type Item = (&'a[u8], &'a W);
//     fn next(&mut self) -> Option<Self::Item> {
//         while self.mask_word < 4 {
//             let tz = self.cur_mask.trailing_zeros();
//             if tz < 64 {

//                 self.i += 1;
//             } else {
//                 self.mask_word += 1;
//             }
//         }
//         None
//     }
// }

#[cfg(test)]
mod tests {
    use std::ops::Range;
    use crate::trie_map::BytesTrieMap;
    use crate::utils::BitMask;
    use super::*;

    fn check_all_catas<'a, W, V, Z, AlgF, AlgFP, Assert>(
        zipper: Z, mut f_side: AlgF, f_pure: AlgFP, mut assert: Assert)
        where
            Z: Clone + Catamorphism<V>, W: Clone,
            AlgF: FnMut(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> W,
            AlgFP: Fn(&ByteMask, &mut [W], usize, Option<&V>, &[u8]) -> W,
            Assert: FnMut(W, &str),
    {
        let output = zipper.clone().into_cata_side_effect(
            |bm, ch, v, path| f_side(bm, ch, 0, v, path));
        assert(output, "into_cata_side_effect");
        let output = zipper.clone().into_cata_jumping_side_effect(
            |bm, ch, jmp, v, path| f_side(bm, ch, jmp, v, path));
        assert(output, "into_cata_jumping_side_effect");
        let output = zipper.clone().into_cata_cached(
            |bm, ch, v, path| f_pure(bm, ch, 0, v, path));
        assert(output, "into_cata_cached");
        let output = zipper.clone().into_cata_jumping_cached(
            |bm, ch, jmp, v, path| f_pure(bm, ch, jmp, v, path));
        assert(output, "into_cata_jumping_cached");
    }

    #[test]
    fn cata_test1() {
        let tests = [
            (vec![], 0), //Empty special case
            (vec!["1"], 1), //A branch at the root
            (vec!["1", "2"], 3),
            (vec!["1", "2", "3", "4", "5", "6"], 21),
            (vec!["a1", "a2"], 3), //A branch above the root
            (vec!["a1", "a2", "a3", "a4", "a5", "a6"], 21),
            (vec!["12345"], 5), //A deep leaf
            (vec!["1", "12", "123", "1234", "12345"], 15), //Values along the path
            (vec!["123", "123456", "123789"], 18), //A branch that also has a value
            (vec!["12", "123", "123456", "123789"], 20),
            (vec!["1", "2", "123", "123765", "1234", "12345", "12349"], 29) //A challenging mix of everything
        ];
        for (keys, expected_sum) in tests {
            let map: BytesTrieMap<()> = keys.into_iter().map(|v| (v, ())).collect();
            let zip = map.read_zipper();

            let alg = |_child_mask: &ByteMask, children: &mut [u32], _jump_len: usize, val: Option<&()>, path: &[u8]| {
                let this_digit = if val.is_some() {
                    (*path.last().unwrap() as char).to_digit(10).unwrap()
                } else {
                    0
                };
                let sum_of_branches = children.into_iter().fold(0, |sum, child| sum + *child);
                sum_of_branches + this_digit
            };

            //Test all combinations of (jumping,cached)
            check_all_catas(zip, alg, alg, |sum, _| assert_eq!(sum, expected_sum));
        }
    }

    #[test]
    fn cata_test2() {
        let mut btm = BytesTrieMap::new();
        let rs = ["arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

        //These algorithms should perform the same with both "jumping" and "non-jumping" versions

        // like val count, but without counting internal values
        fn leaf_cnt(children: &[usize], val: Option<&usize>) -> usize {
            if children.len() > 0 {
                children.iter().sum() //Internal node
            } else {
                assert!(val.is_some()); //Cata doesn't include dangling paths, but it might in the future
                1 //leaf node
            }
        }
        let alg = |_mask: &ByteMask, children: &mut [usize], _jmp: usize, val: Option<&usize>, _path: &[u8]| {
            leaf_cnt(children, val)
        };
        check_all_catas(btm.read_zipper(), alg, alg, |cnt, _| assert_eq!(cnt, 11));

        // Finds the longest path in the trie
        fn longest_path(children: &mut[Vec<u8>], path: &[u8]) -> Vec<u8> {
            if children.len() == 0 {
                path.to_vec()
            } else {
                children.iter_mut().max_by_key(|p| p.len()).map_or(vec![], std::mem::take)
            }
        }
        let alg = |_mask: &ByteMask, children: &mut [Vec<u8>], _jmp: usize, _val: Option<&usize>, path: &[u8]| {
            longest_path(children, path)
        };
        check_all_catas(btm.read_zipper(), alg, alg, |longest, _|
            assert_eq!(std::str::from_utf8(longest.as_slice()).unwrap(), "rubicundus"));

        // Finds all values that are positioned at branch points (where children.len() > 0)
        fn vals_at_branches(children: &mut [Vec<usize>], val: Option<&usize>) -> Vec<usize> {
            if children.len() > 0 {
                match val {
                    Some(val) => vec![*val],
                    None => {
                        let mut r = children.first_mut().map_or(vec![], std::mem::take);
                        for w in children[1..].iter_mut() { r.extend(w.drain(..)); }
                        r
                    }
                }
            } else {
                vec![]
            }
        }
        let alg = |_mask: &ByteMask, children: &mut [Vec<usize>], _jmp: usize, val: Option<&usize>, _path: &[u8]| {
            vals_at_branches(children, val)
        };
        check_all_catas(btm.read_zipper(), alg, alg, |at_truncated, _|
            assert_eq!(at_truncated, vec![3]));
    }

    #[test]
    fn cata_test3() {
        let tests = [
            (vec![], 0, 0),
            (vec!["i"], 1, 1), //1 leaf, 1 node
            (vec!["i", "ii"], 2, 1), //1 leaf, 2 total "nodes"
            (vec!["ii", "iiiii"], 5, 1), //1 leaf, 5 total "nodes"
            (vec!["ii", "iii", "iiiii", "iiiiiii"], 7, 1), //1 leaf, 7 total "nodes"
            (vec!["ii", "iiii", "iij", "iijjj"], 7, 3), //2 leaves, 1 fork, 7 total "nodes"
        ];
        for (keys, expected_sum_ordinary, expected_sum_jumping) in tests {
            let map: BytesTrieMap<()> = keys.into_iter().map(|v| (v, ())).collect();
            let zip = map.read_zipper();

            let map_f = |_v: &(), _path: &[u8]| {
                // println!("map path=\"{}\"", String::from_utf8_lossy(_path));
                1
            };
            let collapse_f = |_v: &(), upstream: u32, _path: &[u8]| {
                // println!("collapse path=\"{}\", upstream={upstream}", String::from_utf8_lossy(_path));
                upstream
            };
            let alg_f = |_child_mask: &ByteMask, children: &mut [u32], path: &[u8]| {
                // println!("aggregate path=\"{}\", children={children:?}", String::from_utf8_lossy(path));
                let sum = children.into_iter().fold(0, |sum, child| sum + *child);
                if path.len() > 0 {
                    sum + 1
                } else {
                    sum
                }
            };

            //Test both the jumping and non-jumping versions
            let sum = zip.clone().into_cata_side_effect(SplitCata::new(map_f, collapse_f, alg_f));
            assert_eq!(sum, expected_sum_ordinary);

            let sum = zip.into_cata_jumping_side_effect(SplitCataJumping::new(map_f, collapse_f, alg_f, |_subpath, w, _path| w));
            assert_eq!(sum, expected_sum_jumping);
        }
    }

    #[test]
    fn cata_test4() {
        #[derive(Debug, PartialEq)]
        enum Trie<V> {
            Value(V),
            Collapse(V, Box<Trie<V>>),
            Alg(Vec<(char, Trie<V>)>),
            Jump(String, Box<Trie<V>>)
        }
        use Trie::*;

        let mut btm = BytesTrieMap::new();
        let rs = ["arr", "arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

        let s = btm.read_zipper().into_cata_jumping_side_effect(SplitCataJumping::new(
            |v, _path| { Some(Box::new(Value(*v))) },
            |v, w, _path| { Some(Box::new(Collapse(*v, w.unwrap()))) },
            |cm, ws, _path| {
                let mut it = cm.iter();
                Some(Box::new(Alg(ws.iter_mut().map(|w| (it.next().unwrap() as char, *std::mem::take(w).unwrap())).collect())))},
            |sp, w, _path| { Some(Box::new(Jump(std::str::from_utf8(sp).unwrap().to_string(), w.unwrap()))) }
        ));

        assert_eq!(s, Some(Alg([
            ('a', Jump("rr".into(), Collapse(0, Jump("w".into(), Value(1).into()).into()).into())),
            ('b', Jump("ow".into(), Value(2).into())),
            ('c', Jump("annon".into(), Value(3).into())),
            ('r', Alg([
                ('o', Jump("m".into(), Alg([
                    ('\'', Jump("i".into(), Value(12).into())),
                    ('a', Jump("n".into(), Collapse(4, Alg([
                        ('e', Value(5)),
                        ('u', Jump("s".into(), Value(6).into()))
                    ].into()).into()).into())),
                    ('u', Jump("lus".into(), Value(7).into()))].into()).into())),
                ('u', Jump("b".into(), Alg([
                    ('e', Alg([
                        ('n', Jump("s".into(), Value(8).into())),
                        ('r', Value(9))].into())),
                    ('i', Jump("c".into(), Alg([
                        ('o', Jump("n".into(), Value(10).into())),
                        ('u', Jump("ndus".into(), Value(11).into()))].into()).into()))].into()).into()))].into()))].into()).into()));
    }

    #[test]
    fn cata_test4_single() {
        #[derive(Debug, PartialEq)]
        struct Trie<V> {
            prefix: String,
            value: Option<V>,
            children: Vec<(char, Trie<V>)>
        }

        let mut btm = BytesTrieMap::new();
        let rs = ["arr", "arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom'i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

        let s: Option<Trie<usize>> = btm.read_zipper().into_cata_jumping_side_effect(|bm, ws: &mut [Option<Trie<usize>>], jump, mv, path| {
            Some(Trie{
                prefix: String::from_utf8(path[path.len()-jump..].to_vec()).unwrap(),
                value: mv.cloned(),
                children: bm.iter().zip(ws).map(|(b, t)| (b as char, std::mem::take(t).unwrap())).collect()
            })
        });

        assert_eq!(s, Some(Trie { prefix: "".into(), value: None, children: [
            ('a', Trie { prefix: "rr".into(), value: Some(0), children: [
                ('o', Trie { prefix: "w".into(), value: Some(1), children: [].into() })].into() }),
            ('b', Trie { prefix: "ow".into(), value: Some(2), children: [].into() }),
            ('c', Trie { prefix: "annon".into(), value: Some(3), children: [].into() }),
            ('r', Trie { prefix: "".into(), value: None, children: [
                ('o', Trie { prefix: "m".into(), value: None, children: [
                    ('\'', Trie { prefix: "i".into(), value: Some(12), children: [].into() }),
                    ('a', Trie { prefix: "n".into(), value: Some(4), children: [
                        ('e', Trie { prefix: "".into(), value: Some(5), children: [].into() }),
                        ('u', Trie { prefix: "s".into(), value: Some(6), children: [].into() })].into() }),
                    ('u', Trie { prefix: "lus".into(), value: Some(7), children: [].into() })].into() }),
                ('u', Trie { prefix: "b".into(), value: None, children: [
                    ('e', Trie { prefix: "".into(), value: None, children: [
                        ('n', Trie { prefix: "s".into(), value: Some(8), children: [].into() }),
                        ('r', Trie { prefix: "".into(), value: Some(9), children: [].into() })].into() }),
                    ('i', Trie { prefix: "c".into(), value: None, children: [
                        ('o', Trie { prefix: "n".into(), value: Some(10), children: [].into() }),
                        ('u', Trie { prefix: "ndus".into(), value: Some(11), children: [].into() })].into() })].into() })].into() })].into() }));

        let keys = [vec![b'a', b'b', b'c'], vec![b'a', b'b', b'c', b'x', b'y']];
        let btm: BytesTrieMap<usize> = keys.into_iter().enumerate().map(|(i, k)| (k, i)).collect();

        let s: Option<Trie<usize>> = btm.read_zipper().into_cata_jumping_side_effect(|bm, ws: &mut [Option<Trie<usize>>], jump, mv, path| {
            Some(Trie{
                prefix: String::from_utf8(path[path.len()-jump..].to_vec()).unwrap(),
                value: mv.cloned(),
                children: bm.iter().zip(ws).map(|(b, t)| (b as char, std::mem::take(t).unwrap())).collect()
            })
        });

        println!("{:?}", s);
    }

    /// Tests going from a map directly to a catamorphism
    #[test]
    fn cata_test5() {
        let empty = BytesTrieMap::<u64>::new();
        let result = empty.into_cata_side_effect(SplitCata::new(|_, _| 1, |_, _, _| 2, |_, _, _| 3));
        assert_eq!(result, 3);

        let mut nonempty = BytesTrieMap::<u64>::new();
        nonempty.insert(&[1, 2, 3], !0);
        let result = nonempty.into_cata_side_effect(SplitCata::new(|_, _| 1, |_, _, _| 2, |_, _, _| 3));
        assert_eq!(result, 3);
    }

    #[test]
    fn cata_test6() {
        let mut btm = BytesTrieMap::new();
        let rs = ["Hello, my name is", "Helsinki", "Hell"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

        let mut map_cnt = 0;
        let mut collapse_cnt = 0;
        let mut alg_cnt = 0;
        let mut jump_cnt = 0;

        btm.read_zipper().into_cata_jumping_side_effect(SplitCataJumping::new(
            |_, _path| {
                // println!("map: \"{}\"", String::from_utf8_lossy(_path));
                map_cnt += 1;
            },
            |_, _, _path| {
                // println!("collapse: \"{}\"", String::from_utf8_lossy(_path));
                collapse_cnt += 1;
            },
            |_, _, _path| {
                // println!("alg: \"{}\"", String::from_utf8_lossy(_path));
                alg_cnt += 1;
            },
            |_sub_path, _, _path| {
                // println!("jump: over \"{}\" to \"{}\"", String::from_utf8_lossy(_sub_path), String::from_utf8_lossy(_path));
                jump_cnt += 1;
            }
        ));
        // println!("map_cnt={map_cnt}, collapse_cnt={collapse_cnt}, alg_cnt={alg_cnt}, jump_cnt={jump_cnt}");

        assert_eq!(map_cnt, 2);
        assert_eq!(collapse_cnt, 1);
        assert_eq!(alg_cnt, 2);
        assert_eq!(jump_cnt, 3);
    }

    /// Covers the full spectrum of byte values
    #[test]
    fn cata_test7() {
        let mut btm = BytesTrieMap::new();
        let rs = [[0, 0, 0, 0], [0, 255, 170, 170], [0, 255, 255, 255], [0, 255, 88, 88]];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r, i); });

        let mut map_cnt = 0;
        let mut collapse_cnt = 0;
        let mut alg_cnt = 0;
        let mut jump_cnt = 0;

        btm.read_zipper().into_cata_jumping_side_effect(SplitCataJumping::new(
            |_, _path| {
                // println!("map: {_path:?}");
                map_cnt += 1;
            },
            |_, _, _path| {
                // println!("collapse: {_path:?}");
                collapse_cnt += 1;
            },
            |_mask, _, _path| {
                // println!("alg: {_path:?}, mask: {_mask:?}");
                alg_cnt += 1;
            },
            |_sub_path, _, _path| {
                // println!("jump: over {_sub_path:?} to {_path:?}");
                jump_cnt += 1;
            }
        ));
        // println!("map_cnt={map_cnt}, collapse_cnt={collapse_cnt}, alg_cnt={alg_cnt}, jump_cnt={jump_cnt}");

        assert_eq!(map_cnt, 4);
        assert_eq!(collapse_cnt, 0);
        assert_eq!(alg_cnt, 3);
        assert_eq!(jump_cnt, 4);
    }

    /// Tests that cata hits the root value
    #[test]
    fn cata_test8() {
        let keys = ["", "ab", "abc"];
        let btm: BytesTrieMap<usize> = keys.into_iter().enumerate().map(|(i, k)| (k, i)).collect();

        btm.into_cata_jumping_side_effect(SplitCataJumping::new(
            |v, path| {
                // println!("map: {path:?}");
                assert_eq!(path, &[97, 98, 99]);
                assert_eq!(*v, 2);
            },
            |v, _, path| {
                // println!("collapse: {path:?}");
                match *v {
                    1 => assert_eq!(path, &[97, 98]),
                    0 => assert_eq!(path, &[]),
                    _ => unreachable!(),
                }
            },
            |_mask, _, path| {
                // println!("alg: {path:?}");
                assert_eq!(path, &[]);
            },
            |sub_path, _, path| {
                // println!("jump: over {sub_path:?} to {path:?}");
                assert_eq!(sub_path, &[98]);
                assert_eq!(path, &[97]);
            }
        ))
    }

    #[test]
    fn cata_test9() {
        let keys = [vec![0], vec![0, 1, 2], vec![0, 1, 3]];
        let btm: BytesTrieMap<usize> = keys.into_iter().enumerate().map(|(i, k)| (k, i)).collect();

        btm.into_cata_jumping_side_effect(|mask, children, jump_len, val, path| {
            // println!("mask={mask:?}, children={children:?}, jump_len={jump_len}, val={val:?}, path={path:?}");
            match path {
                [0, 1, 2] => {
                    assert_eq!(jump_len, 0);
                    assert_eq!(children.len(), 0);
                    assert_eq!(*mask, ByteMask::EMPTY);
                    assert_eq!(val, Some(&1));
                },
                [0, 1, 3] => {
                    assert_eq!(jump_len, 0);
                    assert_eq!(children.len(), 0);
                    assert_eq!(*mask, ByteMask::EMPTY);
                    assert_eq!(val, Some(&2));
                },
                [0, 1] => {
                    assert_eq!(jump_len, 0);
                    assert_eq!(children.len(), 2);
                    assert_eq!(*mask, ByteMask::from_iter([2, 3]));
                    assert_eq!(val, None);
                },
                [0] => {
                    assert_eq!(jump_len, 1);
                    assert_eq!(children.len(), 1);
                    assert_eq!(*mask, ByteMask::from(1));
                    assert_eq!(val, Some(&0));
                },
                _ => panic!()
            }
        })
    }

    #[test]
    fn cata_testa() {
        let keys = [vec![0, 128, 1], vec![0, 128, 1, 255, 2]];
        let btm: BytesTrieMap<usize> = keys.into_iter().enumerate().map(|(i, k)| (k, i)).collect();

        btm.into_cata_jumping_side_effect(|mask, children, jump_len, val, path| {
            println!("mask={mask:?}, children={children:?}, jump_len={jump_len}, val={val:?}, path={path:?}");
            match path {
                [0, 128, 1, 255, 2] => {
                    assert_eq!(jump_len, 1);
                    assert_eq!(children.len(), 0);
                    assert_eq!(*mask, ByteMask::EMPTY);
                    assert_eq!(val, Some(&1));
                },
                [0, 128, 1] => {
                    assert_eq!(jump_len, 3);
                    assert_eq!(children.len(), 1);
                    assert_eq!(*mask, ByteMask::from(255));
                    assert_eq!(val, Some(&0));
                },
                a => panic!("{a:?}")
            }
        })
    }

    #[test]
    fn cata_test_cached() {
        let make_map = || {
            // let btm: BytesTrieMap<u8> = BytesTrieMap::range::<false, u16>(0x0, 0x101, 0x1, 0);
            // if true { return btm; }
            // let keys = [vec![0, 128, 1], vec![0, 128, 1, 255, 2]];
            // let btm: BytesTrieMap<u8> = keys.into_iter().enumerate()
            //     .map(|(i, k)| (k, i as u8)).collect();
            // if true { return btm; }
            let mut map: BytesTrieMap<u8> = BytesTrieMap::from_iter([([0], 0)]);
            for _level in 0..3 {
                let prev_zipper = map.read_zipper();
                let next_map = BytesTrieMap::new_from_ana(false, |quit, _val, children, _path| {
                    if quit { return }
                    for ii in 0..=2 {
                        children.graft_at_byte(ii, &prev_zipper);
                    }
                });
                drop(prev_zipper);
                map = next_map;
            }
            map
        };

        use std::rc::Rc;
        #[allow(dead_code)] // not accessing the fields, but using debug/eq
        #[derive(Clone, Debug, PartialEq)]
        struct Node<V> {
            value: Option<V>,
            children: Vec<Rc<Node<V>>>,
        }
        impl<V: Clone> Node<V> {
            fn new(value: Option<&V>, children: &[Rc<Node<V>>]) -> Self {
                Self { value: value.cloned(), children: children.to_vec() }
            }
        }

        // fn visit<'a, V, Z>(z: &mut Z) -> Rc<Node<*const u8>>
        //     where V: 'a, Z: Zipper<V> + ZipperReadOnly<'a, V> + ZipperMoving
        // {
        //     let value = shared_addr(z).map(|x| x as *const u8);
        //     let mut children = Vec::new();
        //     for ii in 0..z.child_count() {
        //         z.descend_indexed_branch(ii);
        //         if !z.is_value() {
        //             children.push(visit(z));
        //         }
        //         z.ascend_byte();
        //     }
        //     Rc::new(Node { value, children })
        // }
        // println!("tree: {:#?}", visit(&mut make_map().read_zipper()));
        use core::sync::atomic::{AtomicU64, Ordering::*};
        let calls_cached = AtomicU64::new(0);
        let tree_cached: Rc::<Node<u8>> = make_map().into_cata_cached(
            |_bm, children, value, _path| {
                calls_cached.fetch_add(1, Relaxed);
                Rc::new(Node::new(value, children))
            });
        let calls_cached = calls_cached.load(Relaxed);

        let mut calls_side = 0;
        let tree_side: Rc::<Node<u8>> = make_map().into_cata_side_effect(
            |_bm, children, value, _path| {
                calls_side += 1;
                Rc::new(Node::new(value, children))
            });

        assert_eq!(tree_side, tree_cached);
        eprintln!("calls_cached: {calls_cached}\ncalls_side: {calls_side}");
    }

    /// Generate some basic tries using the [TrieBuilder::push_byte] API
    #[test]
    fn ana_test1() {
        // Generate 5 'i's
        let mut invocations = 0;
        let map: BytesTrieMap<()> = BytesTrieMap::<()>::new_from_ana(5, |idx, val, children, _path| {
            // println!("path=\"{}\"", String::from_utf8_lossy(_path));
            *val = Some(());
            if idx > 0 {
                children.push_byte(b'i', idx - 1)
            }
            invocations += 1;
        });
        assert_eq!(map.val_count(), 5);
        assert_eq!(invocations, 6);

        // Generate all 3-lenght 'L' | 'R' permutations
        let mut invocations = 0;
        let map: BytesTrieMap<()> = BytesTrieMap::<()>::new_from_ana(3, |idx, val, children, _path| {
            // println!("path=\"{}\"", String::from_utf8_lossy(_path));
            if idx > 0 {
                children.push_byte(b'L', idx - 1);
                children.push_byte(b'R', idx - 1);
            } else {
                *val = Some(());
            }
            invocations += 1;
        });
        assert_eq!(map.val_count(), 8);
        assert_eq!(invocations, 15);
    }

    /// Test the [`TrieBuilder::set_child_mask`] API to set multiple children at once
    #[test]
    fn ana_test2() {
        let map: BytesTrieMap<()> = BytesTrieMap::<()>::new_from_ana(([0u64; 4], 0), |(mut mask, idx), val, children, _path| {
            // println!("path=\"{}\"", String::from_utf8_lossy(_path));
            if idx < 5 {
                mask[1] |= 1u64 << 1+idx;
                let child_vec = vec![(mask, idx+1); idx+1];
                children.set_child_mask(mask , child_vec);
            } else {
                *val = Some(());
            }
        });
        assert_eq!(map.val_count(), 120); // 1 * 2 * 3 * 4 * 5
        // for (path, ()) in map.iter() {
        //     println!("{}", String::from_utf8_lossy(&path));
        // }
    }
    /// Test the [`TrieBuilder::push`] API to set whole string paths
    #[test]
    fn ana_test3() {
        let map: BytesTrieMap<()> = BytesTrieMap::<()>::new_from_ana(3, |idx, val, children, _path| {
            // println!("path=\"{}\"", String::from_utf8_lossy(_path));
            if idx > 0 {
                children.push(b"Left:", idx-1);
                children.push(b"Right:", idx-1);
            } else {
                *val = Some(());
            }
        });
        // for (path, ()) in map.iter() {
        //     println!("{}", String::from_utf8_lossy(&path));
        // }
        assert_eq!(map.val_count(), 8);
        assert_eq!(map.get(b"Left:Right:Left:"), Some(&()));
        assert_eq!(map.get(b"Right:Left:Right:"), Some(&()));

        //Try intermixing whole strings and bytes
        let map: BytesTrieMap<()> = BytesTrieMap::<()>::new_from_ana(7, |idx, val, children, _path| {
            // println!("path=\"{}\"", String::from_utf8_lossy(_path));
            if idx > 0 {
                if idx % 2 == 0 {
                    children.push_byte(b'+', idx-1);
                    children.push_byte(b'-', idx-1);
                } else {
                    children.push(b"Left", idx-1);
                    children.push(b"Right", idx-1);
                }
            } else {
                *val = Some(());
            }
        });
        // for (path, ()) in map.iter() {
        //     println!("{}", String::from_utf8_lossy(&path));
        // }
        assert_eq!(map.val_count(), 128);
        assert_eq!(map.get(b"Right-Right+Left-Left"), Some(&()));
        assert_eq!(map.get(b"Left-Right-Right+Left"), Some(&()));

        //Intermix them in the same child list
        let map: BytesTrieMap<()> = BytesTrieMap::<()>::new_from_ana(7, |idx, val, children, _path| {
            // println!("path=\"{}\"", String::from_utf8_lossy(_path));
            if idx > 0 {
                if idx % 2 == 0 {
                    children.push_byte(b'+', idx-1);
                    children.push(b"Left", idx-1);
                } else {
                    children.push_byte(b'-', idx-1);
                    children.push(b"Right", idx-1);
                }
            } else {
                *val = Some(());
            }
        });
        // for (path, ()) in map.iter() {
        //     println!("{}", String::from_utf8_lossy(&path));
        // }
        assert_eq!(map.val_count(), 128);
        assert_eq!(map.get(b"Right+-+-+-"), Some(&()));
        assert_eq!(map.get(b"-+-+-+-"), Some(&()));
        assert_eq!(map.get(b"RightLeftRightLeftRightLeftRight"), Some(&()));
    }

    const GREETINGS: &[&str] = &["Hallo,Afrikaans", "Përshëndetje,Albanian", "እው ሰላም ነው,Amharic", "مرحبًا,Arabic",
        "Barev,Armenian", "Kamisaki,Aymara", "Salam,Azerbaijani", "Kaixo,Basque", "Вітаю,Belarusian", "হ্যালো,Bengali",
        "Zdravo,Bosnian", "Здравейте,Bulgarian", "ဟယ်လို,Burmese", "你好,Cantonese", "Hola,Catalan", "Kamusta,Cebuano",
        "Kamusta,Cebuano", "Moni,Chichewa", "Bonghjornu,Corsican", "Zdravo,Croatian", "Ahoj,Czech", "Hej,Danish",
        "Hallo,Dutch", "Hello,English", "Tere,Estonian", "Hello,Ewe", "سلام,Farsi (Persian)", "Bula,Fijian",
        "Kumusta,Filipino", "Hei,Finnish", "Bonjour,French", "Dia dhuit,Gaelic (Irish)", "Ola,Galician", "გამარჯობა,Georgian",
        "Guten tag,German", "γεια,Greek", "Mba'éichapa,Guarani", "Bonjou,Haitian Creole", "Aloha,Hawaiian",
        "שלום,Hebrew", "नमस्ते,Hindi", "Nyob zoo,Hmong", "Szia,Hungarian", "Halló,Icelandic", "Ndewo,Igbo",
        "TRASH-NO-COMMA", //Trash here, to test error-cases
        "Hello,Ilocano", "Halo,Indonesian", "Ciao,Italian", "こんにちは,Japanese", "Сәлеметсіз бе,Kazakh",
        "TRASH-NOTHING-AFTER-COMMA,", //Trash here, to test error-cases
        "សួស្តី,Khmer", "Mwaramutse,Kinyarwanda", "안녕하세요,Korean", "Slav,Kurdish", "ສະບາຍດີ,Lao", "Salve,Latin",
        ",TRASH-NOTHING-BEFORE-COMMA", //Trash here, to test error-cases
        "Sveika,Latvian", "Sveiki,Lithuanian", "Moien,Luxembourgish", "Salama,Malagasy", "Selamat pagi,Malay",
        "", //Trash here, empty string
        "Bongu,Maltese", "你好,Mandarin", "Kia ora,Maori", "नमस्कार,Marathi", "сайн уу,Mongolian", "Niltze Tialli Pialli,Nahuatl",
        "Ya’at’eeh,Navajo", "नमस्कार,Nepali", "Hei,Norwegian", "سلام,Pashto", "Cześć,Polish", "Olá,Portuguese",
        "ਸਤ ਸ੍ਰੀ ਅਕਾਲ,Punjabi", "Akkam,Oromo", "Allianchu,Quechua", "Bunâ,Romanian", "Привет,Russian", "Talofa,Samoan",
        "Thobela,Sepedi", "Здраво,Serbian", "Dumela,Sesotho", "Ahoj,Slovak", "Zdravo,Slovenian", "Hello,Somali",
        "Hola,Spanish", "Jambo,Swahili", "Hallå,Swedish", "Kamusta,Tagalog", "Ia Orana,Tahitian", "Li-hó,Taiwanese",
        "வணக்கம்,Tamil", "สวัสดี,Thai", "Tashi delek,Tibetan", "Mālō e lelei,Tongan", "Avuxeni,Tsonga", "Merhaba,Turkish",
        "привіт,Ukrainian", "السلام عليكم,Urdu", "Salom,Uzbek", "Xin chào,Vietnamese", "Helo,Welsh", "Molo,Xhosa",
    ];

    /// Test pushing into the trie, one byte at a time
    #[test]
    fn ana_test4() {
        let mut greetings_vec = GREETINGS.to_vec();
        let btm = BytesTrieMap::<Range<usize>>::new_from_ana(0..greetings_vec.len(), |mut range, val, children, path| {
            let n = path.len();

            //Sort the keys in the range by the first byte of each substring
            let string_slice = &mut greetings_vec[range.clone()];
            string_slice.sort_by_key(|s| s.as_bytes().get(n));

            //Discard the strings that are too short (that have ended prematurely)
            while range.len() > 0 && greetings_vec[range.start].len() <= n { range.start += 1; }

            while range.len() > 0 {
                //Find the range of strings that start with the same byte as the first string
                let mut m = range.start + 1;
                let byte = greetings_vec[range.start].as_bytes()[n];
                while range.contains(&m) && greetings_vec[m].as_bytes()[n] == byte {
                    m += 1;
                }

                let (mut same_prefix_range, remaining) = (range.start..m, m..range.end);

                //If this is the end of a path, set the value
                if byte == b',' {

                    //Sort by the languages
                    //NOTE: there is some ambiguity in the desired behavior, since the validity test
                    // sorts the greetings but not the languages.  However, if we don't sort the languages,
                    // then non-contiguous and non-prefixing empty language strings can't be removed unless
                    // we attempt to represent the results of a node by a list instead of a range
                    let string_slice = &mut greetings_vec[same_prefix_range.clone()];
                    string_slice.sort_by_key(|s| &s[n+1..]);

                    //Discard the strings have nothing after the ','
                    while same_prefix_range.len() > 0 && greetings_vec[same_prefix_range.start].len() <= n+1 {
                        same_prefix_range.start += 1;
                    }
                    //If we didn't discard all the items
                    if same_prefix_range.len() > 0 {
                        *val = Some(same_prefix_range);
                    }
                } else {
                    //Recursive case
                    children.push_byte(byte, same_prefix_range);
                }
                range = remaining;
            }
        });

        let mut check: Vec<&str> = GREETINGS.into_iter().copied()
            .filter(|x| {
                let comma_idx = x.find(",").unwrap_or(0);
                comma_idx != 0 && comma_idx < x.len()-1
            })
            .collect();
        check.sort_by_key(|x| x.split_once(",").map(|s| s.0).unwrap_or(&""));
        let mut it = check.iter();

        let mut rz = btm.read_zipper();
        while let Some(range) = rz.to_next_val() {
            for language_idx in range.clone().into_iter() {
                let greeting = std::str::from_utf8(rz.path()).unwrap();
                let language = &greetings_vec[language_idx][rz.path().len()+1..];

                // println!("language: {}, greeting: {}", language, greeting);
                assert_eq!(*it.next().unwrap(), format!("{greeting},{language}"));
            }
        }
    }

    #[test]
    fn ana_test5() {
        let _btm = BytesTrieMap::<&str>::new_from_ana(GREETINGS, |string_slice, val, children, _path| {

            fn split_key(in_str: &str) -> (&str, &str) {
                let det = in_str.find(',').unwrap_or(usize::MAX);
                if det == 0 {
                    ("", &in_str[1..])
                } else if det == usize::MAX {
                    ("", in_str)
                } else {
                    (&in_str[0..det], &in_str[det+1..])
                }
            }

            if string_slice.len() == 1 {
                let (_, split_val) = split_key(string_slice[0]);
                *val = Some(split_val);
            } else {
                for i in 0..string_slice.len() {
                    let (key, _) = split_key(string_slice[0]);
                    children.tolerant_push(key.as_bytes(), &string_slice[i..i+1]);
                }
            }
        });

        let mut rz = _btm.read_zipper();
        while let Some(language) = rz.to_next_val() {
            //GOAT, this feature (and therefore this test) is WIP
            println!("language: {}, greeting: {}", language, std::str::from_utf8(rz.path()).unwrap());
        }
    }

    #[test]
    fn apo_test1() {
        let mut btm = BytesTrieMap::new();
        let rs = ["arro^w", "bow", "cann^on", "roman", "romane", "romanus^", "romulus", "rubens", "ruber", "rubicon", "rubicundus", "rom^i"];
        rs.iter().enumerate().for_each(|(i, r)| { btm.insert(r.as_bytes(), i); });

        let mut alphabetic = [0u64; 4];
        for c in "abcdefghijklmnopqrstuvwxyz".bytes() { alphabetic.set_bit(c) }

        let trie_ref = btm.trie_ref_at_path([]);
        let counted = BytesTrieMap::new_from_ana(trie_ref, |trie_ref, _v, builder, loc| {

            let iter = crate::utils::ByteMaskIter::new(trie_ref.child_mask());
            for b in iter {
                if alphabetic.test_bit(b) {
                    let new_trie_ref = trie_ref.trie_ref_at_path([b]);
                    builder.push_byte(b, new_trie_ref);
                }
                // todo I didn't find a histogram/groupby function, so couldn't aggregate letter counts yet, just returning one
                else {
                    let new_map = BytesTrieMap::from_iter(loc.into_iter().copied().map(|x| ([x], 1)));
                    let temp_zipper = new_map.read_zipper();
                    builder.graft_at_byte(b, &temp_zipper)
                }
            }
        });

        println!("test");
        let mut rz = counted.read_zipper();
        while let Some(v) = rz.to_next_val() {
            // todo write out useful print function, that shows the count submaps
            println!("v: {}, p: {}", v, std::str::from_utf8(rz.path()).unwrap());
        }
    }
}
