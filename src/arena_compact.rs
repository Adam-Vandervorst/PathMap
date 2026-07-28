//! Compact Arena Trie Representation
//!
//! This format represents tries (or prefix trees) in a compact, efficient manner.
//!
//! ## Variable-Length Encoding: `varint64`
//!
//! The format uses variable-length encoding (VLE) for 64-bit integers. In this scheme:
//! - Numbers are encoded using 7 bits per byte.
//! - The most significant bit (MSB) indicates if more bytes follow (1) or not (0).
//! - Up to 9 bytes are used, preserving the last MSB in the resulting `u64`.
//! - This allows representation of the full range of `u64` values.
//!
//! See: [read_varint_u64] and [push_varint_u64] for the implementation and examples.
//!
//! # File Format Description
//!
//! ### File Header
//! The file begins with an 8-byte magic signature ([COMPACT_TREE_MAGIC]`=ACTree01`).
//! This signature helps quickly reject files not intended as tries.
//!
//! ### Root Offset
//! At offset `8`, a `u64` in little-endian byte order specifies the root node's offset.
//! This value can be updated to create a modified trie by setting a new root.
//!
//! ### Arena Layout
//! Starting at offset `16`, the arena stores dynamically sized objects (nodes and line data).
//! Each object is uniquely addressable by its starting offset.
//!
//! **Key Feature:** Siblings of any parent are encoded sequentially. This design:
//! - Allows storing only the offset to the first child.
//! - All children can be accessed by reading the nodes sequentially.
//!
//! ### Object Types in the Arena
//! The arena contains three object types:
//!
//! - **Line Data:**  
//!   - Format: `[length: varint64][data: u8; length]`  
//!   - A byte slice (`&[u8]`) with a variable-length size.
//!
//! - **Branch Node:** (Top bit of the first byte = 0)  
//!   - Byte 1: `[header: u8]`  
//!     - Bit #6: Has value? (1 = yes, 0 = no)  
//!     - Bits #0–5: Number of children (max 32).  
//!   - If value exists: `[node_value: varint64]`  
//!   - If children  > 0: `[first_child: varint64]`  
//!   - If children < 32: `[child_bytes: u8; num_children]` (ascending order)  
//!   - If children >=32: `[child_mask: u64; 4]`            (little-endian).
//!
//! - **Line Node:** (Top bit of the first byte = 1)  
//!   - Byte 1: `[header: u8]`  
//!     - Bit #6: Has value? (1 = yes, 0 = no)  
//!     - Bits #0–5: Number of children (max 1).  
//!   - If value exists: `[node_value: varint64]`  
//!   - If child exists: `[first_child: varint64]`  
//!   - Always: `[line_offset: varint64]` (points to line data).
//!
//! ## Diagram of File Format
//!
//! ```text
//! File format: [MAGIC=ACTree01][root_id: u64][arena of nodes]...
//! Where [arena of nodes] stores dynamically sized nodes and line data,
//! written densely one after another.
//!
//! Object types:
//! line data:   [length: varint64][u8; length]
//!    function: 
//!
//! branch node: [header: u8] (header & 0x80 == 0)
//!              [if (header&0x40 != 0) node_value : varint64         ]
//!              [if (header&0x3f != 0) first_child: varint64         ]
//!              [if (header&0x3f < 32) child_bytes: [u8; header&0x3f]]
//!              [if (header&0x3f >=32) child_mask : [u64; 4]         ]
//!
//! line node:   [header: u8] (header & 0x80 != 0)
//!              [if (header&0x40 != 0) node_value : varint64]
//!              [if (header&0x3f != 0) first_child: varint64]
//!              [                      line_offset: varint64]
//! ```
use std::{io::Write, hash::Hasher};
use std::cell::Cell;
use std::marker::PhantomData;
use fast_slice_utils::starts_with;

use crate::alloc::{GlobalAlloc, global_alloc};
use crate::{
    PathMap,
    morphisms::Catamorphism,
    utils::{BitMask, ByteMask, find_prefix_overlap},
    zipper::{
        Zipper, ZipperValues, ZipperForking, ZipperAbsolutePath, ZipperIteration,
        ZipperMoving, ZipperPath, ZipperPathBuffer, ZipperReadOnlyValues, ZipperSubtries,
        PathObserver,
        ZipperConcrete, ZipperReadOnlyConditionalValues, TrieRef
    },
};

use crate::gxhash::{GxHasher, HashMap, HashMapExt};

/// The identifier of a node (branch node or line node)
///
/// NOTE: this identifier can be (wrongly) reused between different tries,
/// which can catastrophically break the implementation.
///
/// However, in order to fix this issue, we would have to either introduce
/// - a runtime cost (include `Trie ID` or `&Trie` into the `NodeId`),
/// - ... or introduce a *very* inconvenient API, using invariant lifetimes.
///
/// This tradeoff is in favor of interface simplicity and lower runtime cost.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NodeId(u64);

/// The identifier of line data (essentially, `&[u8]`)
///
/// See documentation of [NodeId] for the note about safety
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LineId(u64);
const INVALID_LINE: LineId = LineId(!0);

/// Maximum node size:
/// 1 byte header + 9 byte first child + 9 byte value + 32 child mask
const MAX_BRANCH_NODE_SIZE: usize = 1 + 9 + 9 + 32;
/// Maximum node size:
/// 1 byte header + 9 byte first child + 9 byte value + 9 byte path id
const MAX_LINE_NODE_SIZE: usize = 1 + 9 + 9 + 9;

/// Top bit indicates that the node is a line node
const LINE_FLAG: u8 = 0x80;
/// Bit #6 indicates that this node contains a value
const VALUE_FLAG: u8 = 0x40;

/// Maximum number of bytes in `varint64`
const MAX_VARINT_SIZE: usize = 9;

const U64_SIZE: usize = core::mem::size_of::<u64>();

/// Size of the trailer that [`ArenaCompactTree::merge_zipper_into_file`]
/// appends after each merge: two little-endian `u64`s,
/// `[previous_suffix, previous_root]` (see [`ArenaCompactTree::root_history`]).
const ROOT_TRAILER_SIZE: usize = 2 * U64_SIZE;

/// File magic signature
pub const MAGIC_LENGTH: usize = 8;
// Changes:
// ACTree01 -> ACTree02: Relative offsets
// ACTree02 -> ACTree03: Branchless varint
pub const COMPACT_TREE_MAGIC: [u8; MAGIC_LENGTH] = *b"ACTree03";

const VARINT_LEN_BIAS: u8 = u8::MAX - 8;
/// Decodes a variable-length encoded `u64` integer from a byte slice.
///
/// If the first byte is up to `VARINT_LEN_BIAS` (247), it represents the value directly.
/// Otherwise, the first byte (`VARINT_LEN_BIAS + nbytes`) indicates the number of following
/// bytes (`nbytes`) that contain the integer in little-endian order.
///
/// # Arguments
/// * `data` - A byte slice containing the encoded varint.
///
/// # Returns
/// A tuple containing:
/// * The decoded `u64` value.
/// * The number of bytes consumed from the input slice.
///
/// # Examples
/// ```
/// use pathmap::arena_compact::read_varint_u64;
///
/// // Single byte encoding (100)
/// let data = [100];
/// let (value, len) = read_varint_u64(&data);
/// assert_eq!(value, 100);
/// assert_eq!(len, 1);
///
/// // Multi-byte encoding (1000)
/// let data = [249, 232, 3];
/// let (value, len) = read_varint_u64(&data);
/// assert_eq!(value, 1000);
/// assert_eq!(len, 3);
///
/// // Maximum u64 value
/// let data = [255, 255, 255, 255, 255, 255, 255, 255, 255];
/// let (value, len) = read_varint_u64(&data);
/// assert_eq!(value, u64::MAX);
/// assert_eq!(len, 9);
/// ```
pub fn read_varint_u64(data: &[u8]) -> (u64, usize) {
    let first = data[0];
    if first <= VARINT_LEN_BIAS {
        return (first as u64, 1);
    }
    let len = (first - VARINT_LEN_BIAS) as usize;
    let rest = unsafe {
        data.as_ptr().add(1)
            .cast::<u64>().read_unaligned()
    };
    let zeros = (64 - len * 8) as u32;
    let value = (rest << zeros) >> zeros;
    (value, len + 1)
}

/// Encodes a `u64` integer into a variable-length format and writes it to a `Writer`.
///
/// The encoding uses a single byte for values up to `VARINT_LEN_BIAS` (247). For larger values,
/// it writes a header byte (`VARINT_LEN_BIAS + nbytes`) followed by the `nbytes` least significant
/// bytes of the integer in little-endian order. The maximum encoding size is 9 bytes.
///
/// # Arguments
/// * `dst` - A mutable reference to a type implementing `Write`, such as `Vec<u8>` or `BufWriter`.
/// * `int` - The unsigned 64-bit integer to encode.
///
/// # Examples
/// ```
/// use std::io::Write;
/// use pathmap::arena_compact::push_varint_u64;
///
/// // Single byte encoding for small value (100)
/// let mut buf = Vec::new();
/// push_varint_u64(&mut buf, 100).unwrap();
/// assert_eq!(buf, [100]);
///
/// // Multi-byte encoding for larger value (1000)
/// let mut buf = Vec::new();
/// push_varint_u64(&mut buf, 1000).unwrap();
/// assert_eq!(buf, [249, 232, 3]);
///
/// // Maximum u64 value (2^64 - 1)
/// let mut buf = Vec::new();
/// push_varint_u64(&mut buf, u64::MAX).unwrap();
/// assert_eq!(buf, [255, 255, 255, 255, 255, 255, 255, 255, 255]);
/// ```
pub fn push_varint_u64(dst: &mut impl Write, int: u64)
    -> Result<usize, std::io::Error>
{
    if int <= VARINT_LEN_BIAS as u64 {
        dst.write_all(&[int as u8])?;
        return Ok(1)
    }
    let nbytes = (8 - int.leading_zeros() / 8) as usize;
    let arr = int.to_le_bytes();
    dst.write_all(&[VARINT_LEN_BIAS + nbytes as u8])?;
    dst.write_all(&arr[..nbytes])?;
    Ok(nbytes + 1)
}

/*
// older varints
/// Read `u64` in variable-length encoding (VLE) from a slice.
///
/// This function implements varint decoding, where numbers are encoded using
/// 7 bits per byte, with the most significant bit (MSB) indicating whether
/// more bytes follow (1) or not (0). It can read up to 9 bytes to represent
/// a full 64-bit value.
///
/// # Returns
/// A tuple containing:
/// * `u64` - The decoded unsigned 64-bit integer.
/// * `usize` - The number of bytes consumed from the input slice.
///
/// # Examples
///
/// ```
/// use pathmap::arena_compact::read_varint_u64;
///
/// // Single byte encoding (127)
/// let bytes = [0x7F];
/// let (value, bytes_read) = read_varint_u64(&bytes);
/// assert_eq!(value, 127);
/// assert_eq!(bytes_read, 1);
///
/// // Two byte encoding (130) - shows little-endian style shift
/// let bytes = [0x82, 0x01];
/// let (value, bytes_read) = read_varint_u64(&bytes);
/// assert_eq!(value, 130);
/// assert_eq!(bytes_read, 2);
///
/// // Maximum u64 value (2^64 - 1) using 9 bytes
/// let bytes = [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF];
/// let (value, bytes_read) = read_varint_u64(&bytes);
/// assert_eq!(value, u64::MAX);
/// assert_eq!(bytes_read, 9);
/// ```
///
/// Panics when the VLE encoding is longer than the slice.
/// Will never panic if slice length is at least 9.
pub fn read_varint_u64(data: &[u8]) -> (u64, usize) {
    let mut value = 0;
    let mut shift = 0;
    let mut bread = 0;
    for ii in 0..8 {
        let byte = data[ii];
        value = value | (((byte & 0x7f) as u64) << shift);
        bread += 1;
        if (byte >> 7) == 0 {
            return (value, bread);
        }
        shift += 7;
    }
    // Read last byte without clearing the top bit
    let byte = data[8];
    value = value | ((byte as u64) << shift);
    bread += 1;
    (value, bread)
}

/// Writes a variable-length unsigned 64-bit integer to a Writer.
///
/// This function encodes a `u64` value into a varint format, using 7 bits
/// per byte, with the most significant bit (MSB) set to 1 if more bytes follow
/// and 0 if it's the last byte. Uses up to 9 bytes for encoding.
///
/// # Arguments
/// * `dst` - Reference to Writer e.g. `Vec<u8>`, `File`, `BufWriter`.
/// * `int` - The unsigned 64-bit integer to encode.
///
/// # Examples
/// ```
/// use std::io::Write;
/// use pathmap::arena_compact::push_varint_u64;
///
/// // Single byte encoding (127)
/// let mut buf = Vec::new();
/// push_varint_u64(&mut buf, 127);
/// assert_eq!(buf, [0x7F]);
///
/// // Two byte encoding (130) - shows little-endian style shift
/// let mut buf = Vec::new();
/// push_varint_u64(&mut buf, 130);
/// assert_eq!(buf, [0x82, 0x01]);
///
/// // Maximum u64 value (2^64 - 1) using 8 bytes
/// let mut buf = Vec::new();
/// push_varint_u64(&mut buf, u64::MAX);
/// assert_eq!(buf, [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]);
/// ```
pub fn push_varint_u64(dst: &mut impl Write, mut int: u64)
    -> Result<usize, std::io::Error>
{
    let mut buf = [0_u8; MAX_VARINT_SIZE];
    for ii in 0..MAX_VARINT_SIZE - 1 {
        let mut byte = (int & 0x7f) as u8;
        int = int >> 7;
        byte = byte | ((int > 0) as u8) << 7;
        buf[ii] = byte;
        if int == 0 {
            dst.write_all(&buf[..ii + 1])?;
            return Ok(ii + 1);
        }
    }
    // write the last byte;
    buf[MAX_VARINT_SIZE - 1] = int as u8;
    dst.write_all(&buf)?;
    Ok(MAX_VARINT_SIZE)
}
*/

/// Read a node from the start of a given slice
///
/// # Usage
/// ```ignore
/// use pathmap::arena_compact::read_node;
/// use pathmap::arena_compact::Node;
/// let (node, length) = read_node(&[0x00]);
/// assert!(matches!(node, Node::Branch(_)));
/// assert_eq!(node.child_count(), 0);
/// assert_eq!(length, 1);
/// ```
fn read_node(data: &[u8], node_id: NodeId) -> (Node, usize) {
    let head = data[0];
    let mut pos = 1;
    if head & LINE_FLAG == 0 {
        let mut node = NodeBranch::empty();
        let has_value = (head & VALUE_FLAG) != 0;
        node.value = if has_value {
            let (value, off) = read_varint_u64(&data[pos..]);
            pos += off;
            Some(value)
        } else {
            None
        };
        let nchildren = (head & 0x3f) as usize;
        assert!(nchildren <= 32, "invalid children count");
        if nchildren > 0 {
            let (first_child, off) = read_varint_u64(&data[pos..]);
            pos += off;
            node.first_child = Some(NodeId(node_id.0 - first_child));
        }
        let children_bytes = &data[pos..pos + nchildren];
        pos += nchildren;
        node.bytemask = if nchildren == 32 {
            #[cfg(not(target_endian = "little"))]
            compile_error!("big endian not supported");
            let ptr = children_bytes.as_ptr().cast::<[u64; 4]>();
            // Safety: we're not reading past the end,
            // since children_bytes is exact size
            ByteMask::from(unsafe { ptr.read_unaligned() })
        } else {
            ByteMask::from_iter(children_bytes.iter().copied())
        };
        (Node::Branch(node), pos)
    } else {
        let mut line = NodeLine::empty();
        let has_value = (head & VALUE_FLAG) != 0;
        if has_value {
            let (value, off) = read_varint_u64(&data[pos..]);
            pos += off;
            line.value = Some(value);
        }
        let has_child = (head & 0x1) != 0;
        if has_child {
            let (child, off) = read_varint_u64(&data[pos..]);
            pos += off;
            line.child = Some(NodeId(node_id.0 - child));
        }
        let (line_id, off) = read_varint_u64(&data[pos..]);
        pos += off;
        line.path = LineId(node_id.0 - line_id);
        (Node::Line(line), pos)
    }
}

const USE_COUNTERS: bool = cfg!(feature="act_counters");

#[derive(Default, Clone)]
pub struct Counters {
    nodes: usize,
    nodes_size: usize,
    children: usize,
    child_mask_size: usize,
    lines: usize,
    lines_size: usize,
    values: usize,
    values_size: usize,
    offsets: usize,
    offsets_size: usize,
    line_data: usize,
    line_data_size: usize,
    line_data_reuse: usize,
    line_data_reuse_size: usize,
}

const SI_PREFIX: &[u8] = b"KMGTPE";

struct SiCount(usize);

impl std::fmt::Display for SiCount {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        let mut value = self.0 as f64;
        if value < 1000.0 {
            return write!(fmt, "{value:3.0}");
        }
        let mut idx = 0;
        while value > 995.0 && idx < SI_PREFIX.len() {
            idx += 1;
            value = value / 1000.0;
        }
        write!(fmt, "{value:3.2}{}", SI_PREFIX[idx - 1] as char)
    }
}

impl std::fmt::Debug for Counters {
    fn fmt(&self, fmt: &mut std::fmt::Formatter) -> std::fmt::Result {
        let total_size = self.nodes_size + self.lines_size
            + self.line_data_size + 16 + 8;
        write!(fmt,
"Total file size: {total}B
Offsets: {offsets_size}B / {offsets} ({offsets_avg:1.3})
Contents:
    Line data: {line_data_size}B / {line_data} ({line_data_avg:1.3}) (saved by reuse={reuse})
    Line nodes: {lines_size}B / {lines} ({lines_avg:1.3})
    Branch nodes: {nodes_size}B / {nodes} ({nodes_avg:1.3})
        Children: average={children_avg:1.3}, mask size={mask_avg:1.3}",
            total=SiCount(total_size),
            offsets_size=SiCount(self.offsets_size),
            offsets=SiCount(self.offsets),
            offsets_avg=self.offsets_size as f64 / self.offsets as f64,
            line_data_size=SiCount(self.line_data_size),
            line_data=SiCount(self.line_data),
            line_data_avg=self.line_data_size as f64 / self.line_data as f64,
            reuse=SiCount(self.line_data_reuse_size),
            lines_size=SiCount(self.lines_size),
            lines=SiCount(self.lines),
            lines_avg=self.lines_size as f64 / self.lines as f64,
            nodes_size=SiCount(self.nodes_size),
            nodes=SiCount(self.nodes),
            nodes_avg=self.nodes_size as f64 / self.nodes as f64,
            children_avg=self.children as f64 / self.nodes as f64,
            mask_avg=self.child_mask_size as f64 / self.nodes as f64,
        )
    }
}

impl Counters {
    #[inline(always)]
    fn add_line(&mut self, size: usize) {
        if !USE_COUNTERS { return; }
        self.lines += 1;
        self.lines_size += size;
    }
    #[inline(always)]
    fn add_line_data(&mut self, size: usize) {
        if !USE_COUNTERS { return; }
        self.line_data += 1;
        self.line_data_size += size;
    }
    #[inline(always)]
    fn add_line_data_reuse(&mut self, size: usize) {
        if !USE_COUNTERS { return; }
        self.line_data_reuse += 1;
        self.line_data_reuse_size += size;
    }
    #[inline(always)]
    fn add_node(&mut self, size: usize) {
        if !USE_COUNTERS { return; }
        self.nodes += 1;
        self.nodes_size += size;
    }
    #[inline(always)]
    fn add_offset(&mut self, size: usize) {
        if !USE_COUNTERS { return; }
        self.offsets += 1;
        self.offsets_size += size;
    }
    #[inline(always)]
    fn add_value(&mut self, size: usize) {
        if !USE_COUNTERS { return; }
        self.values += 1;
        self.values_size += size;
    }
    #[inline(always)]
    fn add_children(&mut self, children: usize, size: usize) {
        if !USE_COUNTERS { return; }
        self.children += children;
        self.child_mask_size += size;
    }
}

/// Represents a trie stored in compact format.
///
/// See module-level documentation for the file format details.
///
/// `Storage` type is the backing mechanism for trie data
///
/// Currently supported `Storage`:
/// - [`Vec<u8>`], used for in-memory serialization.
/// - [`memmap2::Mmap`], used for from-disk reading.
/// - TODO(igorm): `Wrapper(File)` for direct to-disk serialization.
///
/// [ArenaCompactTree] can be constructed using [`ArenaCompactTree::<Vec<u8>>::from_zipper`]:
///
/// ... Or opened from disk using [`ArenaCompactTree::<Mmap>::open`]:
pub struct ArenaCompactTree<Storage> {
    /// Backing storage for the trie
    storage: Storage,
    /// Always points past the last byte of serialized data
    position: u64,
    /// Used for re-use of lines. Look up LineId by line hash.
    /// In case of collisions, line can't be cached.
    line_map: HashMap<u64, LineId>,
    /// Hasher for the lines.
    hasher: GxHasher,
    /// Number of stored lines
    lines: usize,
    /// Counters to debug storage usage
    counters: Counters,
    /// Currently read value, so that the reader can borrow it
    value: Cell<u64>,
}

pub type ACTVec = ArenaCompactTree<Vec<u8>>;
pub type ACTMmap = ArenaCompactTree<Mmap>;
pub type ACTVecZipper<'tree, Value> = ACTZipper<'tree, Vec<u8>, Value>;
pub type ACTMmapZipper<'tree, Value> = ACTZipper<'tree, Mmap, Value>;

impl<Storage> ArenaCompactTree<Storage> {
    fn write_line(
        dst: &mut impl Write, line: &NodeLine, node_id: NodeId,
        counters: &mut Counters,
    ) -> Result<(), std::io::Error> {
        const ARC_HEAD: u8 = 0x80;
        let value_flag = if line.value.is_some() { VALUE_FLAG } else { 0 };
        let child_flag = if line.child.is_some() { 1 } else { 0 };
        let head = ARC_HEAD | value_flag | child_flag;
        dst.write_all(&[head]).unwrap();
        if let Some(value) = line.value {
            let size = push_varint_u64(dst, value)?;
            counters.add_value(size);
        }
        if let Some(child) = line.child {
            let offset = node_id.0.checked_sub(child.0)
                .expect("Children are expected to be written first");
            let size = push_varint_u64(dst, offset as u64)?;
            counters.add_offset(size);
        }
        let offset = node_id.0.checked_sub(line.path.0)
            .expect("Children are expected to be written first");
        let size = push_varint_u64(dst, offset as u64)?;
        counters.add_offset(size);
        Ok(())
    }

    fn write_node(
        dst: &mut impl Write, node: &NodeBranch, node_id: NodeId,
        counters: &mut Counters,
    ) -> Result<(), std::io::Error> {
        let nchildren = node.bytemask.count_bits();
        let value_flag = if node.value.is_some() { VALUE_FLAG } else { 0 };
        let head = nchildren.min(32) as u8 | value_flag;
        dst.write_all(&[head]).unwrap();
        if let Some(value) = node.value {
            let size = push_varint_u64(dst, value)?;
            counters.add_value(size);
        }
        if let Some(first_child) = node.first_child {
            let offset = node_id.0.checked_sub(first_child.0)
                .expect("Children are expected to be written first");
            assert!(nchildren > 0, "child count == 0 and first_child is Some");
            let size = push_varint_u64(dst, offset as u64)?;
            counters.add_offset(size);
        }
        if nchildren >= 32 {
            counters.add_children(nchildren as usize, 32);
            for word in node.bytemask.0 {
                dst.write_all(&word.to_le_bytes())?;
            }
        } else {
            counters.add_children(nchildren as usize, nchildren as usize);
            for byte in node.bytemask.iter() {
                dst.write_all(&[byte])?;
            }
        }
        Ok(())
    }

    pub fn counters(&self) -> &Counters {
        &self.counters
    }
}

impl<Storage> ArenaCompactTree<Storage>
where Storage: AsRef<[u8]>
{
    /// Get the reference to the serialized bytes
    ///
    /// # Examples
    /// ```
    /// use pathmap::{PathMap, arena_compact::ArenaCompactTree};
    /// let items = ["ace", "acf", "adg", "adh", "bjk"];
    /// let btm = PathMap::from_iter(items.iter().map(|i| (i, ())));
    /// let tree1 = ArenaCompactTree::from_zipper(btm.read_zipper(), |_v| 0);
    /// let the_serialized_bytes = tree1.get_data();
    /// println!("serialized data: {the_serialized_bytes:?}");
    /// ```
    pub fn get_data(&self) -> &[u8] {
        self.storage.as_ref()
    }

    /// Read node provided [NodeId]
    ///
    /// Returns a tuple of the read [Node] and next child [NodeId]
    /// The next child id is potentially invalid.
    fn get_node(&self, node_id: NodeId) -> (Node, NodeId) {
        let data = &self.storage.as_ref()[node_id.0 as usize..];
        let (node, off) = read_node(data, node_id);
        let next = NodeId(node_id.0 + off as u64);
        (node, next)
    }

    /// Read line data provided [LineId]
    ///
    /// Returns a byte slice of line data.
    fn get_line(&self, line_id: LineId) -> &[u8] {
        let start = &self.storage.as_ref()[line_id.0 as usize..];
        let (len, off) = read_varint_u64(start);
        assert!(len != 0);
        &start[off..off + len as usize]
    }

    /// Read root [Node]
    ///
    /// Returns root [Node], together with root's [NodeId].
    fn get_root(&self) -> (Node, NodeId) {
        let root_slice = &self.storage.as_ref()[MAGIC_LENGTH..][..U64_SIZE];
        let root_buf: &[u8; U64_SIZE] = root_slice.try_into()
            .expect("buffer size must be U64_SIZE, we just made it this way");
        let root_id = NodeId(u64::from_le_bytes(*root_buf));
        (self.get_node(root_id).0, root_id)
    }

    /// The chain of historical roots recorded in the file, newest first.
    ///
    /// Each [`ArenaCompactTree::merge_zipper_into_file`] appends a
    /// [`ROOT_TRAILER_SIZE`]-byte trailer `[previous_suffix, previous_root]`
    /// capturing the root that was live just before that merge, so the roots
    /// form a singly-linked list: the current root (at [`MAGIC_LENGTH`]) is the
    /// head, and each trailer's `previous_root` points back to the prior one,
    /// with `previous_suffix` giving the file offset of that root's own trailer.
    ///
    /// Walking stops at the base file, whose trailing zero padding reads back as
    /// a zero `previous_root`. A file that has never been merged therefore yields
    /// a single element: its current root.
    ///
    /// The `previous_suffix` field is written for future use (chaining and
    /// suffix reclamation); this reader only follows it to enumerate roots.
    pub fn root_history(&self) -> Vec<NodeId> {
        let data = self.storage.as_ref();
        let (_, root_id) = self.get_root();
        let mut roots = vec![root_id];
        // The most recent merge's trailer, if any, occupies the final bytes.
        let mut off = data.len().saturating_sub(ROOT_TRAILER_SIZE);
        while off >= MAGIC_LENGTH + U64_SIZE && off + ROOT_TRAILER_SIZE <= data.len() {
            let suffix_buf: [u8; U64_SIZE] = data[off..][..U64_SIZE].try_into().unwrap();
            let root_buf: [u8; U64_SIZE] = data[off + U64_SIZE..][..U64_SIZE].try_into().unwrap();
            let previous_suffix = u64::from_le_bytes(suffix_buf);
            let previous_root = u64::from_le_bytes(root_buf);
            // A base file ends in zero padding, so its final u64 is zero.
            if previous_root == 0 {
                break;
            }
            roots.push(NodeId(previous_root));
            if previous_suffix == 0 {
                break;
            }
            off = previous_suffix as usize;
        }
        roots
    }

    /// Find existing [LineId] that contains provided line `data`
    ///
    /// This is done by calculating the hash of the data, and storing it in a map.
    /// Because of this, this function can give a false negative in case of collision
    /// This happens in `~1/5e9` cases, so we probably don't care about that.
    ///
    /// NOTE: the hash function is chosen to be deterministic, for consistency,
    /// Which means it's possible to contruct a malicious set of paths which
    /// will not able to reuse lines.
    fn find_line_reuse(&self, data: impl AsRef<[u8]>) -> Option<LineId> {
        let data = data.as_ref();
        let mut hasher = self.hasher.clone();
        hasher.write(data);
        let hash = hasher.finish();
        let line_id = *self.line_map.get(&hash)?;
        (self.get_line(line_id) == data).then_some(line_id)
    }

    /// Read `index`'th sibling starting from `node_id`
    ///
    /// Returns [Node] data together with it's [NodeId] and next siblings's [NodeId]
    fn nth_node(&self, mut node_id: NodeId, index: usize) -> (Node, NodeId, NodeId) {
        let (mut node, mut next) = self.get_node(node_id);
        for _ii in 0..index {
            let (nnode, nnext) = self.get_node(next);
            node_id = next;
            next = nnext;
            node = nnode;
        }
        (node, node_id, next)
    }

    /// Returns the value at the specified `path`, or `None` if no value exists
    pub fn get_val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<u64> {
        let mut path = path.as_ref();
        let mut cur_node = self.get_root().0;
        loop {
            match cur_node {
                Node::Line(line) => {
                    let lpath = self.get_line(line.path);
                    if !starts_with(path, lpath) {
                        return None;
                    }
                    path = &path[lpath.len()..];
                    if path.is_empty() && line.value.is_some() {
                        return line.value;
                    }
                    cur_node = self.get_node(line.child?).0;
                }
                Node::Branch(node) => {
                    if path.is_empty() {
                        return node.value;
                    }
                    if !node.bytemask.test_bit(path[0]) {
                        return None;
                    }
                    let first_child = node.first_child?;
                    let idx = node.bytemask.index_of(path[0]) as usize;
                    cur_node = self.nth_node(first_child, idx).0;
                    path = &path[1..];
                }
            }
        }
    }

    /// Deprecated alias for [Self::get_val_at]
    #[deprecated] //GOAT-old-names
    pub fn get<K: AsRef<[u8]>>(&self, path: K) -> Option<u64> {
        self.get_val_at(path)
    }
}

impl<Storage> ArenaCompactTree<Storage>
where Storage: Write
{
    fn push_node(&mut self, node: &NodeBranch)
        -> Result<NodeId, std::io::Error>
    {
        let node_id = NodeId(self.position);
        let mut cursor = std::io::Cursor::new([0; MAX_BRANCH_NODE_SIZE]);
        Self::write_node(&mut cursor, node, node_id, &mut self.counters)?;
        let len = cursor.position();
        self.counters.add_node(len as usize);
        self.storage.write_all(&cursor.get_ref()[..len as usize])?;
        self.position += len;
        Ok(node_id)
    }

    fn push_line(&mut self, line: &NodeLine)
        -> Result<NodeId, std::io::Error>
    {
        let node_id = NodeId(self.position);
        let mut cursor = std::io::Cursor::new([0; MAX_LINE_NODE_SIZE]);
        Self::write_line(&mut cursor, line, node_id, &mut self.counters)?;
        let len = cursor.position();
        self.counters.add_line(len as usize);
        self.storage.write_all(&cursor.get_ref()[..len as usize])?;
        self.position += len;
        Ok(node_id)
    }

    fn push(&mut self, node: &Node) -> Result<NodeId, std::io::Error> {
        let (node_id, _kind) = match node {
            Node::Line(line) => (self.push_line(line), "line"),
            Node::Branch(branch) => (self.push_node(branch), "bra"),
        };
        if DO_TRACE { eprintln!("push {node_id:?} node={node:?}"); }
        // debug_assert_eq!(self.position, self.storage.len() as u64, "failed push {_kind}");
        node_id
    }

    fn finalize(&mut self) -> Result<(), std::io::Error> {
        // Invariant: There must always be a 9-byte slice at the end
        // This allows [ValueSlice] to always point at correct data,
        // And readers to always be able to read a varint.
        self.storage.write_all(&[0; MAX_VARINT_SIZE - 1])?;
        self.storage.flush()
    }
}
/*
impl ArenaCompactTree<File> {
    fn find_line_reuse(&mut self, line: impl AsRef<[u8]>) -> Option<LineId> {
        use std::io::SeekFrom;
        use std::io::Seek;
        let line = line.as_ref();
        let mut hasher = self.hasher.clone();
        hasher.write(line);
        let hash = hasher.finish();
        let line_id = *self.line_map.get(&hash)?;
        self.storage.seek(SeekFrom::Start(line_id.0 as u64)).unwrap();
        (self.get_line(line_id) == line).then_some(line_id)
    }
}
*/

impl ArenaCompactTree<Vec<u8>> {
    fn new() -> Self {
        // Allocate the space for the header + root node
        let mut storage = COMPACT_TREE_MAGIC.to_vec();
        storage.extend_from_slice(&[0; U64_SIZE]);
        Self {
            position: storage.len() as u64,
            storage,
            line_map: HashMap::new(),
            hasher: Default::default(),
            lines: 0,
            counters: Counters::default(),
            value: Cell::new(0),
        }
    }

    /// Construct [ArenaCompactTree] from a read zipper.
    /// # Examples
    /// ```
    /// use pathmap::{PathMap, arena_compact::ArenaCompactTree};
    /// let items = ["ace", "acf", "adg", "adh", "bjk"];
    /// let btm = PathMap::from_iter(items.iter().map(|i| (i, ())));
    /// let tree1 = ArenaCompactTree::from_zipper(btm.read_zipper(), |_v| 0);
    /// let mut zipper = tree1.read_zipper();
    /// for path in items {
    ///     use pathmap::zipper::{ZipperMoving, ZipperPath};
    ///     zipper.reset();
    ///     assert!(zipper.descend_to_existing(path) == path.len());
    ///     assert_eq!(zipper.path(), path.as_bytes());
    /// }
    /// let tree2 = ArenaCompactTree::from_zipper(tree1.read_zipper(), |_v| 0);
    /// assert_eq!(tree1.get_data(), tree2.get_data())
    /// ```
    #[inline]
    pub fn from_zipper<V, Z, M>(zipper: Z, map: M) -> Self
    where
        V: Clone + Send + Sync + Unpin,
        Z: Catamorphism<V>,
        M: Fn(&V) -> u64,
    {
        build_arena_tree(zipper, map)
    }

    fn push_v(&mut self, node: &Node) -> NodeId {
        self.push(node).expect("push to vec doesn't fail")
    }

    fn set_root(&mut self, node: &Node) -> NodeId {
        let node_id = self.push_v(node);
        let root_buf = &mut self.storage[MAGIC_LENGTH..][..U64_SIZE];
        root_buf.copy_from_slice(&node_id.0.to_le_bytes());
        node_id
    }

    fn add_path(&mut self, line: impl AsRef<[u8]>) -> LineId {
        let line = line.as_ref();
        let line_id = LineId(self.position);

        const REUSE_ARCS: bool = true;
        if REUSE_ARCS {
            // caching lines
            if let Some(prev) = self.find_line_reuse(line) {
                self.counters.add_line_data_reuse(line.len());
                return prev;
            }
            let mut hasher = self.hasher.clone();
            hasher.write(line);
            self.line_map.insert(hasher.finish(), line_id);
        }
        let lenlen = push_varint_u64(&mut self.storage, line.len() as u64)
            .expect("writing to vec should never fail.");
        self.storage.extend_from_slice(line);
        self.counters.add_line_data(lenlen + line.len());
        self.position = self.storage.len() as u64;
        self.lines += 1;
        line_id
    }
}

use memmap2::Mmap;
use std::path::Path;

impl ArenaCompactTree<Mmap> {
    /// Memmap a file and use it as backing storage for the trie
    ///
    /// # Examples
    /// ```
    /// use pathmap::{PathMap, arena_compact::ArenaCompactTree};
    /// use tempfile::NamedTempFile;
    /// use std::io::Write;
    /// # fn main() -> std::io::Result<()> {
    /// let mut file = NamedTempFile::new()?;
    /// let items = ["ace", "acf", "adg", "adh", "bjk"];
    /// let btm = PathMap::from_iter(items.iter().map(|i| (i, ())));
    /// let tree1 = ArenaCompactTree::from_zipper(btm.read_zipper(), |_v| 0);
    /// file.write_all(tree1.get_data())?;
    /// let tree_path = file.path();
    /// let tree2 = ArenaCompactTree::open_mmap(tree_path)?;
    /// assert_eq!(tree1.get_data(), tree2.get_data());
    /// # Ok(())
    /// # }
    /// ```
    pub fn open_mmap(path: impl AsRef<Path>) -> std::io::Result<Self> {
        let file = std::fs::File::open(&path)?;
        let memmap = unsafe { Mmap::map(&file) }?;
        if &memmap[..MAGIC_LENGTH] != &COMPACT_TREE_MAGIC {
            return Err(std::io::Error::other("Invalid file magic"));
        }
        Ok(Self {
            position: memmap.as_ref().len() as u64,
            storage: memmap,
            line_map: Default::default(),
            lines: Default::default(),
            hasher: Default::default(),
            value: Cell::new(0),
            counters: Counters::default(),
        })
    }


    /// ```
    /// use pathmap::{PathMap, arena_compact::ArenaCompactTree};
    /// use tempfile::NamedTempFile;
    /// use std::io::Write;
    /// # fn main() -> std::io::Result<()> {
    /// let mut file = NamedTempFile::new()?;
    /// let tree_path = "test_tree.tree";
    /// let items = ["ace", "acf", "adg", "adh", "bjk"];
    /// let btm = PathMap::from_iter(items.iter().map(|i| (i, ())));
    /// let tree1 = ArenaCompactTree::dump_from_zipper(
    ///     btm.read_zipper(), |_v| 0, tree_path)?;
    /// let tree2 = ArenaCompactTree::from_zipper(
    ///     btm.read_zipper(), |_v| 0);
    /// assert_eq!(tree1.get_data(), tree2.get_data());
    /// # Ok(())
    /// # }
    /// ```
    pub fn dump_from_zipper<V, Z, F, P>(
        zipper: Z, map_val: F, path: P
    ) -> Result<Self, std::io::Error>
        where
            V: Clone + Send + Sync + Unpin,
            Z: Catamorphism<V>,
            F: Fn(&V) -> u64,
            P: AsRef<Path>
    {
        let arena = dump_arena_tree(zipper, map_val, path)?;
        let file = arena.storage.buf_writer.into_inner()?;
        let memmap = unsafe { Mmap::map(&file) }?;
        if &memmap[..MAGIC_LENGTH] != &COMPACT_TREE_MAGIC {
            return Err(std::io::Error::other("Invalid file magic"));
        }
        Ok(Self {
            position: memmap.as_ref().len() as u64,
            storage: memmap,
            line_map: Default::default(),
            lines: Default::default(),
            hasher: Default::default(),
            value: Cell::new(0),
            counters: arena.counters,
        })
    }
}

#[derive(Clone, Debug)]
pub enum Node {
    Line(NodeLine),
    Branch(NodeBranch),
}

impl Node {
    pub fn child_count(&self) -> usize {
        match self {
            Node::Line(line) => if line.child.is_some() { 1 } else { 0 },
            Node::Branch(node) => node.bytemask.count_bits(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct NodeLine {
    pub path: LineId,
    // pub footprint: u64,
    pub value: Option<u64>,
    pub child: Option<NodeId>,
}

impl NodeLine {
    pub fn empty() -> Self {
        Self {
            path: INVALID_LINE,
            // footprint: 0,
            value: None,
            child: None,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct NodeBranch {
    pub bytemask: ByteMask,
    pub first_child: Option<NodeId>,
    // pub footprint: u64,
    pub value: Option<u64>,
}

impl NodeBranch {
    pub fn empty() -> Self {
        Self {
            bytemask: ByteMask::EMPTY,
            first_child: None,
            // footprint: 0,
            value: None,
        }
    }
}

// benchmark for morphisms (caching/side, jumping/plain)
// val_count ?
fn build_arena_tree<V, Z, F>(zipper: Z, map_val: F) -> ArenaCompactTree<Vec<u8>>
    where
        V: Clone + Send + Sync + Unpin,
        Z: Catamorphism<V>,
        F: Fn(&V) -> u64,
{
    let mut arena = ArenaCompactTree::new();
    let map_val = &map_val;
    let root = zipper.into_cata_jumping_side_effect::<Node, _>(|bm, children, jump, v, path| {
        let mut first_child: Option<NodeId> = None;
        for child in children.iter() {
            let id = arena.push_v(child);
            first_child = first_child.or(Some(id));
        }
        let node = NodeBranch {
            bytemask: ByteMask::from(*bm),
            first_child,
            value: v.map(map_val),
        };
        if jump == 0 {
            return Node::Branch(node);
        }

        let mut line = NodeLine::empty();
        line.path = arena.add_path(&path[path.len() - jump..]);

        if !children.is_empty() {
            first_child = Some(arena.push_v(&Node::Branch(node)));
        } else {
            line.value = v.map(map_val);
        }

        line.child = first_child;
        Node::Line(line)
    });
    let _root_id = arena.set_root(&root);
    arena.finalize().unwrap();
    arena
}

use std::io::{BufWriter, Seek, SeekFrom};
use std::fs::{File, OpenOptions};

pub struct FileDumper {
    buf_writer: BufWriter<File>,
    line_buf: Vec<u8>,
    line_map: HashMap::<u64, (usize, usize, LineId)>,
}

impl Write for FileDumper {
    fn write(&mut self, data: &[u8]) -> Result<usize, std::io::Error> {
        self.buf_writer.write(data)
    }

    fn flush(&mut self) -> Result<(), std::io::Error> {
        self.buf_writer.flush()
    }
}

/// BufWriter buffer size. The default of 8KiB is too small.
const DUMPER_BUFFER_SIZE: usize = 4*1024*1024;
impl ArenaCompactTree<FileDumper> {
    fn open(path: impl AsRef<Path>) -> Result<Self, std::io::Error> {
        let mut file = OpenOptions::new()
            .read(true).write(true)
            .create(true).truncate(true)
            .open(path)?;
        file.seek(SeekFrom::Start(0))?;
        file.write_all(&COMPACT_TREE_MAGIC)?;
        file.write_all(&[0; 8])?;
        let position = file.stream_position()?;
        let buf_writer = BufWriter::with_capacity(DUMPER_BUFFER_SIZE, file);
        let storage = FileDumper {
            buf_writer,
            line_buf: Default::default(),
            line_map: Default::default(),
        };
        let act = ArenaCompactTree {
            storage,
            position,
            line_map: HashMap::new(),
            hasher: GxHasher::default(),
            lines: 0,
            counters: Counters::default(),
            value: Cell::new(0),
        };
        Ok(act)
    }

    fn set_root(&mut self, node: &Node) -> Result<NodeId, std::io::Error> {
        let node_id = self.push(node)?;
        self.storage.buf_writer.seek(SeekFrom::Start(8))?;
        self.storage.write_all(&node_id.0.to_le_bytes())?;
        self.storage.buf_writer.seek(SeekFrom::Start(self.position))?;
        Ok(node_id)
    }

    fn add_path(
        &mut self, path: impl AsRef<[u8]>
    ) -> Result<LineId, std::io::Error> {
        let path = path.as_ref();
        let mut hasher = self.hasher.clone();
        hasher.write(path);
        let hash = hasher.finish();
        if let Some(&(start, len, prev)) = self.storage.line_map.get(&hash) {
            let buf = &self.storage.line_buf[start..start+len];
            if buf == path {
                self.counters.add_line_data_reuse(path.len());
                return Ok(prev);
            }
        }
        let line_id = LineId(self.position);
        let line_start = self.storage.line_buf.len();
        self.storage.line_buf.extend_from_slice(path);
        let lenlen = push_varint_u64(
            &mut self.storage, path.len() as u64
        )? as u64;
        self.position += lenlen;
        self.storage.write_all(path)?;
        self.position += path.len() as u64;
        self.counters.add_line_data(lenlen as usize + path.len());
        self.storage.line_map.insert(hash, (line_start, path.len(), line_id));
        Ok(line_id)
    }
}

fn dump_arena_tree<V, Z, F, P>(
    zipper: Z, map_val: F, path: P
) -> Result<ArenaCompactTree<FileDumper>, std::io::Error>
    where
        V: Clone + Send + Sync + Unpin,
        Z: Catamorphism<V>,
        F: Fn(&V) -> u64,
        P: AsRef<Path>,
{
    // A bit of code duplication compared to build_arena_tree
    let mut arena = ArenaCompactTree::<FileDumper>::open(path)?;
    let map_val = &map_val;
    let root = zipper.into_cata_jumping_side_effect_fallible::<Node, std::io::Error, _>(|bm, children, jump, v, path| {
        let mut first_child: Option<NodeId> = None;
        for child in children.iter() {
            let id = arena.push(child)?;
            first_child = first_child.or(Some(id));
        }
        let node = NodeBranch {
            bytemask: ByteMask::from(*bm),
            first_child,
            value: v.map(map_val),
        };
        if jump == 0 {
            return Ok(Node::Branch(node));
        }

        let mut line = NodeLine::empty();
        line.path = arena.add_path(&path[path.len() - jump..])?;

        if !children.is_empty() {
            first_child = Some(arena.push(&Node::Branch(node))?);
        } else {
            line.value = v.map(map_val);
        }

        line.child = first_child;
        Ok(Node::Line(line))
    })?;

    let _root_id = arena.set_root(&root)?;
    arena.finalize().unwrap();
    Ok(arena)
}

impl ArenaCompactTree<Mmap> {
    /// Merge a zipper's trie into the existing ACT file at `path`, appending
    /// only the new data and updating the root pointer.
    ///
    /// The old file contents are never rewritten: since all node references
    /// are backward relative offsets, appended nodes can point into the
    /// existing arena, and subtrees the zipper does not touch are shared
    /// byte-for-byte. Only the nodes along changed paths (plus their sibling
    /// runs, which the format requires to be contiguous) are appended, and
    /// the root offset at byte 8 is rewritten to the new root.
    ///
    /// Each merge also appends a `[previous_suffix, previous_root]` trailer
    /// recording the pre-merge root, chaining the roots into a singly-linked
    /// list that [`Self::root_history`] walks.
    ///
    /// Where both tries hold a value on the same path, the zipper's value
    /// wins. If the zipper adds nothing, the file is left untouched.
    ///
    /// Returns the updated tree, memory-mapped from the merged file.
    ///
    /// # Examples
    /// ```
    /// use pathmap::{PathMap, arena_compact::ArenaCompactTree};
    /// # fn main() -> std::io::Result<()> {
    /// let dir = tempfile::tempdir()?;
    /// let file = dir.path().join("merge.act");
    /// let base = PathMap::from_iter([("apple", 1u64), ("banana", 2)]);
    /// let act = ArenaCompactTree::from_zipper(base.read_zipper(), |&v| v);
    /// std::fs::write(&file, act.get_data())?;
    ///
    /// let update = PathMap::from_iter([("apricot", 3u64), ("banana", 20)]);
    /// let merged = ArenaCompactTree::merge_zipper_into_file(
    ///     &file, update.read_zipper(), |&v| v)?;
    /// assert_eq!(merged.get_val_at("apple"), Some(1));
    /// assert_eq!(merged.get_val_at("apricot"), Some(3));
    /// assert_eq!(merged.get_val_at("banana"), Some(20)); // zipper value wins
    /// # Ok(())
    /// # }
    /// ```
    pub fn merge_zipper_into_file<V, Z, F, P>(
        path: P, zipper: Z, map_val: F,
    ) -> Result<Self, std::io::Error>
    where
        Z: Zipper + ZipperMoving + ZipperValues<V>,
        F: Fn(&V) -> u64,
        P: AsRef<Path>,
    {
        let file = OpenOptions::new().read(true).write(true).open(&path)?;
        let old_map = unsafe { Mmap::map(&file) }?;
        let old = old_map.as_ref();
        if old.len() < MAGIC_LENGTH + U64_SIZE + MAX_VARINT_SIZE
            || &old[..MAGIC_LENGTH] != &COMPACT_TREE_MAGIC
        {
            return Err(std::io::Error::other("Invalid file magic"));
        }
        let root_buf: [u8; U64_SIZE] = old[MAGIC_LENGTH..][..U64_SIZE].try_into().unwrap();
        let root_id = NodeId(u64::from_le_bytes(root_buf));

        // Was the old file itself produced by a merge? A base file ends with the
        // zero padding, so its final u64 is zero; a merged file records a
        // non-zero `previous_root` there. When it is a merged file, its trailer
        // begins `ROOT_TRAILER_SIZE` bytes from the end, and the new trailer's
        // `previous_suffix` links back to it, extending the root chain.
        let old_len = old.len();
        let old_prev_root: [u8; U64_SIZE] = old[old_len - U64_SIZE..].try_into().unwrap();
        let previous_suffix = if u64::from_le_bytes(old_prev_root) != 0 {
            (old_len - ROOT_TRAILER_SIZE) as u64
        } else {
            0
        };

        let mut out = BufWriter::with_capacity(DUMPER_BUFFER_SIZE, file);
        out.seek(SeekFrom::End(0))?;
        let mut merger = ZipperMerger {
            old,
            out,
            position: old.len() as u64,
            zipper,
            map_val,
            counters: Counters::default(),
            _marker: PhantomData,
        };
        let (merged, changed) = merger.merge_node(root_id)?;
        if changed {
            let new_root = merger.push_merged(merged)?;
            // Append the `[previous_suffix, previous_root]` trailer. It records
            // the pre-merge root so the roots form a walkable linked list (see
            // `root_history`), and its `ROOT_TRAILER_SIZE` bytes also satisfy
            // the trailing-padding invariant the varint reader relies on.
            merger.out.write_all(&previous_suffix.to_le_bytes())?;
            merger.out.write_all(&root_id.0.to_le_bytes())?;
            merger.out.seek(SeekFrom::Start(MAGIC_LENGTH as u64))?;
            merger.out.write_all(&new_root.0.to_le_bytes())?;
        }
        let ZipperMerger { out, counters, .. } = merger;
        let file = out.into_inner()?;
        drop(old_map);
        let memmap = unsafe { Mmap::map(&file) }?;
        Ok(Self {
            position: memmap.as_ref().len() as u64,
            storage: memmap,
            line_map: Default::default(),
            lines: Default::default(),
            hasher: Default::default(),
            value: Cell::new(0),
            counters,
        })
    }
}

/// A single in-construction trie node used by [ACTOutputStream]
///
/// One frame exists per byte of the most recently pushed path. A frame
/// accumulates completed child subtrees (in ascending byte order, which the
/// sorted input guarantees) until the input stream moves past it, at which
/// point it is sealed and written to the arena.
struct StreamFrame {
    /// Bytes of the children attached so far
    mask: ByteMask,
    /// Completed child nodes, parallel to the set bits of `mask` (ascending)
    children: Vec<Node>,
    /// Value at this node, if the exact path was pushed
    value: Option<u64>,
}

impl StreamFrame {
    fn empty() -> Self {
        StreamFrame {
            mask: ByteMask::EMPTY,
            children: Vec::new(),
            value: None,
        }
    }

    /// A frame with no children and no value is a pure pass-through and can
    /// be folded into a line node instead of becoming a branch node
    fn is_passthrough(&self) -> bool {
        self.mask.is_empty_mask() && self.value.is_none()
    }
}

/// Builds an [ArenaCompactTree] on disk from a stream of ordered paths.
///
/// Paths must be pushed in strictly increasing lexicographic (byte) order.
/// Memory usage is bounded by the longest path pushed (plus the line-reuse
/// cache), so this can build tries far larger than available RAM.
///
/// # Examples
/// ```
/// use pathmap::arena_compact::ACTOutputStream;
/// # fn main() -> std::io::Result<()> {
/// let dir = tempfile::tempdir()?;
/// let file = dir.path().join("file.act");
/// let mut b = ACTOutputStream::new(&file)?;
/// b.push("123")?;
/// b.push("124")?;
/// let tree = b.finish()?;
/// assert_eq!(tree.get_val_at("123"), Some(0));
/// assert_eq!(tree.get_val_at("124"), Some(0));
/// assert_eq!(tree.get_val_at("125"), None);
/// # Ok(())
/// # }
/// ```
pub struct ACTOutputStream {
    act: ArenaCompactTree<FileDumper>,
    /// `stack[d]` is the in-construction node at depth `d` along `prev_path`;
    /// `stack[0]` is the root
    stack: Vec<StreamFrame>,
    /// The most recently pushed path
    prev_path: Vec<u8>,
    /// Number of paths pushed so far
    count: u64,
}

impl ACTOutputStream {
    /// Create (or truncate) the file at `path` and start streaming a trie into it
    pub fn new(path: impl AsRef<Path>) -> Result<Self, std::io::Error> {
        Ok(ACTOutputStream {
            act: ArenaCompactTree::<FileDumper>::open(path)?,
            stack: Vec::from([StreamFrame::empty()]),
            prev_path: Vec::new(),
            count: 0,
        })
    }

    /// Add `path` to the trie with a value of `0`
    ///
    /// Paths must arrive in strictly increasing lexicographic order,
    /// otherwise an [InvalidInput](std::io::ErrorKind::InvalidInput) error
    /// is returned. A path that extends the previous one (e.g. `"ab"` after
    /// `"a"`) is fine; both keep their values.
    pub fn push(&mut self, path: impl AsRef<[u8]>) -> Result<(), std::io::Error> {
        self.push_val(path, 0)
    }

    /// Add `path` to the trie with the given `value`
    ///
    /// See [push](Self::push) for the ordering requirements.
    pub fn push_val(
        &mut self, path: impl AsRef<[u8]>, value: u64,
    ) -> Result<(), std::io::Error> {
        let path = path.as_ref();
        if self.count > 0 && path <= &self.prev_path[..] {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "paths must be pushed in strictly increasing order",
            ));
        }
        let common = find_prefix_overlap(path, &self.prev_path);
        self.collapse_to(common)?;
        for _ in common..path.len() {
            self.stack.push(StreamFrame::empty());
        }
        self.stack.last_mut().unwrap().value = Some(value);
        self.prev_path.truncate(common);
        self.prev_path.extend_from_slice(&path[common..]);
        self.count += 1;
        Ok(())
    }

    /// Seal every frame deeper than `target`, writing completed subtrees to
    /// the arena and attaching them as children of the frame at `target`
    fn collapse_to(&mut self, target: usize) -> Result<(), std::io::Error> {
        while self.stack.len() - 1 > target {
            let top = self.stack.len() - 1;
            let frame = self.stack.pop().unwrap();
            let node = self.seal(frame)?;
            // Fold pure pass-through ancestors into a line segment
            while self.stack.len() - 1 > target
                && self.stack.last().unwrap().is_passthrough()
            {
                self.stack.pop();
            }
            let start = self.stack.len() - 1;
            // `prev_path[start]` goes into the parent's mask; if the chain is
            // longer, the remaining bytes become line data
            let node = if top - start >= 2 {
                let mut line = NodeLine::empty();
                line.path = self.act.add_path(&self.prev_path[start + 1..top])?;
                match node {
                    Node::Branch(branch) if branch.bytemask.is_empty_mask() => {
                        line.value = branch.value;
                    }
                    node => {
                        line.child = Some(self.act.push(&node)?);
                    }
                }
                Node::Line(line)
            } else {
                node
            };
            let parent = self.stack.last_mut().unwrap();
            parent.mask.set_bit(self.prev_path[start]);
            parent.children.push(node);
        }
        Ok(())
    }

    /// Write `frame`'s children to the arena (contiguously, so that
    /// `first_child` suffices to address them) and return the branch node
    fn seal(&mut self, frame: StreamFrame) -> Result<Node, std::io::Error> {
        let mut first_child: Option<NodeId> = None;
        for child in frame.children.iter() {
            let id = self.act.push(child)?;
            first_child = first_child.or(Some(id));
        }
        Ok(Node::Branch(NodeBranch {
            bytemask: frame.mask,
            first_child,
            value: frame.value,
        }))
    }

    /// Seal the remaining frames, write the root, and flush to disk
    ///
    /// Returns the finished tree, memory-mapped from the written file.
    pub fn finish(mut self) -> Result<ArenaCompactTree<Mmap>, std::io::Error> {
        self.collapse_to(0)?;
        let root_frame = self.stack.pop().unwrap();
        let root = self.seal(root_frame)?;
        self.act.set_root(&root)?;
        self.act.finalize()?;
        let ArenaCompactTree { storage, counters, .. } = self.act;
        let file = storage.buf_writer.into_inner()?;
        let memmap = unsafe { Mmap::map(&file) }?;
        Ok(ArenaCompactTree {
            position: memmap.as_ref().len() as u64,
            storage: memmap,
            line_map: Default::default(),
            lines: Default::default(),
            hasher: Default::default(),
            value: Cell::new(0),
            counters,
        })
    }
}

#[cfg(feature="nightly")]
#[path="arena_compact_nightly.rs"]
mod arena_compact_nightly;
#[cfg(feature="nightly")]
pub use arena_compact_nightly::*;

/// A merged subtree: either an existing node reused as-is, or a freshly
/// built node (whose descendants have already been appended).
enum Merged {
    /// Reuse the old subtree at this id. When placed into a sibling run the
    /// node itself is shallow-copied (the format requires siblings to be
    /// contiguous), but everything below it stays shared with the old file.
    Reuse(NodeId),
    /// A new node to append; references old and new data by absolute id.
    Fresh(Node),
}

/// State for [ArenaCompactTree::merge_zipper_into_file]: reads the old arena
/// through `old`, appends through `out`, and walks `zipper` in lockstep with
/// the old trie. Every merge method returns the zipper to its entry position.
struct ZipperMerger<'a, V, Z, F> {
    old: &'a [u8],
    out: BufWriter<File>,
    /// Append position: the absolute offset the next object will get
    position: u64,
    zipper: Z,
    map_val: F,
    counters: Counters,
    _marker: PhantomData<fn(&V) -> u64>,
}

impl<'a, V, Z, F> ZipperMerger<'a, V, Z, F>
where
    Z: Zipper + ZipperMoving + ZipperValues<V>,
    F: Fn(&V) -> u64,
{
    fn old_node(&self, id: NodeId) -> (Node, usize) {
        read_node(&self.old[id.0 as usize..], id)
    }

    fn old_line(&self, id: LineId) -> &'a [u8] {
        let old: &'a [u8] = self.old;
        let start = &old[id.0 as usize..];
        let (len, off) = read_varint_u64(start);
        &start[off..off + len as usize]
    }

    /// The zipper's value at its current focus, mapped to `u64`
    fn z_val(&self) -> Option<u64> {
        self.zipper.val().map(|v| (self.map_val)(v))
    }

    /// Append a node; all ids it references must be below `self.position`
    fn push_fresh(&mut self, node: &Node) -> Result<NodeId, std::io::Error> {
        let node_id = NodeId(self.position);
        let mut cursor = std::io::Cursor::new([0; MAX_BRANCH_NODE_SIZE]);
        match node {
            Node::Branch(branch) => {
                ArenaCompactTree::<Vec<u8>>::write_node(
                    &mut cursor, branch, node_id, &mut self.counters)?;
            }
            Node::Line(line) => {
                ArenaCompactTree::<Vec<u8>>::write_line(
                    &mut cursor, line, node_id, &mut self.counters)?;
            }
        }
        let len = cursor.position();
        self.out.write_all(&cursor.get_ref()[..len as usize])?;
        self.position += len;
        Ok(node_id)
    }

    /// Append a merged child as part of a sibling run. `Reuse` becomes a
    /// shallow copy: same value/mask/line, child pointers into the old file.
    fn push_merged(&mut self, merged: Merged) -> Result<NodeId, std::io::Error> {
        match merged {
            Merged::Fresh(node) => self.push_fresh(&node),
            Merged::Reuse(id) => {
                let (node, _) = self.old_node(id);
                self.push_fresh(&node)
            }
        }
    }

    /// Append line data, returning its id
    fn add_line_data(&mut self, data: &[u8]) -> Result<LineId, std::io::Error> {
        debug_assert!(!data.is_empty());
        let line_id = LineId(self.position);
        let lenlen = push_varint_u64(&mut self.out, data.len() as u64)?;
        self.out.write_all(data)?;
        self.position += (lenlen + data.len()) as u64;
        Ok(line_id)
    }

    /// Merge the zipper's current position with the old node `id`.
    /// Returns the merged subtree and whether anything changed; when nothing
    /// changed, nothing has been appended and the old node is reused.
    fn merge_node(&mut self, id: NodeId) -> Result<(Merged, bool), std::io::Error> {
        match self.old_node(id).0 {
            Node::Branch(branch) => self.merge_branch(id, branch),
            Node::Line(line) => match self.merge_line_from(&line, 0)? {
                Some(merged) => Ok((merged, true)),
                None => Ok((Merged::Reuse(id), false)),
            },
        }
    }

    fn merge_branch(
        &mut self, id: NodeId, branch: NodeBranch,
    ) -> Result<(Merged, bool), std::io::Error> {
        let z_mask = self.zipper.child_mask();
        let value = self.z_val().or(branch.value);
        let mut changed = value != branch.value;

        // Ids of the old children (siblings are stored sequentially)
        let mut old_kids = Vec::with_capacity(branch.bytemask.count_bits());
        if let Some(first) = branch.first_child {
            let mut cur = first;
            for _ in 0..branch.bytemask.count_bits() {
                old_kids.push(cur);
                let (_, len) = self.old_node(cur);
                cur = NodeId(cur.0 + len as u64);
            }
        }

        let union = branch.bytemask.or(&z_mask);
        let mut children: Vec<Merged> = Vec::with_capacity(union.count_bits());
        let mut old_idx = 0;
        for byte in union.iter() {
            let in_old = branch.bytemask.test_bit(byte);
            let in_new = z_mask.test_bit(byte);
            if in_old {
                let child_id = old_kids[old_idx];
                old_idx += 1;
                if in_new {
                    self.zipper.descend_to_byte(byte);
                    let (merged, child_changed) = self.merge_node(child_id)?;
                    self.zipper.ascend_byte();
                    changed |= child_changed;
                    children.push(merged);
                } else {
                    children.push(Merged::Reuse(child_id));
                }
            } else {
                changed = true;
                self.zipper.descend_to_byte(byte);
                let node = self.fresh_subtree()?;
                self.zipper.ascend_byte();
                children.push(Merged::Fresh(node));
            }
        }
        if !changed {
            return Ok((Merged::Reuse(id), false));
        }
        let mut first_child = None;
        for child in children {
            let child_id = self.push_merged(child)?;
            first_child = first_child.or(Some(child_id));
        }
        let node = NodeBranch { bytemask: union, first_child, value };
        Ok((Merged::Fresh(Node::Branch(node)), true))
    }

    /// Merge the zipper (positioned `k` bytes into `line`'s segment) with the
    /// remainder of the line. Returns `None` when the zipper adds nothing
    /// (in which case nothing has been appended).
    fn merge_line_from(
        &mut self, line: &NodeLine, k: usize,
    ) -> Result<Option<Merged>, std::io::Error> {
        let data = self.old_line(line.path);
        let len = data.len();
        // Scan forward while the zipper follows the segment exactly
        let mut j = k;
        while j < len && self.z_val().is_none() && {
            let z_mask = self.zipper.child_mask();
            z_mask.count_bits() == 1 && z_mask.test_bit(data[j])
        } {
            self.zipper.descend_to_byte(data[j]);
            j += 1;
        }

        let inner: Option<Merged> = if j == len {
            // Reached the end of the segment
            if let Some(child) = line.child {
                let (merged, child_changed) = self.merge_node(child)?;
                child_changed.then_some(merged)
            } else {
                // Old leaf; the zipper may update the value or extend below
                let z_mask = self.zipper.child_mask();
                let value = self.z_val().or(line.value);
                if value == line.value && z_mask.is_empty_mask() {
                    None
                } else {
                    let mut fresh = Vec::with_capacity(z_mask.count_bits());
                    for byte in z_mask.iter() {
                        self.zipper.descend_to_byte(byte);
                        fresh.push(self.fresh_subtree()?);
                        self.zipper.ascend_byte();
                    }
                    let mut first_child = None;
                    for node in &fresh {
                        let child_id = self.push_fresh(node)?;
                        first_child = first_child.or(Some(child_id));
                    }
                    let node = NodeBranch { bytemask: z_mask, first_child, value };
                    Some(Merged::Fresh(Node::Branch(node)))
                }
            }
        } else {
            // The zipper diverges at segment offset `j`
            let b_old = data[j];
            let z_mask = self.zipper.child_mask();
            let z_val = self.z_val();
            let matched = z_mask.test_bit(b_old);
            let cont: Option<Merged> = if matched {
                self.zipper.descend_to_byte(b_old);
                let merged = self.merge_line_from(line, j + 1)?;
                self.zipper.ascend_byte();
                merged
            } else {
                None
            };
            let extras = z_mask.count_bits() - (matched as usize);
            if z_val.is_none() && extras == 0 && cont.is_none() {
                None
            } else {
                // Build a branch at offset `j`: the old segment continuation
                // plus whatever the zipper adds here
                let mut cont = Some(match cont {
                    Some(merged) => merged,
                    None => self.tail_child(line, data, j + 1)?,
                });
                let mut mask = z_mask;
                mask.set_bit(b_old);
                let mut children: Vec<Merged> = Vec::with_capacity(mask.count_bits());
                for byte in mask.iter() {
                    if byte == b_old {
                        children.push(cont.take().unwrap());
                    } else {
                        self.zipper.descend_to_byte(byte);
                        let node = self.fresh_subtree()?;
                        self.zipper.ascend_byte();
                        children.push(Merged::Fresh(node));
                    }
                }
                let mut first_child = None;
                for child in children {
                    let child_id = self.push_merged(child)?;
                    first_child = first_child.or(Some(child_id));
                }
                let node = NodeBranch { bytemask: mask, first_child, value: z_val };
                Some(Merged::Fresh(Node::Branch(node)))
            }
        };

        self.zipper.ascend(j - k);
        let Some(inner) = inner else { return Ok(None) };
        if j == k {
            return Ok(Some(inner));
        }
        // Wrap the merged node in a line for the matched prefix data[k..j];
        // reuse the old line data when the whole segment matched.
        let path_id = if k == 0 && j == len {
            line.path
        } else {
            self.add_line_data(&data[k..j])?
        };
        let node = match inner {
            Merged::Fresh(Node::Branch(branch)) if branch.bytemask.is_empty_mask() => {
                Node::Line(NodeLine { path: path_id, value: branch.value, child: None })
            }
            inner => {
                let child_id = self.push_merged(inner)?;
                Node::Line(NodeLine { path: path_id, value: None, child: Some(child_id) })
            }
        };
        Ok(Some(Merged::Fresh(node)))
    }

    /// The old, unmerged continuation of `line` from segment offset `k`,
    /// packaged so it can sit in a new sibling run
    fn tail_child(
        &mut self, line: &NodeLine, data: &[u8], k: usize,
    ) -> Result<Merged, std::io::Error> {
        if k == data.len() {
            Ok(match line.child {
                Some(child) => Merged::Reuse(child),
                None => Merged::Fresh(Node::Branch(NodeBranch {
                    bytemask: ByteMask::EMPTY,
                    first_child: None,
                    value: line.value,
                })),
            })
        } else {
            let path_id = self.add_line_data(&data[k..])?;
            Ok(Merged::Fresh(Node::Line(NodeLine {
                path: path_id,
                value: if line.child.is_none() { line.value } else { None },
                child: line.child,
            })))
        }
    }

    /// Serialize the zipper's current subtree (absent from the old trie),
    /// compressing single-child chains into line nodes. Descendants are
    /// appended; the returned node is pushed by the caller's sibling run.
    fn fresh_subtree(&mut self) -> Result<Node, std::io::Error> {
        let mut segment: Vec<u8> = Vec::new();
        loop {
            if self.z_val().is_some() {
                break;
            }
            let mask = self.zipper.child_mask();
            if mask.count_bits() != 1 {
                break;
            }
            let byte = mask.iter().next().unwrap();
            segment.push(byte);
            self.zipper.descend_to_byte(byte);
        }
        let value = self.z_val();
        let mask = self.zipper.child_mask();
        let mut children = Vec::with_capacity(mask.count_bits());
        for byte in mask.iter() {
            self.zipper.descend_to_byte(byte);
            children.push(self.fresh_subtree()?);
            self.zipper.ascend_byte();
        }
        let mut first_child = None;
        for child in &children {
            let child_id = self.push_fresh(child)?;
            first_child = first_child.or(Some(child_id));
        }
        let branch = NodeBranch { bytemask: mask, first_child, value };
        let node = if segment.is_empty() {
            Node::Branch(branch)
        } else {
            let path_id = self.add_line_data(&segment)?;
            if mask.is_empty_mask() {
                Node::Line(NodeLine { path: path_id, value, child: None })
            } else {
                let child_id = self.push_fresh(&Node::Branch(branch))?;
                Node::Line(NodeLine { path: path_id, value: None, child: Some(child_id) })
            }
        };
        self.zipper.ascend(segment.len());
        Ok(node)
    }
}

/*
fn tree_to_btm(tree: &ArenaCompactTree) -> PathMap<()> {
    struct PathIdx(NodeId, usize)
    let (_root, root_id) = tree.get_root();
    PathMap::<()>::new_from_ana(PathIdx(root_id, 0), |PathIdx(node_id, depth), val, children, _path| {
        match tree.get_node(node_id) {
            Node::Line(line) => {
                *val = line.value.map(|_| ());
            }
            Node::Branch(node) => {
                *val = node.value.map(|_| ());
            }
        }
    })
}
*/
#[derive(Clone, Debug)]
struct StackFrame {
    node_id: NodeId,
    child_count: usize,
    child_index: usize,
    next_id: Option<NodeId>,
    node_depth: usize,
}
impl StackFrame {
    fn from(node: &Node, node_id: NodeId) -> Self {
        StackFrame {
            node_id,
            child_count: node.child_count(),
            child_index: 0,
            next_id: None,
            node_depth: 0,
        }
    }
}

pub struct ACTZipper<'tree, Storage, Value>
where Storage: AsRef<[u8]>
{
    tree: &'tree ArenaCompactTree<Storage>,
    cur_node: Node,
    stack: Vec<StackFrame>,
    path: Vec<u8>,
    origin_depth: usize,
    origin_node_depth: usize,
    pub invalid: usize,
    _marker: PhantomData<Value>,
}

impl<'tree, Storage, Value> Clone for ACTZipper<'tree, Storage, Value>
where Storage: AsRef<[u8]>
{
    fn clone(&self) -> Self {
        let Self {
            tree, cur_node, stack, path,
            origin_depth, origin_node_depth, invalid, ..
        } = self;
        Self {
            tree,
            cur_node: cur_node.clone(),
            stack: stack.clone(),
            path: path.clone(),
            origin_depth: *origin_depth,
            origin_node_depth: *origin_node_depth,
            invalid: *invalid,
            _marker: PhantomData,
        }
    }
}

impl<Storage> ArenaCompactTree<Storage>
where Storage: AsRef<[u8]>
{
    #[inline]
    pub fn read_zipper_u64<'tree>(&'tree self) -> ACTZipper<'tree, Storage, u64> {
        ACTZipper::from_tree(self)
    }

    #[inline]
    pub fn read_zipper_at_path_u64<'tree>(&'tree self, path: &[u8]) -> ACTZipper<'tree, Storage, u64> {
        let mut rz = ACTZipper::from_tree(self);
        rz.descend_to(path);
        rz.with_root_here()
    }

    #[inline]
    pub fn read_zipper_at_borrowed_path_u64<'tree>(&'tree self, path: &[u8]) -> ACTZipper<'tree, Storage, u64> {
        self.read_zipper_at_path_u64(path)
    }

    #[inline]
    pub fn read_zipper<'tree>(&'tree self) -> ACTZipper<'tree, Storage, ()> {
        ACTZipper::from_tree(self)
    }

    #[inline]
    pub fn read_zipper_at_path<'tree>(&'tree self, path: &[u8]) -> ACTZipper<'tree, Storage, ()> {
        let mut rz = ACTZipper::from_tree(self);
        rz.descend_to(path);
        rz.with_root_here()
    }

    #[inline]
    pub fn read_zipper_at_borrowed_path<'tree>(&'tree self, path: &[u8]) -> ACTZipper<'tree, Storage, ()> {
        self.read_zipper_at_path(path)
    }
}

impl<'tree, Storage, Value> ACTZipper<'tree, Storage, Value>
where Storage: AsRef<[u8]>
{
    fn from_tree(tree: &'tree ArenaCompactTree<Storage>) -> Self {
        let (cur_node, node_id) = tree.get_root();
        let stack_frame = StackFrame::from(&cur_node, node_id);
        ACTZipper {
            tree, cur_node,
            path: Vec::new(),
            invalid: 0,
            origin_depth: 0,
            origin_node_depth: 0,
            stack: Vec::from([stack_frame]),
            _marker: PhantomData,
        }
    }

    fn with_root_here(mut self) -> Self {
        self.origin_depth = self.path.len();
        if self.stack.len() > 1 {
            let last = self.stack.len() - 1;
            self.stack.swap(0, last);
            self.stack.truncate(1);
        }
        self.origin_node_depth = self.stack[0].node_depth;
        self
    }
}

impl<'tree, Storage> ZipperReadOnlyConditionalValues<'tree, ()> for ACTZipper<'tree, Storage, ()>
where Storage: AsRef<[u8]>
{
    type WitnessT = ();
    fn witness<'w>(&self) -> Self::WitnessT {}
    fn get_val_with_witness<'w>(&self, _witness: &'w Self::WitnessT) -> Option<&'w ()> where 'tree: 'w {
        self.get_val()
    }
}

impl<'tree, Storage> ZipperReadOnlyConditionalValues<'tree, u64> for ACTZipper<'tree, Storage, u64>
where Storage: AsRef<[u8]>
{
    type WitnessT = ();
    fn witness<'w>(&self) -> Self::WitnessT {}
    fn get_val_with_witness<'w>(&self, _witness: &'w Self::WitnessT) -> Option<&'w u64> where 'tree: 'w {
        self.get_val()
    }
}

impl<'tree, Storage, Value> Zipper for ACTZipper<'tree, Storage, Value>
where Storage: AsRef<[u8]>
{
    /// Returns `true` if the zipper's focus is on a path within the trie, otherwise `false`
    fn path_exists(&self) -> bool {
        self.invalid == 0
    }

    /// Returns `true` if there is a value at the zipper's focus, otherwise `false`
    fn is_val(&self) -> bool {
        if self.invalid > 0 {
            return false;
        }
        match &self.cur_node {
            Node::Branch(node) => {
                node.value.is_some()
            }
            Node::Line(line) => {
                if line.value.is_none() {
                    false
                } else {
                    let last = self.stack.last().unwrap();
                    let line = self.tree.get_line(line.path);
                    line.len() == last.node_depth
                }
            }
        }
    }

    /// Returns the number of child branches from the focus node
    ///
    /// Returns 0 if the focus is on a leaf
    fn child_count(&self) -> usize {
        if self.invalid > 0 {
            return 0;
        }
        match &self.cur_node {
            Node::Branch(node) => {
                node.bytemask.count_bits()
            }
            Node::Line(path) => {
                let last = self.stack.last().unwrap();
                let path = self.tree.get_line(path.path);
                if last.node_depth < path.len() {
                    1
                } else {
                    0
                }
            }
        }
    }

    /// Returns 256-bit mask indicating which children exist from the branch at the zipper's focus
    ///
    /// Returns an empty mask if the focus is on a leaf or non-existent path
    fn child_mask(&self) -> ByteMask {
        if self.invalid > 0 {
            return ByteMask::EMPTY;
        }
        match &self.cur_node {
            Node::Branch(node) => {
                node.bytemask
            }
            Node::Line(path) => {
                let top_frame = self.stack.last().unwrap();
                let path = self.tree.get_line(path.path);
                if top_frame.node_depth == path.len() {
                    ByteMask::EMPTY
                } else {
                    ByteMask::from(path[top_frame.node_depth])
                }
            }
        }
    }
}

impl<'tree, Storage, Value> ZipperPath for ACTZipper<'tree, Storage, Value>
where Storage: AsRef<[u8]>
{
    /// Returns the path from the zipper's root to the current focus
    fn path(&self) -> &[u8] { &self.path[self.origin_depth..] }
}

impl<'tree, Storage, Value> ZipperAbsolutePath for ACTZipper<'tree, Storage, Value>
where Storage: AsRef<[u8]>
{
    fn origin_path(&self) -> &[u8] {
        &self.path[..]
    }

    fn root_prefix_path(&self) -> &[u8] {
        &self.path[..self.origin_depth]
    }
}

impl<'tree, Storage, Value> ZipperPathBuffer for ACTZipper<'tree, Storage, Value>
where Storage: AsRef<[u8]>
{
    unsafe fn origin_path_assert_len(&self, len: usize) -> &[u8] {
        // Safety: we're not creating a slice larger than capacity
        assert!(self.path.capacity() >= len);
        unsafe{ core::slice::from_raw_parts(self.path.as_ptr(), len) }
    }

    fn reserve_buffers(&mut self, path_len: usize, stack_depth: usize) {
        self.path.reserve(path_len.saturating_sub(self.path.len()));
        self.stack.reserve(stack_depth.saturating_sub(self.stack.len()));
    }

    fn prepare_buffers(&mut self) {
    }
}

impl<'tree, Storage> ZipperSubtries<(), GlobalAlloc> for ACTZipper<'tree, Storage, ()>
where Storage: AsRef<[u8]>
{
    fn native_subtries(&self) -> bool { false }
    fn try_make_map(&self) -> Option<PathMap<(), GlobalAlloc>> { None }
    fn trie_ref(&self) -> Option<TrieRef<'_, (), GlobalAlloc>> { None }
    fn alloc(&self) -> GlobalAlloc { global_alloc() }
}

const DO_TRACE: bool = false;
impl<'tree, Storage, Value> ACTZipper<'tree, Storage, Value>
where Storage: AsRef<[u8]>
{
    fn trace_pos(&self) {
        if !DO_TRACE { return; }
        let last_frame = self.stack.last().unwrap();
        eprintln!("node={:?}, path={:?}, depth={}",
            last_frame.node_id, self.path, last_frame.node_depth);
    }
    fn get_value(&self) -> Option<u64> {
        if !self.is_val() {
            return None;
        }
        let top_frame = self.stack.last()?;
        let node_id = top_frame.node_id.0;
        let data = &self.tree.storage.as_ref()[node_id as usize..];
        let head = data[0];
        if head & VALUE_FLAG == 0 {
            return None;
        }
        let value = read_varint_u64(&data[1..]).0;
        Some(value)
    }

    /// Internal method to facilitate traversing to a path without needing to clone the zipper
    fn with_lookup_from_focus<R, F>(&self, path: &[u8], mut f: F) -> Option<R>
    where
        F: FnMut(Node, usize) -> Option<R>,
    {
        if self.invalid > 0 {
            return None;
        }

        let mut path = path;
        let mut cur_node = self.cur_node.clone();
        let mut node_depth = self.stack.last()?.node_depth;

        loop {
            match cur_node {
                Node::Branch(node) => {
                    if path.is_empty() {
                        return f(Node::Branch(node), node_depth);
                    }
                    if !node.bytemask.test_bit(path[0]) {
                        return None;
                    }
                    let first_child = node.first_child?;
                    let idx = node.bytemask.index_of(path[0]) as usize;
                    cur_node = self.tree.nth_node(first_child, idx).0;
                    node_depth = 0;
                    path = &path[1..];
                }
                Node::Line(line) => {
                    let line_path = self.tree.get_line(line.path);
                    let rest_path = &line_path[node_depth..];
                    if !starts_with(path, rest_path) {
                        return None;
                    }
                    if path.len() < rest_path.len() {
                        node_depth += path.len();
                        return f(Node::Line(line), node_depth);
                    }
                    path = &path[rest_path.len()..];
                    if path.is_empty() {
                        if line.value.is_some() {
                            return f(Node::Line(line), line_path.len());
                        }
                        cur_node = self.tree.get_node(line.child?).0;
                        node_depth = 0;
                        continue;
                    }
                    cur_node = self.tree.get_node(line.child?).0;
                    node_depth = 0;
                }
            }
        }
    }
    fn get_value_at(&self, path: &[u8]) -> Option<u64> {
        self.with_lookup_from_focus(path, |node, node_depth| {
            match node {
                Node::Branch(node) => node.value,
                Node::Line(line) => {
                    let line_path = self.tree.get_line(line.path);
                    if node_depth < line_path.len() {
                        None
                    } else {
                        line.value
                    }
                }
            }
        })
    }

    fn ascend_invalid(&mut self, limit: Option<&mut usize>) -> bool {
        if self.invalid == 0 {
            return true;
        }
        let len = self.path.len();
        let mut invalid_cut = self.invalid.min(len - self.origin_depth);
        if let Some(limit) = limit {
            invalid_cut = invalid_cut.min(*limit);
            *limit -= invalid_cut;
        }
        self.path.truncate(len - invalid_cut);
        self.invalid = self.invalid - invalid_cut;
        self.invalid == 0
    }

    fn ascend_to_branch(&mut self, need_value: bool) -> usize {
        self.trace_pos();
        let start_len = self.path.len();
        if self.invalid > 0 {
            if !self.ascend_invalid(None) {
                return start_len - self.path.len();
            }

            match &self.cur_node {
                Node::Line(line) => {
                    if need_value && line.value.is_some() {
                        return start_len - self.path.len();
                    }
                }
                Node::Branch(node) => {
                    if need_value && node.value.is_some() {
                        return start_len - self.path.len();
                    }
                }
            }
        }
        while let Some(top_frame) = self.stack.last_mut() {
            let mut nchildren = top_frame.child_count;
            let mut this_steps = top_frame.node_depth
                .min(self.path.len() - self.origin_depth);
            top_frame.node_depth = 0;
            if self.stack.len() > 1 {
                self.stack.pop();
                let prev = self.stack.last().unwrap();
                self.cur_node = self.tree.get_node(prev.node_id).0;
                nchildren = prev.child_count;
                    this_steps += 1;
            }
            self.path.truncate(self.path.len() - this_steps);
            // eprintln!("path={:?}", self.path);
            let brk = match &self.cur_node {
                Node::Branch(node) => {
                    (nchildren > 1) || (need_value && node.value.is_some())
                }
                _ => false,
            };
            if brk || self.at_root() {
                break;
            }
        }
        start_len - self.path.len()
    }

    fn descend_cond(&mut self, path: &[u8], on_value: bool) -> usize {
        self.trace_pos();
        if self.invalid > 0 {
            return 0;
        }
        let mut descended = 0;
        let mut path = path.as_ref();
        'descend: while !path.is_empty() {
            match &self.cur_node {
                Node::Line(line) => {
                    let frame = self.stack.last_mut().unwrap();
                    let node_path = &self.tree.get_line(line.path);
                    let rest_path = &node_path[frame.node_depth..];
                    let common = find_prefix_overlap(path, rest_path);
                    descended += common;
                    path = &path[common..];
                    let into_child = rest_path.len() == common && line.child.is_some();
                    let line_child_hack = if into_child { 1 } else { 0 };
                    frame.node_depth += common - line_child_hack;
                    self.path.extend_from_slice(&rest_path[..common]);
                    if on_value && descended > 0 && line.value.is_some() {
                        break 'descend;
                    }
                    if common < rest_path.len() {
                        break 'descend;
                    }
                    let Some(node_id) = line.child else { break 'descend };
                    let (node, _next_id) = self.tree.get_node(node_id);
                    // no need to update next_id
                    self.stack.push(StackFrame::from(&node, node_id));
                    self.cur_node = node;
                }
                Node::Branch(node) => {
                    if on_value && descended > 0 && node.value.is_some() {
                        break 'descend;
                    }
                    if !node.bytemask.test_bit(path[0]) {
                        break 'descend;
                    }
                    let idx = node.bytemask.index_of(path[0]) as usize;
                    let frame = self.stack.last_mut().unwrap();
                    let ((node, next_id), node_id) = if frame.next_id.is_some() && frame.child_index + 1 == idx {
                        // Optimization: if we know the exact next node, descend
                        (self.tree.get_node(frame.next_id.unwrap()), frame.next_id.unwrap())
                    } else {
                        let (node, node_id, next_id) = self.tree
                            .nth_node(node.first_child.unwrap(), idx);
                        ((node, next_id), node_id)
                    };
                    frame.child_index = idx;
                    frame.next_id = Some(next_id);
                    self.stack.push(StackFrame::from(&node, node_id));
                    self.cur_node = node;
                    self.path.push(path[0]);
                    path = &path[1..];
                    descended += 1;
                }
            }
        }
        descended
    }

    fn to_sibling(&mut self, next: bool) -> Option<u8> {
        let top_frame = self.stack.last().unwrap();
        if self.stack.len() <= 1 || top_frame.node_depth > 0 {
            // can't move to sibling at root, or along the path
            return None;
        }
        let top2_frame = &self.stack[self.stack.len() - 2];
        let sibling_idx = if next {
            let idx = top2_frame.child_index + 1;
            if idx >= top2_frame.child_count {
                return None;
            }
            idx
        } else {
            if top2_frame.child_index == 0 {
                return None;
            }
            top2_frame.child_index - 1
        };
        if self.ascend(1) == 0 {
            return None;
        }
        self.descend_indexed_byte(sibling_idx)
    }
}

impl<'tree, Storage> ZipperValues<()> for ACTZipper<'tree, Storage, ()>
where Storage: AsRef<[u8]>
{
    fn val(&self) -> Option<&()> {
        self.get_value().map(|_x| &())
    }
    fn val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&()> {
        self.get_value_at(path.as_ref()).map(|_x| &())
    }
}

impl<'tree, Storage> ZipperValues<u64> for ACTZipper<'tree, Storage, u64>
where Storage: AsRef<[u8]>
{
    fn val(&self) -> Option<&u64> {
        //GOAT, see soundness discussion in ZipperReadOnlyValues impl below
        self.get_val()
    }
    fn val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&u64> {
        //GOAT, see soundness discussion in ZipperReadOnlyValues impl below
        self.get_val_at(path)
    }
}

impl<'tree, Storage> ZipperForking<()> for ACTZipper<'tree, Storage, ()>
where Storage: AsRef<[u8]>
{
    type ReadZipperT<'t> = ACTZipper<'t, Storage, ()> where Self: 't;
    fn fork_read_zipper<'a>(&'a self) -> Self::ReadZipperT<'a> {
        self.clone().with_root_here()
    }
}

impl<'tree, Storage> ZipperForking<u64> for ACTZipper<'tree, Storage, u64>
where Storage: AsRef<[u8]>
{
    type ReadZipperT<'t> = ACTZipper<'t, Storage, u64> where Self: 't;
    fn fork_read_zipper<'a>(&'a self) -> Self::ReadZipperT<'a> {
        self.clone().with_root_here()
    }
}

impl<'tree, Storage> ZipperReadOnlyValues<'tree, ()> for ACTZipper<'tree, Storage, ()>
where Storage: AsRef<[u8]>
{
    fn get_val(&self) -> Option<&'tree ()> {
        self.get_value().map(|_x| &())
    }
    fn get_val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&'tree ()> {
        self.get_value_at(path.as_ref()).map(|_x| &())
    }
}

impl<'tree, Storage> ZipperReadOnlyValues<'tree, u64> for ACTZipper<'tree, Storage, u64>
where Storage: AsRef<[u8]>
{
    fn get_val(&self) -> Option<&'tree u64> {
        let value = self.get_value()?;
        if self.tree.value.get() != value {
            self.tree.value.set(value);
        }
        let ptr = self.tree.value.as_ptr();
        // technically if someone borrows the value twice, they will hit UB
        // since we provided a read-only reference to the value, and we ALSO
        // can update it.
        // all of this is done so that the value can be borrowed with the same
        // lifetime as the tree.
        //
        //LP: GOAT, UNSOUND!!, this seems like a pretty horrible soundness hole
        // For `val()` the simple fix is to move the temporary value Cell onto the zipper, but that doesn't
        // address `get_val()`, `val_at()`, nor `get_val_at()`.  It seems like the only comprehensive fix is
        // to split the ZipperValues trait into one that can return borrowed values and one that returns
        // cloned values.  And ZipperReadOnlyValues simply could not be implemented on ACTZipper.
        Some(unsafe { &*ptr })
    }
    fn get_val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&'tree u64> {
        let value = self.get_value_at(path.as_ref())?;
        if self.tree.value.get() != value {
            self.tree.value.set(value);
        }
        let ptr = self.tree.value.as_ptr();
        Some(unsafe { &*ptr })
    }
}

impl<'tree, Storage, Value> ZipperConcrete for ACTZipper<'tree, Storage, Value>
where Storage: AsRef<[u8]>
{
    fn shared_node_id(&self) -> Option<u64> {
        // TODO: no way to detect now
        None
    }
    fn is_shared(&self) -> bool {
        // TODO: no way to detect now
        false
    }
}

/// An interface to enable moving a zipper around the trie and inspecting paths
impl<'tree, Storage, Value> ZipperMoving for ACTZipper<'tree, Storage, Value>
where Storage: AsRef<[u8]>
{
    /// Returns `true` if the zipper cannot ascend further, otherwise returns `false`
    fn at_root(&self) -> bool { self.path.len() <= self.origin_depth }

    #[inline]
    fn focus_byte(&self) -> Option<u8> {
        self.path.last().cloned()
    }

    /// Resets the zipper's focus back to the root
    fn reset(&mut self) {
        // self.ascend(self.path.len() - self.origin_depth);
        let (cur_node, _) = self.tree.get_node(self.stack[0].node_id);
        self.cur_node = cur_node;
        self.stack.truncate(1);
        self.stack[0].node_depth = self.origin_node_depth;
        self.path.truncate(self.origin_depth);
        self.invalid = 0;
    }

    /// Returns the total number of values contained at and below the zipper's focus, including the focus itself
    ///
    /// WARNING: This is not a cheap method. It may have an order-N cost
    fn val_count(&self) -> usize {
        let mut zipper = self.clone();
        zipper.reset();
        let mut count = 0;
        if zipper.is_val() {
            count += 1;
        }
        while zipper.to_next_val() {
            count += 1;
        }
        count
    }

    /// Moves the zipper deeper into the trie, to the `key` specified relative to the current zipper focus
    ///
    /// Returns `true` if the zipper points to an existing path within the tree, otherwise `false`.  The
    /// zipper's location will be updated, regardless of whether or not the path exists within the tree.
    fn descend_to<P: AsRef<[u8]>>(&mut self, path: P) {
        let path = path.as_ref();
        let depth = path.len();
        let descended = self.descend_to_existing(path);
        if descended != depth {
            self.path.extend_from_slice(&path[descended..]);
            self.invalid += depth - descended;
        }
    }

    /// Moves the zipper deeper into the trie, following the path specified by `k`, relative to the current
    /// zipper focus.  Descent stops at the point where the path does not exist
    ///
    /// Returns the number of bytes descended along the path.  The zipper's focus will always be on an
    /// existing path after this method returns, unless the method was called with the focus on a
    /// non-existent path.
    fn descend_to_existing<P: AsRef<[u8]>>(&mut self, path: P) -> usize {
        self.descend_cond(path.as_ref(), false)
    }

    /// Moves the zipper deeper into the trie, following the path specified by `k`, relative to the current
    /// zipper focus.  Descent stops if a value is encountered or if the path ceases to exist.
    ///
    /// Returns the number of bytes descended along the path.
    ///
    /// If the focus is already on a value, this method will descend to the *next* value along
    /// the path.
    fn descend_to_value<K: AsRef<[u8]>>(&mut self, path: K) -> usize {
        self.descend_cond(path.as_ref(), true)
    }

    fn descend_to_val<K: AsRef<[u8]>>(&mut self, path: K) -> usize {
        self.descend_cond(path.as_ref(), true)
    }

    /// Moves the zipper one byte deeper into the trie.  Identical in effect to [descend_to](Self::descend_to)
    /// with a 1-byte key argument
    fn descend_to_byte(&mut self, k: u8) {
        self.descend_to(&[k])
    }

    /// Descends the zipper's focus one byte into a child branch uniquely identified by `child_idx`
    ///
    /// `child_idx` must within the range `0..child_count()` or this method will do nothing and return `false`
    ///
    /// WARNING: The branch represented by a given index is not guaranteed to be stable across modifications
    /// to the trie.  This method should only be used as part of a directed traversal operation, but
    /// index-based paths may not be stored as locations within the trie.
    fn descend_indexed_byte(&mut self, idx: usize) -> Option<u8> {
        if self.invalid > 0 {
            return None;
        }
        self.trace_pos();
        let mut child_id: Option<NodeId> = None;
        let descended_byte;
        match &self.cur_node {
            Node::Line(line) => {
                let top_frame = self.stack.last_mut().unwrap();
                let path = self.tree.get_line(line.path);
                let rest_path = &path[top_frame.node_depth..];
                if idx != 0 || rest_path.is_empty() {
                    return None;
                }
                descended_byte = Some(rest_path[0]);
                self.path.push(rest_path[0]);
                if let (true, Some(line_child)) = (rest_path.len() == 1, line.child) {
                    child_id = Some(line_child);
                } else {
                    top_frame.node_depth += 1;
                    return descended_byte;
                }
            }
            Node::Branch(node) => {
                let top_frame = self.stack.last_mut().unwrap();
                if idx > top_frame.child_count {
                    return None;
                }
                let byte = node.bytemask.indexed_bit::<true>(idx);
                descended_byte = byte;
                if let Some(byte) = byte {
                    if top_frame.next_id.is_some() && top_frame.child_index + 1 == idx {
                        child_id = top_frame.next_id;
                    } else {
                        let first_child = node.first_child.unwrap();
                        child_id = Some(self.tree.nth_node(first_child, idx).1);
                    }
                    self.path.push(byte);
                }
            }
        }
        if let Some(child_id) = child_id {
            let top_frame = self.stack.last_mut().unwrap();
            let (node, next_id) = self.tree.get_node(child_id);
            top_frame.child_index = idx;
            top_frame.next_id = Some(next_id);
            self.stack.push(StackFrame::from(&node, child_id));
            self.cur_node = node;
        }
        if child_id.is_some() { descended_byte } else { None }
    }

    /// Descends the zipper's focus one step into the first child branch in a depth-first traversal
    ///
    /// NOTE: This method should have identical behavior to passing `0` to [descend_indexed_byte](ZipperMoving::descend_indexed_byte),
    /// although with less overhead
    fn descend_first_byte(&mut self) -> Option<u8> {
        self.descend_indexed_byte(0)
    }

    /// Descends the zipper's focus until a branch or a value is encountered.  Returns `true` if the focus
    /// moved otherwise returns `false`
    fn descend_until<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool {
        self.trace_pos();
        let mut descended = false;
        'descend: while self.child_count() == 1 {
            let child_id;
            match &self.cur_node {
                Node::Line(line) => {
                    let top_frame = self.stack.last_mut().unwrap();
                    let path = self.tree.get_line(line.path);
                    let rest_path = &path[top_frame.node_depth..];
                    let line_child_hack = if line.child.is_some() { 1 } else { 0 };
                    top_frame.node_depth += rest_path.len() - line_child_hack;
                    self.path.extend_from_slice(rest_path);
                    obs.descend_to(rest_path);
                    child_id = line.child;
                    if line.value.is_some() {
                        descended = true;
                        break 'descend;
                    }
                }
                Node::Branch(node) => {
                    let Some(byte) = node.bytemask.iter().next()
                        else { break 'descend };
                    self.path.push(byte);
                    obs.descend_to_byte(byte);
                    child_id = node.first_child;
                }
            }
            descended = true;
            if let Some(child_id) = child_id {
                let top_frame = self.stack.last_mut().unwrap();
                let (node, next_id) = self.tree.get_node(child_id);
                top_frame.child_index = 0;
                top_frame.next_id = Some(next_id);
                let frame = StackFrame::from(&node, child_id);
                let nchildren = frame.child_count;
                self.stack.push(frame);
                self.cur_node = node.clone();
                if let Node::Branch(node) = node {
                    if node.value.is_some() || nchildren > 1 {
                        break 'descend;
                    }
                }
            }
        }
        descended
    }

    /// Ascends the zipper `steps` steps.  Returns `true` if the zipper sucessfully moved `steps`
    ///
    /// If the root is fewer than `n` steps from the zipper's position, then this method will stop at
    /// the root and return `false`
    fn ascend(&mut self, steps: usize) -> usize {
        self.trace_pos();
        let mut remaining = steps;
        if !self.ascend_invalid(Some(&mut remaining)) {
            return steps - remaining;
        }
        while let Some(top_frame) = self.stack.last_mut() {
            let rest_path = &self.path[self.origin_depth..];
            let mut this_steps = remaining.min(top_frame.node_depth).min(rest_path.len());
            top_frame.node_depth -= this_steps;
            remaining -= this_steps;
            if top_frame.node_depth == 0 && self.stack.len() > 1 && remaining > 0 {
                self.stack.pop();
                let prev = self.stack.last().unwrap();
                self.cur_node = self.tree.get_node(prev.node_id).0;
                this_steps += 1;
                remaining -= 1;
            }
            self.path.truncate(self.path.len() - this_steps);
            if self.at_root() || remaining == 0 {
                return steps - remaining;
            }
        }
        unreachable!();
    }

    /// Ascends the zipper up a single byte.  Equivalent to passing `1` to [ascend](Self::ascend)
    fn ascend_byte(&mut self) -> bool {
        self.ascend(1) == 1
    }

    /// Ascends the zipper to the nearest upstream branch point or value.  Returns the number of bytes
    /// ascended.  Returns `0` if the zipper was already at the root
    fn ascend_until(&mut self) -> usize {
        self.ascend_to_branch(true)
    }

    /// Ascends the zipper to the nearest upstream branch point, skipping over values along the way.  Returns
    /// the number of bytes ascended.  Returns `0` if the zipper was already at the root
    fn ascend_until_branch(&mut self) -> usize {
        self.ascend_to_branch(false)
    }

    #[inline]
    fn to_next_sibling_byte(&mut self) -> Option<u8> {
        self.to_sibling(true)
    }

    #[inline]
    fn to_prev_sibling_byte(&mut self) -> Option<u8> {
        self.to_sibling(false)
    }

    // default
    // fn to_next_step(&mut self) -> bool;
}

impl<Storage, Value> ZipperIteration for ACTZipper<'_, Storage, Value>
where Storage: AsRef<[u8]>
{
    /// Systematically advances to the next value accessible from the zipper, traversing in a depth-first
    /// order
    ///
    /// Returns a reference to the value or `None` if the zipper has encountered the root.
    fn to_next_val(&mut self) -> bool {
        while self.to_next_step()  {
            if self.is_val() {
                return true;
            }
        }
        false
    }

    /// Descends the zipper's focus `k`` bytes, following the first child at each branch, and continuing
    /// with depth-first exploration until a path that is `k` bytes from the focus has been found
    ///
    /// Returns `true` if the zipper has sucessfully descended `k` steps, or `false` otherwise.  If this
    /// method returns `false` then the zipper will be in its original position.
    ///
    /// WARNING: This is not a constant-time operation, and may be as bad as `order n` with respect to the paths
    /// below the zipper's focus.  Although a typical cost is `order log n` or better.
    ///
    /// See: [to_next_k_path](ZipperIteration::to_next_k_path)
    fn descend_first_k_path(&mut self, k: usize) -> bool {
        for ii in 0..k {
            if self.descend_first_byte().is_none() {
                self.ascend(ii);
                return false;
            }
        }
        return true;
    }

    /// Moves the zipper's focus to the next location with the same path length as the current focus,
    /// following a depth-first exploration from a common root `k` steps above the current focus
    ///
    /// Returns `true` if the zipper has sucessfully moved to a new location at the same level, or `false`
    /// if no further locations exist.  If this method returns `false` then the zipper will be ascended `k`
    /// steps to the common root.  (The focus position when [descend_first_k_path](ZipperIteration::descend_first_k_path) was called)
    ///
    /// WARNING: This is not a constant-time operation, and may be as bad as `order n` with respect to the paths
    /// below the zipper's focus.  Although a typical cost is `order log n` or better.
    ///
    /// See: [descend_first_k_path](ZipperIteration::descend_first_k_path)
    fn to_next_k_path(&mut self, k: usize) -> bool {
        let mut depth = k;
        'outer: loop {
            while depth > 0 && self.child_count() <= 1 {
                if self.ascend(1) == 0 {
                    break 'outer;
                }
                depth -= 1;
            }
            let stack = self.stack.last_mut().unwrap();
            let idx = stack.child_index + 1;
            if idx >= stack.child_count {
                if depth == 0 || self.ascend(1) == 0 {
                    break 'outer;
                }
                depth -= 1;
                continue 'outer;
            }
            assert!(self.descend_indexed_byte(idx).is_some());
            depth += 1;
            for _ii in 0..k - depth {
                if self.descend_first_byte().is_none() {
                    continue 'outer;
                }
                depth += 1;
            }
            return true;
        }
        self.ascend(depth);
        false
    }
}

#[cfg(test)]
mod tests {
    use super::{ArenaCompactTree, ACTZipper};
    use crate::{
        morphisms::Catamorphism, PathMap, zipper::{zipper_iteration_tests, zipper_moving_tests, ZipperIteration, ZipperPath, ZipperValues}
    };

    zipper_moving_tests::zipper_moving_tests!(arena_compact_zipper,
        |keys: &[&[u8]]| {
            let btm = keys.into_iter().map(|k| (k, ())).collect::<PathMap<()>>();
            ArenaCompactTree::from_zipper(btm.read_zipper(), |&_v| 0)
        },
        |trie: &mut ArenaCompactTree<Vec<u8>>, path: &[u8]| -> ACTZipper<'_, Vec<u8>, ()> {
            trie.read_zipper_at_path(path)
        }
    );

    zipper_iteration_tests::zipper_iteration_tests!(arena_compact_zipper,
        |keys: &[&[u8]]| {
            let btm = keys.into_iter().map(|k| (k, ())).collect::<PathMap<()>>();
            ArenaCompactTree::from_zipper(btm.read_zipper(), |&_v| 0)
        },
        |trie: &mut ArenaCompactTree<Vec<u8>>, path: &[u8]| -> ACTZipper<'_, Vec<u8>, ()> {
            trie.read_zipper_at_path(path)
        }
    );

    const PATHS: &[&str] = &[
        "arrow", "bow", "cannon", "roman", "romane", "romanus", "romulus",
        "rubens", "ruber", "rubicon", "rubicundus", "rom'i",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaab",
        "aaaaaaaaaaaaaaaaaaaaaaaaaaaaac",
        "bbbbbbbbbbbbbbbbbbbbbbbbbbaaaa",
        "bbbbbbbbbbbbbbbbbbbbbbbbbbcccc",
    ];

    #[test]
    fn test_act_from_zipper() {
        let path_vals = PATHS.iter().enumerate()
            .map(|(idx, path)| (path, idx as u64));

        let btm = PathMap::from_iter(path_vals);
        let act = ArenaCompactTree::from_zipper(btm.read_zipper(), |&v| v);

        let mut btm_zipper = btm.read_zipper();
        let mut act_zipper = act.read_zipper_u64();

        loop {
            btm_zipper.to_next_val();
            act_zipper.to_next_val();

            let btm_val = btm_zipper.val().copied();
            let act_val = act_zipper.val().copied();

            assert_eq!(btm_zipper.path(), act_zipper.path());
            assert_eq!(btm_val, act_val);

            if act_val.is_none() {
                break;
            }
        }
    }

    #[test]
    fn test_act_get() {
        let path_vals = PATHS.iter().enumerate()
            .map(|(idx, path)| (path, idx as u64));
        let btm = PathMap::from_iter(path_vals.clone());
        let act = ArenaCompactTree::from_zipper(btm.read_zipper(), |&v| v);
        for (path, idx) in path_vals {
            assert_eq!(Some(idx), act.get_val_at(path));
        }
    }

    /// Regression test: `get_val_at` must return `None` for a byte that is
    /// absent from a branch's child mask, rather than reading the wrong
    /// sibling (byte below the mask range) or walking past the last sibling
    /// (byte above the mask range, which subtract-overflow panics in debug).
    #[test]
    fn test_act_get_absent_branch_byte() {
        // Single-char keys force a branch root with children on {b'b', b'd', b'f'}.
        let items: [(&str, u64); 3] = [("b", 1), ("d", 2), ("f", 3)];
        let btm = PathMap::from_iter(items.iter().copied());
        let act = ArenaCompactTree::from_zipper(btm.read_zipper(), |&v| v);

        // Present keys still resolve correctly.
        for (k, v) in items {
            assert_eq!(act.get_val_at(k), Some(v), "present key {k}");
        }

        // Absent bytes below, between, and above the child mask range.
        // b'a' is below the minimum child (would have read the first sibling),
        // b'g'/b'z' are above the maximum (would have walked past the last).
        for absent in ["a", "c", "e", "g", "z"] {
            assert_eq!(act.get_val_at(absent), None, "absent byte {absent}");
        }

        // Absent path that descends one present child then diverges.
        assert_eq!(act.get_val_at("bx"), None);
    }

    #[test]
    fn test_act_round_trip() {
        let path_vals = PATHS.iter().enumerate()
            .map(|(idx, path)| (path, idx as u64));

        let btm = PathMap::from_iter(path_vals);
        let act1 = ArenaCompactTree::from_zipper(btm.read_zipper(), |&v| v);
        let act2 = ArenaCompactTree::from_zipper(act1.read_zipper_u64(), |&v: &u64| v);
        assert_eq!(act1.get_data(), act2.get_data());
    }

    #[test]
    fn test_act_cata() {
        let path_vals = PATHS.iter().enumerate()
            .map(|(idx, path)| (path, idx as u64));

        let btm = PathMap::from_iter(path_vals);
        let btm_value = btm.read_zipper().into_cata_side_effect(|bm, ch, val, path| {
            let path = std::str::from_utf8(path).unwrap();
            let children = ch.join(", ");
            format!("('{path}' {val:?} {bm:?}\n{children})")
        });
        let act = ArenaCompactTree::from_zipper(btm.read_zipper(), |&v| v);
        let act_value = act.read_zipper_u64().into_cata_side_effect(|bm, ch: &mut[String], val: Option<&u64>, path| {
            let path = std::str::from_utf8(path).unwrap();
            let children = ch.join(", ");
            format!("('{path}' {val:?} {bm:?}\n{children})")
        });
        assert_eq!(btm_value, act_value);
    }

    fn build_act_file(path: &std::path::Path, items: &[(&str, u64)]) {
        let btm = PathMap::from_iter(items.iter().map(|&(k, v)| (k, v)));
        let act = ArenaCompactTree::from_zipper(btm.read_zipper(), |&v| v);
        std::fs::write(path, act.get_data()).unwrap();
    }

    /// Assert `act` holds exactly `items` (no duplicates in `items`),
    /// both by point lookups and by an ordered walk.
    fn assert_act_content(act: &super::ACTMmap, items: &[(&str, u64)]) {
        for &(k, v) in items {
            assert_eq!(act.get_val_at(k), Some(v), "key {k}");
        }
        let btm = PathMap::from_iter(items.iter().map(|&(k, v)| (k, v)));
        let mut bz = btm.read_zipper();
        let mut az = act.read_zipper_u64();
        loop {
            let more_b = bz.to_next_val();
            let more_a = az.to_next_val();
            assert_eq!(more_b, more_a, "walks end together");
            assert_eq!(bz.path(), az.path());
            assert_eq!(bz.val().copied(), az.val().copied());
            if !more_a {
                break;
            }
        }
    }

    #[test]
    fn test_act_merge_zipper_into_file() {
        use super::MAGIC_LENGTH;
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("merge.act");
        let base: &[(&str, u64)] = &[
            ("arrow", 1), ("bow", 2), ("roman", 3), ("romane", 4),
            ("rubicon", 5), ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaab", 6),
        ];
        let add: &[(&str, u64)] = &[
            ("bow", 20),                            // value conflict -> zipper wins
            ("rom", 7),                             // value inside a line segment
            ("romanus", 8),                         // splits the line under "roman"
            ("rub", 9), ("rubble", 10),             // diverges inside the "rubicon" line
            ("zebra", 11),                          // fresh subtree at the root
            ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaab", 6),  // identical entry (unchanged subtree)
            ("arrowhead", 12),                      // extends an existing leaf
        ];
        build_act_file(&file, base);
        let before = std::fs::read(&file).unwrap();

        let add_map = PathMap::from_iter(add.iter().map(|&(k, v)| (k, v)));
        let merged = ArenaCompactTree::merge_zipper_into_file(
            &file, add_map.read_zipper(), |&v| v).unwrap();

        // Append-only: everything except the root pointer is byte-identical
        let after = std::fs::read(&file).unwrap();
        assert!(after.len() > before.len(), "merge must append");
        assert_eq!(&after[..MAGIC_LENGTH], &before[..MAGIC_LENGTH]);
        assert_eq!(&after[MAGIC_LENGTH + 8..before.len()], &before[MAGIC_LENGTH + 8..]);

        assert_act_content(&merged, &[
            ("arrow", 1), ("arrowhead", 12), ("bow", 20), ("rom", 7),
            ("roman", 3), ("romane", 4), ("romanus", 8), ("rub", 9),
            ("rubble", 10), ("rubicon", 5), ("zebra", 11),
            ("aaaaaaaaaaaaaaaaaaaaaaaaaaaaab", 6),
        ]);
        for absent in ["row", "arrowh", "arrowheads", "zebr", "zebras", "romanu"] {
            assert_eq!(merged.get_val_at(absent), None, "absent {absent}");
        }
    }

    #[test]
    fn test_act_merge_noop() {
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("noop.act");
        let base: &[(&str, u64)] = &[
            ("arrow", 1), ("bow", 2), ("roman", 3), ("romane", 4), ("rubicon", 5),
        ];
        build_act_file(&file, base);
        let before = std::fs::read(&file).unwrap();

        // A subset with identical values adds nothing
        let subset = PathMap::from_iter([("bow", 2u64), ("romane", 4)]);
        let merged = ArenaCompactTree::merge_zipper_into_file(
            &file, subset.read_zipper(), |&v| v).unwrap();
        assert_eq!(std::fs::read(&file).unwrap(), before, "no-op merge must not touch the file");
        assert_act_content(&merged, base);
    }

    #[test]
    fn test_act_merge_wide_branch() {
        // Merging into a >=32-child branch exercises the mask encoding
        let dir = tempfile::tempdir().unwrap();
        let file = dir.path().join("wide.act");
        let evens: Vec<Vec<u8>> = (0..=254u16).step_by(2).map(|b| vec![b as u8]).collect();
        let odds: Vec<Vec<u8>> = (1..=255u16).step_by(2).map(|b| vec![b as u8]).collect();
        let base_map = PathMap::from_iter(evens.iter().map(|k| (k, 1u64)));
        let act = ArenaCompactTree::from_zipper(base_map.read_zipper(), |&v| v);
        std::fs::write(&file, act.get_data()).unwrap();

        let add_map = PathMap::from_iter(odds.iter().map(|k| (k, 2u64)));
        let merged = ArenaCompactTree::merge_zipper_into_file(
            &file, add_map.read_zipper(), |&v| v).unwrap();
        for b in 0..=255u8 {
            assert_eq!(merged.get_val_at([b]), Some(1 + (b & 1) as u64), "byte {b}");
        }
        assert_eq!(merged.get_val_at([0, 0]), None);
    }

    #[test]
    fn test_act_merge_repeated_and_act_source() {
        // Several merge waves over an LCG key soup; the last wave merges from
        // an ACT zipper instead of a PathMap zipper.
        // Written under the project's `tests/` dir so the merged file can be inspected.
        let tests_dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
        std::fs::create_dir_all(&tests_dir).unwrap();
        let file = tests_dir.join("act_merge.act");
        let mut state: u64 = 0x1234_5678_9abc_def0;
        let mut next = move || {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            state >> 33
        };
        let mut make_wave = |n: usize| -> Vec<(String, u64)> {
            (0..n).map(|_| {
                let r = next();
                // small alphabet + variable length -> shared prefixes and line splits
                let len = 1 + (r % 12) as usize;
                let key: String = (0..len)
                    .map(|i| (b'a' + ((r >> (i * 2)) & 0x3) as u8) as char)
                    .collect();
                (key, r % 1000)
            }).collect()
        };

        let wave0 = make_wave(200);
        let base_map: PathMap<u64> = wave0.iter().map(|(k, v)| (k, *v)).collect();
        let act = ArenaCompactTree::from_zipper(base_map.read_zipper(), |&v| v);
        std::fs::write(&file, act.get_data()).unwrap();

        let mut expect: std::collections::HashMap<String, u64> =
            wave0.into_iter().collect();
        for wave_idx in 0..3 {
            let wave = make_wave(300);
            let wave_map: PathMap<u64> = wave.iter().map(|(k, v)| (k, *v)).collect();
            let before = std::fs::read(&file).unwrap();
            let merged = if wave_idx < 2 {
                ArenaCompactTree::merge_zipper_into_file(
                    &file, wave_map.read_zipper(), |&v| v).unwrap()
            } else {
                // final wave: merge from an ACT zipper (ACT -> ACT merge)
                let wave_act = ArenaCompactTree::from_zipper(wave_map.read_zipper(), |&v| v);
                ArenaCompactTree::merge_zipper_into_file(
                    &file, wave_act.read_zipper_u64(), |&v| v).unwrap()
            };
            // PathMap::from_iter and HashMap::extend agree: later entries win
            expect.extend(wave.into_iter());
            let after = std::fs::read(&file).unwrap();
            assert_eq!(&after[16..before.len()], &before[16..], "append-only violated");

            let items: Vec<(&str, u64)> = expect.iter().map(|(k, v)| (k.as_str(), *v)).collect();
            assert_act_content(&merged, &items);

            // The root chain grows by one per merge: the base root plus one
            // recorded root for each merge performed so far. Roots are appended,
            // so newest-first they strictly decrease in file offset, and the head
            // is the live root at the header.
            let history = merged.root_history();
            assert_eq!(history.len(), wave_idx + 2, "root history length");
            assert_eq!(history[0], merged.get_root().1, "history head is live root");
            for pair in history.windows(2) {
                assert!(pair[0].0 > pair[1].0, "roots must be newest-first: {history:?}");
            }
        }
    }

    #[test]
    fn test_act_output_stream() -> Result<(), std::io::Error> {
        use super::ACTOutputStream;
        use crate::zipper::ZipperReadOnlyValues;
        let mut paths = PATHS.to_vec();
        paths.sort();

        let dir = tempfile::tempdir()?;
        let file = dir.path().join("stream.act");
        let mut out = ACTOutputStream::new(&file)?;
        for (idx, path) in paths.iter().enumerate() {
            out.push_val(path, idx as u64)?;
        }
        let tree = out.finish()?;
        for (idx, path) in paths.iter().enumerate() {
            assert_eq!(tree.get_val_at(path), Some(idx as u64));
        }
        assert_eq!(tree.get_val_at("arr"), None);
        assert_eq!(tree.get_val_at("arrows"), None);

        // The streamed tree must enumerate the same paths/values as one
        // built through the catamorphism
        let btm = PathMap::from_iter(
            paths.iter().enumerate().map(|(idx, path)| (path, idx as u64)));
        let act = ArenaCompactTree::from_zipper(btm.read_zipper(), |&v| v);
        let mut cata_zipper = act.read_zipper_u64();
        let mut stream_zipper = tree.read_zipper_u64();
        loop {
            let cata_next = cata_zipper.to_next_val();
            let stream_next = stream_zipper.to_next_val();
            assert_eq!(cata_next, stream_next);
            assert_eq!(cata_zipper.path(), stream_zipper.path());
            assert_eq!(cata_zipper.get_val(), stream_zipper.get_val());
            if !cata_next {
                break;
            }
        }
        Ok(())
    }

    #[test]
    fn test_act_output_stream_prefixes() -> Result<(), std::io::Error> {
        use super::ACTOutputStream;
        let dir = tempfile::tempdir()?;
        let file = dir.path().join("prefixes.act");
        let mut out = ACTOutputStream::new(&file)?;
        // Empty path, paths extending previous ones, and a long chain
        let paths: &[&str] = &["", "a", "ab", "abc", "abcdefgh", "b"];
        for (idx, path) in paths.iter().enumerate() {
            out.push_val(path, idx as u64)?;
        }
        let tree = out.finish()?;
        for (idx, path) in paths.iter().enumerate() {
            assert_eq!(tree.get_val_at(path), Some(idx as u64), "path={path:?}");
        }
        assert_eq!(tree.get_val_at("abcd"), None);
        assert_eq!(tree.get_val_at("ba"), None);
        Ok(())
    }

    #[test]
    fn test_act_output_stream_wide_branch() -> Result<(), std::io::Error> {
        use super::ACTOutputStream;
        let dir = tempfile::tempdir()?;
        let file = dir.path().join("wide.act");
        let mut out = ACTOutputStream::new(&file)?;
        // 256 children at the root exercises the child-mask encoding
        for byte in 0..=255_u8 {
            out.push_val([byte], byte as u64)?;
        }
        let tree = out.finish()?;
        for byte in 0..=255_u8 {
            assert_eq!(tree.get_val_at([byte]), Some(byte as u64));
        }
        assert_eq!(tree.get_val_at([0, 0]), None);
        Ok(())
    }

    #[test]
    fn test_act_output_stream_rejects_unordered() -> Result<(), std::io::Error> {
        use super::ACTOutputStream;
        let dir = tempfile::tempdir()?;
        let file = dir.path().join("unordered.act");
        let mut out = ACTOutputStream::new(&file)?;
        out.push("bcd")?;
        assert!(out.push("bcd").is_err(), "duplicates must be rejected");
        assert!(out.push("abc").is_err(), "out-of-order must be rejected");
        assert!(out.push("b").is_err(), "prefix of previous is out-of-order");
        out.push("bce")?;
        let tree = out.finish()?;
        assert_eq!(tree.get_val_at("bcd"), Some(0));
        assert_eq!(tree.get_val_at("bce"), Some(0));
        assert_eq!(tree.get_val_at("abc"), None);
        Ok(())
    }

    #[test]
    fn test_act_mmap() -> Result<(), std::io::Error> {
        use tempfile::NamedTempFile;
        use std::io::Write;
        let path_vals = PATHS.iter().enumerate()
            .map(|(idx, path)| (path, idx as u64));

        let btm = PathMap::from_iter(path_vals);
        let act = ArenaCompactTree::from_zipper(btm.read_zipper(), |&v| v);
        let mut tmp = NamedTempFile::new()?;
        tmp.write_all(act.get_data())?;
        let act_mmap = ArenaCompactTree::open_mmap(tmp.path())?;

        let btm_value = btm.read_zipper().into_cata_side_effect(|bm, ch, v, path| {
            let path = std::str::from_utf8(path).unwrap();
            let children = ch.join(", ");
            format!("('{path}' {v:?} {bm:?}\n{children})")
        });
        let act_value = act_mmap.read_zipper_u64().into_cata_side_effect(|bm, ch, val: Option<&u64>, path| {
            let path = std::str::from_utf8(path).unwrap();
            let children = ch.join(", ");
            format!("('{path}' {val:?} {bm:?}\n{children})")
        });
        assert_eq!(btm_value, act_value);
        Ok(())
    }

    /// A deterministic pseudo-random `PathMap`
    ///
    /// The small alphabet and short paths make prefixes collide heavily, so
    /// the trie mixes branch nodes, line nodes, and values on interior paths.
    /// Paths are never empty: `.paths` carries no root value, so an empty path
    /// would show up as a round-trip difference that says nothing about ACT.
    #[cfg(any(feature = "serialization", feature = "nightly"))]
    fn random_pathmap(seed: u64, count: usize) -> PathMap<u64> {
        use rand::{Rng, SeedableRng, rngs::StdRng};
        const ALPHABET: &[u8] = b"abcde";
        let mut rng = StdRng::seed_from_u64(seed);
        let mut map = PathMap::new();
        for idx in 0..count {
            let len = rng.random_range(1..12);
            let path: Vec<u8> = (0..len)
                .map(|_| ALPHABET[rng.random_range(0..ALPHABET.len())]).collect();
            map.set_val_at(&path[..], idx as u64);
        }
        map
    }

    /// Asserts that `tree` holds exactly the paths and values of `map`
    #[cfg(any(feature = "serialization", feature = "nightly"))]
    fn assert_act_matches_map(map: &PathMap<u64>, tree: &ArenaCompactTree<super::Mmap>) {
        let mut map_zipper = map.read_zipper();
        let mut act_zipper = tree.read_zipper_u64();
        loop {
            let map_next = map_zipper.to_next_val();
            assert_eq!(map_next, act_zipper.to_next_val());
            assert_eq!(map_zipper.path(), act_zipper.path());
            assert_eq!(map_zipper.val().copied(), act_zipper.val().copied());
            if !map_next { break }
        }
    }

    /// `PathMap` -> `.paths` -> `.act`, checking the tree that comes out the
    /// far end against the map that went in
    #[cfg(all(feature = "serialization", not(miri)))] // miri really hates the zlib-ng-sys C API
    #[test]
    fn test_act_paths_round_trip() -> Result<(), std::io::Error> {
        use super::ACTOutputStream;
        use crate::paths_serialization::{for_each_deserialized_path, serialize_paths_with_auxdata};

        let map = random_pathmap(0xAC7_0001, 5000);

        // `.paths` stores no values, so the aux-data callback collects them on
        // the side, indexed by the order the paths were written in
        let mut paths_data = Vec::new();
        let mut values = Vec::new();
        let ser = serialize_paths_with_auxdata(
            map.read_zipper(), &mut paths_data,
            |idx, _path, val: &u64| { assert_eq!(values.len(), idx); values.push(*val) })?;
        assert_eq!(ser.path_count, map.val_count());

        // The deserializer replays paths in the order the zipper produced
        // them, i.e. strictly increasing, which is exactly what the streaming
        // ACT builder requires
        let dir = tempfile::tempdir()?;
        let file = dir.path().join("round_trip.act");
        let mut out = ACTOutputStream::new(&file)?;
        let de = for_each_deserialized_path(
            &paths_data[..], |idx, path| out.push_val(path, values[idx]))?;
        let tree = out.finish()?;
        assert_eq!(de.path_count, ser.path_count);

        assert_act_matches_map(&map, &tree);
        Ok(())
    }

    /// The same build, driven through [act_serialization_sink_with_vals]
    ///
    /// The producer owns its paths, which is what the sink's resume type
    /// requires: one lifetime is fixed for every path the coroutine is fed.
    #[cfg(feature = "nightly")]
    #[test]
    fn test_act_serialization_sink() -> Result<(), std::io::Error> {
        use std::ops::{Coroutine, CoroutineState};
        use std::pin::pin;
        use super::{ACTOutputStream, act_serialization_sink_with_vals};

        let map = random_pathmap(0xAC7_0002, 5000);
        let mut items: Vec<(Vec<u8>, u64)> = Vec::with_capacity(map.val_count());
        let mut zipper = map.read_zipper();
        while zipper.to_next_val() {
            items.push((zipper.path().to_vec(), *zipper.val().unwrap()));
        }

        let dir = tempfile::tempdir()?;
        let file = dir.path().join("sink.act");
        let mut sink = pin!(act_serialization_sink_with_vals(ACTOutputStream::new(&file)?));
        for (path, val) in items.iter() {
            match sink.as_mut().resume(Some((&path[..], *val))) {
                CoroutineState::Yielded(()) => {}
                CoroutineState::Complete(res) => { res?; panic!("sink ended early") }
            }
        }
        let tree = match sink.as_mut().resume(None) {
            CoroutineState::Complete(res) => res?,
            CoroutineState::Yielded(()) => panic!("`None` must end the stream"),
        };

        assert_act_matches_map(&map, &tree);
        Ok(())
    }
}
