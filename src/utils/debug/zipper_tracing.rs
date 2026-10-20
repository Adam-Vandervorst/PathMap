
//! Records every call made on traced zippers into a single shared binary trace, so a run can later
//! be replayed for debugging or visualization
//!
//! Usage:
//! 1. Call [open] (or [open_file]) once, to supply the writer and the value type `V` for the trace
//! 2. Wrap each zipper of interest in a [TraceZipper], giving it an id.  Every zipper writes to the same trace
//! 3. Call [close] to flush the trace
//!
//! The trace is a header followed by a stream of `(zipper_id, TraceOp)` events, which [decode_trace]
//! turns back into [TraceOp]s.
//!
//! An event is written as a call begins, so the trace records which operations were called and with
//! what arguments, but not their results.  A player needs its own copy of the trie to follow along.
//!
//! Calls made on a `TraceZipper` while another traced call on the same thread is in progress are not
//! recorded, because they're the inner workings of the outer call.  For example, when a traced write
//! zipper grafts from a traced read zipper, only the graft is recorded.  The same applies to calls
//! made from user code that runs inside a traced call, such as a [PathObserver], or the closure passed
//! to [ZipperWriting::get_val_or_set_mut_with].
//!
//! When an operation takes another zipper as an argument, such as [ZipperWriting::graft], the argument
//! is recorded by id if it's also a `TraceZipper`, or by its contents if it isn't (see [TraceSrc]).
//! A traced argument is recognized by probing its [Zipper::path_exists] method, so any wrapper that forwards
//! `path_exists` to a `TraceZipper` is reported as that zipper.  That's right for transparent wrappers like
//! `&mut` and `Box`, but an abstract zipper such as a [PrefixZipper] around a `TraceZipper` will be
//! misreported as the `TraceZipper` it wraps.
//!
//! The internal accessor methods (e.g. [ZipperInfallibleSubtries::get_focus]), [ZipperConcrete],
//! [ZipperPathBuffer], and [ZipperReadOnlySubtries] are forwarded without being recorded.

use core::any::{type_name, TypeId};
use core::cell::Cell;
use core::sync::atomic::{AtomicBool, Ordering};
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::Path;
use std::sync::{Mutex, MutexGuard};

use crate::alloc::Allocator;
use crate::ring::{AlgebraicStatus, DistributiveLattice, Lattice};
use crate::trie_node::{TaggedNodeRef, TrieNodeODRc};
use crate::utils::ByteMask;
use crate::write_zipper::write_zipper_priv::WriteZipperPriv;
use crate::zipper::*;
use crate::zipper::read_zipper_core::ReadZipperCore;
use crate::zipper::zipper_priv::ZipperReadOnlyPriv;
use crate::PathMap;

const TRACE_MAGIC: &[u8; 8] = b"PMTRACE\0";
const TRACE_VERSION: u64 = 1;

// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---
// Encoding
// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---

/// A type that can be written into, and read back from, a zipper trace
///
/// Implemented for the value types expected to be used with tracing, and for the types that make up a [TraceOp]
pub trait TraceValue: Sized + 'static {
    fn encode(&self, out: &mut Vec<u8>);
    /// Decodes a value from the front of `input`, advancing `input` past it
    fn decode(input: &mut &[u8]) -> Option<Self>;
}

impl TraceValue for () {
    fn encode(&self, _out: &mut Vec<u8>) {}
    fn decode(_input: &mut &[u8]) -> Option<Self> { Some(()) }
}

impl TraceValue for u8 {
    fn encode(&self, out: &mut Vec<u8>) { out.push(*self) }
    fn decode(input: &mut &[u8]) -> Option<Self> {
        let (&byte, rest) = input.split_first()?;
        *input = rest;
        Some(byte)
    }
}

impl TraceValue for bool {
    fn encode(&self, out: &mut Vec<u8>) { out.push(*self as u8) }
    fn decode(input: &mut &[u8]) -> Option<Self> {
        match u8::decode(input)? {
            0 => Some(false),
            1 => Some(true),
            _ => None
        }
    }
}

/// LEB128 encoding
impl TraceValue for u64 {
    fn encode(&self, out: &mut Vec<u8>) {
        let mut x = *self;
        loop {
            let byte = (x & 0x7f) as u8;
            x >>= 7;
            if x == 0 {
                out.push(byte);
                return
            }
            out.push(byte | 0x80);
        }
    }
    fn decode(input: &mut &[u8]) -> Option<Self> {
        let mut x = 0u64;
        let mut shift = 0;
        loop {
            let byte = u8::decode(input)?;
            if shift >= 64 {
                return None
            }
            x |= ((byte & 0x7f) as u64) << shift;
            if byte & 0x80 == 0 {
                return Some(x)
            }
            shift += 7;
        }
    }
}

macro_rules! impl_trace_value_via_u64 {
    ($($t:ty),*) => {$(
        impl TraceValue for $t {
            fn encode(&self, out: &mut Vec<u8>) { (*self as u64).encode(out) }
            fn decode(input: &mut &[u8]) -> Option<Self> { u64::decode(input)?.try_into().ok() }
        }
    )*};
}
impl_trace_value_via_u64!(u16, u32, usize);

impl TraceValue for ByteMask {
    fn encode(&self, out: &mut Vec<u8>) {
        for word in self.0 {
            out.extend_from_slice(&word.to_le_bytes());
        }
    }
    fn decode(input: &mut &[u8]) -> Option<Self> {
        let mut mask = ByteMask::new();
        for word in mask.0.iter_mut() {
            let (bytes, rest) = input.split_first_chunk::<8>()?;
            *word = u64::from_le_bytes(*bytes);
            *input = rest;
        }
        Some(mask)
    }
}

impl<T: TraceValue> TraceValue for Option<T> {
    fn encode(&self, out: &mut Vec<u8>) {
        match self {
            None => out.push(0),
            Some(val) => {
                out.push(1);
                val.encode(out);
            }
        }
    }
    fn decode(input: &mut &[u8]) -> Option<Self> {
        match u8::decode(input)? {
            0 => Some(None),
            1 => Some(Some(T::decode(input)?)),
            _ => None
        }
    }
}

impl<T: TraceValue> TraceValue for Vec<T> {
    fn encode(&self, out: &mut Vec<u8>) {
        self.len().encode(out);
        for item in self {
            item.encode(out);
        }
    }
    fn decode(input: &mut &[u8]) -> Option<Self> {
        let len = usize::decode(input)?;
        //Don't trust `len` for the allocation, in case the input is corrupt
        let mut items = Vec::with_capacity(len.min(input.len()));
        for _ in 0..len {
            items.push(T::decode(input)?);
        }
        Some(items)
    }
}

impl<T0: TraceValue, T1: TraceValue> TraceValue for (T0, T1) {
    fn encode(&self, out: &mut Vec<u8>) {
        self.0.encode(out);
        self.1.encode(out);
    }
    fn decode(input: &mut &[u8]) -> Option<Self> {
        Some((T0::decode(input)?, T1::decode(input)?))
    }
}

impl TraceValue for String {
    fn encode(&self, out: &mut Vec<u8>) { self.as_bytes().to_vec().encode(out) }
    fn decode(input: &mut &[u8]) -> Option<Self> { String::from_utf8(Vec::<u8>::decode(input)?).ok() }
}

// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---
// Opcodes
// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---

/// The source argument of an operation that reads from another zipper, such as [ZipperWriting::graft]
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TraceSrc<V> {
    /// The source is the [TraceZipper] with this id
    Traced(u64),
    /// The source isn't traced, so its contents are recorded instead.  The `(path, value)` pairs are
    /// relative to the source's focus, and a value at the focus itself has an empty path
    Unknown(Vec<(Vec<u8>, V)>),
}

impl<V: TraceValue> TraceValue for TraceSrc<V> {
    fn encode(&self, out: &mut Vec<u8>) {
        match self {
            Self::Traced(id) => {
                out.push(0);
                id.encode(out);
            },
            Self::Unknown(entries) => {
                out.push(1);
                entries.encode(out);
            }
        }
    }
    fn decode(input: &mut &[u8]) -> Option<Self> {
        match u8::decode(input)? {
            0 => Some(Self::Traced(u64::decode(input)?)),
            1 => Some(Self::Unknown(Vec::decode(input)?)),
            _ => None
        }
    }
}

/// Defines [TraceOp], with an explicit opcode for each variant, so the encoding stays stable as ops are added
macro_rules! trace_ops {
    ($( $(#[$attr:meta])* $code:literal => $name:ident $({ $($field:ident : $ty:ty),* $(,)? })? ),* $(,)?) => {
        /// One call recorded in a zipper trace.  Most variants correspond to the zipper method with the same name
        #[derive(Clone, Debug, PartialEq, Eq)]
        pub enum TraceOp<V> {
            $( $(#[$attr])* $name $({ $($field: $ty),* })? ),*
        }

        impl<V: TraceValue> TraceValue for TraceOp<V> {
            fn encode(&self, out: &mut Vec<u8>) {
                match self {
                    $( Self::$name $({ $($field),* })? => {
                        out.push($code);
                        $($( $field.encode(out); )*)?
                    } )*
                }
            }
            fn decode(input: &mut &[u8]) -> Option<Self> {
                match u8::decode(input)? {
                    $( $code => Some(Self::$name $({ $($field: <$ty>::decode(input)?),* })?), )*
                    _ => None
                }
            }
        }
    };
}

trace_ops! {
    /// A [TraceZipper] was created around a zipper of type `type_name`
    0 => Created { type_name: String, root_prefix_path: Vec<u8>, path: Vec<u8> },
    /// The [TraceZipper] was dropped
    1 => Dropped,
    /// The value at the focus was modified through a reference returned by an earlier call, such as
    /// [ZipperWriting::get_val_mut].  `val` is the value once the reference was released
    2 => ValWritten { val: V },

    //Zipper
    3 => PathExists,
    4 => IsVal,
    5 => ChildCount,
    6 => ChildMask,

    //ZipperValues, ZipperValuesAt
    7 => Val,
    8 => ValAt { path: Vec<u8> },

    //ZipperSubtries
    9 => NativeSubtries,
    10 => TryMakeMap,
    11 => TrieRef,

    //ZipperMoving
    12 => Depth,
    13 => AtRoot,
    14 => FocusByte,
    15 => Reset,
    16 => ValCount,
    17 => DescendTo { path: Vec<u8> },
    18 => DescendToCheck { path: Vec<u8> },
    19 => DescendToExisting { path: Vec<u8> },
    20 => DescendToVal { path: Vec<u8> },
    21 => DescendToByte { byte: u8 },
    22 => DescendToExistingByte { byte: u8 },
    23 => DescendIndexedByte { idx: usize },
    24 => DescendFirstByte,
    25 => DescendLastByte,
    26 => DescendUntil,
    27 => DescendUntilMaxBytes { max_bytes: usize },
    28 => Ascend { steps: usize },
    29 => AscendByte,
    30 => AscendUntil,
    31 => AscendUntilBranch,
    32 => ToNextSiblingByte,
    33 => ToPrevSiblingByte,
    34 => ToNextStep,

    //ZipperIteration
    35 => ToNextVal,
    36 => DescendLastPath,
    37 => DescendFirstKPath { k: usize },
    38 => ToNextKPath { k: usize },

    //ZipperPath, ZipperAbsolutePath
    39 => Path,
    40 => MoveToPath { path: Vec<u8> },
    41 => OriginPath,
    42 => RootPrefixPath,

    //ZipperReadOnlyValues, ZipperReadOnlyIteration, and their conditional (witness) forms
    43 => GetVal,
    44 => GetValAt { path: Vec<u8> },
    45 => ToNextGetVal,

    //ZipperInfallibleSubtries
    46 => MakeMap,
    47 => GetTrieRef,

    //ZipperProduct
    48 => FocusFactor,
    49 => FactorCount,
    50 => PathIndices,

    //ZipperWriting
    51 => GetValMut,
    52 => GetValOrSetMut { default: V },
    53 => GetValOrSetMutWith,
    54 => SetVal { val: V },
    55 => SetValAt { path: Vec<u8>, val: V },
    56 => RemoveVal { prune: bool },
    57 => ZipperHead,
    58 => Graft { src: TraceSrc<V> },
    59 => GraftSrcAt { src: TraceSrc<V>, path: Vec<u8> },
    /// `map` holds the map's `(path, value)` pairs, as in [TraceSrc::Unknown]
    60 => GraftMap { map: Vec<(Vec<u8>, V)> },
    61 => GraftChildMaps { child_mask: ByteMask, maps: Vec<Vec<(Vec<u8>, V)>>, remove_unset: bool },
    62 => GraftMaskedBranches { src: TraceSrc<V>, child_mask: ByteMask, remove_unset: bool },
    63 => JoinInto { src: TraceSrc<V> },
    64 => JoinMapInto { map: Vec<(Vec<u8>, V)> },
    65 => JoinIntoTake { src: TraceSrc<V>, prune: bool },
    66 => JoinKPathInto { byte_cnt: usize, prune: bool },
    67 => MeetKPathInto { byte_cnt: usize, prune: bool },
    68 => InsertPrefix { prefix: Vec<u8> },
    69 => RemovePrefix { n: usize },
    70 => MeetInto { src: TraceSrc<V>, prune: bool },
    71 => Meet2 { src_a: TraceSrc<V>, src_b: TraceSrc<V> },
    72 => SubtractInto { src: TraceSrc<V>, prune: bool },
    73 => Restrict { src: TraceSrc<V> },
    74 => Restricting { src: TraceSrc<V> },
    75 => TakeMap { prune: bool },
    76 => RemoveBranches { prune: bool },
    77 => RemoveSubtrie { prune: bool },
    78 => RemoveUnmaskedBranches { mask: ByteMask, prune: bool },
    79 => CreatePath,
    80 => PrunePath,
    81 => PruneAscend,
}

// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---
// Trace sink
// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---

struct TraceSink {
    out: Box<dyn Write + Send>,
    val_type: TypeId,
    val_type_name: &'static str,
}

static SINK: Mutex<Option<TraceSink>> = Mutex::new(None);

thread_local! {
    /// Set while a traced call is running on this thread
    static IN_TRACED_OP: Cell<bool> = const { Cell::new(false) };
    /// `Some` while an argument is being probed (see [probe_trace_id]).  A probed `TraceZipper` fills in its id
    static PROBE: Cell<Option<Option<u64>>> = const { Cell::new(None) };
}

fn lock_sink() -> MutexGuard<'static, Option<TraceSink>> {
    //A panic while holding the lock leaves the sink usable, and the trace is most valuable after a panic
    SINK.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

/// Starts a new trace, writing to `out`.  Every [TraceZipper] must use `V` as its value type
///
/// Panics if a trace is already open
pub fn open<V: TraceValue>(mut out: impl Write + Send + 'static) -> io::Result<()> {
    let mut sink = lock_sink();
    assert!(sink.is_none(), "zipper_tracing: a trace is already open");
    let mut header = TRACE_MAGIC.to_vec();
    TRACE_VERSION.encode(&mut header);
    type_name::<V>().to_string().encode(&mut header);
    out.write_all(&header)?;
    *sink = Some(TraceSink { out: Box::new(out), val_type: TypeId::of::<V>(), val_type_name: type_name::<V>() });
    Ok(())
}

/// Starts a new trace, writing to a newly created file at `path`.  See [open]
pub fn open_file<V: TraceValue, P: AsRef<Path>>(path: P) -> io::Result<()> {
    open::<V>(BufWriter::new(File::create(path)?))
}

/// Flushes and closes the trace.  Calls on [TraceZipper]s that are still alive afterwards are not recorded
pub fn close() -> io::Result<()> {
    match lock_sink().take() {
        Some(mut sink) => sink.out.flush(),
        None => Ok(())
    }
}

fn is_open() -> bool {
    lock_sink().is_some()
}

/// Writes one event to the trace, if a trace is open.  `typed` events may contain `W` values, so
/// `W` must match the trace's value type
fn write_event<W: TraceValue>(id: u64, op: &TraceOp<W>, typed: bool) {
    let mut buf = Vec::new();
    id.encode(&mut buf);
    op.encode(&mut buf);
    let mut sink = lock_sink();
    if let Some(sink) = sink.as_mut() {
        if typed {
            assert!(sink.val_type == TypeId::of::<W>(), "zipper_tracing: trace was opened for values of type {}, but a TraceZipper has values of type {}", sink.val_type_name, type_name::<W>());
        }
        if let Err(err) = sink.out.write_all(&buf) {
            //Avoid a double-panic (and abort) when this is a drop during unwinding
            if !std::thread::panicking() {
                panic!("zipper_tracing: failed to write trace: {err}");
            }
        }
    }
}

fn flush_sink() {
    if let Some(sink) = lock_sink().as_mut() {
        let _ = sink.out.flush();
    }
}

/// Decodes a complete trace into `(zipper_id, op)` events
pub fn decode_trace<V: TraceValue>(mut bytes: &[u8]) -> io::Result<Vec<(u64, TraceOp<V>)>> {
    let invalid = |msg: &str| io::Error::new(io::ErrorKind::InvalidData, format!("zipper_tracing: {msg}"));
    let input = &mut bytes;
    let (magic, rest) = input.split_first_chunk::<8>().ok_or_else(|| invalid("truncated header"))?;
    if magic != TRACE_MAGIC {
        return Err(invalid("not a zipper trace"))
    }
    *input = rest;
    if u64::decode(input) != Some(TRACE_VERSION) {
        return Err(invalid("unsupported trace version"))
    }
    let val_type_name = String::decode(input).ok_or_else(|| invalid("truncated header"))?;
    if val_type_name != type_name::<V>() {
        return Err(invalid(&format!("trace has values of type {val_type_name}, not {}", type_name::<V>())))
    }
    let mut events = Vec::new();
    while !input.is_empty() {
        let id = u64::decode(input).ok_or_else(|| invalid("truncated event"))?;
        let op = TraceOp::decode(input).ok_or_else(|| invalid("invalid or truncated op"))?;
        events.push((id, op));
    }
    Ok(events)
}

/// Marks this thread as being inside a traced call, until dropped
struct InOpGuard;

impl InOpGuard {
    /// Returns `None` if the thread is already inside a traced call
    fn enter() -> Option<Self> {
        IN_TRACED_OP.with(|in_op| {
            if in_op.get() {
                None
            } else {
                in_op.set(true);
                Some(InOpGuard)
            }
        })
    }
}

impl Drop for InOpGuard {
    fn drop(&mut self) {
        IN_TRACED_OP.with(|in_op| in_op.set(false))
    }
}

// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---
// TraceZipper
// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---

/// A [Zipper] type that wraps another zipper and records every call made on it into the trace.  See
/// the [module documentation](self)
pub struct TraceZipper<Z> {
    z: Z,
    id: u64,
    /// Set when a `&mut V` was handed out, so the value can be recorded once the reference is released
    val_mut_ref_outstanding: AtomicBool,
    /// Records the value at the focus.  Set alongside `val_mut_ref_outstanding`, from a context that knows `V`
    write_back: Option<fn(&Z, u64)>,
}

impl<Z: ZipperAbsolutePath> TraceZipper<Z> {
    /// Wraps `z`, so calls on it will be recorded as coming from zipper `id`
    ///
    /// Panics if no trace is open
    pub fn new(id: u64, z: Z) -> Self {
        assert!(is_open(), "zipper_tracing: open must be called before creating a TraceZipper");
        if let Some(_guard) = InOpGuard::enter() {
            let op = TraceOp::<()>::Created {
                type_name: type_name::<Z>().to_string(),
                root_prefix_path: z.root_prefix_path().to_vec(),
                path: z.path().to_vec(),
            };
            write_event(id, &op, false);
        }
        Self { z, id, val_mut_ref_outstanding: AtomicBool::new(false), write_back: None }
    }
}

impl<Z> TraceZipper<Z> {
    /// Returns the id that identifies this zipper in the trace
    pub fn id(&self) -> u64 {
        self.id
    }

    /// Records an op that contains no values.  The returned guard must be held for the duration of the call
    #[inline]
    fn begin(&self, op: impl FnOnce() -> TraceOp<()>) -> Option<InOpGuard> {
        self.begin_inner(op, false)
    }

    /// Records an op that may contain values of type `V`
    #[inline]
    fn begin_v<V: TraceValue>(&self, op: impl FnOnce() -> TraceOp<V>) -> Option<InOpGuard> {
        self.begin_inner(op, true)
    }

    fn begin_inner<W: TraceValue>(&self, op: impl FnOnce() -> TraceOp<W>, typed: bool) -> Option<InOpGuard> {
        //The guard is entered before building the op, so calls made on other zippers to capture
        // arguments aren't recorded
        let guard = InOpGuard::enter()?;
        self.flush_val_write();
        write_event(self.id, &op(), typed);
        Some(guard)
    }

    fn flush_val_write(&self) {
        if self.val_mut_ref_outstanding.swap(false, Ordering::Relaxed) {
            if let Some(write_back) = self.write_back {
                write_back(&self.z, self.id);
            }
        }
    }

    /// Answers a probe with this zipper's id, if a probe is active.  Returns `true` if it answered
    fn answer_probe(&self) -> bool {
        PROBE.with(|probe| {
            if probe.get() == Some(None) {
                //This zipper is about to be read as another op's argument, so its value needs to be current in the trace
                self.flush_val_write();
                probe.set(Some(Some(self.id)));
                true
            } else {
                false
            }
        })
    }

    /// Call after recording an op that hands out a `&mut V` to the value at the focus
    fn arm_write_back<V: TraceValue + Clone>(&mut self) where Z: ZipperValues<V> {
        self.write_back = Some(write_back_val::<V, Z>);
        self.val_mut_ref_outstanding.store(true, Ordering::Relaxed);
    }
}

fn write_back_val<V: TraceValue + Clone, Z: ZipperValues<V>>(z: &Z, id: u64) {
    if let Some(val) = z.val() {
        write_event(id, &TraceOp::ValWritten { val: val.clone() }, true);
    }
}

impl<Z> Drop for TraceZipper<Z> {
    fn drop(&mut self) {
        if let Some(_guard) = InOpGuard::enter() {
            self.flush_val_write();
            write_event(self.id, &TraceOp::<()>::Dropped, false);
            flush_sink();
        }
    }
}

fn map_entries<V: Clone + Send + Sync + Unpin, A: Allocator>(map: &PathMap<V, A>) -> Vec<(Vec<u8>, V)> {
    map.iter().map(|(path, val)| (path, val.clone())).collect()
}

/// Returns the id of `src` if it's a [TraceZipper] (or forwards `path_exists` to one).  See the module documentation
fn probe_trace_id<Z: Zipper>(src: &Z) -> Option<u64> {
    struct ProbeGuard;
    impl Drop for ProbeGuard {
        fn drop(&mut self) {
            PROBE.with(|probe| probe.set(None))
        }
    }
    PROBE.with(|probe| probe.set(Some(None)));
    let _guard = ProbeGuard;
    src.path_exists();
    PROBE.with(|probe| probe.get()).flatten()
}

fn trace_src<V: Clone + Send + Sync + Unpin, A: Allocator, S: ZipperInfallibleSubtries<V, A>>(src: &S) -> TraceSrc<V> {
    match probe_trace_id(src) {
        Some(id) => TraceSrc::Traced(id),
        None => TraceSrc::Unknown(map_entries(&src.make_map())),
    }
}

impl<Z: Zipper> Zipper for TraceZipper<Z> {
    fn path_exists(&self) -> bool {
        if self.answer_probe() {
            return false
        }
        let _g = self.begin(|| TraceOp::PathExists);
        self.z.path_exists()
    }
    fn is_val(&self) -> bool { let _g = self.begin(|| TraceOp::IsVal); self.z.is_val() }
    fn child_count(&self) -> usize { let _g = self.begin(|| TraceOp::ChildCount); self.z.child_count() }
    fn child_mask(&self) -> ByteMask { let _g = self.begin(|| TraceOp::ChildMask); self.z.child_mask() }
}

impl<V, Z: ZipperValues<V>> ZipperValues<V> for TraceZipper<Z> {
    fn val(&self) -> Option<&V> { let _g = self.begin(|| TraceOp::Val); self.z.val() }
}

impl<V, Z: ZipperValuesAt<V>> ZipperValuesAt<V> for TraceZipper<Z> {
    fn val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&V> {
        let path = path.as_ref();
        let _g = self.begin(|| TraceOp::ValAt { path: path.to_vec() });
        self.z.val_at(path)
    }
}

impl<V: Clone + Send + Sync, A: Allocator, Z: ZipperSubtries<V, A>> ZipperSubtries<V, A> for TraceZipper<Z> {
    fn native_subtries(&self) -> bool { let _g = self.begin(|| TraceOp::NativeSubtries); self.z.native_subtries() }
    fn try_make_map(&self) -> Option<PathMap<V, A>> { let _g = self.begin(|| TraceOp::TryMakeMap); self.z.try_make_map() }
    fn trie_ref(&self) -> Option<TrieRef<'_, V, A>> { let _g = self.begin(|| TraceOp::TrieRef); self.z.trie_ref() }
    fn alloc(&self) -> A { self.z.alloc() }
}

impl<Z: ZipperMoving> ZipperMoving for TraceZipper<Z> {
    fn depth(&self) -> usize { let _g = self.begin(|| TraceOp::Depth); self.z.depth() }
    fn at_root(&self) -> bool { let _g = self.begin(|| TraceOp::AtRoot); self.z.at_root() }
    fn focus_byte(&self) -> Option<u8> { let _g = self.begin(|| TraceOp::FocusByte); self.z.focus_byte() }
    fn reset(&mut self) { let _g = self.begin(|| TraceOp::Reset); self.z.reset() }
    fn val_count(&self) -> usize { let _g = self.begin(|| TraceOp::ValCount); self.z.val_count() }
    fn descend_to<K: AsRef<[u8]>>(&mut self, k: K) {
        let k = k.as_ref();
        let _g = self.begin(|| TraceOp::DescendTo { path: k.to_vec() });
        self.z.descend_to(k)
    }
    fn descend_to_check<K: AsRef<[u8]>>(&mut self, k: K) -> bool {
        let k = k.as_ref();
        let _g = self.begin(|| TraceOp::DescendToCheck { path: k.to_vec() });
        self.z.descend_to_check(k)
    }
    fn descend_to_existing<K: AsRef<[u8]>>(&mut self, k: K) -> usize {
        let k = k.as_ref();
        let _g = self.begin(|| TraceOp::DescendToExisting { path: k.to_vec() });
        self.z.descend_to_existing(k)
    }
    fn descend_to_val<K: AsRef<[u8]>>(&mut self, k: K) -> usize {
        let k = k.as_ref();
        let _g = self.begin(|| TraceOp::DescendToVal { path: k.to_vec() });
        self.z.descend_to_val(k)
    }
    fn descend_to_byte(&mut self, k: u8) { let _g = self.begin(|| TraceOp::DescendToByte { byte: k }); self.z.descend_to_byte(k) }
    fn descend_to_existing_byte(&mut self, k: u8) -> bool { let _g = self.begin(|| TraceOp::DescendToExistingByte { byte: k }); self.z.descend_to_existing_byte(k) }
    fn descend_indexed_byte(&mut self, idx: usize) -> Option<u8> { let _g = self.begin(|| TraceOp::DescendIndexedByte { idx }); self.z.descend_indexed_byte(idx) }
    fn descend_first_byte(&mut self) -> Option<u8> { let _g = self.begin(|| TraceOp::DescendFirstByte); self.z.descend_first_byte() }
    fn descend_last_byte(&mut self) -> Option<u8> { let _g = self.begin(|| TraceOp::DescendLastByte); self.z.descend_last_byte() }
    fn descend_until(&mut self) -> bool { let _g = self.begin(|| TraceOp::DescendUntil); self.z.descend_until() }
    fn descend_until_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool { let _g = self.begin(|| TraceOp::DescendUntil); self.z.descend_until_observed(obs) }
    fn descend_until_max_bytes(&mut self, max_bytes: usize) -> bool { let _g = self.begin(|| TraceOp::DescendUntilMaxBytes { max_bytes }); self.z.descend_until_max_bytes(max_bytes) }
    fn descend_until_max_bytes_observed<Obs: PathObserver>(&mut self, max_bytes: usize, obs: &mut Obs) -> bool { let _g = self.begin(|| TraceOp::DescendUntilMaxBytes { max_bytes }); self.z.descend_until_max_bytes_observed(max_bytes, obs) }
    fn ascend(&mut self, steps: usize) -> usize { let _g = self.begin(|| TraceOp::Ascend { steps }); self.z.ascend(steps) }
    fn ascend_byte(&mut self) -> bool { let _g = self.begin(|| TraceOp::AscendByte); self.z.ascend_byte() }
    fn ascend_until(&mut self) -> usize { let _g = self.begin(|| TraceOp::AscendUntil); self.z.ascend_until() }
    fn ascend_until_branch(&mut self) -> usize { let _g = self.begin(|| TraceOp::AscendUntilBranch); self.z.ascend_until_branch() }
    fn to_next_sibling_byte(&mut self) -> Option<u8> { let _g = self.begin(|| TraceOp::ToNextSiblingByte); self.z.to_next_sibling_byte() }
    fn to_prev_sibling_byte(&mut self) -> Option<u8> { let _g = self.begin(|| TraceOp::ToPrevSiblingByte); self.z.to_prev_sibling_byte() }
    fn to_next_step(&mut self) -> bool { let _g = self.begin(|| TraceOp::ToNextStep); self.z.to_next_step() }
    fn to_next_step_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool { let _g = self.begin(|| TraceOp::ToNextStep); self.z.to_next_step_observed(obs) }
}

impl<Z: ZipperIteration> ZipperIteration for TraceZipper<Z> {
    fn to_next_val(&mut self) -> bool { let _g = self.begin(|| TraceOp::ToNextVal); self.z.to_next_val() }
    fn to_next_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool { let _g = self.begin(|| TraceOp::ToNextVal); self.z.to_next_val_observed(obs) }
    fn descend_last_path(&mut self) -> bool { let _g = self.begin(|| TraceOp::DescendLastPath); self.z.descend_last_path() }
    fn descend_last_path_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> bool { let _g = self.begin(|| TraceOp::DescendLastPath); self.z.descend_last_path_observed(obs) }
    fn descend_first_k_path(&mut self, k: usize) -> bool { let _g = self.begin(|| TraceOp::DescendFirstKPath { k }); self.z.descend_first_k_path(k) }
    fn descend_first_k_path_observed<Obs: PathObserver>(&mut self, k: usize, obs: &mut Obs) -> bool { let _g = self.begin(|| TraceOp::DescendFirstKPath { k }); self.z.descend_first_k_path_observed(k, obs) }
    fn to_next_k_path(&mut self, k: usize) -> bool { let _g = self.begin(|| TraceOp::ToNextKPath { k }); self.z.to_next_k_path(k) }
    fn to_next_k_path_observed<Obs: PathObserver>(&mut self, k: usize, obs: &mut Obs) -> bool { let _g = self.begin(|| TraceOp::ToNextKPath { k }); self.z.to_next_k_path_observed(k, obs) }
}

impl<Z: ZipperPath> ZipperPath for TraceZipper<Z> {
    fn path(&self) -> &[u8] { let _g = self.begin(|| TraceOp::Path); self.z.path() }
    fn move_to_path<K: AsRef<[u8]>>(&mut self, path: K) -> usize {
        let path = path.as_ref();
        let _g = self.begin(|| TraceOp::MoveToPath { path: path.to_vec() });
        self.z.move_to_path(path)
    }
}

impl<Z: ZipperAbsolutePath> ZipperAbsolutePath for TraceZipper<Z> {
    fn origin_path(&self) -> &[u8] { let _g = self.begin(|| TraceOp::OriginPath); self.z.origin_path() }
    fn root_prefix_path(&self) -> &[u8] { let _g = self.begin(|| TraceOp::RootPrefixPath); self.z.root_prefix_path() }
}

impl<Z: ZipperPathBuffer> ZipperPathBuffer for TraceZipper<Z> {
    unsafe fn origin_path_assert_len(&self, len: usize) -> &[u8] { unsafe{ self.z.origin_path_assert_len(len) } }
    fn prepare_buffers(&mut self) { self.z.prepare_buffers() }
    fn reserve_buffers(&mut self, path_len: usize, stack_depth: usize) { self.z.reserve_buffers(path_len, stack_depth) }
}

impl<Z: ZipperConcrete> ZipperConcrete for TraceZipper<Z> {
    fn shared_node_id(&self) -> Option<u64> { self.z.shared_node_id() }
    fn is_shared(&self) -> bool { self.z.is_shared() }
}

impl<'a, V, Z> ZipperReadOnlyValues<'a, V> for TraceZipper<Z> where Z: ZipperReadOnlyValues<'a, V> {
    fn get_val(&self) -> Option<&'a V> { let _g = self.begin(|| TraceOp::GetVal); self.z.get_val() }
    fn get_val_at<K: AsRef<[u8]>>(&self, path: K) -> Option<&'a V> {
        let path = path.as_ref();
        let _g = self.begin(|| TraceOp::GetValAt { path: path.to_vec() });
        self.z.get_val_at(path)
    }
}

impl<'a, V, Z> ZipperReadOnlyConditionalValues<'a, V> for TraceZipper<Z> where Z: ZipperReadOnlyConditionalValues<'a, V> {
    type WitnessT = Z::WitnessT;
    fn witness<'w>(&self) -> Self::WitnessT { self.z.witness() }
    fn get_val_with_witness<'w>(&self, witness: &'w Self::WitnessT) -> Option<&'w V> where 'a: 'w {
        let _g = self.begin(|| TraceOp::GetVal);
        self.z.get_val_with_witness(witness)
    }
}

impl<'a, V, Z> ZipperReadOnlyIteration<'a, V> for TraceZipper<Z> where Z: ZipperReadOnlyIteration<'a, V> {
    fn to_next_get_val(&mut self) -> Option<&'a V> { let _g = self.begin(|| TraceOp::ToNextGetVal); self.z.to_next_get_val() }
    fn to_next_get_val_observed<Obs: PathObserver>(&mut self, obs: &mut Obs) -> Option<&'a V> { let _g = self.begin(|| TraceOp::ToNextGetVal); self.z.to_next_get_val_observed(obs) }
}

impl<'a, V, Z> ZipperReadOnlyConditionalIteration<'a, V> for TraceZipper<Z> where Z: ZipperReadOnlyConditionalIteration<'a, V> {
    fn to_next_get_val_with_witness<'w>(&mut self, witness: &'w Self::WitnessT) -> Option<&'w V> where 'a: 'w {
        let _g = self.begin(|| TraceOp::ToNextGetVal);
        self.z.to_next_get_val_with_witness(witness)
    }
    fn to_next_get_val_with_witness_observed<'w, Obs: PathObserver>(&mut self, witness: &'w Self::WitnessT, obs: &mut Obs) -> Option<&'w V> where 'a: 'w {
        let _g = self.begin(|| TraceOp::ToNextGetVal);
        self.z.to_next_get_val_with_witness_observed(witness, obs)
    }
}

impl<V: Clone + Send + Sync, A: Allocator, Z: ZipperInfallibleSubtries<V, A>> ZipperInfallibleSubtries<V, A> for TraceZipper<Z> {
    fn make_map(&self) -> PathMap<V, A> { let _g = self.begin(|| TraceOp::MakeMap); self.z.make_map() }
    fn get_trie_ref(&self) -> TrieRef<'_, V, A> { let _g = self.begin(|| TraceOp::GetTrieRef); self.z.get_trie_ref() }
    fn get_focus(&self) -> OpaqueAbstractNodeRef<'_, V, A> { self.z.get_focus() }
    fn get_focus_at<K: AsRef<[u8]>>(&self, path: K) -> OpaqueAbstractNodeRef<'_, V, A> { self.z.get_focus_at(path) }
    fn try_borrow_focus(&self) -> Option<OpaqueTrieNodeRef<'_, V, A>> { self.z.try_borrow_focus() }
}

impl<'a, V: Clone + Send + Sync + 'a, A: Allocator + 'a, Z> ZipperReadOnlySubtries<'a, V, A> for TraceZipper<Z>
    where Z: ZipperReadOnlySubtries<'a, V, A>, Self: ZipperReadOnlyPriv<'a, V, A> + ZipperSubtries<V, A>
{
    type TrieRefT = <Z as ZipperReadOnlySubtries<'a, V, A>>::TrieRefT;
    fn trie_ref_at_path<K: AsRef<[u8]>>(&self, path: K) -> Self::TrieRefT { self.z.trie_ref_at_path(path) }
}

impl<'a, V: Clone + Send + Sync, A: Allocator, Z: ZipperReadOnlyPriv<'a, V, A>> ZipperReadOnlyPriv<'a, V, A> for TraceZipper<Z> {
    fn borrow_raw_parts<'z>(&'z self) -> (TaggedNodeRef<'z, V, A>, &'z [u8], Option<&'z V>) { self.z.borrow_raw_parts() }
    fn take_core(&mut self) -> Option<ReadZipperCore<'a, 'static, V, A>> { self.z.take_core() }
}

impl<Z: ZipperProduct> ZipperProduct for TraceZipper<Z> {
    fn factor_count(&self) -> usize { let _g = self.begin(|| TraceOp::FactorCount); self.z.factor_count() }
    fn focus_factor(&self) -> usize { let _g = self.begin(|| TraceOp::FocusFactor); self.z.focus_factor() }
    fn path_indices(&self) -> &[usize] { let _g = self.begin(|| TraceOp::PathIndices); self.z.path_indices() }
}

impl<V: Clone + Send + Sync, A: Allocator, Z: WriteZipperPriv<V, A>> WriteZipperPriv<V, A> for TraceZipper<Z> {
    fn take_focus(&mut self, prune: bool) -> Option<TrieNodeODRc<V, A>> { self.z.take_focus(prune) }
    fn take_root_prefix_path(&mut self) -> Vec<u8> { self.z.take_root_prefix_path() }
    fn alloc(&self) -> A { WriteZipperPriv::alloc(&self.z) }
}

impl<V, A, Z> ZipperWriting<V, A> for TraceZipper<Z>
    where V: TraceValue + Clone + Send + Sync + Unpin, A: Allocator, Z: ZipperWriting<V, A> + ZipperValues<V>
{
    type ZipperHead<'z> = Z::ZipperHead<'z> where Self: 'z;
    fn get_val_mut(&mut self) -> Option<&mut V> {
        let g = self.begin(|| TraceOp::GetValMut);
        if g.is_some() {
            self.arm_write_back::<V>();
        }
        self.z.get_val_mut()
    }
    fn get_val_or_set_mut(&mut self, default: V) -> &mut V {
        let g = self.begin_v(|| TraceOp::GetValOrSetMut { default: default.clone() });
        if g.is_some() {
            self.arm_write_back::<V>();
        }
        self.z.get_val_or_set_mut(default)
    }
    fn get_val_or_set_mut_with<F>(&mut self, func: F) -> &mut V where F: FnOnce() -> V {
        let g = self.begin(|| TraceOp::GetValOrSetMutWith);
        if g.is_some() {
            self.arm_write_back::<V>();
        }
        self.z.get_val_or_set_mut_with(func)
    }
    fn set_val(&mut self, val: V) -> Option<V> { let _g = self.begin_v(|| TraceOp::SetVal { val: val.clone() }); self.z.set_val(val) }
    fn set_val_at<K: AsRef<[u8]>>(&mut self, path: K, val: V) -> Option<V> {
        let path = path.as_ref();
        let _g = self.begin_v(|| TraceOp::SetValAt { path: path.to_vec(), val: val.clone() });
        self.z.set_val_at(path, val)
    }
    fn remove_val(&mut self, prune: bool) -> Option<V> { let _g = self.begin(|| TraceOp::RemoveVal { prune }); self.z.remove_val(prune) }
    fn zipper_head<'z>(&'z mut self) -> Self::ZipperHead<'z> { let _g = self.begin(|| TraceOp::ZipperHead); self.z.zipper_head() }
    fn graft<RZ: ZipperInfallibleSubtries<V, A>>(&mut self, read_zipper: &RZ) {
        let _g = self.begin_v(|| TraceOp::Graft { src: trace_src(read_zipper) });
        self.z.graft(read_zipper)
    }
    fn graft_src_at<RZ: ZipperInfallibleSubtries<V, A>, K: AsRef<[u8]>>(&mut self, src: &RZ, path: K) {
        let path = path.as_ref();
        let _g = self.begin_v(|| TraceOp::GraftSrcAt { src: trace_src(src), path: path.to_vec() });
        self.z.graft_src_at(src, path)
    }
    fn graft_map(&mut self, map: PathMap<V, A>) {
        let _g = self.begin_v(|| TraceOp::GraftMap { map: map_entries(&map) });
        self.z.graft_map(map)
    }
    fn graft_child_maps<I: IntoIterator<Item=PathMap<V, A>>>(&mut self, child_mask: ByteMask, maps: I, remove_unset: bool) {
        let maps: Vec<PathMap<V, A>> = maps.into_iter().collect();
        let _g = self.begin_v(|| TraceOp::GraftChildMaps { child_mask, maps: maps.iter().map(map_entries).collect(), remove_unset });
        self.z.graft_child_maps(child_mask, maps, remove_unset)
    }
    fn graft_masked_branches<RZ: ZipperInfallibleSubtries<V, A>>(&mut self, src: &RZ, child_mask: ByteMask, remove_unset: bool) {
        let _g = self.begin_v(|| TraceOp::GraftMaskedBranches { src: trace_src(src), child_mask, remove_unset });
        self.z.graft_masked_branches(src, child_mask, remove_unset)
    }
    fn join_into<RZ: ZipperInfallibleSubtries<V, A>>(&mut self, read_zipper: &RZ) -> AlgebraicStatus where V: Lattice {
        let _g = self.begin_v(|| TraceOp::JoinInto { src: trace_src(read_zipper) });
        self.z.join_into(read_zipper)
    }
    fn join_map_into(&mut self, map: PathMap<V, A>) -> AlgebraicStatus where V: Lattice {
        let _g = self.begin_v(|| TraceOp::JoinMapInto { map: map_entries(&map) });
        self.z.join_map_into(map)
    }
    fn join_into_take<RZ: ZipperInfallibleSubtries<V, A> + ZipperWriting<V, A>>(&mut self, src_zipper: &mut RZ, prune: bool) -> AlgebraicStatus where V: Lattice {
        let _g = self.begin_v(|| TraceOp::JoinIntoTake { src: trace_src(&*src_zipper), prune });
        self.z.join_into_take(src_zipper, prune)
    }
    fn join_k_path_into(&mut self, byte_cnt: usize, prune: bool) -> bool where V: Lattice {
        let _g = self.begin(|| TraceOp::JoinKPathInto { byte_cnt, prune });
        self.z.join_k_path_into(byte_cnt, prune)
    }
    fn meet_k_path_into(&mut self, byte_cnt: usize, prune: bool) -> bool where V: Lattice {
        let _g = self.begin(|| TraceOp::MeetKPathInto { byte_cnt, prune });
        self.z.meet_k_path_into(byte_cnt, prune)
    }
    fn insert_prefix<K: AsRef<[u8]>>(&mut self, prefix: K) -> bool {
        let prefix = prefix.as_ref();
        let _g = self.begin(|| TraceOp::InsertPrefix { prefix: prefix.to_vec() });
        self.z.insert_prefix(prefix)
    }
    fn remove_prefix(&mut self, n: usize) -> bool { let _g = self.begin(|| TraceOp::RemovePrefix { n }); self.z.remove_prefix(n) }
    fn meet_into<RZ: ZipperInfallibleSubtries<V, A>>(&mut self, read_zipper: &RZ, prune: bool) -> AlgebraicStatus where V: Lattice {
        let _g = self.begin_v(|| TraceOp::MeetInto { src: trace_src(read_zipper), prune });
        self.z.meet_into(read_zipper, prune)
    }
    fn meet_2<RZA: ZipperInfallibleSubtries<V, A>, RZB: ZipperInfallibleSubtries<V, A>>(&mut self, rz_a: &RZA, rz_b: &RZB) -> AlgebraicStatus where V: Lattice {
        let _g = self.begin_v(|| TraceOp::Meet2 { src_a: trace_src(rz_a), src_b: trace_src(rz_b) });
        self.z.meet_2(rz_a, rz_b)
    }
    fn subtract_into<RZ: ZipperInfallibleSubtries<V, A>>(&mut self, read_zipper: &RZ, prune: bool) -> AlgebraicStatus where V: DistributiveLattice {
        let _g = self.begin_v(|| TraceOp::SubtractInto { src: trace_src(read_zipper), prune });
        self.z.subtract_into(read_zipper, prune)
    }
    fn restrict<RZ: ZipperInfallibleSubtries<V, A>>(&mut self, read_zipper: &RZ) -> AlgebraicStatus {
        let _g = self.begin_v(|| TraceOp::Restrict { src: trace_src(read_zipper) });
        self.z.restrict(read_zipper)
    }
    fn restricting<RZ: ZipperInfallibleSubtries<V, A>>(&mut self, read_zipper: &RZ) -> bool {
        let _g = self.begin_v(|| TraceOp::Restricting { src: trace_src(read_zipper) });
        self.z.restricting(read_zipper)
    }
    fn take_map(&mut self, prune: bool) -> Option<PathMap<V, A>> { let _g = self.begin(|| TraceOp::TakeMap { prune }); self.z.take_map(prune) }
    fn remove_branches(&mut self, prune: bool) -> bool { let _g = self.begin(|| TraceOp::RemoveBranches { prune }); self.z.remove_branches(prune) }
    fn remove_subtrie(&mut self, prune: bool) -> bool { let _g = self.begin(|| TraceOp::RemoveSubtrie { prune }); self.z.remove_subtrie(prune) }
    fn remove_unmasked_branches(&mut self, mask: ByteMask, prune: bool) {
        let _g = self.begin(|| TraceOp::RemoveUnmaskedBranches { mask, prune });
        self.z.remove_unmasked_branches(mask, prune)
    }
    fn create_path(&mut self) -> bool { let _g = self.begin(|| TraceOp::CreatePath); self.z.create_path() }
    fn prune_path(&mut self) -> usize { let _g = self.begin(|| TraceOp::PrunePath); self.z.prune_path() }
    fn prune_ascend(&mut self) -> usize { let _g = self.begin(|| TraceOp::PruneAscend); self.z.prune_ascend() }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;
    use super::*;

    /// The trace is global, so tests that use it must not overlap
    static TEST_LOCK: Mutex<()> = Mutex::new(());

    #[derive(Clone, Default)]
    struct SharedBuf(Arc<Mutex<Vec<u8>>>);

    impl Write for SharedBuf {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> { self.0.lock().unwrap().extend_from_slice(buf); Ok(buf.len()) }
        fn flush(&mut self) -> io::Result<()> { Ok(()) }
    }

    /// Runs `f` with a trace open, and returns the decoded trace
    fn traced(f: impl FnOnce()) -> Vec<(u64, TraceOp<u64>)> {
        let _lock = TEST_LOCK.lock().unwrap_or_else(|poisoned| poisoned.into_inner());
        let buf = SharedBuf::default();
        open::<u64>(buf.clone()).unwrap();
        f();
        close().unwrap();
        let bytes = buf.0.lock().unwrap().clone();
        decode_trace(&bytes).unwrap()
    }

    #[test]
    fn trace_zipper_moves() {
        let map: PathMap<u64> = [("apple", 1), ("apricot", 2), ("banana", 3)].into_iter().collect();
        let events = traced(|| {
            let mut rz = TraceZipper::new(7, map.read_zipper());
            rz.descend_to(b"ap");
            assert!(rz.path_exists());
            assert_eq!(rz.descend_first_byte(), Some(b'p'));
            assert_eq!(rz.ascend(2), 2);
            assert!(rz.to_next_val());
            assert_eq!(rz.val(), Some(&1));
        });
        let ops: Vec<TraceOp<u64>> = events.iter().map(|(id, op)| { assert_eq!(*id, 7); op.clone() }).collect();
        assert!(matches!(&ops[0], TraceOp::Created { root_prefix_path, path, .. } if root_prefix_path.is_empty() && path.is_empty()));
        assert_eq!(&ops[1..], &[
            TraceOp::DescendTo { path: b"ap".to_vec() },
            TraceOp::PathExists,
            TraceOp::DescendFirstByte,
            TraceOp::Ascend { steps: 2 },
            TraceOp::ToNextVal,
            TraceOp::Val,
            TraceOp::Dropped,
        ]);
    }

    #[test]
    fn trace_zipper_writes() {
        let mut dst: PathMap<u64> = PathMap::new();
        let src: PathMap<u64> = [("a", 1), ("ab", 2)].into_iter().collect();
        let events = traced(|| {
            let mut wz = TraceZipper::new(1, dst.write_zipper());
            let rz = TraceZipper::new(2, src.read_zipper());
            wz.descend_to(b"x");
            *wz.get_val_or_set_mut(5) += 10;
            wz.descend_to_byte(b'y');
            //Graft from a traced zipper is recorded by id, and the graft's reads of `rz` aren't recorded
            wz.graft(&rz);
            wz.reset();
            //Graft from an untraced zipper records the source's contents
            let mut untraced = src.read_zipper();
            untraced.descend_to(b"a");
            wz.descend_to(b"z");
            wz.graft(&untraced);
            drop(rz);
        });
        let expected: Vec<(u64, TraceOp<u64>)> = vec![
            (1, TraceOp::DescendTo { path: b"x".to_vec() }),
            (1, TraceOp::GetValOrSetMut { default: 5 }),
            (1, TraceOp::ValWritten { val: 15 }),
            (1, TraceOp::DescendToByte { byte: b'y' }),
            (1, TraceOp::Graft { src: TraceSrc::Traced(2) }),
            (1, TraceOp::Reset),
            (1, TraceOp::DescendTo { path: b"z".to_vec() }),
            (1, TraceOp::Graft { src: TraceSrc::Unknown(vec![(vec![], 1), (b"b".to_vec(), 2)]) }),
            (2, TraceOp::Dropped),
            (1, TraceOp::Dropped),
        ];
        let events: Vec<_> = events.into_iter().filter(|(_, op)| !matches!(op, TraceOp::Created { .. })).collect();
        assert_eq!(events, expected);
        assert_eq!(dst.get(b"x"), Some(&15));
        assert_eq!(dst.get(b"xyab"), Some(&2));
        assert_eq!(dst.get(b"zb"), Some(&2));
    }

    #[test]
    fn trace_zipper_probe() {
        let mut dst: PathMap<u64> = PathMap::new();
        let mut src: PathMap<u64> = PathMap::new();
        let events = traced(|| {
            let mut wz = TraceZipper::new(1, dst.write_zipper());
            let mut src_wz = TraceZipper::new(2, src.write_zipper());
            src_wz.descend_to(b"s");
            *src_wz.get_val_or_set_mut(1) = 3;
            src_wz.reset();
            *src_wz.get_val_or_set_mut(4) = 5;
            //The source's pending write is recorded before the graft, and a transparent wrapper reports the inner id
            wz.graft(&&mut src_wz);
        });
        let events: Vec<_> = events.into_iter().filter(|(_, op)| !matches!(op, TraceOp::Created { .. })).collect();
        assert_eq!(&events[2..], &[
            (2, TraceOp::ValWritten { val: 3 }),
            (2, TraceOp::Reset),
            (2, TraceOp::GetValOrSetMut { default: 4 }),
            (2, TraceOp::ValWritten { val: 5 }),
            (1, TraceOp::Graft { src: TraceSrc::Traced(2) }),
            (2, TraceOp::Dropped),
            (1, TraceOp::Dropped),
        ]);
    }

    #[test]
    fn trace_round_trip() {
        let ops: Vec<TraceOp<u64>> = vec![
            TraceOp::Created { type_name: "Z".to_string(), root_prefix_path: vec![1, 2], path: vec![] },
            TraceOp::DescendIndexedByte { idx: 300 },
            TraceOp::GraftChildMaps { child_mask: [b'a', b'z'].into_iter().collect(), maps: vec![vec![(vec![], u64::MAX)], vec![]], remove_unset: true },
            TraceOp::Meet2 { src_a: TraceSrc::Traced(u64::MAX), src_b: TraceSrc::Unknown(vec![(b"q".to_vec(), 0)]) },
        ];
        let mut bytes = Vec::new();
        for op in &ops {
            op.encode(&mut bytes);
        }
        let mut input = &bytes[..];
        for op in &ops {
            assert_eq!(&TraceOp::<u64>::decode(&mut input).unwrap(), op);
        }
        assert!(input.is_empty());
    }
}
