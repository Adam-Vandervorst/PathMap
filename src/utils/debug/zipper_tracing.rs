
//! Records calls made on traced zippers into explicit binary trace targets, so a run can later
//! be replayed for debugging or visualization
//!
//! Enabled by the non-default `trace_zipper` feature. Values are currently limited to `u64` and
//! `()`; see <https://github.com/Adam-Vandervorst/PathMap/issues/170> for broader value support.
//!
//! Create a [`TraceTarget`], clone its handle into each [`TraceZipper`], drop all attached zippers,
//! then call [`TraceTarget::close`]. Targets are independent and zippers may move between threads.
//!
//! ```
//! use pathmap::{PathMap, zipper::*};
//! use pathmap::utils::debug::zipper_tracing::{decode_trace, TraceTarget, TraceZipper};
//! use std::{io::{self, Write}, sync::{Arc, Mutex}};
//!
//! #[derive(Clone, Default)]
//! struct SharedBuffer(Arc<Mutex<Vec<u8>>>);
//!
//! impl Write for SharedBuffer {
//!     fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
//!         self.0.lock().unwrap().extend_from_slice(bytes);
//!         Ok(bytes.len())
//!     }
//!     fn flush(&mut self) -> io::Result<()> { Ok(()) }
//! }
//!
//! let buffer = SharedBuffer::default();
//! let target = TraceTarget::new::<u64>(buffer.clone())?;
//! let mut source = PathMap::<u64>::new();
//! let mut destination = PathMap::<u64>::new();
//! {
//!     let mut src = TraceZipper::new(source.write_zipper(), target.clone());
//!     let mut dst = TraceZipper::new(destination.write_zipper(), target.clone());
//!     src.set_val_at(b"hello", 42);
//!     dst.graft(&src); // Same-target source operations precede this interaction.
//! } // Both zippers record their departure and publish their remaining events.
//! target.close()?; // Reports incomplete recording or output errors.
//!
//! let events = decode_trace::<u64>(&buffer.0.lock().unwrap())?;
//! assert!(!events.is_empty());
//! assert_eq!(destination.get(b"hello"), Some(&42));
//! # Ok::<(), std::io::Error>(())
//! ```
//!
//! Each thread buffers events for a target together, preserving its order across zippers. Thread
//! migration and same-target cross-zipper calls publish preceding events before their dependencies.
//! A consumer writes length-delimited bitcode batches; [`decode_trace`] assigns sequence numbers
//! in published order. Version 3 uses the bitcode 0.6 encoding and does not read older trace files.
//! Overflow/output errors disable recording and are reported by close; zipper calls keep running.
//!
//! An event is captured as a call begins, so the trace records which operations were called and with
//! what arguments, but not their results.  A player needs its own copy of the trie to follow along.
//!
//! Calls made on a `TraceZipper` while another traced call on the same target and thread is in progress are not
//! recorded, because they're the inner workings of the outer call.  For example, when a traced write
//! zipper grafts from a traced read zipper, only the graft is recorded.  The same applies to calls
//! made from user code that runs inside a traced call, such as a [PathObserver], or the closure passed
//! to [ZipperWriting::get_val_or_set_mut_with].
//!
//! When an operation takes another zipper as an argument, such as [ZipperWriting::graft], the argument
//! is recorded by id if it is a `TraceZipper` on the same target, or by its contents otherwise (see [TraceSrc]).
//! A traced argument is recognized by probing its [Zipper::path_exists] method, so any wrapper that forwards
//! `path_exists` to a `TraceZipper` is reported as that zipper.  That's right for transparent wrappers like
//! `&mut` and `Box`, but an abstract zipper such as a [PrefixZipper] around a `TraceZipper` will be
//! misreported as the `TraceZipper` it wraps.
//!
//! The internal accessor methods (e.g. [ZipperInfallibleSubtries::get_focus]), [ZipperConcrete],
//! [ZipperPathBuffer], and [ZipperReadOnlySubtries] are forwarded without being recorded.

use core::any::{type_name, TypeId};
use core::cell::{Cell, RefCell};
use core::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::collections::{HashMap, HashSet};
use std::fs::File;
use std::io::{self, BufWriter, Write};
use std::path::Path;
use std::sync::{Arc, Mutex, MutexGuard, Weak};
use std::sync::mpsc::{self, SyncSender, TrySendError};
use std::thread::{self, JoinHandle};

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
const TRACE_VERSION: u64 = 3;

// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---
// Encoding
// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---

mod sealed {
    pub trait Sealed {}
    impl Sealed for () {}
    impl Sealed for u64 {}
}

/// A value supported by zipper tracing: `u64` or `()`.
///
/// Broader value support is tracked in <https://github.com/Adam-Vandervorst/PathMap/issues/170>.
/// This trait is sealed until that interface is settled.
pub trait TraceValue: sealed::Sealed + Copy + Send + Sync + 'static {
    #[doc(hidden)]
    fn into_trace(self) -> u64;
    #[doc(hidden)]
    fn from_trace(value: u64) -> Self;
}

impl TraceValue for u64 {
    fn into_trace(self) -> u64 { self }
    fn from_trace(value: u64) -> Self { value }
}

impl TraceValue for () {
    fn into_trace(self) -> u64 { 0 }
    fn from_trace(_: u64) -> Self {}
}

// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---
// Opcodes
// ***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---***---

/// The source argument of an operation that reads from another zipper, such as [ZipperWriting::graft]
#[derive(Clone, Debug, PartialEq, Eq, bitcode::Encode, bitcode::Decode)]
pub enum TraceSrc<V> {
    /// The source is the [TraceZipper] with this id
    Traced(u64),
    /// The source isn't traced, so its contents are recorded instead.  The `(path, value)` pairs are
    /// relative to the source's focus, and a value at the focus itself has an empty path
    Unknown(Vec<(Vec<u8>, V)>),
}

impl<V> TraceSrc<V> {
    fn map_values<W>(self, mut f: impl FnMut(V) -> W) -> TraceSrc<W> {
        match self {
            Self::Traced(id) => TraceSrc::Traced(id),
            Self::Unknown(entries) => TraceSrc::Unknown(entries.into_iter().map(|(p, v)| (p, f(v))).collect()),
        }
    }
}

// Only these fields contain map values; all remaining fields pass through unchanged.
macro_rules! map_trace_field {
    (val, $value:expr, $f:ident) => { $f($value) };
    (default, $value:expr, $f:ident) => { $f($value) };
    (src, $value:expr, $f:ident) => { $value.map_values(&mut $f) };
    (src_a, $value:expr, $f:ident) => { $value.map_values(&mut $f) };
    (src_b, $value:expr, $f:ident) => { $value.map_values(&mut $f) };
    (map, $value:expr, $f:ident) => { $value.into_iter().map(|(p, v)| (p, $f(v))).collect() };
    (maps, $value:expr, $f:ident) => { $value.into_iter().map(|m| m.into_iter().map(|(p, v)| (p, $f(v))).collect()).collect() };
    ($field:ident, $value:expr, $f:ident) => { $value };
}

// Variant order is part of this version's bitcode schema. Keep new variants at the end.
macro_rules! trace_ops {
    ($( $(#[$attr:meta])* $code:literal => $name:ident $({ $($field:ident : $ty:ty),* $(,)? })? ),* $(,)?) => {
        /// One call recorded in a zipper trace. Most variants correspond to the named zipper method.
        #[derive(Clone, Debug, PartialEq, Eq, bitcode::Encode, bitcode::Decode)]
        pub enum TraceOp<V> {
            $( $(#[$attr])* $name $({ $($field: $ty),* })? ),*
        }

        // Bitcode uses declaration order, so keep the documented opcodes honest.
        const _: () = {
            enum Opcode { $( $name ),* }
            $( assert!(Opcode::$name as usize == $code); )*
        };

        impl<V> TraceOp<V> {
            fn map_values<W>(self, mut f: impl FnMut(V) -> W) -> TraceOp<W> {
                match self {
                    $( Self::$name $({ $($field),* })? => TraceOp::$name $({
                        $($field: map_trace_field!($field, $field, f)),*
                    })? ),*
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

type Event = (u64, TraceOp<u64>);

fn lock<T>(mutex: &Mutex<T>) -> MutexGuard<'_, T> {
    mutex.lock().unwrap_or_else(|poisoned| poisoned.into_inner())
}

#[derive(Default)]
struct Failure {
    failed: AtomicBool,
    error: Mutex<Option<(io::ErrorKind, String)>>,
}

impl Failure {
    fn set(&self, error: io::Error) {
        let mut saved = lock(&self.error);
        if saved.is_none() {
            *saved = Some((error.kind(), error.to_string()));
            self.failed.store(true, Ordering::Release);
        }
    }

    fn result(&self) -> io::Result<()> {
        match &*lock(&self.error) {
            Some((kind, message)) => Err(io::Error::new(*kind, message.clone())),
            None => Ok(()),
        }
    }
}

#[derive(Default)]
struct Producer {
    events: Mutex<Vec<Event>>,
}

struct Lifecycle {
    live: HashSet<u64>,
    closed: bool,
    worker: Option<JoinHandle<()>>,
}

struct TargetInner {
    identity: u64,
    val_type: TypeId,
    next_id: AtomicU64,
    lifecycle: Mutex<Lifecycle>,
    sender: SyncSender<Option<Vec<Event>>>,
    failure: Arc<Failure>,
    pool: Arc<Mutex<Vec<Vec<Event>>>>,
    batch_size: usize,
}

/// A cloneable, thread-safe destination for zipper traces, enabled by `trace_zipper`.
///
/// Each thread buffers events for this target together. A consumer encodes published batches
/// with bitcode and writes them to the supplied writer. Recording never waits for queue space:
/// overflow or output failure disables further recording and is reported by [`Self::close`].
/// Drop all attached zippers before closing. Explicit close is required to observe output errors.
#[derive(Clone)]
pub struct TraceTarget(Arc<TargetInner>);

static NEXT_TARGET: AtomicU64 = AtomicU64::new(1);

thread_local! {
    static PRODUCERS: RefCell<HashMap<u64, (Weak<TargetInner>, Arc<Producer>)>> = RefCell::new(HashMap::new());
    static IN_TRACED_OP: RefCell<Vec<u64>> = const { RefCell::new(Vec::new()) };
    // Capturing a source is instrumentation, including when it belongs to another target.
    static CAPTURING: Cell<bool> = const { Cell::new(false) };
    static PROBE: Cell<Option<(u64, Option<u64>)>> = const { Cell::new(None) };
}

impl TraceTarget {
    /// Opens a trace for `u64` or `()` values. The writer is owned by the consumer thread.
    /// Up to 4096 batches can wait for the consumer; producer batches contain up to 256 events.
    pub fn new<V: TraceValue>(out: impl Write + Send + 'static) -> io::Result<Self> {
        Self::with_capacity::<V>(out, 4096)
    }

    /// Opens a trace with a limit on queued batches. A full queue disables recording;
    /// [`Self::close`] then reports that the trace is incomplete. Capacity must be nonzero.
    pub fn with_capacity<V: TraceValue>(out: impl Write + Send + 'static, queued_batches: usize) -> io::Result<Self> {
        Self::with_limits::<V>(out, 256, queued_batches)
    }

    /// Opens a trace backed by a newly created file.
    pub fn open_file<V: TraceValue>(path: impl AsRef<Path>) -> io::Result<Self> {
        Self::new::<V>(BufWriter::new(File::create(path)?))
    }

    fn with_limits<V: TraceValue>(mut out: impl Write + Send + 'static, batch_size: usize, queue_size: usize) -> io::Result<Self> {
        assert!(batch_size > 0 && queue_size > 0);
        out.write_all(TRACE_MAGIC)?;
        out.write_all(&TRACE_VERSION.to_le_bytes())?;
        out.write_all(&[u8::from(TypeId::of::<V>() == TypeId::of::<u64>())])?;
        let (sender, receiver) = mpsc::sync_channel::<Option<Vec<Event>>>(queue_size);
        let failure = Arc::new(Failure::default());
        let pool = Arc::new(Mutex::new(Vec::new()));
        let worker_failure = failure.clone();
        let worker_pool = pool.clone();
        let worker = thread::Builder::new().name("pathmap-trace".into()).spawn(move || {
            let result = (|| -> io::Result<()> {
                let mut buffer = bitcode::Buffer::new();
                while let Ok(Some(mut events)) = receiver.recv() {
                    let bytes = buffer.encode(&events);
                    out.write_all(&(bytes.len() as u64).to_le_bytes())?;
                    out.write_all(bytes)?;
                    events.clear();
                    let mut pool = lock(&worker_pool);
                    if pool.len() < queue_size {
                        pool.push(events);
                    }
                }
                out.flush()
            })();
            if let Err(error) = result {
                worker_failure.set(error);
            }
        })?;
        Ok(Self(Arc::new(TargetInner {
            identity: NEXT_TARGET.fetch_add(1, Ordering::Relaxed),
            val_type: TypeId::of::<V>(),
            next_id: AtomicU64::new(1),
            lifecycle: Mutex::new(Lifecycle { live: HashSet::new(), closed: false, worker: Some(worker) }),
            sender,
            failure,
            pool,
            batch_size,
        })))
    }

    /// Closes the target, draining accepted batches and flushing the writer.
    ///
    /// Fails without closing if any attached zippers remain alive; drop them and retry.
    /// Recording/output errors are sticky and are returned by this and subsequent close calls.
    pub fn close(&self) -> io::Result<()> {
        let mut state = lock(&self.0.lifecycle);
        if !state.live.is_empty() {
            return Err(io::Error::other(format!("zipper_tracing: {} zippers still alive", state.live.len())));
        }
        if !state.closed {
            state.closed = true;
            // Blocking is confined to explicit close, after every producer has departed.
            let _ = self.0.sender.send(None);
            if state.worker.take().is_some_and(|worker| worker.join().is_err()) {
                self.0.failure.set(io::Error::other("zipper_tracing: consumer panicked"));
            }
        }
        self.0.failure.result()
    }

    fn register(&self, id: Option<u64>) -> u64 {
        let mut state = lock(&self.0.lifecycle);
        assert!(!state.closed, "zipper_tracing: target is closed");
        let id = id.unwrap_or_else(|| self.0.next_id.fetch_add(1, Ordering::Relaxed));
        assert!(id < u64::MAX, "zipper_tracing: exhausted zipper IDs");
        assert!(state.live.insert(id), "zipper_tracing: zipper ID already in use");
        self.0.next_id.fetch_max(id + 1, Ordering::Relaxed);
        id
    }

    fn producer(&self) -> Arc<Producer> {
        PRODUCERS.with(|producers| {
            let mut producers = producers.borrow_mut();
            if producers.len() > 16 {
                producers.retain(|_, (target, _)| target.strong_count() != 0);
            }
            producers.entry(self.0.identity)
                .or_insert_with(|| (Arc::downgrade(&self.0), Arc::new(Producer::default())))
                .1.clone()
        })
    }

    // Keep the producer locked through submission: a thread moving another zipper away from
    // this producer must not publish a later batch ahead of the batch we just removed.
    fn publish_locked(&self, events: &mut Vec<Event>) {
        if events.is_empty() { return }
        if self.0.failure.failed.load(Ordering::Acquire) {
            events.clear();
            return
        }
        let replacement = lock(&self.0.pool).pop().unwrap_or_default();
        let batch = std::mem::replace(events, replacement);
        match self.0.sender.try_send(Some(batch)) {
            Ok(()) => {},
            Err(TrySendError::Full(_)) => self.0.failure.set(io::Error::other("zipper_tracing: queue overflow; trace is incomplete")),
            Err(TrySendError::Disconnected(_)) => self.0.failure.set(io::Error::other("zipper_tracing: consumer stopped; trace is incomplete")),
        }
    }

    fn publish(&self, producer: &Producer) {
        self.publish_locked(&mut lock(&producer.events));
    }
}

/// Decodes a complete version-3 trace into `(seq, zipper_id, op)` events.
///
/// Sequence numbers reflect published order; independent threads may publish in either order.
/// The header versions both the event schema and its bitcode encoding (currently bitcode 0.6).
pub fn decode_trace<V: TraceValue>(bytes: &[u8]) -> io::Result<Vec<(u64, u64, TraceOp<V>)>> {
    let invalid = |msg: &str| io::Error::new(io::ErrorKind::InvalidData, format!("zipper_tracing: {msg}"));
    if bytes.len() < 17 || &bytes[..8] != TRACE_MAGIC {
        return Err(invalid("invalid or truncated header"))
    }
    if u64::from_le_bytes(bytes[8..16].try_into().unwrap()) != TRACE_VERSION {
        return Err(invalid("unsupported trace version"))
    }
    if bytes[16] != u8::from(TypeId::of::<V>() == TypeId::of::<u64>()) {
        return Err(invalid("trace value type mismatch"))
    }
    let mut input = &bytes[17..];
    let mut events = Vec::new();
    let mut buffer = bitcode::Buffer::new();
    while !input.is_empty() {
        let (length, rest) = input.split_first_chunk::<8>().ok_or_else(|| invalid("truncated batch length"))?;
        let length = usize::try_from(u64::from_le_bytes(*length)).map_err(|_| invalid("batch too large"))?;
        let (batch, rest) = rest.split_at_checked(length).ok_or_else(|| invalid("truncated batch"))?;
        let batch: Vec<Event> = buffer.decode(batch).map_err(|_| invalid("invalid bitcode batch"))?;
        for (id, op) in batch {
            events.push((events.len() as u64, id, op.map_values(V::from_trace)));
        }
        input = rest;
    }
    Ok(events)
}

/// Suppresses nested calls on the same target while forwarding an outer operation.
struct InOpGuard(u64);

impl InOpGuard {
    fn enter(target: &TraceTarget) -> Option<Self> {
        let identity = target.0.identity;
        if CAPTURING.with(Cell::get) { return None }
        IN_TRACED_OP.with(|active| {
            let mut active = active.borrow_mut();
            if active.contains(&identity) {
                None
            } else {
                active.push(identity);
                Some(Self(identity))
            }
        })
    }
}

impl Drop for InOpGuard {
    fn drop(&mut self) {
        IN_TRACED_OP.with(|active| {
            let mut active = active.borrow_mut();
            let index = active.iter().rposition(|id| *id == self.0).unwrap();
            active.remove(index);
        });
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
    write_back: Option<fn(&Self)>,
    target: TraceTarget,
    producer: Mutex<Arc<Producer>>,
}

impl<Z: ZipperAbsolutePath> TraceZipper<Z> {
    /// Wraps `z`, allocating a zipper ID within `target`.
    ///
    /// Panics if the target is closed or has a different value type.
    pub fn new<V: TraceValue>(z: Z, target: TraceTarget) -> Self
    where Z: ZipperValues<V> {
        Self::construct::<V>(z, target, None)
    }

    /// Wraps `z` using an explicit ID, for clients that assign their own trace identities.
    ///
    /// An ID cannot be used by two live zippers on the same target. Reuse after drop is
    /// allowed, e.g. when the replay client associates a replacement zipper with the same map.
    pub fn with_id<V: TraceValue>(id: u64, z: Z, target: TraceTarget) -> Self
    where Z: ZipperValues<V> {
        Self::construct::<V>(z, target, Some(id))
    }

    fn construct<V: TraceValue>(z: Z, target: TraceTarget, id: Option<u64>) -> Self {
        assert!(target.0.val_type == TypeId::of::<V>(), "zipper_tracing: target value type mismatch");
        let op = TraceOp::<()>::Created {
            type_name: type_name::<Z>().to_string(),
            root_prefix_path: z.root_prefix_path().to_vec(),
            path: z.path().to_vec(),
        };
        let producer = Mutex::new(target.producer());
        let id = target.register(id);
        let traced = Self { z, id, target, producer, val_mut_ref_outstanding: AtomicBool::new(false), write_back: None };
        traced.record(op);
        traced
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
        if self.target.0.failure.failed.load(Ordering::Acquire) { return None }
        let guard = InOpGuard::enter(&self.target)?;
        if typed {
            assert!(self.target.0.val_type == TypeId::of::<W>(), "zipper_tracing: target value type mismatch");
        }
        self.flush_val_write();
        let op = op();
        let interaction = match &op {
            TraceOp::Graft { src } | TraceOp::GraftSrcAt { src, .. } |
            TraceOp::GraftMaskedBranches { src, .. } | TraceOp::JoinInto { src } |
            TraceOp::JoinIntoTake { src, .. } | TraceOp::MeetInto { src, .. } |
            TraceOp::SubtractInto { src, .. } | TraceOp::Restrict { src } |
            TraceOp::Restricting { src } => matches!(src, TraceSrc::Traced(_)),
            TraceOp::Meet2 { src_a, src_b } => matches!(src_a, TraceSrc::Traced(_)) || matches!(src_b, TraceSrc::Traced(_)),
            _ => false,
        };
        self.record(op);
        if interaction {
            self.target.publish(&lock(&self.producer));
        }
        Some(guard)
    }

    fn with_producer<R>(&self, f: impl FnOnce(&Producer) -> R) -> R {
        let current = self.target.producer();
        let mut previous = lock(&self.producer);
        if !Arc::ptr_eq(&previous, &current) {
            self.target.publish(&previous);
            *previous = current;
        }
        f(&previous)
    }

    fn record<V: TraceValue>(&self, op: TraceOp<V>) {
        if self.target.0.failure.failed.load(Ordering::Acquire) { return }
        self.with_producer(|producer| {
            let mut events = lock(&producer.events);
            events.push((self.id, op.map_values(V::into_trace)));
            if events.len() >= self.target.0.batch_size {
                self.target.publish_locked(&mut events);
            }
        });
    }

    fn flush_val_write(&self) {
        if self.val_mut_ref_outstanding.swap(false, Ordering::Relaxed) {
            if let Some(write_back) = self.write_back {
                write_back(self);
            }
        }
    }

    /// A probe also publishes this source's history before its use by another zipper.
    fn answer_probe(&self) -> bool {
        let Some((target, _)) = PROBE.with(Cell::get) else { return false };
        if target == self.target.0.identity {
            self.flush_val_write();
            self.with_producer(|producer| self.target.publish(producer));
            PROBE.with(|probe| probe.set(Some((target, Some(self.id)))));
        }
        true
    }

    /// Call after recording an op that hands out a `&mut V` to the value at the focus
    fn arm_write_back<V: TraceValue + Clone>(&mut self) where Z: ZipperValues<V> {
        self.write_back = Some(write_back_val::<V, Z>);
        self.val_mut_ref_outstanding.store(true, Ordering::Relaxed);
    }
}

fn write_back_val<V: TraceValue, Z: ZipperValues<V>>(zipper: &TraceZipper<Z>) {
    if let Some(val) = zipper.z.val() {
        zipper.record(TraceOp::ValWritten { val: *val });
    }
}

impl<Z> Drop for TraceZipper<Z> {
    fn drop(&mut self) {
        self.flush_val_write();
        self.record(TraceOp::<()>::Dropped);
        self.target.publish(&lock(&self.producer));
        lock(&self.target.0.lifecycle).live.remove(&self.id);
    }
}

fn map_entries<V: Clone + Send + Sync + Unpin, A: Allocator>(map: &PathMap<V, A>) -> Vec<(Vec<u8>, V)> {
    map.iter().map(|(path, val)| (path, val.clone())).collect()
}

/// Captures only same-target zipper identities. Other sources are captured as snapshots.
fn trace_src<V: Clone + Send + Sync + Unpin, A: Allocator, S: ZipperInfallibleSubtries<V, A>>(src: &S) -> TraceSrc<V> {
    struct CaptureGuard(bool, Option<(u64, Option<u64>)>);
    impl Drop for CaptureGuard {
        fn drop(&mut self) {
            CAPTURING.with(|capturing| capturing.set(self.0));
            PROBE.with(|probe| probe.set(self.1));
        }
    }
    let target = IN_TRACED_OP.with(|active| *active.borrow().last().unwrap());
    let _guard = CaptureGuard(CAPTURING.with(|capturing| capturing.replace(true)), PROBE.with(|probe| probe.replace(Some((target, None)))));
    src.path_exists();
    let id = PROBE.with(Cell::get).and_then(|(_, id)| id);
    match id {
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


    #[derive(Clone, Default)]
    struct SharedBuf(Arc<Mutex<Vec<u8>>>);

    impl Write for SharedBuf {
        fn write(&mut self, buf: &[u8]) -> io::Result<usize> { self.0.lock().unwrap().extend_from_slice(buf); Ok(buf.len()) }
        fn flush(&mut self) -> io::Result<()> { Ok(()) }
    }

    /// Runs `f` with a trace open, and returns the decoded trace's `(zipper_id, op)` events, after
    /// checking they're numbered in order
    fn traced(f: impl FnOnce(&TraceTarget)) -> Vec<(u64, TraceOp<u64>)> {
        let buf = SharedBuf::default();
        let target = TraceTarget::new::<u64>(buf.clone()).unwrap();
        f(&target);
        target.close().unwrap();
        let bytes = buf.0.lock().unwrap().clone();
        let events = decode_trace(&bytes).unwrap();
        for (idx, (seq, _, _)) in events.iter().enumerate() {
            assert_eq!(*seq, idx as u64);
        }
        events.into_iter().map(|(_, id, op)| (id, op)).collect()
    }

    #[test]
    fn trace_zipper_moves() {
        let map: PathMap<u64> = [("apple", 1), ("apricot", 2), ("banana", 3)].into_iter().collect();
        let events = traced(|target| {
            let mut rz = TraceZipper::with_id(7, map.read_zipper(), target.clone());
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
        let events = traced(|target| {
            let mut wz = TraceZipper::with_id(1, dst.write_zipper(), target.clone());
            let rz = TraceZipper::with_id(2, src.read_zipper(), target.clone());
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
        let events = traced(|target| {
            let mut wz = TraceZipper::with_id(1, dst.write_zipper(), target.clone());
            let mut src_wz = TraceZipper::with_id(2, src.write_zipper(), target.clone());
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
        let bytes = bitcode::encode(&ops);
        assert_eq!(bitcode::decode::<Vec<TraceOp<u64>>>(&bytes).unwrap(), ops);
    }
    fn read_events(buf: &SharedBuf) -> Vec<(u64, u64, TraceOp<u64>)> {
        decode_trace(&lock(&buf.0)).unwrap()
    }

    #[test]
    fn close_rejects_live_zippers_and_can_be_retried() {
        let buf = SharedBuf::default();
        let target = TraceTarget::new::<u64>(buf.clone()).unwrap();
        let mut map = PathMap::<u64>::new();
        let mut zipper = TraceZipper::new(map.write_zipper(), target.clone());
        let value = zipper.get_val_or_set_mut(1);
        *value = 42;
        assert!(target.close().unwrap_err().to_string().contains("still alive"));
        // Closing failed without inspecting the outstanding reference or disabling recording.
        *value = 43;
        drop(zipper);
        target.close().unwrap();
        target.close().unwrap();
        let events = read_events(&buf);
        assert!(matches!(&events[events.len() - 2].2, TraceOp::ValWritten { val: 43 }));
        assert!(matches!(&events.last().unwrap().2, TraceOp::Dropped));
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            TraceZipper::new(map.read_zipper(), target.clone())
        })).is_err());
    }

    #[test]
    fn unit_values_and_malformed_batches() {
        let buf = SharedBuf::default();
        let target = TraceTarget::new::<()>(buf.clone()).unwrap();
        let mut map = PathMap::<()>::new();
        {
            let mut zipper = TraceZipper::new(map.write_zipper(), target.clone());
            zipper.set_val_at(b"a", ());
        }
        target.close().unwrap();
        let bytes = lock(&buf.0).clone();
        let events = decode_trace::<()>(&bytes).unwrap();
        assert!(matches!(&events[1].2, TraceOp::SetValAt { path, val: () } if path == b"a"));
        assert!(decode_trace::<u64>(&bytes).is_err());
        assert!(decode_trace::<()>(&bytes[..16]).is_err());
        assert!(decode_trace::<()>(&bytes[..bytes.len() - 1]).is_err());
        let mut corrupt = bytes.clone();
        corrupt[17..25].copy_from_slice(&u64::MAX.to_le_bytes());
        assert!(decode_trace::<()>(&corrupt).is_err());
        let mut corrupt = bytes;
        corrupt[25..].fill(255);
        assert!(decode_trace::<()>(&corrupt).is_err());
    }

    #[test]
    fn independent_targets_snapshot_cross_target_sources() {
        let left_buf = SharedBuf::default();
        let right_buf = SharedBuf::default();
        let left = TraceTarget::new::<u64>(left_buf.clone()).unwrap();
        let right = TraceTarget::new::<u64>(right_buf.clone()).unwrap();
        let mut src = PathMap::<u64>::new();
        let mut dst = PathMap::<u64>::new();
        {
            let mut source = TraceZipper::new(src.write_zipper(), left.clone());
            let mut destination = TraceZipper::new(dst.write_zipper(), right.clone());
            *source.get_val_or_set_mut(1) = 7;
            destination.graft(&source);
        }
        left.close().unwrap();
        right.close().unwrap();
        let events = read_events(&right_buf);
        assert!(events.iter().any(|(_, _, op)| matches!(op, TraceOp::Graft { src: TraceSrc::Unknown(entries) } if entries == &vec![(vec![], 7)])));
        // Instrumentation reads of the foreign source were suppressed.
        assert!(!read_events(&left_buf).iter().any(|(_, _, op)| matches!(op, TraceOp::PathExists | TraceOp::MakeMap)));
        assert_eq!(dst.get(b""), Some(&7));
    }

    #[test]
    fn per_thread_order_survives_zipper_migration_and_interaction() {
        let buf = SharedBuf::default();
        let target = TraceTarget::new::<u64>(buf.clone()).unwrap();
        let mut src = PathMap::<u64>::new();
        let mut dst = PathMap::<u64>::new();
        thread::scope(|scope| {
            let mut source = TraceZipper::new(src.write_zipper(), target.clone());
            let mut destination = TraceZipper::new(dst.write_zipper(), target.clone());
            source.set_val(1);
            destination.descend_to_byte(b'x');
            // Both zippers share this thread's buffer, so these alternating calls stay ordered.
            source.descend_to_byte(b'a');
            let source = scope.spawn(move || {
                source.set_val(2);
                *source.get_val_mut().unwrap() = 3;
                source
            }).join().unwrap();
            // The source's pending value and old-thread buffer must precede this graft.
            destination.graft(&source);
            destination.reset();
            drop(source);
        });
        target.close().unwrap();
        let ops: Vec<_> = read_events(&buf).into_iter().map(|(_, id, op)| (id, op)).collect();
        assert_eq!(&ops[2..6], &[
            (1, TraceOp::SetVal { val: 1 }),
            (2, TraceOp::DescendToByte { byte: b'x' }),
            (1, TraceOp::DescendToByte { byte: b'a' }),
            (1, TraceOp::SetVal { val: 2 }),
        ]);
        let write = ops.iter().position(|(_, op)| matches!(op, TraceOp::ValWritten { val: 3 })).unwrap();
        let graft = ops.iter().position(|(_, op)| matches!(op, TraceOp::Graft { src: TraceSrc::Traced(1) })).unwrap();
        let reset = ops.iter().position(|(_, op)| matches!(op, TraceOp::Reset)).unwrap();
        assert!(write < graft && graft < reset);
        assert_eq!(dst.get(b"x"), Some(&3));
    }

    #[test]
    fn zippers_record_concurrently_on_one_target() {
        let buf = SharedBuf::default();
        let target = TraceTarget::new::<u64>(buf.clone()).unwrap();
        thread::scope(|scope| {
            for _ in 0..2 {
                let target = target.clone();
                scope.spawn(move || {
                    let mut map = PathMap::<u64>::new();
                    let mut zipper = TraceZipper::new(map.write_zipper(), target);
                    zipper.set_val(10);
                    zipper.set_val(20);
                });
            }
        });
        target.close().unwrap();
        let events = read_events(&buf);
        for id in 1..=2 {
            let ops: Vec<_> = events.iter().filter(|(_, z, _)| *z == id).map(|(_, _, op)| op).collect();
            assert!(matches!(ops[0], TraceOp::Created { .. }));
            assert_eq!(ops[1], &TraceOp::SetVal { val: 10 });
            assert_eq!(ops[2], &TraceOp::SetVal { val: 20 });
            assert_eq!(ops[3], &TraceOp::Dropped);
        }
    }

    #[test]
    fn output_errors_are_returned_by_close_without_panicking_zipper_calls() {
        struct BrokenWriter(usize);
        impl Write for BrokenWriter {
            fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
                self.0 += 1;
                if self.0 > 3 {
                    Err(io::Error::new(io::ErrorKind::BrokenPipe, "test output failure"))
                } else {
                    Ok(bytes.len())
                }
            }
            fn flush(&mut self) -> io::Result<()> { Ok(()) }
        }
        let target = TraceTarget::new::<u64>(BrokenWriter(0)).unwrap();
        let mut map = PathMap::<u64>::new();
        {
            let mut zipper = TraceZipper::new(map.write_zipper(), target.clone());
            zipper.set_val(7);
        }
        assert_eq!(target.close().unwrap_err().kind(), io::ErrorKind::BrokenPipe);
        assert_eq!(target.close().unwrap_err().kind(), io::ErrorKind::BrokenPipe);
        assert_eq!(map.get(b""), Some(&7));
    }

    #[test]
    fn queue_overflow_disables_recording_without_blocking() {
        struct GatedWriter {
            writes: usize,
            entered: mpsc::Sender<()>,
            release: mpsc::Receiver<()>,
        }
        impl Write for GatedWriter {
            fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
                if self.writes == 3 {
                    self.entered.send(()).unwrap();
                    self.release.recv().unwrap();
                }
                self.writes += 1;
                Ok(bytes.len())
            }
            fn flush(&mut self) -> io::Result<()> { Ok(()) }
        }
        let (entered_tx, entered_rx) = mpsc::channel();
        let (release_tx, release_rx) = mpsc::channel();
        let writer = GatedWriter { writes: 0, entered: entered_tx, release: release_rx };
        let target = TraceTarget::with_limits::<u64>(writer, 1, 1).unwrap();
        let mut map = PathMap::<u64>::new();
        let mut zipper = TraceZipper::new(map.write_zipper(), target.clone());
        entered_rx.recv().unwrap();
        zipper.set_val(1); // Fills the only waiting slot.
        zipper.set_val(2); // Must fail recording immediately rather than wait for the writer.
        assert!(target.0.failure.failed.load(Ordering::Acquire));
        zipper.set_val(3); // Map operations continue after failure.
        drop(zipper);
        release_tx.send(()).unwrap();
        assert!(target.close().unwrap_err().to_string().contains("overflow"));
        assert_eq!(map.get(b""), Some(&3));
    }

}
