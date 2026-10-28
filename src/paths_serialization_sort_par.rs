//! Parallel external bytewise sorting for unordered `.paths` streams.
//!
//! Same contract as [`super::sort_paths`], built the way the `sortbin` tool is:
//!
//! * **Ingest.** One thread inflates the input straight into a segment arena;
//!   the decompressed `[u32 len][bytes]` stream *is* the arena, so paths are
//!   never copied. Full segments go to background workers, which index them
//!   into 16-byte keys (an 8-byte big-endian prefix plus offset and length),
//!   sort and deduplicate them. Most comparisons are settled by the prefix
//!   alone, without touching the path bytes.
//! * **Spill.** Only when the budget is filling up: the sorted segments in
//!   memory are merged into one run file, in the background while decoding
//!   continues, so there are few, large runs and the decoder rarely waits.
//! * **Output.** Splitters sampled from all segments and runs cut the key
//!   space into ranges. Ranges are independent (every copy of a path lands in
//!   the same one), so each is merged and deduplicated by one worker, then
//!   deflated by one worker with the previous range's last 32 KiB as its
//!   dictionary. The raw deflate blocks are concatenated into one zlib stream,
//!   as pigz does, so the result decodes like any other `.paths` file.
//!
//! Without the parallel deflate the output alone would cost as much as all of
//! the rest: level-7 deflate runs at roughly 20 MB/s per core.
//!
//! Segment arenas, key arrays, merge buffers and deflate streams are recycled
//! rather than freed, so memory stays flat across spills instead of growing
//! with allocator fragmentation.
use super::SerializationStats;
use libz_ng_sys::*;
use std::{
    cmp::Ordering,
    fs::{self, File},
    io::{self, Read, Write},
    ops::Range,
    path::{Path, PathBuf},
    sync::{
        Condvar, Mutex, PoisonError,
        atomic::{AtomicUsize, Ordering::Relaxed},
    },
    thread::{Scope, ScopedJoinHandle},
};

const MIB: usize = 1 << 20;
/// Largest segment handed to one sorting worker.
const MAX_SEGMENT: usize = 64 * MIB;
/// Most decompressed bytes produced per `inflate` call.
const INFLATE_STEP: usize = 256 * 1024;
/// A run keeps one sample per this many bytes (more for long paths).
const SAMPLE_GAP: usize = 4096;
/// Deflate window, and so the dictionary each range is primed with.
const WINDOW: usize = 32 * 1024;
/// Same level as `serialize_paths_from_funcs`.
const LEVEL: i32 = 7;
/// zlib header for deflate with a 32 KiB window at level 7..=9.
const ZLIB_HEADER: [u8; 2] = [0x78, 0xDA];

fn lock<T>(m: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
    m.lock().unwrap_or_else(PoisonError::into_inner)
}

fn into_inner<T>(m: Mutex<T>) -> T {
    m.into_inner().unwrap_or_else(PoisonError::into_inner)
}

fn invalid(msg: &'static str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, msg)
}

fn too_long() -> io::Error {
    invalid("path exceeds sort memory budget")
}

// ---------------------------------------------------------------------- keys

/// A path in a segment: its first 8 bytes big-endian (zero padded), so that
/// integer order is byte order, and where its bytes are.
#[derive(Clone, Copy)]
struct Key {
    pre: u64,
    off: u32,
    len: u32,
}

#[inline(always)]
fn prefix(p: &[u8]) -> u64 {
    let mut t = [0u8; 8];
    let n = p.len().min(8);
    t[..n].copy_from_slice(&p[..n]);
    u64::from_be_bytes(t)
}

/// Prefix of `data[off..off + len]`, reading 8 bytes at once when it can.
#[inline(always)]
fn prefix_at(data: &[u8], off: usize, len: usize) -> u64 {
    match data.get(off..off + 8) {
        Some(b) => {
            let v = u64::from_be_bytes(b.try_into().unwrap());
            // keep the top len bytes; checked_shl covers len == 0
            v & (!0u64).checked_shl(8 * (8 - len.min(8)) as u32).unwrap_or(0)
        }
        None => prefix(&data[off..off + len]),
    }
}

#[inline(always)]
fn key_path<'a>(bytes: &'a [u8], k: &Key) -> &'a [u8] {
    &bytes[k.off as usize..k.off as usize + k.len as usize]
}

#[inline(always)]
fn cmp_keys(bytes: &[u8], a: &Key, b: &Key) -> Ordering {
    if a.pre != b.pre {
        return a.pre.cmp(&b.pre);
    }
    if a.len >= 8 && b.len >= 8 {
        // the first 8 bytes are known to be equal
        key_path(bytes, a)[8..].cmp(&key_path(bytes, b)[8..])
    } else {
        // equal padded prefixes and one path shorter than 8 bytes: the shorter
        // path is a prefix of the other
        a.len.cmp(&b.len)
    }
}

// ------------------------------------------------------------------ threads

/// Run `f(i)` for every `i < tasks` on up to `threads` threads, taking tasks
/// from a shared counter. Runs inline when one thread is enough.
fn parallel_for(tasks: usize, threads: usize, f: impl Fn(usize) + Sync) {
    let threads = threads.min(tasks);
    if threads <= 1 {
        (0..tasks).for_each(f);
        return;
    }
    let next = AtomicUsize::new(0);
    std::thread::scope(|s| {
        for _ in 0..threads {
            s.spawn(|| {
                loop {
                    let i = next.fetch_add(1, Relaxed);
                    if i >= tasks {
                        break;
                    }
                    f(i);
                }
            });
        }
    });
}

/// Keeps the first error reported by any worker.
#[derive(Default)]
struct FirstError(Mutex<Option<io::Error>>);
impl FirstError {
    fn set(&self, e: io::Error) {
        lock(&self.0).get_or_insert(e);
    }
    fn failed(&self) -> bool {
        lock(&self.0).is_some()
    }
    fn take(self) -> io::Result<()> {
        match into_inner(self.0) {
            Some(e) => Err(e),
            None => Ok(()),
        }
    }
}

// ----------------------------------------------------------------- segments

/// A slice of the decompressed input: whole `[u32 len][bytes]` records, and
/// once sorted, keys for them. `pieces` are independently sorted and
/// deduplicated ranges of `keys`.
#[derive(Default)]
struct Segment {
    bytes: Vec<u8>,
    records: usize,
    keys: Vec<Key>,
    pieces: Vec<Range<usize>>,
}

impl Segment {
    fn cost(&self) -> usize {
        self.bytes.len() + self.records * size_of::<Key>()
    }

    /// Index, sort and deduplicate, as `pieces` pieces sorted in parallel.
    fn sort(&mut self, pieces: usize) {
        let bytes = &self.bytes;
        let mut keys = std::mem::take(&mut self.keys);
        keys.clear();
        keys.reserve(self.records);
        let mut at = 0;
        while at < bytes.len() {
            let len = u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap()) as usize;
            keys.push(Key { pre: prefix_at(bytes, at + 4, len), off: (at + 4) as u32, len: len as u32 });
            at += 4 + len;
        }
        let piece_len = keys.len().div_ceil(pieces.max(1)).max(1 << 14);
        let sort_piece = |piece: &mut [Key]| -> usize {
            piece.sort_unstable_by(|a, b| cmp_keys(bytes, a, b));
            let mut kept = 0;
            for i in 0..piece.len() {
                if kept == 0 || cmp_keys(bytes, &piece[kept - 1], &piece[i]) != Ordering::Equal {
                    piece[kept] = piece[i];
                    kept += 1;
                }
            }
            kept
        };
        let kept: Vec<usize> = if keys.len() <= piece_len {
            vec![sort_piece(&mut keys)]
        } else {
            std::thread::scope(|s| {
                let handles: Vec<_> =
                    keys.chunks_mut(piece_len).map(|piece| s.spawn(move || sort_piece(piece))).collect();
                handles.into_iter().map(|h| h.join().unwrap()).collect()
            })
        };
        self.pieces = kept.iter().enumerate().map(|(i, &n)| i * piece_len..i * piece_len + n).collect();
        self.keys = keys;
    }
}

/// Background sorting of full segments while the decoder keeps going.
#[derive(Default)]
struct Pool {
    state: Mutex<PoolState>,
    cv: Condvar,
}

#[derive(Default)]
struct PoolState {
    queue: Vec<Segment>,
    done: Vec<Segment>,
    pending: usize,
    closed: bool,
    panicked: bool,
}

impl Pool {
    fn submit(&self, seg: Segment, inline: bool) {
        if inline {
            let mut seg = seg;
            seg.sort(1);
            lock(&self.state).done.push(seg);
            return;
        }
        let mut st = lock(&self.state);
        st.pending += 1;
        st.queue.push(seg);
        self.cv.notify_all();
    }

    /// Take the segments sorted so far, without waiting.
    fn take_done(&self) -> Vec<Segment> {
        std::mem::take(&mut lock(&self.state).done)
    }

    /// Wait for every submitted segment and take them all.
    fn drain(&self) -> io::Result<Vec<Segment>> {
        let mut st = lock(&self.state);
        while st.pending > 0 && !st.panicked {
            st = self.cv.wait(st).unwrap_or_else(PoisonError::into_inner);
        }
        if st.panicked {
            return Err(io::Error::other("sort worker panicked"));
        }
        Ok(std::mem::take(&mut st.done))
    }

    fn close(&self) {
        lock(&self.state).closed = true;
        self.cv.notify_all();
    }

    fn work(&self) {
        struct Guard<'a>(&'a Pool);
        impl Drop for Guard<'_> {
            fn drop(&mut self) {
                if std::thread::panicking() {
                    lock(&self.0.state).panicked = true;
                    self.0.cv.notify_all();
                }
            }
        }
        let _guard = Guard(self);
        loop {
            let mut seg = {
                let mut st = lock(&self.state);
                loop {
                    if let Some(seg) = st.queue.pop() {
                        break seg;
                    }
                    if st.closed {
                        return;
                    }
                    st = self.cv.wait(st).unwrap_or_else(PoisonError::into_inner);
                }
            };
            seg.sort(1);
            let mut st = lock(&self.state);
            st.done.push(seg);
            st.pending -= 1;
            self.cv.notify_all();
        }
    }
}

// --------------------------------------------------------------------- runs

/// A sorted, deduplicated run file of `[u32 len][bytes]` records, with a
/// sample of its records: sample `j` is the record starting at `sample_off[j]`.
struct Run {
    path: PathBuf,
    file: File,
    len: u64,
    sample_off: Vec<u64>,
    sample_end: Vec<usize>,
    sample_bytes: Vec<u8>,
}

impl Run {
    fn sample(&self, j: usize) -> &[u8] {
        let start = if j == 0 { 0 } else { self.sample_end[j - 1] };
        &self.sample_bytes[start..self.sample_end[j]]
    }
    fn samples(&self) -> usize {
        self.sample_off.len()
    }
}

#[cfg(unix)]
fn read_at(run: &Run, buf: &mut [u8], off: u64) -> io::Result<()> {
    std::os::unix::fs::FileExt::read_exact_at(&run.file, buf, off)
}

#[cfg(windows)]
fn read_at(run: &Run, mut buf: &mut [u8], mut off: u64) -> io::Result<()> {
    use std::os::windows::fs::FileExt;
    while !buf.is_empty() {
        match run.file.seek_read(buf, off) {
            Ok(0) => return Err(io::ErrorKind::UnexpectedEof.into()),
            Ok(n) => {
                buf = &mut buf[n..];
                off += n as u64;
            }
            Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
            Err(e) => return Err(e),
        }
    }
    Ok(())
}

#[cfg(not(any(unix, windows)))]
fn read_at(run: &Run, buf: &mut [u8], off: u64) -> io::Result<()> {
    use std::io::{Seek, SeekFrom};
    let mut f = File::open(&run.path)?;
    f.seek(SeekFrom::Start(off))?;
    f.read_exact(buf)
}

/// Appends merged ranges to a new run file, sampling as it goes.
struct RunWriter {
    run: Run,
    since: usize,
}

impl RunWriter {
    fn push(&mut self, raw: &[u8]) -> io::Result<()> {
        let mut at = 0;
        while at < raw.len() {
            let len = u32::from_le_bytes(raw[at..at + 4].try_into().unwrap()) as usize;
            // one sample per SAMPLE_GAP bytes, and per 32 path lengths, so
            // samples never hold more than 1/32 of the run
            if self.since >= SAMPLE_GAP.max(32 * len) {
                self.run.sample_off.push(self.run.len + at as u64);
                self.run.sample_bytes.extend_from_slice(&raw[at + 4..at + 4 + len]);
                self.run.sample_end.push(self.run.sample_bytes.len());
                self.since = 0;
            }
            self.since += 4 + len;
            at += 4 + len;
        }
        self.run.file.write_all(raw)?;
        self.run.len += raw.len() as u64;
        Ok(())
    }
}

// -------------------------------------------------------------------- merge

/// Something sorted and deduplicated to merge from.
enum Source<'a> {
    Mem { bytes: &'a [u8], keys: &'a [Key] },
    Disk(&'a Run),
}

/// Ranges of the key space, and where each range starts and ends in each
/// source: key indices for memory, byte offsets for runs. A run's bounds are
/// rounded out to its samples, so its slice can hold records just outside the
/// range; the merge skips those.
struct Plan {
    splitters: Vec<Vec<u8>>,
    bounds: Vec<Vec<(u64, u64)>>,
}

impl Plan {
    fn ranges(&self) -> usize {
        self.splitters.len() + 1
    }

    fn new(sources: &[Source], range_bytes: usize) -> Plan {
        let total: u64 = sources
            .iter()
            .map(|s| match s {
                Source::Mem { keys, .. } => keys.iter().map(|k| 4 + k.len as u64).sum(),
                Source::Disk(run) => run.len,
            })
            .sum();
        let nranges = total.div_ceil(range_bytes as u64).max(1);
        // about 32 candidates per range: plenty to place splitters well
        let gap = (SAMPLE_GAP as u64).max(total / (nranges * 32));

        let mut cand: Vec<(&[u8], u64)> = Vec::new();
        for s in sources {
            let mut acc = 0u64;
            match s {
                Source::Mem { bytes, keys } => {
                    for k in keys.iter() {
                        acc += 4 + k.len as u64;
                        if acc >= gap {
                            cand.push((key_path(bytes, k), acc));
                            acc = 0;
                        }
                    }
                }
                Source::Disk(run) => {
                    for j in 0..run.samples() {
                        let next = run.sample_off.get(j + 1).copied().unwrap_or(run.len);
                        acc += next - run.sample_off[j];
                        if acc >= gap {
                            cand.push((run.sample(j), acc));
                            acc = 0;
                        }
                    }
                }
            }
        }
        cand.sort_unstable_by(|a, b| a.0.cmp(b.0));
        let weight: u64 = cand.iter().map(|c| c.1).sum();
        let step = (weight / nranges).max(1);
        let mut splitters: Vec<Vec<u8>> = Vec::new();
        let (mut acc, mut next) = (0u64, step);
        for &(p, w) in &cand {
            acc += w;
            if acc >= next && splitters.len() + 1 < nranges as usize {
                if splitters.last().map(Vec::as_slice) != Some(p) {
                    splitters.push(p.to_vec());
                }
                next += step;
            }
        }

        let bounds = sources
            .iter()
            .map(|s| match s {
                Source::Mem { bytes, keys } => {
                    let mut at: Vec<u64> = vec![0];
                    at.extend(splitters.iter().map(|sp| {
                        keys.partition_point(|k| key_path(bytes, k) < sp.as_slice()) as u64
                    }));
                    at.push(keys.len() as u64);
                    at.windows(2).map(|w| (w[0], w[1])).collect()
                }
                Source::Disk(run) => {
                    // first sample >= each splitter
                    let js: Vec<usize> = splitters
                        .iter()
                        .map(|sp| {
                            let (mut lo, mut hi) = (0, run.samples());
                            while lo < hi {
                                let mid = (lo + hi) / 2;
                                if run.sample(mid) < sp.as_slice() {
                                    lo = mid + 1;
                                } else {
                                    hi = mid;
                                }
                            }
                            lo
                        })
                        .collect();
                    (0..splitters.len() + 1)
                        .map(|p| {
                            let start = match p.checked_sub(1).map(|q| js[q]) {
                                None | Some(0) => 0,
                                Some(j) => run.sample_off[j - 1],
                            };
                            let end = match js.get(p) {
                                Some(&j) if j < run.samples() => run.sample_off[j],
                                _ => run.len,
                            };
                            (start, end.max(start))
                        })
                        .collect()
                }
            })
            .collect();
        Plan { splitters, bounds }
    }
}

/// Reusable buffers for one range of a batch: the merged records, the read
/// buffer of each run, and the range's deflate dictionary and output.
#[derive(Default)]
struct Slot {
    raw: Vec<u8>,
    count: u64,
    bufs: Vec<Vec<u8>>,
    dict: Vec<u8>,
    packed: Vec<u8>,
    adler: u32,
}

/// The current record of one source within one range.
struct Cursor<'a> {
    cur: &'a [u8],
    src: CursorSrc<'a>,
}

enum CursorSrc<'a> {
    Mem { bytes: &'a [u8], keys: std::slice::Iter<'a, Key> },
    Disk { buf: &'a [u8], at: usize, hi: Option<&'a [u8]> },
}

impl<'a> Cursor<'a> {
    fn mem(bytes: &'a [u8], keys: &'a [Key]) -> Option<Cursor<'a>> {
        let mut c = Cursor { cur: &[], src: CursorSrc::Mem { bytes, keys: keys.iter() } };
        c.advance().ok()?.then_some(c)
    }

    fn disk(buf: &'a [u8], lo: Option<&[u8]>, hi: Option<&'a [u8]>) -> io::Result<Option<Cursor<'a>>> {
        let mut c = Cursor { cur: &[], src: CursorSrc::Disk { buf, at: 0, hi } };
        loop {
            if !c.advance()? {
                return Ok(None);
            }
            if lo.is_none_or(|lo| c.cur >= lo) {
                return Ok(Some(c));
            }
        }
    }

    #[inline(always)]
    fn advance(&mut self) -> io::Result<bool> {
        match &mut self.src {
            CursorSrc::Mem { bytes, keys } => match keys.next() {
                Some(k) => {
                    self.cur = key_path(bytes, k);
                    Ok(true)
                }
                None => Ok(false),
            },
            CursorSrc::Disk { buf, at, hi } => {
                if *at == buf.len() {
                    return Ok(false);
                }
                let head = buf.get(*at..*at + 4).ok_or_else(|| invalid("truncated sort run"))?;
                let len = u32::from_le_bytes(head.try_into().unwrap()) as usize;
                let rec = buf.get(*at + 4..*at + 4 + len).ok_or_else(|| invalid("truncated sort run"))?;
                if hi.is_some_and(|hi| rec >= hi) {
                    *at = buf.len();
                    return Ok(false);
                }
                *at += 4 + len;
                self.cur = rec;
                Ok(true)
            }
        }
    }
}

/// Min-heap entry: the 8 bytes of a cursor's record after the bytes every
/// record of the range shares, and the cursor.
type Entry = (u64, u32);

#[inline(always)]
fn entry_less(c: &[Cursor], skip: usize, a: Entry, b: Entry) -> bool {
    if a.0 != b.0 { a.0 < b.0 } else { c[a.1 as usize].cur[skip..] < c[b.1 as usize].cur[skip..] }
}

fn sift_down(c: &[Cursor], skip: usize, heap: &mut [Entry], mut i: usize) {
    loop {
        let (l, r) = (2 * i + 1, 2 * i + 2);
        let mut m = i;
        if l < heap.len() && entry_less(c, skip, heap[l], heap[m]) {
            m = l;
        }
        if r < heap.len() && entry_less(c, skip, heap[r], heap[m]) {
            m = r;
        }
        if m == i {
            return;
        }
        heap.swap(i, m);
        i = m;
    }
}

/// Merge range `p` of every source into `slot.raw` as records, dropping
/// duplicates, and count them.
fn merge_range(sources: &[Source], plan: &Plan, p: usize, slot: &mut Slot) -> io::Result<()> {
    let Slot { raw: out, count, bufs, .. } = slot;
    out.clear();
    *count = 0;
    bufs.resize_with(sources.len(), Vec::new);
    for (i, s) in sources.iter().enumerate() {
        if let Source::Disk(run) = s {
            let (start, end) = plan.bounds[i][p];
            let buf = &mut bufs[i];
            buf.resize((end - start) as usize, 0);
            read_at(run, buf, start)?;
        }
    }
    let lo = p.checked_sub(1).map(|q| plan.splitters[q].as_slice());
    let hi = plan.splitters.get(p).map(Vec::as_slice);
    // Every record in [lo, hi) starts with the bytes lo and hi share, so
    // comparisons can start after them: the 8-byte prefix then separates
    // records that would otherwise all tie on it.
    let skip = match (lo, hi) {
        (Some(lo), Some(hi)) => lo.iter().zip(hi).take_while(|(a, b)| a == b).count(),
        _ => 0,
    };
    let mut cursors = Vec::with_capacity(sources.len());
    for (i, s) in sources.iter().enumerate() {
        let (start, end) = plan.bounds[i][p];
        let c = match s {
            Source::Mem { bytes, keys } => Cursor::mem(bytes, &keys[start as usize..end as usize]),
            Source::Disk(_) => Cursor::disk(&bufs[i], lo, hi)?,
        };
        cursors.extend(c);
    }
    let mut heap: Vec<Entry> =
        cursors.iter().enumerate().map(|(i, c)| (prefix(&c.cur[skip..]), i as u32)).collect();
    for i in (0..heap.len() / 2).rev() {
        sift_down(&cursors, skip, &mut heap, i);
    }
    let mut prev: Option<&[u8]> = None;
    while let Some(&(_, top)) = heap.first() {
        let c = &mut cursors[top as usize];
        let rec = c.cur;
        if prev != Some(rec) {
            out.extend_from_slice(&(rec.len() as u32).to_le_bytes());
            out.extend_from_slice(rec);
            *count += 1;
            prev = Some(rec);
        }
        if c.advance()? {
            heap[0].0 = prefix(&c.cur[skip..]);
        } else {
            heap.swap_remove(0);
        }
        sift_down(&cursors, skip, &mut heap, 0);
    }
    Ok(())
}

// ------------------------------------------------------------------- zlib

/// A boxed `z_stream`: zlib-ng checks that a stream has not moved since init.
struct ZStream {
    strm: Box<z_stream>,
    deflate: bool,
}

// SAFETY: a z_stream holds no thread-bound state; it is only ever used by one
// thread at a time.
unsafe impl Send for ZStream {}

impl ZStream {
    fn zeroed() -> Box<z_stream> {
        //SAFETY: zlib expects a zeroed stream; null allocator pointers select its default allocator
        #[allow(invalid_value)]
        Box::new(unsafe { std::mem::MaybeUninit::zeroed().assume_init() })
    }

    fn inflate() -> io::Result<ZStream> {
        let mut strm = Self::zeroed();
        if unsafe { zng_inflateInit(&mut *strm) } != Z_OK {
            return Err(io::Error::other("failed to init zlib-ng inflate"));
        }
        Ok(ZStream { strm, deflate: false })
    }

    /// Raw deflate (no zlib wrapper): the wrapper is written once, around
    /// all the blocks.
    fn deflate() -> io::Result<ZStream> {
        let mut strm = Self::zeroed();
        if unsafe { zng_deflateInit2(&mut *strm, LEVEL, Z_DEFLATED, -15, 8, Z_DEFAULT_STRATEGY) } != Z_OK {
            return Err(io::Error::other("failed to init zlib-ng deflate"));
        }
        Ok(ZStream { strm, deflate: true })
    }

    /// Deflate `raw` as a continuation of `dict`. The output ends on a byte
    /// boundary (sync flush), or with the final block when `finish`.
    fn compress(&mut self, dict: &[u8], raw: &[u8], finish: bool, out: &mut Vec<u8>) -> io::Result<()> {
        let s = &mut *self.strm;
        out.clear();
        unsafe {
            if deflateReset(s) != Z_OK
                || (!dict.is_empty() && deflateSetDictionary(s, dict.as_ptr(), dict.len() as uInt) != Z_OK)
            {
                return Err(io::Error::other("zlib-ng deflate reset failed"));
            }
        }
        const FEED: usize = 1 << 30;
        let mut chunks = raw.chunks(FEED).peekable();
        loop {
            let chunk = chunks.next().unwrap_or(&[]);
            let last = chunks.peek().is_none();
            let flush = match (last, finish) {
                (false, _) => Z_NO_FLUSH,
                (true, false) => Z_SYNC_FLUSH,
                (true, true) => Z_FINISH,
            };
            s.next_in = chunk.as_ptr().cast_mut();
            s.avail_in = chunk.len() as uInt;
            loop {
                out.reserve((chunk.len() / 2).max(64 * 1024));
                let room = (out.capacity() - out.len()).min(uInt::MAX as usize);
                s.next_out = unsafe { out.as_mut_ptr().add(out.len()) };
                s.avail_out = room as uInt;
                let ret = unsafe { deflate(s, flush) };
                //SAFETY: deflate wrote `room - avail_out` bytes into the spare capacity
                unsafe { out.set_len(out.len() + room - s.avail_out as usize) };
                match ret {
                    Z_STREAM_END => return Ok(()),
                    Z_OK | Z_BUF_ERROR => {}
                    _ => return Err(io::Error::other("zlib-ng deflate failed")),
                }
                if s.avail_in == 0 && s.avail_out != 0 && flush != Z_FINISH {
                    break;
                }
            }
            if last {
                return Ok(());
            }
        }
    }
}

impl Drop for ZStream {
    fn drop(&mut self) {
        unsafe {
            if self.deflate {
                deflateEnd(&mut *self.strm);
            } else {
                inflateEnd(&mut *self.strm);
            }
        }
    }
}

fn adler(raw: &[u8]) -> u32 {
    raw.chunks(1 << 30).fold(1, |a, c| unsafe { adler32(a, c.as_ptr(), c.len() as uInt) })
}

/// Keep the last WINDOW bytes of `tail` followed by `raw`.
fn roll_window(tail: &mut Vec<u8>, raw: &[u8]) {
    if raw.len() >= WINDOW {
        tail.clear();
        tail.extend_from_slice(&raw[raw.len() - WINDOW..]);
    } else {
        tail.extend_from_slice(raw);
        let excess = tail.len().saturating_sub(WINDOW);
        tail.drain(..excess);
    }
}

/// Writes merged ranges to the target as one zlib stream, deflating the
/// ranges of a batch in parallel.
struct DeflateSink<'s, W: Write> {
    sorter: &'s Sorter<'s>,
    target: &'s mut W,
    tail: Vec<u8>,
    adler: u32,
    stats: SerializationStats,
}

impl<W: Write> DeflateSink<'_, W> {
    fn write(&mut self, bytes: &[u8]) -> io::Result<()> {
        self.target.write_all(bytes)?;
        self.stats.bytes_out += bytes.len();
        Ok(())
    }

    fn push(&mut self, slots: &[Mutex<Slot>], last: bool) -> io::Result<()> {
        // each range continues the stream of everything before it
        for slot in slots {
            let slot = &mut *lock(slot);
            slot.dict.clear();
            slot.dict.extend_from_slice(&self.tail);
            roll_window(&mut self.tail, &slot.raw);
        }
        let n = slots.len();
        let err = FirstError::default();
        let deflaters = &self.sorter.deflaters;
        parallel_for(n, self.sorter.out_threads, |i| {
            let slot = &mut *lock(&slots[i]);
            let finish = last && i + 1 == n;
            slot.packed.clear();
            slot.adler = adler(&slot.raw);
            if slot.raw.is_empty() && !finish {
                return;
            }
            let z = lock(deflaters).pop().map_or_else(ZStream::deflate, Ok);
            match z {
                Ok(mut z) => {
                    if let Err(e) = z.compress(&slot.dict, &slot.raw, finish, &mut slot.packed) {
                        err.set(e);
                    }
                    lock(deflaters).push(z);
                }
                Err(e) => err.set(e),
            }
        });
        err.take()?;
        for slot in slots {
            let slot = &*lock(slot);
            if !slot.raw.is_empty() {
                self.adler = unsafe { adler32_combine(self.adler, slot.adler, slot.raw.len() as z_off_t) };
            }
            self.stats.bytes_in += slot.raw.len();
            self.stats.path_count += slot.count as usize;
            self.target.write_all(&slot.packed)?;
            self.stats.bytes_out += slot.packed.len();
        }
        Ok(())
    }
}

// --------------------------------------------------------------------- sort

type Spill<'scope> = ScopedJoinHandle<'scope, (io::Result<Run>, Vec<Segment>)>;

struct Sorter<'a> {
    temp_dir: &'a Path,
    threads: usize,
    max_path: usize,
    segment: usize,
    /// Segments in memory may cost this much in total...
    resident: usize,
    /// ...and are spilled in the background once they pass this.
    spill_at: usize,
    range_bytes: usize,
    out_threads: usize,
    fanin: usize,
    created: Mutex<Vec<PathBuf>>,
    next_run: AtomicUsize,
    spare_segments: Mutex<Vec<Segment>>,
    spare_slots: Mutex<Vec<Slot>>,
    deflaters: Mutex<Vec<ZStream>>,
}

impl<'a> Sorter<'a> {
    fn new(memory: usize, temp_dir: &'a Path) -> Self {
        let threads = std::thread::available_parallelism().map_or(1, |n| n.get());
        // Ranges in flight during a merge (raw, read buffers, deflate output)
        // take about 1/4 of the budget, sorted segments the other 3/4.
        let range_bytes = (memory / (16 * threads)).clamp(64 * 1024, 8 * MIB);
        let resident = memory / 4 * 3;
        Sorter {
            temp_dir,
            threads,
            max_path: memory / 16,
            segment: (memory / 8).min(MAX_SEGMENT),
            resident,
            spill_at: resident / 4 * 3,
            range_bytes,
            out_threads: (memory / (16 * range_bytes)).clamp(1, threads),
            // a run's slice of a range can overhang by up to two sample gaps
            fanin: (range_bytes / (2 * SAMPLE_GAP)).clamp(2, 128),
            created: Mutex::default(),
            next_run: AtomicUsize::new(0),
            spare_segments: Mutex::default(),
            spare_slots: Mutex::default(),
            deflaters: Mutex::default(),
        }
    }

    fn new_run(&self) -> io::Result<RunWriter> {
        let path = self.temp_dir.join(format!("pathmap-sort-{}", self.next_run.fetch_add(1, Relaxed)));
        let file = File::create_new(&path)?;
        lock(&self.created).push(path.clone());
        let run = Run { path, file, len: 0, sample_off: vec![], sample_end: vec![], sample_bytes: vec![] };
        Ok(RunWriter { run, since: 0 })
    }

    fn remove_run(&self, run: Run) -> io::Result<()> {
        drop(run.file);
        lock(&self.created).retain(|p| *p != run.path);
        fs::remove_file(&run.path)
    }

    /// An empty segment holding `carry`, reusing a spilled one's buffers.
    fn new_segment(&self, carry: &[u8]) -> Segment {
        let mut seg = lock(&self.spare_segments).pop().unwrap_or_default();
        seg.bytes.clear();
        seg.records = 0;
        seg.pieces.clear();
        seg.bytes.reserve(self.segment + 2 * INFLATE_STEP);
        seg.bytes.extend_from_slice(carry);
        seg
    }

    fn recycle(&self, segs: Vec<Segment>) {
        lock(&self.spare_segments).extend(segs);
    }

    /// Merge `sources` range by range, `2 * out_threads` ranges at a time,
    /// handing each batch to `sink` in order (with `true` on the last).
    fn merge(
        &self,
        sources: &[Source],
        mut sink: impl FnMut(&[Mutex<Slot>], bool) -> io::Result<()>,
    ) -> io::Result<()> {
        let plan = Plan::new(sources, self.range_bytes);
        let batch = (2 * self.out_threads).min(plan.ranges());
        let mut spare = std::mem::take(&mut *lock(&self.spare_slots));
        if spare.len() < batch {
            spare.resize_with(batch, Slot::default);
        }
        let slots: Vec<Mutex<Slot>> = spare.into_iter().map(Mutex::new).collect();
        let mut run_batches = || {
            let mut start = 0;
            while start < plan.ranges() {
                let n = batch.min(plan.ranges() - start);
                let err = FirstError::default();
                parallel_for(n, self.out_threads, |i| {
                    if !err.failed()
                        && let Err(e) = merge_range(sources, &plan, start + i, &mut lock(&slots[i]))
                    {
                        err.set(e);
                    }
                });
                err.take()?;
                start += n;
                sink(&slots[..n], start == plan.ranges())?;
            }
            Ok(())
        };
        let result = run_batches();
        *lock(&self.spare_slots) = slots.into_iter().map(into_inner).collect();
        result
    }

    fn merge_to_run(&self, sources: &[Source]) -> io::Result<Run> {
        let mut w = self.new_run()?;
        self.merge(sources, |slots, _| slots.iter().try_for_each(|s| w.push(&lock(s).raw)))?;
        Ok(w.run)
    }

    fn finish_spill(&self, spill: Spill, runs: &mut Vec<Run>) -> io::Result<()> {
        let (run, segs) = spill.join().map_err(|_| io::Error::other("spill panicked"))?;
        self.recycle(segs);
        runs.push(run?);
        Ok(())
    }

    /// Inflate `source` into segments, sorting full ones in the background and
    /// spilling to runs as the budget fills. Returns what is left in memory,
    /// sorted.
    fn ingest<'scope, 'env, R: Read>(
        &'env self,
        scope: &'scope Scope<'scope, 'env>,
        mut source: R,
        pool: &Pool,
        runs: &mut Vec<Run>,
    ) -> io::Result<Vec<Segment>> {
        let inline = self.threads == 1;
        let mut z = ZStream::inflate()?;
        let mut input = vec![0u8; 256 * 1024];
        let mut seg = self.new_segment(&[]);
        let mut scan = 0; // start of the first record not yet walked
        let mut resident = 0; // submitted segments not yet being spilled
        let mut spilling = 0; // segments being spilled
        let mut spill: Option<Spill<'scope>> = None;
        let mut eof = false;
        loop {
            // inflate straight into the segment
            seg.bytes.reserve(INFLATE_STEP);
            let room = (seg.bytes.capacity() - seg.bytes.len()).min(INFLATE_STEP);
            let s = &mut *z.strm;
            s.next_out = unsafe { seg.bytes.as_mut_ptr().add(seg.bytes.len()) };
            s.avail_out = room as uInt;
            let ret = unsafe { inflate(s, Z_NO_FLUSH) };
            //SAFETY: inflate wrote `room - avail_out` bytes into the spare capacity
            unsafe { seg.bytes.set_len(seg.bytes.len() + room - s.avail_out as usize) };
            let ended = match ret {
                Z_STREAM_END => true,
                Z_OK | Z_BUF_ERROR => false,
                Z_MEM_ERROR => return Err(io::ErrorKind::OutOfMemory.into()),
                _ => return Err(invalid("corrupt .paths stream")),
            };

            // walk the records that are now complete
            let mut cut = None;
            while let Some(head) = seg.bytes.get(scan..scan + 4) {
                let len = u32::from_le_bytes(head.try_into().unwrap()) as usize;
                if len > self.max_path {
                    return Err(too_long());
                }
                if scan > 0 && scan + 4 + len > u32::MAX as usize {
                    cut = Some(scan); // keys hold u32 offsets
                    break;
                }
                if scan + 4 + len > seg.bytes.len() {
                    seg.bytes.reserve(scan + 4 + len - seg.bytes.len());
                    break;
                }
                scan += 4 + len;
                seg.records += 1;
                if scan + seg.records * size_of::<Key>() >= self.segment {
                    cut = Some(scan);
                    break;
                }
            }
            if let Some(cut) = cut {
                let next = self.new_segment(&seg.bytes[cut..]);
                seg.bytes.truncate(cut);
                resident += seg.cost();
                pool.submit(std::mem::replace(&mut seg, next), inline);
                scan = 0;

                if spill.as_ref().is_some_and(|h| h.is_finished()) {
                    self.finish_spill(spill.take().unwrap(), runs)?;
                    spilling = 0;
                }
                if spill.is_none() && resident >= self.spill_at {
                    let segs = pool.take_done();
                    if !segs.is_empty() {
                        spilling = segs.iter().map(Segment::cost).sum();
                        resident -= spilling;
                        spill = Some(scope.spawn(move || (self.merge_to_run(&mem_sources(&segs)), segs)));
                    }
                }
                while resident + spilling + self.segment > self.resident {
                    if let Some(h) = spill.take() {
                        self.finish_spill(h, runs)?;
                        spilling = 0;
                    } else {
                        let segs = pool.drain()?;
                        runs.push(self.merge_to_run(&mem_sources(&segs))?);
                        self.recycle(segs);
                        resident = 0;
                    }
                }
                continue; // the carried bytes may hold more complete records
            }

            if ended {
                break;
            }
            if s.avail_in == 0 && s.avail_out != 0 {
                if eof {
                    break; // the stream stopped short; accept its whole records
                }
                let n = loop {
                    match source.read(&mut input) {
                        Err(e) if e.kind() == io::ErrorKind::Interrupted => {}
                        r => break r?,
                    }
                };
                eof = n == 0;
                s.next_in = input.as_mut_ptr();
                s.avail_in = n as uInt;
            }
        }
        if scan != seg.bytes.len() {
            return Err(invalid("truncated .paths stream"));
        }
        if let Some(h) = spill {
            self.finish_spill(h, runs)?;
        }
        // the last segment is the only one nobody else can sort meanwhile;
        // a few pieces sort it fast without widening the final merge much
        let mut segs = pool.drain()?;
        if seg.records > 0 {
            seg.sort(self.threads.min(8));
            segs.push(seg);
        }
        Ok(segs)
    }

    fn sort<R: Read, W: Write>(&self, source: R, target: &mut W) -> io::Result<SerializationStats> {
        let pool = Pool::default();
        let mut runs = Vec::new();
        let segs = std::thread::scope(|s| {
            if self.threads > 1 {
                for _ in 0..self.threads - 1 {
                    s.spawn(|| pool.work());
                }
            }
            let segs = self.ingest(s, source, &pool, &mut runs);
            pool.close();
            segs
        })?;
        lock(&self.spare_segments).clear();

        // too many runs to merge at once: merge the smallest first
        while runs.len() > self.fanin {
            runs.sort_by_key(|r| std::cmp::Reverse(r.len));
            let k = self.fanin.min(runs.len() - self.fanin + 1);
            let group = runs.split_off(runs.len() - k);
            let merged = self.merge_to_run(&group.iter().map(Source::Disk).collect::<Vec<_>>())?;
            for run in group {
                self.remove_run(run)?;
            }
            runs.push(merged);
        }

        let mut sources = mem_sources(&segs);
        sources.extend(runs.iter().map(Source::Disk));
        let mut sink = DeflateSink {
            sorter: self,
            target,
            tail: Vec::new(),
            adler: 1,
            stats: SerializationStats { bytes_out: 0, bytes_in: 0, path_count: 0 },
        };
        sink.write(&ZLIB_HEADER)?;
        self.merge(&sources, |slots, last| sink.push(slots, last))?;
        let adler = sink.adler.to_be_bytes();
        sink.write(&adler)?;
        let stats = sink.stats;
        drop(sources);
        for run in runs {
            self.remove_run(run)?;
        }
        Ok(stats)
    }
}

fn mem_sources(segs: &[Segment]) -> Vec<Source<'_>> {
    segs.iter()
        .flat_map(|seg| {
            seg.pieces.iter().map(|r| Source::Mem { bytes: &seg.bytes, keys: &seg.keys[r.clone()] })
        })
        .collect()
}

/// Sort and deduplicate an unordered `.paths` stream without building a PathMap,
/// using every available core.
///
/// A drop-in replacement for [`super::sort_paths`], with the same arguments,
/// output and temporary files: the output is the usual `.paths` format in
/// strictly increasing byte order, and decodes exactly like that function's.
/// The compressed bytes differ, because the ranges of the output are deflated
/// independently (each primed with the preceding 32 KiB) and concatenated.
///
/// `memory_bytes` (at least 1 MiB) budgets the decompressed paths in memory,
/// their sort keys (16 bytes per path), and the ranges being merged and
/// deflated; zlib state and thread stacks are additional. When the input fits
/// in about 3/4 of the budget, no temporary file is written.
/// Individual paths must fit in 1/16 of the budget.
/// The caller supplies an existing scratch directory in `temp_dir`, exclusive to
/// this sort. Run files are created with `create_new` and removed on success or
/// error; the caller owns creation and deletion of the directory. Allow up to
/// twice the uncompressed input size for runs.
///
/// Unlike [`super::sort_paths`], a stream that ends partway through a path is
/// an error rather than being silently cut short.
pub fn sort_paths<R: Read, W: Write>(
    source: R,
    target: &mut W,
    memory_bytes: usize,
    temp_dir: &Path,
) -> io::Result<SerializationStats> {
    if memory_bytes < MIB {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "sort memory budget must be at least 1 MiB",
        ));
    }
    let sorter = Sorter::new(memory_bytes, temp_dir);
    let result = sorter.sort(source, target);
    let mut cleanup = Ok(());
    for path in into_inner(sorter.created) {
        if let Err(error) = fs::remove_file(path)
            && error.kind() != io::ErrorKind::NotFound
        {
            cleanup = Err(error);
        }
    }
    result.and_then(|stats| cleanup.map(|()| stats))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Tests segment sorting and merging directly
    #[test]
    fn sort_and_merge_matches_bytewise_set_slim() {
        #[cfg(not(miri))]
        const ROUNDS: u8 = 32;
        #[cfg(miri)]
        const ROUNDS: u8 = 2;

        let mut paths = Vec::new();
        for n in 0..ROUNDS {
            for len in [0, 1, 7, 8, 9, 15, 16, 17, 100] {
                let mut path = vec![0; len];
                if let Some(last) = path.last_mut() {
                    *last = n;
                }
                paths.push(path);
            }
            paths.push(vec![255; 17]);
        }
        paths.reverse();
        paths.extend(paths.clone().into_iter().rev());
        let mut expected = paths.clone();
        expected.sort();
        expected.dedup();
        let mut expected_raw = Vec::new();
        for path in &expected {
            expected_raw.extend_from_slice(&(path.len() as u32).to_le_bytes());
            expected_raw.extend_from_slice(path);
        }

        for (memory, records_per_segment) in [(MIB, 19), (3 * MIB, 41), (64 * MIB, paths.len())] {
            let mut sorter = Sorter::new(memory, Path::new("")); // Scratch path is unused by in-memory merges.
            // Small ranges exercise splitter boundaries without large inputs;
            // one worker also keeps the interpreted workload small under Miri.
            sorter.range_bytes = 128;
            sorter.out_threads = 1;
            let segments: Vec<_> = paths.chunks(records_per_segment).map(|chunk| {
                let mut segment = Segment::default();
                for path in chunk {
                    segment.bytes.extend_from_slice(&(path.len() as u32).to_le_bytes());
                    segment.bytes.extend_from_slice(path);
                }
                segment.records = chunk.len();
                segment.sort(1);
                segment
            }).collect();

            let assert_merge = |sources: &[Source<'_>]| {
                let mut actual = Vec::new();
                let mut count = 0;
                sorter.merge(sources, |slots, _| {
                    for slot in slots {
                        let slot = lock(slot);
                        actual.extend_from_slice(&slot.raw);
                        count += slot.count;
                    }
                    Ok(())
                }).unwrap();
                assert_eq!(actual, expected_raw, "budget={memory}");
                assert_eq!(count, expected.len() as u64);
            };
            let sources = mem_sources(&segments);
            assert_merge(&sources);

            // Check run-record parsing and cursor bounds using an in-memory buffer.
            for (start, end) in [(0, expected.len()), (1, expected.len() - 1)] {
                let lo = expected.get(start).map(Vec::as_slice);
                let hi = expected.get(end).map(Vec::as_slice);
                let mut cursor = Cursor::disk(&expected_raw, lo, hi).unwrap().unwrap();
                for (index, path) in expected[start..end].iter().enumerate() {
                    assert_eq!(cursor.cur, path);
                    assert_eq!(cursor.advance().unwrap(), index + 1 < end - start);
                }
            }

        }
    }
}
