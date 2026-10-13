//! External bytewise sorting for unordered `.paths` streams.
use super::{SerializationStats, for_each_deserialized_path, serialize_paths_from_funcs};
use std::{
    fs::{self, File},
    io::{self, BufReader, BufWriter, Read, Write},
    path::{Path, PathBuf},
};

const BUFFER: usize = 16 * 1024;

fn new_run(temp_dir: &Path, next_run: &mut u64) -> io::Result<(PathBuf, File)> {
    let path = temp_dir.join(format!("pathmap-sort-{next_run}"));
    let file = File::create_new(&path)?;
    *next_run += 1;
    Ok((path, file))
}

// Runs are uncompressed length-prefixed paths, avoiding repeated compression
// during merges. These functions share no codec state or in-memory path index.
fn read_path(source: &mut impl Read, path: &mut Vec<u8>, limit: usize) -> io::Result<bool> {
    let mut length = [0; 4];
    loop {
        match source.read(&mut length[..1]) {
            Ok(0) => return Ok(false),
            Ok(_) => break,
            Err(e) if e.kind() == io::ErrorKind::Interrupted => continue,
            Err(e) => return Err(e),
        }
    }
    source.read_exact(&mut length[1..])?;
    let length = u32::from_le_bytes(length) as usize;
    if length > limit {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "path exceeds sort memory budget",
        ));
    }
    path.resize(length, 0);
    source.read_exact(path)?;
    Ok(true)
}
fn write_path(target: &mut impl Write, path: &[u8]) -> io::Result<()> {
    let length = u32::try_from(path.len())
        .map_err(|_| io::Error::other("path exceeds .paths length limit"))?;
    target.write_all(&length.to_le_bytes())?;
    target.write_all(path)
}

struct Chunk {
    bytes: Vec<u8>,
    entries: Vec<(usize, usize)>,
    byte_limit: usize,
    entry_limit: usize,
}
impl Chunk {
    fn new(memory: usize) -> Self {
        let byte_limit = memory / 3;
        let entry_limit = memory / 6 / std::mem::size_of::<(usize, usize)>();
        Self {
            bytes: Vec::with_capacity(byte_limit),
            entries: Vec::with_capacity(entry_limit),
            byte_limit,
            entry_limit,
        }
    }
    fn fits(&self, path: &[u8]) -> bool {
        self.bytes.len() + path.len() <= self.byte_limit && self.entries.len() < self.entry_limit
    }
    fn push(&mut self, path: &[u8]) {
        self.entries.push((self.bytes.len(), path.len()));
        self.bytes.extend_from_slice(path);
    }
    fn spill(&mut self, temp_dir: &Path, next_run: &mut u64) -> io::Result<PathBuf> {
        let bytes = &self.bytes;
        self.entries
            .sort_unstable_by(|&(a, al), &(b, bl)| bytes[a..a + al].cmp(&bytes[b..b + bl]));
        let (path, file) = new_run(temp_dir, next_run)?;
        let mut writer = BufWriter::with_capacity(BUFFER, file);
        let mut previous = None;
        for &(start, len) in &self.entries {
            let path = &bytes[start..start + len];
            if previous != Some(path) {
                write_path(&mut writer, path)?;
            }
            previous = Some(path);
        }
        writer.flush()?;
        drop(writer);
        self.entries.clear();
        self.bytes.clear();
        Ok(path)
    }
}

fn merge(
    left: PathBuf,
    right: PathBuf,
    temp_dir: &Path,
    max_path: usize,
    next_run: &mut u64,
) -> io::Result<PathBuf> {
    let mut a = BufReader::with_capacity(BUFFER, File::open(&left)?);
    let mut b = BufReader::with_capacity(BUFFER, File::open(&right)?);
    let mut ap = Vec::new();
    let mut bp = Vec::new();
    let (path, output) = new_run(temp_dir, next_run)?;
    let mut writer = BufWriter::with_capacity(BUFFER, output);
    let mut has_a = read_path(&mut a, &mut ap, max_path)?;
    let mut has_b = read_path(&mut b, &mut bp, max_path)?;
    while has_a || has_b {
        let order = match (has_a, has_b) {
            (true, true) => ap.cmp(&bp),
            (true, false) => std::cmp::Ordering::Less,
            _ => std::cmp::Ordering::Greater,
        };
        write_path(&mut writer, if order.is_le() { &ap } else { &bp })?;
        if order.is_le() {
            has_a = read_path(&mut a, &mut ap, max_path)?;
        }
        if order.is_ge() {
            has_b = read_path(&mut b, &mut bp, max_path)?;
        }
    }
    writer.flush()?;
    drop(writer);
    drop((a, b));
    fs::remove_file(left)?;
    fs::remove_file(right)?;
    Ok(path)
}

// Binary carry merging: at most one run per level and no unbounded run list.
fn add_run(
    mut run: PathBuf,
    levels: &mut [Option<PathBuf>; 64],
    temp_dir: &Path,
    max_path: usize,
    next_run: &mut u64,
) -> io::Result<()> {
    for slot in levels {
        match slot.take() {
            None => {
                *slot = Some(run);
                return Ok(());
            }
            Some(other) => run = merge(other, run, temp_dir, max_path, next_run)?,
        }
    }
    Err(io::Error::other("too many sort runs"))
}

/// Sort and deduplicate an unordered `.paths` stream without building a PathMap.
///
/// `memory_bytes` (at least 1 MiB) budgets the sorting arena, indices and merge
/// buffers; codec/runtime overhead and the decoder's current path are additional.
/// Individual paths must fit in 1/16 of the budget (checked after decoding).
/// The caller supplies an existing scratch directory in `temp_dir`, exclusive to
/// this sort. Run files are created with `create_new` and removed on success or
/// error; the caller owns creation and deletion of the directory. Allow up to
/// twice the uncompressed input size for runs.
/// The output uses the usual `.paths` format, in strictly increasing byte order.
pub fn sort_paths<R: Read, W: Write>(
    source: R,
    target: &mut W,
    memory_bytes: usize,
    temp_dir: &Path,
) -> io::Result<SerializationStats> {
    if memory_bytes < 1024 * 1024 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "sort memory budget must be at least 1 MiB",
        ));
    }
    let mut next_run = 0;
    let result = (|| {
        let max_path = memory_bytes / 16;
        let mut chunk = Chunk::new(memory_bytes);
        let mut levels = std::array::from_fn(|_| None);
        for_each_deserialized_path(source, |_, path| {
            if path.len() > max_path {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    "path exceeds sort memory budget",
                ));
            }
            if !chunk.fits(path) {
                add_run(
                    chunk.spill(temp_dir, &mut next_run)?,
                    &mut levels,
                    temp_dir,
                    max_path,
                    &mut next_run,
                )?;
            }
            chunk.push(path);
            Ok(())
        })?;
        if !chunk.entries.is_empty() {
            add_run(
                chunk.spill(temp_dir, &mut next_run)?,
                &mut levels,
                temp_dir,
                max_path,
                &mut next_run,
            )?;
        }
        drop(chunk);
        let mut final_run = None;
        for run in levels.into_iter().flatten() {
            final_run = Some(match final_run {
                None => run,
                Some(other) => merge(other, run, temp_dir, max_path, &mut next_run)?,
            });
        }
        let mut source: Box<dyn Read> = match &final_run {
            Some(path) => Box::new(BufReader::with_capacity(BUFFER, File::open(path)?)),
            None => Box::new(io::empty()),
        };
        serialize_paths_from_funcs(
            target,
            &mut Vec::new(),
            |path| read_path(&mut source, path, max_path),
            |path| Some(path),
        )
    })();
    let mut cleanup = Ok(());
    for index in 0..next_run {
        if let Err(error) = fs::remove_file(temp_dir.join(format!("pathmap-sort-{index}"))) {
            if error.kind() != io::ErrorKind::NotFound {
                cleanup = Err(error);
            }
        }
    }
    result.and_then(|stats| cleanup.map(|()| stats))
}
