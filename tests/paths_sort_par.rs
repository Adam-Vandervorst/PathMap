#![cfg(all(feature = "serialization", not(miri)))]
//! `paths_serialization::sort_paths_par` must behave like `sort_paths`.
use pathmap::paths_serialization::{
    sort_paths_par, for_each_deserialized_path, serialize_paths_from_funcs, sort_paths,
};
use rand::{Rng, SeedableRng, rngs::StdRng};
use std::{
    fs::{self, File},
    io,
    path::Path,
};

fn encode(paths: &[Vec<u8>]) -> Vec<u8> {
    let mut out = Vec::new();
    let mut source = (0usize, paths);
    serialize_paths_from_funcs(
        &mut out,
        &mut source,
        |s| {
            s.0 += 1;
            Ok(s.0 <= s.1.len())
        },
        |s| Some(s.1[s.0 - 1].as_slice()),
    )
    .unwrap();
    out
}

fn write_paths(path: &Path, paths: &[Vec<u8>]) {
    fs::write(path, encode(paths)).unwrap();
}

/// Inflate a whole zlib stream, insisting on a clean end and a valid checksum
/// (`for_each_deserialized_path` checks neither).
fn inflate_strict(data: &[u8]) -> Vec<u8> {
    use libz_ng_sys::*;
    #[allow(invalid_value)] // as in the crate: zlib wants a zeroed stream
    let mut strm: Box<z_stream> = Box::new(unsafe { std::mem::MaybeUninit::zeroed().assume_init() });
    assert_eq!(unsafe { zng_inflateInit(&mut *strm) }, Z_OK);
    let mut out: Vec<u8> = Vec::with_capacity(data.len() * 4 + 64);
    strm.next_in = data.as_ptr().cast_mut();
    strm.avail_in = data.len() as _;
    loop {
        out.reserve(1 << 16);
        let room = out.capacity() - out.len();
        strm.next_out = unsafe { out.as_mut_ptr().add(out.len()) };
        strm.avail_out = room as _;
        let ret = unsafe { inflate(&mut *strm, Z_NO_FLUSH) };
        unsafe { out.set_len(out.len() + room - strm.avail_out as usize) };
        if ret == Z_STREAM_END {
            break;
        }
        assert_eq!(ret, Z_OK, "inflate failed");
    }
    assert_eq!(strm.avail_in, 0, "trailing bytes after the zlib stream");
    unsafe { inflateEnd(&mut *strm) };
    out
}

/// Decode `.paths` data strictly.
fn decode(data: &[u8]) -> Vec<Vec<u8>> {
    let raw = inflate_strict(data);
    let mut paths = vec![];
    let mut at = 0;
    while at < raw.len() {
        let len = u32::from_le_bytes(raw[at..at + 4].try_into().unwrap()) as usize;
        paths.push(raw[at + 4..at + 4 + len].to_vec());
        at += 4 + len;
    }
    let mut loose = vec![];
    for_each_deserialized_path(data, |_, p| {
        loose.push(p.to_vec());
        Ok(())
    })
    .unwrap();
    assert_eq!(paths, loose);
    paths
}

fn read_paths(path: &Path) -> Vec<Vec<u8>> {
    decode(&fs::read(path).unwrap())
}

fn sort_file(input: &Path, output: &Path, memory: usize, temp: &Path) -> io::Result<usize> {
    let mut target = tempfile::NamedTempFile::new_in(temp)?;
    let count = sort_paths_par(File::open(input)?, &mut target, memory, temp)?.path_count;
    target.persist(output).map_err(|e| e.error)?;
    Ok(count)
}

#[test]
fn external_sort_many_runs_matches_bytewise_set() {
    let scratch = tempfile::tempdir().unwrap();
    let input = scratch.path().join("input.upaths");
    let output = scratch.path().join("output.paths");
    let mut paths = vec![vec![], vec![0], vec![0, 0], vec![255], vec![]];
    for n in (0u32..35000).rev() {
        let mut path = n.to_be_bytes().to_vec();
        path.extend_from_slice(&[0, 255, 0]);
        path.extend(std::iter::repeat_n((n % 251) as u8, (n % 123) as usize));
        paths.push(path.clone());
        if n % 3 == 0 {
            paths.push(path);
        }
    }
    write_paths(&input, &paths);
    paths.sort();
    paths.dedup();
    assert_eq!(sort_file(&input, &output, 1 << 20, scratch.path()).unwrap(), paths.len());
    assert_eq!(read_paths(&output), paths);
    // A sort-budget error after multiple spills must clean every temporary run.
    let before = fs::read(&output).unwrap();
    paths.push(vec![0; (1 << 16) + 1]);
    write_paths(&input, &paths);
    assert!(sort_file(&input, &output, 1 << 20, scratch.path()).is_err());
    assert_eq!(fs::read(&output).unwrap(), before);
    assert_eq!(fs::read_dir(scratch.path()).unwrap().count(), 2);
}

#[test]
fn sort_empty_duplicates_and_memory_limit() {
    let scratch = tempfile::tempdir().unwrap();
    let input = scratch.path().join("input.upaths");
    let output = scratch.path().join("output.paths");
    for paths in [vec![], vec![vec![]; 3], vec![b"same".to_vec(); 25000]] {
        write_paths(&input, &paths);
        let mut expected = paths;
        expected.sort();
        expected.dedup();
        sort_file(&input, &output, 1 << 20, scratch.path()).unwrap();
        assert_eq!(read_paths(&output), expected);
    }
    write_paths(&input, &[vec![0; (1 << 16) + 1]]);
    assert!(sort_file(&input, &output, 1 << 20, scratch.path()).is_err());
    assert_eq!(fs::read_dir(scratch.path()).unwrap().count(), 2);
}

#[test]
fn caller_scratch_files_survive_run_name_collisions() {
    let scratch = tempfile::tempdir().unwrap();
    let input = scratch.path().join("input.upaths");
    let output = scratch.path().join("output.paths");
    let existing = scratch.path().join("pathmap-sort-1");
    fs::write(&existing, b"caller-owned file").unwrap();
    fs::write(&output, b"existing destination").unwrap();
    write_paths(&input, &vec![vec![42; 64]; 20000]);
    let error = sort_file(&input, &output, 1 << 20, scratch.path()).unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::AlreadyExists);
    assert_eq!(fs::read(&existing).unwrap(), b"caller-owned file");
    assert_eq!(fs::read(&output).unwrap(), b"existing destination");
    assert_eq!(fs::read_dir(scratch.path()).unwrap().count(), 3);
}

/// Paths with heavy duplication, long shared prefixes, empty and 8-byte
/// boundary lengths, NULs, and a few long ones.
fn nasty_paths(rng: &mut StdRng, n: usize) -> Vec<Vec<u8>> {
    let stems: Vec<Vec<u8>> = (0..40)
        .map(|i| {
            let len = [0, 1, 7, 8, 9, 15, 16, 17, 100][i % 9];
            (0..len).map(|_| rng.random_range(0..3u8)).collect()
        })
        .collect();
    (0..n)
        .map(|_| match rng.random_range(0..10) {
            0 => vec![],
            1 => stems[rng.random_range(0..stems.len())].clone(),
            2 => (0..rng.random_range(0..2000)).map(|_| rng.random()).collect(),
            _ => {
                let mut p = stems[rng.random_range(0..stems.len())].clone();
                let tail = rng.random_range(0..24);
                p.extend((0..tail).map(|_| rng.random_range(0..4u8)));
                p
            }
        })
        .collect()
}

#[test]
fn matches_sort_paths_across_budgets() {
    let scratch = tempfile::tempdir().unwrap();
    let mut rng = StdRng::seed_from_u64(0x5eed);
    // 1 MiB with ~10 MB of input forces spills and intermediate merges;
    // 64 MiB keeps everything in memory.
    for (n, memory) in [(0, 1 << 20), (1, 1 << 20), (5000, 1 << 20), (200_000, 1 << 20), (200_000, 3 << 20), (200_000, 64 << 20)] {
        let paths = nasty_paths(&mut rng, n);
        let input = encode(&paths);
        let mut expected_out = Vec::new();
        let expected = sort_paths(input.as_slice(), &mut expected_out, memory, scratch.path()).unwrap();
        let mut out = Vec::new();
        let stats = sort_paths_par(input.as_slice(), &mut out, memory, scratch.path()).unwrap();
        assert_eq!(fs::read_dir(scratch.path()).unwrap().count(), 0, "runs left behind");

        let mut sorted = paths.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(decode(&out), sorted, "n={n} memory={memory}");
        assert_eq!(decode(&expected_out), sorted);
        assert_eq!(stats.path_count, expected.path_count);
        assert_eq!(stats.bytes_in, expected.bytes_in);
        assert_eq!(stats.bytes_out, out.len());
    }
}

#[test]
fn rejects_truncated_input() {
    let scratch = tempfile::tempdir().unwrap();
    // an uncompressed-looking record whose body is cut short: build it by
    // compressing a stream with a lying length header
    use libz_ng_sys::*;
    let raw = [10u8, 0, 0, 0, 1, 2, 3];
    #[allow(invalid_value)] // as in the crate: zlib wants a zeroed stream
    let mut strm: Box<z_stream> = Box::new(unsafe { std::mem::MaybeUninit::zeroed().assume_init() });
    assert_eq!(unsafe { zng_deflateInit(&mut *strm, 7) }, Z_OK);
    let mut data = vec![0u8; 256];
    strm.next_in = raw.as_ptr().cast_mut();
    strm.avail_in = raw.len() as _;
    strm.next_out = data.as_mut_ptr();
    strm.avail_out = data.len() as _;
    assert_eq!(unsafe { deflate(&mut *strm, Z_FINISH) }, Z_STREAM_END);
    data.truncate(strm.total_out as usize);
    unsafe { deflateEnd(&mut *strm) };
    let err = sort_paths_par(data.as_slice(), &mut Vec::new(), 1 << 20, scratch.path()).unwrap_err();
    assert_eq!(err.kind(), io::ErrorKind::InvalidData);
}
