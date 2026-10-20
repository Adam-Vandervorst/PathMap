#![cfg(feature = "serialization")]
use pathmap::paths_serialization::{
    for_each_deserialized_path, serialize_paths_from_funcs, sort_paths,
};
use std::{
    fs::{self, File},
    io,
    path::Path,
};
fn write_paths(path: &Path, paths: &[Vec<u8>]) {
    let mut source = (0usize, paths);
    serialize_paths_from_funcs(
        &mut File::create(path).unwrap(),
        &mut source,
        |s| {
            s.0 += 1;
            Ok(s.0 <= s.1.len())
        },
        |s| Some(s.1[s.0 - 1].as_slice()),
    )
    .unwrap();
}
fn read_paths(path: &Path) -> Vec<Vec<u8>> {
    let mut paths = vec![];
    for_each_deserialized_path(File::open(path).unwrap(), |_, p| {
        paths.push(p.to_vec());
        Ok(())
    })
    .unwrap();
    paths
}
fn sort_file(input: &Path, output: &Path, memory: usize, temp: &Path) -> io::Result<usize> {
    let mut target = tempfile::NamedTempFile::new_in(temp)?;
    let count = sort_paths(File::open(input)?, &mut target, memory, temp)?.path_count;
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
    assert_eq!(
        sort_file(&input, &output, 1 << 20, scratch.path()).unwrap(),
        paths.len()
    );
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
