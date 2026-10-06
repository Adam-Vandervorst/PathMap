#![cfg(feature = "arena_compact")]
use pathmap::arena_compact::{ACTOutputStream, ArenaCompactTree};

#[test]
fn bounded_cache_eviction_preserves_disk_queries() -> std::io::Result<()> {
    let paths: Vec<_> = (0u32..1000).map(|n| {
        let mut path = n.to_be_bytes().to_vec();
        path.extend_from_slice(format!("unique suffix {n:08}").as_bytes());
        path
    }).collect();
    // Disabled cache and several bounded entry counts.
    for entries in [0, 1, 2, 4096] {
        let dir = tempfile::tempdir()?;
        let file = dir.path().join("bounded.act");
        let mut out = ACTOutputStream::with_cache_limit(&file, entries)?;
        for path in &paths { out.push(path)?; }
        drop(out.finish()?);
        let tree = ArenaCompactTree::open_mmap(&file)?;
        for path in &paths { assert_eq!(tree.get_val_at(path), Some(0)); }
        assert_eq!(tree.get_val_at(b"absent"), None);
        assert_eq!(tree.iter().map(|(p, _)| p).collect::<Vec<_>>(), paths);
    }
    Ok(())
}

#[test]
fn cached_offsets_reuse_buffered_and_flushed_lines() -> std::io::Result<()> {
    let paths: Vec<_> = (0u32..24000).map(|n| {
        let suffix = if n >= 23900 { (n - 23900) / 2 } else { n / 2 };
        let mut path = n.to_be_bytes().to_vec();
        path.extend_from_slice(&suffix.to_be_bytes());
        path.extend_from_slice(&[42; 508]);
        path
    }).collect();
    let dir = tempfile::tempdir()?;
    let mut sizes = vec![];
    for entries in [0, 2, 30000] {
        let file = dir.path().join(format!("cache-{entries}.act"));
        let mut out = ACTOutputStream::with_cache_limit(&file, entries)?;
        for path in &paths { out.push(path)?; }
        let tree = out.finish()?;
        sizes.push(std::fs::metadata(&file)?.len());
        // Exceeds the 4 MiB write buffer; the final paths reuse early on-disk lines.
        assert!(sizes.last().unwrap() > &(4 * 1024 * 1024));
        assert_eq!(tree.iter().map(|(p, _)| p).collect::<Vec<_>>(), paths);
        for path in paths.iter().step_by(257) { assert_eq!(tree.get_val_at(path), Some(0)); }
        assert_eq!(tree.get_val_at(b"absent"), None);
    }
    assert!(sizes[1] < sizes[0]);
    assert!(sizes[2] < sizes[1]);
    // The ordinary zipper dumper uses the same file-backed line cache.
    let map = pathmap::PathMap::from_iter(paths.iter().map(|path| (path, ())));
    let tree = ArenaCompactTree::dump_from_zipper(map.read_zipper(), |_| 0, dir.path().join("zipper.act"))?;
    assert_eq!(tree.iter().map(|(p, _)| p).collect::<Vec<_>>(), paths);
    Ok(())
}
