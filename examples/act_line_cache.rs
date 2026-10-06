//! Compare ACT line-cache policies on the same ordered .paths input.
//! cargo run --release --example act_line_cache --features arena_compact,act_counters -- INPUT.paths OUTPUT.act POLICY
//! POLICY is none, bounded (4194304 fingerprint/offset entries), or unbounded.
use pathmap::{arena_compact::ACTOutputStream, paths_serialization::for_each_deserialized_path};
use std::{
    fs::File,
    io::{self, BufReader},
    time::Instant,
};

fn main() -> io::Result<()> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len() != 3 {
        return Err(io::Error::other(
            "expected INPUT.paths OUTPUT.act none|bounded|unbounded",
        ));
    }
    let entries = match args[2].as_str() {
        "none" => 0,
        "bounded" => 4194304,
        "unbounded" => usize::MAX,
        _ => return Err(io::Error::other("unknown cache policy")),
    };
    let start = Instant::now();
    let mut output = ACTOutputStream::with_cache_limit(&args[1], entries)?;
    let stats = for_each_deserialized_path(BufReader::new(File::open(&args[0])?), |_, path| {
        output.push(path)
    })?;
    let tree = output.finish()?;
    println!(
        "policy={} paths={} elapsed={:.3}s file_bytes={}\n{:?}",
        args[2],
        stats.path_count,
        start.elapsed().as_secs_f64(),
        tree.get_data().len(),
        tree.counters()
    );
    Ok(())
}
