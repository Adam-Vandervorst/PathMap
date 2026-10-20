//! Replays trace files written by pathmap's [TraceZipper](pathmap::utils::debug::TraceZipper), and renders
//! them as a self-contained, animated HTML page

use std::io;
use std::path::{Path, PathBuf};

use pathmap::PathMap;
use pathmap::arena_compact::ArenaCompactTree;
use pathmap::ring::{DistributiveLattice, Lattice};
use pathmap::utils::debug::zipper_tracing::{decode_trace, TraceValue};

mod annotations;
mod html;
mod replay;

pub use annotations::{Annotations, EventRange, Label, Mark, RangeNote, Zoom};
pub use html::render_html;
pub use replay::{replay, quote_path, Frame, MapView, NodeView, Replay, ReplayConfig, ZipperView};

/// A value type that traces can be replayed with
pub trait ReplayValue: TraceValue + Clone + Send + Sync + Unpin + Lattice + DistributiveLattice + core::fmt::Debug {
    /// The text to show for a value, or `None` to show nothing
    fn display(&self) -> Option<String>;
    /// Converts a value read from an ACT file
    fn from_act(val: u64) -> Self;
}

impl ReplayValue for u64 {
    fn display(&self) -> Option<String> { Some(self.to_string()) }
    fn from_act(val: u64) -> Self { val }
}

impl ReplayValue for () {
    fn display(&self) -> Option<String> { None }
    fn from_act(_val: u64) -> Self {}
}

/// Loads an ACT file into a [PathMap]
pub fn load_act<V: ReplayValue>(path: &Path) -> io::Result<PathMap<V>> {
    let act = ArenaCompactTree::open_mmap(path)?;
    Ok(act.iter().map(|(path, val)| (path, V::from_act(val))).collect())
}

fn render<V: ReplayValue>(trace: &[u8], acts: &[PathBuf], ann: Option<&Annotations>, cfg: &ReplayConfig, title: &str) -> io::Result<(String, Vec<String>)> {
    let events = decode_trace::<V>(trace)?;
    let seeds = acts.iter()
        .map(|path| Ok((format!("{}", path.file_name().unwrap_or(path.as_os_str()).to_string_lossy()), load_act::<V>(path)?)))
        .collect::<io::Result<Vec<_>>>()?;
    let replay = replay(&events, seeds, cfg);
    let html = render_html(&replay, title, ann).map_err(io::Error::other)?;
    Ok((html, replay.warnings))
}

/// Replays a trace, seeding maps from `acts`, and returns the HTML page, steered by `ann` if given, and any warnings
///
/// Traces with `u64` and `()` values are supported
pub fn render_trace(trace: &[u8], acts: &[PathBuf], ann: Option<&Annotations>, cfg: &ReplayConfig, title: &str) -> io::Result<(String, Vec<String>)> {
    match render::<u64>(trace, acts, ann, cfg, title) {
        //The trace's value type is only known from its header, so a mismatch means it should be tried as ()
        Err(err) if err.kind() == io::ErrorKind::InvalidData => render::<()>(trace, acts, ann, cfg, title).map_err(|_| err),
        result => result,
    }
}
