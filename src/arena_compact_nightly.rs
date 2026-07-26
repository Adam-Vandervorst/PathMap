use super::*;

/// The shared body of the sinks below: resume with an item to push it, resume
/// with `None` to seal the trie and return it
fn act_sink<T>(
    mut out: ACTOutputStream,
    mut push: impl FnMut(&mut ACTOutputStream, T) -> std::io::Result<()>,
) -> impl std::ops::Coroutine<
    Option<T>,
    Yield = (),
    Return = std::io::Result<ArenaCompactTree<Mmap>>,
> {
    #[coroutine] move |mut i: Option<T>| {
        while let Some(item) = i {
            push(&mut out, item)?;
            i = yield ();
        }
        out.finish()
    }
}

/// Returns a coroutine to incrementally build an `.act` file from pushed paths
///
/// This is the push-driven counterpart to [ACTOutputStream::push]: instead of
/// the caller driving a loop, the sink is resumed with one path at a time,
/// which suits producers that are themselves loops or coroutines.
///
/// Paths must arrive in strictly increasing lexicographic order (see
/// [ACTOutputStream::push]) and every path gets a value of `0`. Passing `None`
/// signals the end of input; the coroutine then seals the trie and returns it,
/// memory-mapped from the written file.
///
/// The resume type fixes a single lifetime for every path the sink is fed, so
/// the producer must own its paths — a borrowed scratch buffer refilled per
/// path will not type-check.
///
/// # Examples
/// ```
/// #![feature(coroutines, coroutine_trait)]
/// use std::ops::{Coroutine, CoroutineState};
/// use std::pin::pin;
/// use pathmap::arena_compact::{ACTOutputStream, act_serialization_sink};
/// # fn main() -> std::io::Result<()> {
/// let dir = tempfile::tempdir()?;
/// let out = ACTOutputStream::new(dir.path().join("sink.act"))?;
/// let mut sink = pin!(act_serialization_sink(out));
/// for path in [b"123".as_slice(), b"124".as_slice()] {
///     match sink.as_mut().resume(Some(path)) {
///         CoroutineState::Yielded(()) => {}
///         CoroutineState::Complete(r) => { r?; unreachable!("ended early") }
///     }
/// }
/// let tree = match sink.as_mut().resume(None) {
///     CoroutineState::Complete(r) => r?,
///     CoroutineState::Yielded(()) => unreachable!("`None` ends the stream"),
/// };
/// assert_eq!(tree.get_val_at("123"), Some(0));
/// assert_eq!(tree.get_val_at("125"), None);
/// # Ok(())
/// # }
/// ```
pub fn act_serialization_sink<'p>(
    out: ACTOutputStream,
) -> impl std::ops::Coroutine<
    Option<&'p [u8]>,
    Yield = (),
    Return = std::io::Result<ArenaCompactTree<Mmap>>,
> {
    act_sink(out, |out: &mut ACTOutputStream, p: &'p [u8]| out.push(p))
}

/// Returns a coroutine to incrementally build an `.act` file from pushed
/// `(path, value)` pairs
///
/// See [act_serialization_sink], which this mirrors; the only difference is
/// that each path carries a value instead of defaulting to `0`.
pub fn act_serialization_sink_with_vals<'p>(
    out: ACTOutputStream,
) -> impl std::ops::Coroutine<
    Option<(&'p [u8], u64)>,
    Yield = (),
    Return = std::io::Result<ArenaCompactTree<Mmap>>,
> {
    act_sink(out, |out: &mut ACTOutputStream, (p, v): (&'p [u8], u64)| out.push_val(p, v))
}
