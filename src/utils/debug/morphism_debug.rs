//! Debug utilities for catamorphisms and other morphisms

use crate::utils::ByteMask;
use crate::alloc::Allocator;
use crate::PathMap;
use crate::zipper::*;
use crate::morphisms::cata_jumping_cached_debug_body;

/// Debug extension trait for catamorphisms
///
/// This trait provides debug-only catamorphism methods that may expose additional
/// information useful for debugging and development.
pub trait CatamorphismDebug<V> {
    /// A debug-only version of [`cata_jumping_cached`](crate::morphisms::CatamorphismCached::cata_jumping_cached)
    /// where the full absolute path is available to the closure.
    ///
    /// Using data from the full path for your algorithm **will** lead to incorrect behavior.
    /// You must either adapt your algorithm not to require full path data or use one of the
    /// methods in [`crate::morphisms::CatamorphismSideEffecting`].
    fn cata_jumping_cached_debug<W, AlgF>(&self, alg_f: AlgF) -> W
    where
        W: Clone,
        AlgF: Fn(&ByteMask, &mut [W], Option<&V>, &[u8], &[u8]) -> W,
        Self: Sized,
    {
        self.cata_jumping_cached_fallible_debug(|mask, children, value, prefix, path| {
            Ok::<_, core::convert::Infallible>(alg_f(mask, children, value, prefix, path))
        })
        .unwrap()
    }

    /// Fallible form of [`Self::cata_jumping_cached_debug`].
    fn cata_jumping_cached_fallible_debug<W, E, AlgF>(&self, alg_f: AlgF) -> Result<W, E>
        where
            W: Clone,
            AlgF: Fn(&ByteMask, &mut [W], Option<&V>, &[u8], &[u8]) -> Result<W, E>;
}

impl<'a, Z, V: 'a> CatamorphismDebug<V> for Z where Z: Clone + Zipper + ZipperReadOnlyConditionalValues<'a, V> + ZipperConcrete + ZipperAbsolutePath + ZipperPathBuffer {
    fn cata_jumping_cached_fallible_debug<W, E, AlgF>(&self, alg_f: AlgF) -> Result<W, E>
    where
        W: Clone,
        AlgF: Fn(&ByteMask, &mut [W], Option<&V>, &[u8], &[u8]) -> Result<W, E>
    {
        cata_jumping_cached_debug_body(self.clone(), alg_f)
    }
}

impl<V: 'static + Clone + Send + Sync + Unpin, A: Allocator + 'static> CatamorphismDebug<V> for PathMap<V, A> {
    fn cata_jumping_cached_fallible_debug<W, E, AlgF>(&self, alg_f: AlgF) -> Result<W, E>
        where
            W: Clone,
            AlgF: Fn(&ByteMask, &mut [W], Option<&V>, &[u8], &[u8]) -> Result<W, E>
    {
        self.read_zipper().cata_jumping_cached_fallible_debug(alg_f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::morphisms::CatamorphismCached;

    #[test]
    fn debug_cached_cata_uses_the_zipper_focus_and_absolute_paths() {
        let map: PathMap<()> = [
            (b"a".as_slice(), ()),
            (b"ab".as_slice(), ()),
            (b"ac".as_slice(), ()),
            (b"z".as_slice(), ()),
        ]
        .into_iter()
        .collect();
        let mut zipper = map.read_zipper();
        zipper.descend_to(b"a");
        let paths = std::cell::RefCell::new(Vec::new());

        let count = zipper.cata_jumping_cached_debug(|_mask, children: &mut [usize], value, _prefix, path| {
            paths.borrow_mut().push(path.to_vec());
            value.is_some() as usize + children.iter().sum::<usize>()
        });

        assert_eq!(count, 3);
        assert!(paths.borrow().iter().all(|path| path.starts_with(b"a")));
        assert!(paths.borrow().contains(&b"a".to_vec()));
        assert_eq!(zipper.path(), b"a");
    }

    #[test]
    fn debug_cached_cata_does_not_ascend_past_a_unary_focus() {
        let map: PathMap<()> = [(b"abc".as_slice(), ()), (b"z".as_slice(), ())]
            .into_iter()
            .collect();
        let mut zipper = map.read_zipper();
        zipper.descend_to(b"a");
        let paths = std::cell::RefCell::new(Vec::new());

        let count = zipper.cata_jumping_cached_debug(|_mask, children: &mut [usize], value, _prefix, path| {
            paths.borrow_mut().push(path.to_vec());
            value.is_some() as usize + children.iter().sum::<usize>()
        });

        assert_eq!(count, 1);
        assert!(paths.borrow().iter().all(|path| path.starts_with(b"a")));
        assert_eq!(zipper.path(), b"a");
    }

    #[test]
    fn debug_cached_cata_short_circuits_shared_subtries() {
        let child: PathMap<()> = [(b"c".as_slice(), ()), (b"d".as_slice(), ())]
            .into_iter()
            .collect();
        let mut map = PathMap::new();
        let mut writer = map.write_zipper();
        for path in [b"a".as_slice(), b"b".as_slice()] {
            writer.reset();
            writer.descend_to(path);
            writer.graft_map(child.clone());
        }
        drop(writer);

        let cached_calls = std::sync::atomic::AtomicUsize::new(0);
        let cached = map.cata_jumping_cached(|_mask, children: &mut [usize], value, _prefix| {
            cached_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            value.is_some() as usize + children.iter().sum::<usize>()
        });

        let debug_calls = std::sync::atomic::AtomicUsize::new(0);
        let debug = map.cata_jumping_cached_debug(|_mask, children: &mut [usize], value, _prefix, _path| {
            debug_calls.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
            value.is_some() as usize + children.iter().sum::<usize>()
        });

        assert_eq!(cached, 4);
        assert_eq!(debug, cached);
        assert_eq!(debug_calls.load(std::sync::atomic::Ordering::Relaxed), cached_calls.load(std::sync::atomic::Ordering::Relaxed));
    }
}
