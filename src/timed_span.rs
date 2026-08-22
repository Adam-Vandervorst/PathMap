use core::sync::atomic::Ordering;

use span_timing::{Counter, timing_entries};

/// Set to `true` to enable timing on ReadZipperCore and ACTZipper ops.  Currently not implemented for
/// other zipper types, except insofar as they call through to a zipper with the implementation.
pub(crate) const ENABLED: bool = false;

/// Wrapper macro to enable and disable span timing
macro_rules! timed_span {
    ($entry:expr, $counters:expr $(,)?) => {
        let _timed_span_guard = if $crate::timed_span::ENABLED {
            Some(::span_timing::timed_span!($entry, $counters))
        } else {
            None
        };
    };
}

pub(crate) use timed_span;

timing_entries! {
    pub enum TimingEntries {
        Reset,
        ValueCount,
        DescendTo,
        DescendToExisting,
        DescendToVal,  //ReadZipperCore doesn't have a native impl for this method yet
        DescendToByte,
        DescendIndexedByte,
        DescendFirstByte,
        DescendUntil,
        // MoveToPath,  This is only implemented with a default impl, and it's composed from other zipper ops
        AscendByte,
        Ascend,
        ToNextSiblingByte,
        ToPrevSiblingByte,
        // ToNextStep,  This is only implemented with a default impl, and it's composed from other zipper ops
        AscendUntil,
        AscendUntilBranch,
        ToNextVal,
        DescendFirstKPath,
        ToNextKPath,
        ToNextGetValue,
        ForkReadZipper,
    }
    pub static COUNTERS: [Counter];
}

pub fn reset_counters() {
    for counter in &COUNTERS {
        counter.reset();
    }
}

pub fn print_counters() {
    println!("{:>20},Count,TicksDelta,TicksAverage", "Name");
    for &entry in TimingEntries::ALL {
        let counter = &COUNTERS[entry as usize];
        let count = counter.count.load(Ordering::Relaxed);
        let ticks = counter.ticks.load(Ordering::Relaxed);
        if count == 0 && ticks == 0 {
            continue;
        }
        let average = ticks as f64 / count as f64;
        println!("{:>20},{},{},{}", entry.to_str(), count, ticks, average);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_timed_span() {
        reset_counters();
        {
            timed_span!(TimingEntries::Reset, COUNTERS);
            for ii in 0..100_000 {
                core::hint::black_box(ii);
            }
        }
        print_counters();
    }
}
