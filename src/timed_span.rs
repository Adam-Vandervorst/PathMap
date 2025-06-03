use std::sync::atomic::{AtomicU64, Ordering};

macro_rules! entries {
    (
        pub enum $name:ident {
            $($entry:ident $(= $value:expr)?),*
            $(,)?
        }
    ) => {
        #[derive(Clone, Copy)]
        pub enum $name {
            $($entry $(= $value)?),*
        }
        impl $name {
            const ALL: &[$name] = &[$($name::$entry),*];
            const COUNT: usize = $name::ALL.len();
            pub fn to_str(&self) -> &'static str {
                match self {
                    $(
                        $name::$entry => stringify!($entry)
                    ),*
                }
            }
        }

    }
}

entries!{
    pub enum Entries {
        Reset,
        ValueCount,
        DescendTo,
        DescendToExisting,
        DescendToValue,
        DescendToByte,
        DescendIndexedBranch,
        DescendFirstByte,
        DescendUntil,
        MoveToPath,
        AscendByte,
        Ascend,
        ToNextSiblingByte,
        ToPrevSiblingByte,
        ToNextStep,
        AscendUntil,
        AscendUntilBranch,
        ToNextVal,
        DescendFirstKPath,
        ToNextKPath,
        ToNextGetValue,
        ForkReadZipper,
    }
}

pub struct Counter {
    pub count: AtomicU64,
    pub cycles: AtomicU64,
}

impl Counter {
    const fn new() -> Self {
        Self {
            count: AtomicU64::new(0),
            cycles: AtomicU64::new(0),
        }
    }
}

pub static COUNTERS: [Counter; Entries::COUNT] =
    [const { Counter::new() }; Entries::COUNT];

pub fn reset_counters() {
    for counter in &COUNTERS {
        counter.count.store(0, Ordering::Relaxed);
        counter.cycles.store(0, Ordering::Relaxed);
    }
}

pub fn print_counters() {
    println!("{:>20},Count,TSCDelta,TSCAverage", "Name");
    for &entry in Entries::ALL {
        let counter = &COUNTERS[entry as usize];
        let count = counter.count.load(Ordering::Relaxed);
        let cycles = counter.cycles.load(Ordering::Relaxed);
        if count == 0 && cycles == 0 { continue; }
        let average = cycles as f64 / count as f64;
        println!("{:>20},{},{},{}", entry.to_str(), count, cycles, average);
    }
}

#[allow(dead_code)]
mod tsc {
    use std::arch::asm;
    use std::sync::atomic::{AtomicU64, Ordering};
    #[cfg(target_arch = "aarch64")]
    #[inline]
    fn read_cycle_counter() -> u64 {
        let val: u64;
        unsafe {
            asm!(
                "mrs {}, CNTVCT_EL0",
                out(reg) val,
                options(nostack, nomem)
            );
        }
        val
    }

    #[cfg(any(target_arch = "x86", target_arch = "x86_64"))]
    #[inline]
    fn read_cycle_counter() -> u64 {
        let lo: u32;
        let hi: u32;
        unsafe {
            asm!(
                "rdtsc",
                out("eax") lo,
                out("edx") hi,
                options(nostack, nomem)
            );
        }
        ((hi as u64) << 32) | (lo as u64)
    }

    pub struct TimedSpanGuard<'a> {
        start: u64,
        counter: &'a AtomicU64,
    }

    impl<'a> TimedSpanGuard<'a> {
        pub fn new(counter: &'a AtomicU64) -> Self {
            Self {
                start: read_cycle_counter(),
                counter,
            }
        }
    }

    impl<'a> Drop for TimedSpanGuard<'a> {
        fn drop(&mut self) {
            let end = read_cycle_counter();
            self.counter.fetch_add(end - self.start, Ordering::Relaxed);
        }
    }
}

#[allow(dead_code)]
mod std_instant {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::Instant;
    pub struct TimedSpanGuard<'a> {
        start: Instant,
        counter: &'a AtomicU64,
    }

    impl<'a> TimedSpanGuard<'a> {
        pub fn new(counter: &'a AtomicU64) -> Self {
            Self {
                start: Instant::now(),
                counter,
            }
        }
    }

    impl<'a> Drop for TimedSpanGuard<'a> {
        fn drop(&mut self) {
            let duration = self.start.elapsed().as_nanos() as u64;
            self.counter.fetch_add(duration, Ordering::Relaxed);
        }
    }
}

#[allow(dead_code)]
mod clock_monotonic {
    use std::sync::atomic::{AtomicU64, Ordering};

    #[cfg(target_os="linux")]
    mod linux {
        // linux/time.h
        // const CLOCK_REALTIME          : i32 = 0;
        // const CLOCK_MONOTONIC         : i32 = 1;
        // const CLOCK_PROCESS_CPUTIME_ID: i32 = 2;
        // const CLOCK_THREAD_CPUTIME_ID : i32 = 3;
        const CLOCK_MONOTONIC_RAW     : i32 = 4;
        // const CLOCK_REALTIME_COARSE   : i32 = 5;
        const CLOCK_MONOTONIC_COARSE  : i32 = 6;
        // const CLOCK_BOOTTIME          : i32 = 7;
        // const CLOCK_REALTIME_ALARM    : i32 = 8;
        // const CLOCK_BOOTTIME_ALARM    : i32 = 9;

        #[allow(non_camel_case_types)]
        #[repr(C)]
        struct timespec {
            tv_sec: u64,
            tv_nsec: i32,
        }

        extern "C" {
            fn clock_gettime(clockid: i32, tp: &mut timespec) -> i32;
        }
        pub fn get_time() -> u64 {
            let mut time = timespec { tv_sec: 0, tv_nsec: 0 };
            let rv = unsafe { clock_gettime(CLOCK_MONOTONIC_RAW, &mut time) };
            debug_assert!(rv == 0, "failed clock_gettime?");
            time.tv_sec * 1_000_000_000 + time.tv_nsec as u64
        }
    }
    #[cfg(target_os="linux")]
    use linux::get_time;

    #[cfg(all(target_os="macos", target_arch="aarch64"))]
    mod macos {
        const CLOCK_MONOTONIC_RAW       : i32 = 4;
        const CLOCK_MONOTONIC_RAW_APPROX: i32 = 5;
        const CLOCK_MONOTONIC           : i32 = 6;
        // const CALENDAR_CLOCK: u64 = 1;
        #[allow(non_camel_case_types)]
        #[repr(C)]
        struct timespec {
            tv_sec: u64,
            tv_nsec: i32,
        }
        extern "C" {
            // host_get_clock_service(mach_host_self(), SYSTEM_CLOCK, &cclock);
            // fn clock_get_time(clock_serv: &mut u64, cur_time: &mut mach_timespec) -> i64;
            // mach_port_deallocate(mach_task_self(), cclock);
            fn clock_gettime(clock_serv: i32, cur_time: &mut timespec) -> i64;
        }

        pub fn get_time() -> u64 {
            let mut time = timespec { tv_sec: 0, tv_nsec: 0 };
            let rv = unsafe { clock_gettime(CLOCK_MONOTONIC_RAW, &mut time) };
            debug_assert!(rv == 0, "failed clock_gettime?");
            (time.tv_sec as u64 * 1_000_000_000) + time.tv_nsec as u64
        }
    }

    #[cfg(all(target_os="macos", target_arch="aarch64"))]
    use macos::get_time;

    pub struct TimedSpanGuard<'a> {
        start: u64,
        counter: &'a AtomicU64,
    }

    impl<'a> TimedSpanGuard<'a> {
        pub fn new(counter: &'a AtomicU64) -> Self {
            Self {
                start: get_time(),
                counter,
            }
        }
    }

    impl<'a> Drop for TimedSpanGuard<'a> {
        fn drop(&mut self) {
            let end = get_time();
            self.counter.fetch_add(end - self.start, Ordering::Relaxed);
        }
    }
}

pub use tsc::TimedSpanGuard;
pub const ENABLED: bool = true;

macro_rules! timed_span {
    ($name:ident, $dst:path) => {
        let _guard = if $crate::timed_span::ENABLED {
            let index = $crate::timed_span::Entries::$name as usize;
            let counter = &$dst[index];
            counter.count.fetch_add(1, core::sync::atomic::Ordering::Relaxed);
            Some($crate::timed_span::TimedSpanGuard::new(&counter.cycles))
        } else {
            None
        };
    };
    ($name:ident) => {
        $crate::timed_span::timed_span!($name, $crate::timed_span::COUNTERS)
    };
}

pub(crate) use timed_span;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_timed_span() {
        reset_counters();
        {
            timed_span!(Reset);
            for ii in 0..100_000 {
                core::hint::black_box(ii);
            }
        }
        print_counters();
    }
}
