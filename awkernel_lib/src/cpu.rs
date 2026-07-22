use crate::arch::ArchImpl;
use core::{
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

pub const NUM_MAX_CPU: usize = 512;

/// Number of 64-bit words needed to represent a set of `NUM_MAX_CPU` CPUs.
pub const CPU_SET_WORDS: usize = NUM_MAX_CPU / 64;

static NUM_CPU: AtomicUsize = AtomicUsize::new(0);

/// A set of CPU cores, represented as a bitmask supporting up to `NUM_MAX_CPU`
/// CPUs. This is the affinity mask type of the `affinity_btree_queue` crate,
/// so schedulers can pass it to the run queue without conversion. All
/// constructors are `const fn`; build sets with the chainable builder, e.g.
/// `CpuSet::empty().with(1).with(2)`.
pub type CpuSet = affinity_btree_queue::CpuMask<CPU_SET_WORDS>;

/// Return a new set keeping only the worker CPUs (`1..num_cpus`) of `set`.
/// CPU 0 is the primary core and is always excluded.
pub const fn masked_workers(set: CpuSet, num_cpus: usize) -> CpuSet {
    set.masked_below(num_cpus).without(0)
}

/// Return the set of all worker CPUs (`1..num_cpus`).
pub const fn all_workers(num_cpus: usize) -> CpuSet {
    masked_workers(CpuSet::all(), num_cpus)
}

#[cfg(feature = "std")]
mod sleep_cpu_std;

#[cfg(feature = "std")]
use sleep_cpu_std::SleepCpuStd as SleepCpuImpl;

#[cfg(not(feature = "std"))]
mod sleep_cpu_no_std;

#[cfg(not(feature = "std"))]
use sleep_cpu_no_std::SleepCpuNoStd as SleepCpuImpl;

static SLEEP_CPU_IMPL: SleepCpuImpl = SleepCpuImpl;

pub trait CPU {
    /// CPU ID returns the ID of the CPU.
    /// The ID is unique for each CPU and starts from 0 to `num_cpu() - 1`.
    fn cpu_id() -> usize;

    /// Raw CPU ID returns the ID of the CPU without any modification.
    fn raw_cpu_id() -> usize;
}

#[inline(always)]
pub fn cpu_id() -> usize {
    ArchImpl::cpu_id()
}

#[inline(always)]
pub fn raw_cpu_id() -> usize {
    ArchImpl::raw_cpu_id()
}

/// # Safety
///
/// This function must be called during the kernel initialization.
pub unsafe fn set_num_cpu(num_cpu: usize) {
    NUM_CPU.store(num_cpu, Ordering::Relaxed);
}

#[inline(always)]
pub fn num_cpu() -> usize {
    NUM_CPU.load(Ordering::Relaxed)
}

pub trait SleepCpu {
    /// Sleep current CPU.
    fn sleep(&self, timeout: Option<Duration>);

    /// Wake up the CPU.
    ///
    /// If the CPU is already awake, return `false`.
    /// Otherwise, return `true`.
    fn wake_up(cpu_id: usize) -> bool;
}

/// Sleep the current CPU.
#[inline(always)]
pub fn sleep_cpu(timeout: Option<Duration>) {
    SLEEP_CPU_IMPL.sleep(timeout);
}

/// Wake up the CPU with the given `cpu_id`.
///
/// If the CPU is already awake, return `false`.
/// Otherwise, return `true`.
#[inline(always)]
pub fn wake_cpu(cpu_id: usize) -> bool {
    SleepCpuImpl::wake_up(cpu_id)
}

/// Initialize sleep.
/// After calling this, `sleep_cpu()` and `wake_cpu()` will be available.
///
/// # Safety
///
/// This function must be called once during kernel initialization.
pub unsafe fn init_sleep() {
    #[cfg(not(feature = "std"))]
    sleep_cpu_no_std::init();
}

/// Wait until `init_sleep()` is called.
pub fn wait_init_sleep() {
    #[cfg(not(feature = "std"))]
    sleep_cpu_no_std::wait_init();
}

#[allow(dead_code)] // temporary for RV64
#[cfg(not(feature = "std"))]
pub(crate) fn reset_wakeup_timer() {
    sleep_cpu_no_std::reset_wakeup_timer();
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec::Vec;

    /// Collect the CPUs contained in `set`, in ascending order.
    fn cpus(set: CpuSet) -> Vec<usize> {
        set.iter().collect()
    }

    #[test]
    fn all_workers_excludes_cpu0_and_sizes() {
        // Only CPU 0 exists, so there is no worker core.
        assert!(all_workers(1).is_empty());

        assert_eq!(cpus(all_workers(2)), [1]);
        assert_eq!(cpus(all_workers(4)), [1, 2, 3]);

        // Word boundary: num_cpus 64 keeps CPUs 1..=63 (CPU 0 dropped).
        let w64 = all_workers(64);
        assert_eq!(cpus(w64), (1..64).collect::<Vec<_>>());

        // num_cpus 65 spills one bit (CPU 64) into the second word.
        let w65 = all_workers(65);
        assert_eq!(cpus(w65), (1..65).collect::<Vec<_>>());

        // Two full words minus CPU 0.
        let w128 = all_workers(128);
        assert_eq!(cpus(w128), (1..128).collect::<Vec<_>>());

        // CPU 0 is never a worker, at any size.
        for n in [1, 2, 4, 64, 65, 128] {
            assert!(!all_workers(n).contains(0), "num_cpus={n}");
        }
    }

    #[test]
    fn all_workers_iter_is_ascending_across_words() {
        // The 63 -> 64 transition crosses the first word boundary.
        let v = cpus(all_workers(65));
        assert_eq!(v.first(), Some(&1));
        assert_eq!(v.last(), Some(&64));
        assert!(
            v.windows(2).all(|w| w[0] < w[1]),
            "must be strictly ascending"
        );
    }

    #[test]
    fn masked_workers_normalizes() {
        // CPU 0 is stripped even when explicitly present.
        let s = CpuSet::empty().with(0).with(1).with(2);
        assert_eq!(cpus(masked_workers(s, 4)), [1, 2]);

        // Out-of-range CPUs are trimmed.
        let s = CpuSet::empty().with(1).with(100);
        assert_eq!(cpus(masked_workers(s, 4)), [1]);

        // Around a word boundary: with num_cpus=65, valid CPUs are 0..=64,
        // so CPU 65 is out of range and dropped.
        let s = CpuSet::empty().with(64).with(65);
        assert_eq!(cpus(masked_workers(s, 65)), [64]);
    }

    #[test]
    fn masked_workers_is_idempotent_on_valid_sets() {
        // An already-normalized set is a fixed point. This is the invariant
        // `clustered_edf::wake_task` relies on (`masked_workers(s, n) != s`
        // is false for a valid set).
        let s = all_workers(64);
        assert_eq!(masked_workers(s, 64), s);

        let s = CpuSet::empty().with(1).with(2);
        assert_eq!(masked_workers(s, 4), s);
    }
}
