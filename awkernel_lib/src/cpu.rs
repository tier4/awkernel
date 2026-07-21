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
