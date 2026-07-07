use crate::arch::ArchImpl;
use core::{
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

pub const NUM_MAX_CPU: usize = 512;

/// Number of 64-bit words needed to represent a set of `NUM_MAX_CPU` CPUs.
pub const CPU_SET_WORDS: usize = NUM_MAX_CPU / 64;

static NUM_CPU: AtomicUsize = AtomicUsize::new(0);

/// A set of CPU cores, represented as a bitmask supporting up to `NUM_MAX_CPU` CPUs.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct CpuSet([u64; CPU_SET_WORDS]);

impl CpuSet {
    /// Create an empty set.
    pub const fn empty() -> Self {
        Self([0; CPU_SET_WORDS])
    }

    /// Create a set containing all worker CPUs (`1..num_cpu()`).
    pub fn any() -> Self {
        Self::all_workers(num_cpu())
    }

    /// Create a set from a bitmask of CPUs 0..64.
    /// Bit `i` of `bits` corresponds to CPU `i`.
    pub const fn from_bits(bits: u64) -> Self {
        let mut words = [0; CPU_SET_WORDS];
        words[0] = bits;
        Self(words)
    }

    /// Return a new set with the bit for `cpu` set.
    /// Panics if `cpu >= NUM_MAX_CPU`.
    pub const fn insert(mut self, cpu: usize) -> Self {
        assert!(cpu < NUM_MAX_CPU, "CPU index out of range");
        self.0[cpu / 64] |= 1 << (cpu % 64);
        self
    }

    /// True if the bit for `cpu` is set.
    pub const fn contains(&self, cpu: usize) -> bool {
        cpu < NUM_MAX_CPU && (self.0[cpu / 64] >> (cpu % 64)) & 1 == 1
    }

    /// True if no bit is set.
    pub const fn is_empty(&self) -> bool {
        let mut i = 0;
        while i < CPU_SET_WORDS {
            if self.0[i] != 0 {
                return false;
            }
            i += 1;
        }
        true
    }

    /// Return word `idx` of the backing bitmask. Panics if `idx >= CPU_SET_WORDS`.
    pub const fn word(&self, idx: usize) -> u64 {
        self.0[idx]
    }

    /// Return a new set keeping only CPUs in `1..num_cpus`
    /// (CPU 0 is always excluded).
    pub const fn masked_workers(mut self, num_cpus: usize) -> Self {
        let mut i = 0;
        while i < CPU_SET_WORDS {
            let lo = i * 64;
            if lo >= num_cpus {
                self.0[i] = 0;
            } else {
                let valid = num_cpus - lo; // 1..=64 bits of this word are valid.
                if valid < 64 {
                    self.0[i] &= (1 << valid) - 1;
                }
            }
            i += 1;
        }
        self.0[0] &= !1; // Exclude CPU 0.
        self
    }

    /// Return the set of all worker CPUs (`1..num_cpus`).
    pub const fn all_workers(num_cpus: usize) -> Self {
        let mut set = Self([u64::MAX; CPU_SET_WORDS]);
        set = set.masked_workers(num_cpus);
        set
    }

    /// Iterate over the CPUs contained in the set, in ascending order.
    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.0.iter().enumerate().flat_map(|(w, &word)| {
            (0..64)
                .filter(move |bit| (word >> bit) & 1 == 1)
                .map(move |bit| w * 64 + bit)
        })
    }
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
