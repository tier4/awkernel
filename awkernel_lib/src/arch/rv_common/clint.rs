use crate::cpu::{cpu_id, num_cpu};
use core::ptr::{read_volatile, write_volatile};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    InvalidHartId,
}

pub struct Clint {
    pub(super) base_addr: usize,
    pub(super) mtime_freq: usize,
}

impl Clint {
    const MSWI_BASE: usize = 0x0000;
    // const MTIMECMP_BASE: usize = 0x4000; // TODO use this for timer interrupts
    const MTIME_OFFSET: usize = 0xbff8;

    #[inline]
    const fn msip(&self, hart_id: usize) -> *mut u32 {
        (self.base_addr + Self::MSWI_BASE + hart_id * 4) as *mut u32
    }

    // TODO use this for timer interrupts
    // #[inline]
    // const fn mtimecmp(&self, hart_id: usize) -> *mut u64 {
    //     (self.base_addr + Self::MTIMECMP_BASE + hart_id * 8) as *mut u64
    // }

    #[inline]
    const fn mtime(&self) -> *const u64 {
        (self.base_addr + Self::MTIME_OFFSET) as *const u64
    }

    /// Busy wait for a given number of microseconds.
    #[inline]
    pub fn wait_usec(&self, usec: u64) {
        let mtime = self.mtime();
        // Safety: mtime is a memory-mapped register that can be read safely.
        let end = unsafe { read_volatile(mtime) + ((self.mtime_freq as u64 / 1000) * usec) / 1000 };
        // Safety: mtime is a memory-mapped register that can be read safely.
        while unsafe { read_volatile(mtime) } < end {}
    }

    /// Return the uptime in microseconds since the system booted.
    #[inline]
    pub fn uptime_us(&self) -> u64 {
        // Safety: mtime is a memory-mapped register that can be read safely.
        let now = unsafe { read_volatile(self.mtime()) };
        now * 1_000_000 / self.mtime_freq as u64
    }

    /// Return the uptime in nanoseconds since the system booted.
    #[inline]
    pub fn uptime_nano(&self) -> u128 {
        // Safety: mtime is a memory-mapped register that can be read safely.
        let mtime = unsafe { read_volatile(self.mtime()) } as u128;
        mtime * 1_000_000_000 / self.mtime_freq as u128
    }

    /// Trigger a software interrupt to the specified hart.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the hart_id is valid.
    #[inline]
    unsafe fn soft_interrupt_unchecked(&self, hart_id: usize) {
        // Safety: The caller must ensure that the hart_id is valid.
        unsafe { write_volatile(self.msip(hart_id), 1) };
    }

    /// Trigger a software interrupt to the specified hart.
    ///
    /// If the hart_id is invalid, return an error.
    #[inline]
    pub fn soft_interrupt(&self, hart_id: usize) -> Result<(), Error> {
        if hart_id >= num_cpu() {
            return Err(Error::InvalidHartId);
        }
        // Safety: hart_id is within the range of available harts
        unsafe { self.soft_interrupt_unchecked(hart_id) };
        Ok(())
    }

    /// Trigger a software interrupt to all harts, including the current hart.
    #[inline]
    pub fn soft_interrupt_broadcast(&self) {
        for hart_id in 0..num_cpu() {
            // Safety: hart_id is within the range of available harts
            unsafe { self.soft_interrupt_unchecked(hart_id) };
        }
    }

    /// Trigger a software interrupt to all harts, excluding the current hart.
    #[inline]
    pub fn soft_interrupt_broadcast_without_self(&self) {
        let self_hart_id = cpu_id();
        for hart_id in 0..num_cpu() {
            if hart_id != self_hart_id {
                // Safety: hart_id is within the range of available harts
                unsafe { self.soft_interrupt_unchecked(hart_id) };
            }
        }
    }
}
