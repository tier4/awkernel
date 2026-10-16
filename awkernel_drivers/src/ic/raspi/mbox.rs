//! Raspberry Pi firmware property-mailbox portocol implementation.
//!
//! Protocol details are as documented by the Mailbox property interface reference:
//! <https://github.com/raspberrypi/firmware/wiki/Mailbox-property-interface>

use awkernel_aarch64::cache::{clean_dcache_range, invalidate_dcache_range};
use core::{
    ptr::read_volatile,
    sync::atomic::{AtomicUsize, Ordering},
};
pub mod msg;
use msg::Buffer;

static MBOXBASE: AtomicUsize = AtomicUsize::new(0);

const CHANNEL: u32 = 8;
const BUS_ADDR_MASK: usize = 0x3fff_fff0;

pub const MBOX_REQUEST: u32 = 0;
pub const MBOX_TAG_LAST: u32 = 0;

/// Sets the base address of the mailbox.
///
/// # Safety
///
/// This function is unsafe because it performs a volatile write to a memory address.
/// The caller must ensure that the passed `base` address is valid and that writing to this
/// address will not cause undefined behavior.
pub unsafe fn set_mbox_base(base: usize) {
    MBOXBASE.store(base, Ordering::Relaxed);
}

mod registers {
    use awkernel_lib::mmio_rw;
    use bitflags::bitflags;

    mmio_rw!(offset 0x00 => pub READ<u32>); // Read register
    mmio_rw!(offset 0x18 => pub STATUS<Status>); // Status register
    mmio_rw!(offset 0x20 => pub WRITE<u32>); // Write register

    bitflags! {
        pub struct Status: u32 {
            const FULL  = 0x80000000;
            const EMPTY = 0x40000000;
        }
    }
}

/// Mailbox-related errors returned by the mailbox property interface.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// The firmware reported that it could not parse the request buffer.
    Transport,
    /// The firmware never produced a response for this tag.
    Rejected,
    /// The response was shorter than this tag's response type.
    MalformedResponse,
    /// The bus address does not fit in the mailbox's 32-bit hardware register.
    InvalidAddress,
    /// Data buffer larger than the scratch buffer size.
    BufferTooLarge,
    /// The response value does not match the expected value.
    ValueMismatch,
    /// The requested element does not exist.
    DoesNotExist,
    /// The operation was unsuccesful.
    Unsuccessful,
    /// Unsupported operation.
    Unsupported,
}

impl Error {
    /// Returns a human-readable description of the error.
    pub fn description(&self) -> &'static str {
        match self {
            Error::Transport => "mailbox transport failure",
            Error::Rejected => "mailbox request rejected",
            Error::MalformedResponse => "malformed mailbox response",
            Error::InvalidAddress => "mailbox bus address out of range",
            Error::BufferTooLarge => "mailbox buffer too large for scratch buffer",
            Error::ValueMismatch => "mailbox element id mismatch",
            Error::DoesNotExist => "mailbox element does not exist",
            Error::Unsuccessful => "mailbox operation was unsuccessful",
            Error::Unsupported => "mailbox operation is unsupported",
        }
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(self.description())
    }
}

impl core::error::Error for Error {}

/// Property-mailbox tag IDs.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub(crate) enum TagId {
    /* Power tags. */
    GetPowerState = 0x0002_0001,
    GetTiming = 0x0002_0002,
    SetPowerState = 0x0002_8001,
    /* Clocks tags. */
    GetClockState = 0x0003_0001,
    SetClockState = 0x0003_8001,
    GetClockRate = 0x0003_0002,
    GetClockRateMeasured = 0x0003_0047,
    SetClockRate = 0x0003_8002,
    GetMaxClockRate = 0x0003_0004,
    GetMinClockRate = 0x0003_0007,
    GetTurbo = 0x0003_0009,
    SetTurbo = 0x0003_8009,
    /* Voltage tags. */
    GetVoltage = 0x0003_0003,
    SetVoltage = 0x0003_8003,
    GetMaxVoltage = 0x0003_0005,
    GetMinVoltage = 0x0003_0008,
    /* Temperature tags. */
    GetTemperature = 0x0003_0006,
    GetMaxTemperature = 0x0003_000a,
    /* Memory tags. */
    AllocateMemory = 0x0003_000c,
    LockMemory = 0x0003_000d,
    UnlockMemory = 0x0003_000e,
    ReleaseMemory = 0x0003_000f,
    /* Framebuffer tags. */
    AllocateBuffer = 0x0004_0001,
    SetPhysDisplaySize = 0x0004_8003,
    SetVirtDisplaySize = 0x0004_8004,
    SetFrameBufferDepth = 0x0004_8005,
    SetPixelOrder = 0x0004_8006,
    GetPixelPitch = 0x0004_0008,
    SetVirtualOffset = 0x0004_8009,
}

/// Caching modes for the mailbox buffer.
#[derive(Clone, Copy, Debug)]
pub enum Caching {
    L1AndL2 = 0,
    L2Coherent = 1,
    L2Only = 2,
    Uncached = 3,
}

#[repr(C)]
#[repr(align(64))] // Align to cache line size to avoid false sharing.
pub(crate) struct Mbox<T>(pub T);

pub(crate) struct MboxChannel {
    base: usize,
}

impl MboxChannel {
    pub fn new() -> Self {
        let base = MBOXBASE.load(Ordering::Relaxed);
        Self { base }
    }

    pub fn mbox_call_buffer<T>(
        &self,
        buffer: &mut msg::Buffer<T>,
        caching: Caching,
    ) -> Result<(), Error> {
        let buffer_addr = buffer as *mut Buffer<T> as usize;
        let len = core::mem::size_of::<Buffer<T>>();

        if (buffer_addr & BUS_ADDR_MASK) != buffer_addr {
            return Err(Error::InvalidAddress);
        }

        while registers::STATUS
            .read(self.base)
            .contains(registers::Status::FULL)
        {}

        let r = (caching as u32) << 30 | buffer_addr as u32 | CHANNEL;
        // SAFETY: `buffer` is a live mapped mailbox buffer.
        unsafe { clean_dcache_range(buffer_addr, len) };
        registers::WRITE.write(r, self.base);

        loop {
            while registers::STATUS
                .read(self.base)
                .contains(registers::Status::EMPTY)
            {}

            if r != registers::READ.read(self.base) {
                continue;
            }

            // SAFETY: `buffer` is a live mapped mailbox buffer.
            unsafe { invalidate_dcache_range(buffer_addr, len) };
            let ptr1 = (buffer_addr + 4) as *mut u32;
            // SAFETY: `ptr1` is a valid pointer to the response code in the buffer
            match unsafe { read_volatile(ptr1) } {
                0x8000_0000 => return Ok(()),
                0x8000_0001 => return Err(Error::Rejected),
                _ => return Err(Error::MalformedResponse),
            }
        }
    }
}
