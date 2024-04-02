use core::{
    ptr::read_volatile,
    sync::atomic::{AtomicUsize, Ordering},
};

static MBOXBASE: AtomicUsize = AtomicUsize::new(0);

const CHANNEL: u32 = 8;

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

#[repr(C)]
#[repr(align(16))]
pub(crate) struct Mbox<T>(pub T);

pub(crate) struct MboxChannel {
    base: usize,
}

impl MboxChannel {
    pub fn new() -> Self {
        let base = MBOXBASE.load(Ordering::Relaxed);
        Self { base }
    }

    pub fn mbox_call<T>(&self, buffer: &mut Mbox<T>) -> bool {
        let ptr = buffer as *mut Mbox<T> as usize;
        let r = ((ptr & !0xF) | (CHANNEL & 0xF) as usize) as u32;
        let ptr1 = (ptr + 4) as *mut u32;

        while registers::STATUS
            .read(self.base)
            .contains(registers::Status::FULL)
        {
            unsafe { core::arch::asm!("nop") };
        }

        registers::WRITE.write(r, self.base);

        loop {
            unsafe { core::arch::asm!("nop") };
            while registers::STATUS
                .read(self.base)
                .contains(registers::Status::EMPTY)
            {
                unsafe { core::arch::asm!("nop") };
            }

            let rd = registers::READ.read(self.base);

            if r == rd {
                let result = unsafe { read_volatile(ptr1) };
                return result == 0x80000000;
            }
        }
    }
}
