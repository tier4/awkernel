use core::ptr::{read_volatile, write_volatile};

static mut MBOXBASE: usize = 0;

pub unsafe fn set_mbox_base(base: usize) {
    write_volatile(&mut MBOXBASE, base);
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

pub struct MboxChannel {
    base: usize,
    channel: u32,
}

impl MboxChannel {
    pub fn new(channel: u32) -> Self {
        let base = unsafe { read_volatile(&MBOXBASE) };
        Self { base, channel }
    }

    pub fn send(&self, message: u32) {
        while registers::STATUS
            .read(self.base)
            .contains(registers::Status::FULL)
        {}
        registers::WRITE.write(message | self.channel, self.base);
    }

    pub fn receive(&self) -> u32 {
        while registers::STATUS
            .read(self.base)
            .contains(registers::Status::EMPTY)
        {}
        let value = registers::READ.read(self.base);
        value
    }

    pub fn mbox_call(&self, buffer: &mut [u32]) -> bool {
        let r = (buffer.as_ptr() as u32 & 0xFFFFFFF) | (self.channel & 0xF);

        while registers::STATUS
            .read(self.base)
            .contains(registers::Status::FULL)
        {}

        registers::WRITE.write(r, self.base);

        loop {
            while registers::STATUS
                .read(self.base)
                .contains(registers::Status::EMPTY)
            {}

            if r == registers::READ.read(self.base) {
                return buffer[1] == 0x80000000;
            }
        }
    }
}
