use core::ptr::{read_volatile, write_volatile};

/// The base address for the Mbox.
static mut MBOXBASE: usize = 0;

pub unsafe fn set_mbox_base(base: usize) {
    write_volatile(&mut MBOXBASE, base);
}

fn mbox_read_addr() -> *mut u32 {
    unsafe { (read_volatile(&MBOXBASE) + 0x00) as *mut u32 }
}

fn mbox_status() -> *mut u32 {
    unsafe { (read_volatile(&MBOXBASE) + 0x18) as *mut u32 }
}

fn mbox_write_addr() -> *mut u32 {
    unsafe { (read_volatile(&MBOXBASE) + 0x20) as *mut u32 }
}

pub struct MboxChannel {
    channel: u32,
}

impl MboxChannel {
    /// Create a new `MboxChannel`.
    pub fn new(channel: u32) -> Self {
        Self { channel }
    }

    /// Send a message to the `MboxChannel`.
    pub fn send(&self, message: u32) {
        log::info!("  send value{:}", message);
        while unsafe { read_volatile(mbox_status()) } & 0x80000000 != 0 {}
        unsafe { write_volatile(mbox_write_addr(), message | self.channel); }
    }

    /// Receive a message from the `MboxChannel`.
    pub fn receive(&self) -> u32 {
        log::info!("mbox receive1");
        while unsafe { read_volatile(mbox_status()) } & 0x40000000 != 0 {}
        log::info!("mbox receive2");
        let value = unsafe { read_volatile(mbox_read_addr()) };
        log::info!("mbox receive3");
        log::info!(" received value{:}", value);
        value
    }

    pub fn mbox_call(&self, buffer: &mut [u32]) -> bool {
        let r = (buffer.as_ptr() as u32 & 0xFFFFFFF) | (self.channel & 0xF);
        
        while unsafe { read_volatile(mbox_status()) } & 0x80000000 != 0 {}
        
        unsafe { write_volatile(mbox_write_addr(), r); }
        
        loop {
            while unsafe { read_volatile(mbox_status()) } & 0x40000000 != 0 {}
            
            if r == unsafe { read_volatile(mbox_read_addr()) } {
                return buffer[1] == 0x80000000;
            }
        }
    }
}
