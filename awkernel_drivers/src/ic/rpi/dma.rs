use super::mbox::{Mbox, MboxChannel, MBOX_REQUEST, MBOX_TAG_LAST};

/// Its block of memory will be accessed directly, bypassing the cache.
pub const MEM_FLAG_DIRECT: u32 = 1 << 2;

// Its block of memory will be accessed in a non-allocating fashion through the cache.
pub const MEM_FLAG_COHERENT: u32 = 2 << 2;

/// Its block of memory will be accessed by the VPU in a fashion which is allocating in L2, but only coherent in L1.
pub const MEM_FLAG_L1_NONALLOCATING: u32 = MEM_FLAG_DIRECT | MEM_FLAG_COHERENT;

#[derive(Debug)]
pub struct Dma {
    handle: u32,
    bus_addr: u32,
    size: u32,
    align: u32,
    mem_flags: u32,
}

impl Dma {
    pub fn new(size: u32, align: u32, mem_flags: u32) -> Option<Self> {
        let channel = MboxChannel::new();

        let mut mbox = Mbox::<[u32; 9]>([
            9 * 4,         // size
            MBOX_REQUEST,  // process request
            0x3000c,       // (the tag id)
            12,            // (size of the buffer)
            12,            // (size of the data)
            size,          // (num bytes? or pages?)
            align,         // (alignment)
            mem_flags,     // (MEM_FLAG_L1_NONALLOCATING)
            MBOX_TAG_LAST, // end tag
        ]);

        if !channel.mbox_call(&mut mbox) || mbox.0[5] == 0 {
            return None;
        }

        let handle = mbox.0[5];

        let mut mbox = Mbox::<[u32; 7]>([
            7 * 4,        // size
            MBOX_REQUEST, // process request
            0x3000d,      // (the tag id)
            4,            // (size of the buffer)
            4,            // (size of the data)
            handle,
            MBOX_TAG_LAST, // end tag
        ]);

        if !channel.mbox_call(&mut mbox) || mbox.0[5] == 0 {
            return None;
        }

        let bus_addr = mbox.0[5];

        Some(Self {
            handle,
            bus_addr,
            size,
            align,
            mem_flags,
        })
    }

    #[inline(always)]
    pub fn get_bus_addr(&self) -> u32 {
        self.bus_addr
    }
}

impl Drop for Dma {
    fn drop(&mut self) {
        let channel = MboxChannel::new();

        let mut mbox = Mbox::<[u32; 7]>([
            7 * 4,        // size
            MBOX_REQUEST, // process request
            0x3000e,      // (the tag id)
            4,            // (size of the buffer)
            4,            // (size of the data)
            self.handle,
            MBOX_TAG_LAST, // end tag
        ]);

        channel.mbox_call(&mut mbox);

        let mut mbox = Mbox::<[u32; 7]>([
            7 * 4,        // size
            MBOX_REQUEST, // process request
            0x3000f,      // (the tag id)
            4,            // (size of the buffer)
            4,            // (size of the data)
            self.handle,
            MBOX_TAG_LAST, // end tag
        ]);

        channel.mbox_call(&mut mbox);
    }
}
