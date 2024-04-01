use super::mbox::{Mbox, MboxChannel, MBOX_REQUEST, MBOX_TAG_LAST};

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

        if !channel.mbox_call(&mut mbox) {
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

        if !channel.mbox_call(&mut mbox) {
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
