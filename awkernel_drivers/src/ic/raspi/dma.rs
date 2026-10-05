use super::mbox::{
    msg::{Buffer, Tag},
    Caching, Error, TagId,
};

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
}

impl Dma {
    pub fn new(size: u32, align: u32, mem_flags: u32) -> Result<Self, Error> {
        let mut req = Buffer::new(Tag::new(TagId::AllocateMemory, (size, align, mem_flags)));
        req.call(Caching::Uncached)?;
        let handle = *req.tags().try_response()?;
        if handle == 0 {
            return Err(Error::Unsuccessful);
        }

        let mut req = Buffer::new(Tag::new(TagId::LockMemory, handle));
        req.call(Caching::Uncached)?;
        let bus_addr = *req.tags().try_response()?;
        if bus_addr == 0 {
            return Err(Error::Unsuccessful);
        }

        Ok(Self { handle, bus_addr })
    }

    #[inline(always)]
    pub const fn get_bus_addr(&self) -> u32 {
        self.bus_addr
    }
}

impl Drop for Dma {
    fn drop(&mut self) {
        let mut req = Buffer::new(Tag::<u32, u32>::new(TagId::UnlockMemory, self.handle));
        let _ = req.call(Caching::Uncached);

        let mut req = Buffer::new(Tag::<u32, u32>::new(TagId::ReleaseMemory, self.handle));
        let _ = req.call(Caching::Uncached);
    }
}
