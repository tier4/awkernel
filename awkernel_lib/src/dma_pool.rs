//! Memory pool for DMA.

use core::{alloc::Layout, ptr::NonNull};

use rlsf::Tlsf;

use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    paging::{self, PAGESIZE},
    sync::{mcs::MCSNode, mutex::Mutex},
};

const FLLEN: usize = 28; // The maximum block size is (32 << 28) - 1 = 8_589_934_591 (nearly 8GiB)
const SLLEN: usize = 64; // The worst-case internal fragmentation is ((32 << 28) / 64 - 2) = 134_217_726 (nearly 128MiB)
type FLBitmap = u32; // must be longer than FLLEN
type SLBitmap = u64; // must be longer than SLLEN

type TLSFAlloc = Tlsf<'static, FLBitmap, SLBitmap, FLLEN, SLLEN>;

const NUMA_NUM_MAX: usize = 16;

static CONTINUOUS_MEMORY_POOLS: [Mutex<TLSFAlloc>; NUMA_NUM_MAX] =
    array_macro::array![_ => Mutex::new(TLSFAlloc::new()); NUMA_NUM_MAX];

pub struct DMAPool {
    virt_addr: VirtAddr,
    phy_addr: PhyAddr,
    size: usize,
    numa_id: usize,
}

pub unsafe fn init_dma_pool(num_id: usize, start: VirtAddr, size: usize) {
    assert!(num_id < NUMA_NUM_MAX);

    let ptr = start.as_mut_ptr::<u8>();
    let pool = core::slice::from_raw_parts_mut(ptr, size);
    let Some(pool) = NonNull::new(pool) else {
        return;
    };

    let mut node = MCSNode::new();

    CONTINUOUS_MEMORY_POOLS[num_id]
        .lock(&mut node)
        .insert_free_block_ptr(pool);
}

impl DMAPool {
    pub fn new(numa_id: usize, pages: usize) -> Option<Self> {
        assert!(numa_id < NUMA_NUM_MAX);

        let size = pages * PAGESIZE;
        let layout = Layout::from_size_align(size, PAGESIZE).ok()?;

        let mut node = MCSNode::new();

        let pool = {
            let mut allocator = CONTINUOUS_MEMORY_POOLS[numa_id].lock(&mut node);
            allocator.allocate(layout)?
        };

        let virt_addr = VirtAddr::new(pool.as_ptr() as usize);
        let phy_addr = paging::vm_to_phy(virt_addr).unwrap();

        Some(Self {
            virt_addr,
            phy_addr,
            size,
            numa_id,
        })
    }

    #[inline(always)]
    pub fn get_virt_addr(&self) -> VirtAddr {
        self.virt_addr
    }

    #[inline(always)]
    pub fn get_phy_addr(&self) -> PhyAddr {
        self.phy_addr
    }

    #[inline(always)]
    pub fn get_size(&self) -> usize {
        self.size
    }

    #[inline(always)]
    pub fn get_numa_id(&self) -> usize {
        self.numa_id
    }

    #[inline(always)]
    pub unsafe fn get_slice<'a, T: Sized>(&'a self) -> &'a [T] {
        assert!(self.size % core::mem::size_of::<T>() == 0);
        core::slice::from_raw_parts::<'a, T>(
            self.virt_addr.as_ptr(),
            self.size / core::mem::size_of::<T>(),
        )
    }

    #[inline(always)]
    pub unsafe fn get_slice_mut<'a, T: Sized>(&'a mut self) -> &'a mut [T] {
        assert!(self.size % core::mem::size_of::<T>() == 0);
        core::slice::from_raw_parts_mut::<'a, T>(
            self.virt_addr.as_mut_ptr(),
            self.size / core::mem::size_of::<T>(),
        )
    }
}

impl Drop for DMAPool {
    fn drop(&mut self) {
        let ptr = self.virt_addr.as_mut_ptr::<u8>();
        let mut node = MCSNode::new();
        let mut allocator = CONTINUOUS_MEMORY_POOLS[self.numa_id].lock(&mut node);
        unsafe {
            allocator.deallocate(NonNull::new_unchecked(ptr), PAGESIZE);
        }
    }
}
