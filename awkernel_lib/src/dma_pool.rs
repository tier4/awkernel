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

static CONTINUOUS_MEMORY_POOL: [Mutex<TLSFAlloc>; NUMA_NUM_MAX] =
    array_macro::array![_ => Mutex::new(TLSFAlloc::new()); NUMA_NUM_MAX];

#[derive(Debug)]
pub struct DMAPool<T> {
    virt_addr: VirtAddr,
    phy_addr: PhyAddr,
    size: usize,
    numa_id: usize,
    ptr: NonNull<T>,
}

unsafe impl<T: Send> Send for DMAPool<T> {}
unsafe impl<T: Sync> Sync for DMAPool<T> {}

/// # Safety
///
/// `start` must be a valid address.
pub unsafe fn init_dma_pool(numa_id: usize, start: VirtAddr, size: usize) {
    assert!(numa_id < NUMA_NUM_MAX);

    let pool = core::slice::from_raw_parts_mut(start.as_usize() as *mut u8, size);

    let Some(pool) = NonNull::new(pool) else {
        return;
    };

    let mut node = MCSNode::new();

    {
        let mut guard = CONTINUOUS_MEMORY_POOL[numa_id].lock(&mut node);

        guard.insert_free_block_ptr(pool);
    }
}

impl<T> DMAPool<T> {
    pub fn new(numa_id: usize, pages: usize) -> Option<Self> {
        assert!(numa_id < NUMA_NUM_MAX);
        assert!(core::mem::size_of::<T>() <= pages * PAGESIZE);

        let size = pages * PAGESIZE;
        let layout = Layout::from_size_align(size, PAGESIZE).ok()?;

        let mut node = MCSNode::new();

        let pool = {
            let mut allocator = CONTINUOUS_MEMORY_POOL[numa_id].lock(&mut node);
            allocator.allocate(layout)?
        };

        let virt_addr = VirtAddr::new(pool.as_ptr() as usize);
        let phy_addr = paging::vm_to_phy(virt_addr).unwrap();
        let ptr = NonNull::new(pool.as_ptr() as *mut T)?;

        //log::info!("buf_phy_addr:{:?} virt_addr:{:?}", phy_addr, virt_addr);

        Some(Self {
            virt_addr,
            phy_addr,
            size,
            numa_id,
            ptr,
        })
    }

    pub fn leak(self) -> NonNull<T> {
        let ptr = self.ptr;
        core::mem::forget(self);
        ptr
    }

    pub unsafe fn from_raw_parts(
        ptr: *mut T,
        phy_addr: usize,
        size: usize,
        numa_id: usize,
    ) -> Option<Self> {
        assert!(numa_id < NUMA_NUM_MAX);

        let virt_addr = VirtAddr::new(ptr as usize);
        let phy_addr = PhyAddr::new(phy_addr);
        let ptr = NonNull::new(ptr)?;
        //let ptr = NonNull::new_unchecked(core::ptr::slice_from_raw_parts_mut(ptr, size));

        Some(Self {
            virt_addr,
            phy_addr,
            size,
            numa_id,
            ptr,
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
}

impl<T> AsMut<T> for DMAPool<T> {
    fn as_mut(&mut self) -> &mut T {
        unsafe { self.ptr.as_mut() }
    }
}

impl<T> AsRef<T> for DMAPool<T> {
    fn as_ref(&self) -> &T {
        unsafe { self.ptr.as_ref() }
    }
}

impl<T> Drop for DMAPool<T> {
    fn drop(&mut self) {
        let ptr = self.virt_addr.as_mut_ptr::<u8>();
        let mut node = MCSNode::new();
        let mut allocator = CONTINUOUS_MEMORY_POOL[self.numa_id].lock(&mut node);
        unsafe {
            allocator.deallocate(NonNull::new_unchecked(ptr), PAGESIZE);
        }
    }
}
