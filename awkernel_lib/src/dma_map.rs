//! DMA Mapping API
//!
//! This DMA mapping layer expects that transfers passed to it are already
//! limited to the device's Maximum Data Transfer Size (MDTS, stored in
//! DmaConstraints::maxsize). If a transfer exceeds maxsize, this layer will return
//! DmaError::SizeTooLarge rather than attempting to split it. For transfers
//! within MDTS but requiring too many segments (exceeding DmaConstraints::nsegments),
//! this layer WILL automatically use bounce buffers to consolidate segments.

use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    dma_pool::DMAPool,
    paging::{self, PAGESIZE},
};
use alloc::vec::Vec;

#[derive(Debug, Clone, Copy)]
pub struct DmaConstraints {
    pub boundary: u64,
    pub maxsegsz: usize,
    pub nsegments: usize,
    pub maxsize: usize,
    pub alignment: usize,
}

impl Default for DmaConstraints {
    fn default() -> Self {
        Self {
            boundary: 0,
            maxsegsz: PAGESIZE,
            nsegments: 1,
            maxsize: usize::MAX,
            alignment: 1,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct DmaSegment {
    pub ds_addr: PhyAddr,
    pub ds_len: usize,
}

pub struct DmaMap {
    tag: DmaConstraints,
    segments: Vec<DmaSegment>,
    /// Memory owned by this map (either bounce buffer or pre-allocated DMA pool)
    owned_memory: Option<DMAPool<u8>>,
    /// Original virtual address (for sync operations)
    orig_vaddr: Option<VirtAddr>,
    mapsize: usize,
    numa_id: usize,
}

#[derive(Debug, Clone, Copy)]
pub enum DmaSyncOp {
    PreRead,
    PostRead,
    PreWrite,
    PostWrite,
}

#[derive(Debug)]
pub enum DmaError {
    AddressTooHigh,
    SizeTooLarge,
    TooManySegments,
    BadAlignment,
    OutOfMemory,
    NotLoaded,
    InvalidAddress,
}

impl DmaMap {
    pub fn new(tag: DmaConstraints, numa_id: usize) -> Result<Self, DmaError> {
        Ok(Self {
            tag,
            segments: Vec::new(),
            owned_memory: None,
            orig_vaddr: None,
            mapsize: 0,
            numa_id,
        })
    }

    pub fn mapsize(&self) -> usize {
        self.mapsize
    }

    pub fn load(&mut self, vaddr: VirtAddr, size: usize) -> Result<(), DmaError> {
        if size > self.tag.maxsize {
            return Err(DmaError::SizeTooLarge);
        }

        if vaddr.as_usize() & (self.tag.alignment - 1) != 0 {
            return Err(DmaError::BadAlignment);
        }

        self.segments.clear();

        let mut lastaddr = PhyAddr::new(0);
        let bmask = if self.tag.boundary > 0 {
            !(self.tag.boundary - 1)
        } else {
            0 // No masking needed when boundary = 0
        };

        let mut buflen = size;
        let mut vaddr_current = vaddr.as_usize();
        let mut seg = 0usize;
        let mut first = true;

        while buflen > 0 {
            // Get the physical address for this segment
            let curaddr = match paging::vm_to_phy(VirtAddr::new(vaddr_current)) {
                Some(paddr) => paddr,
                None => {
                    return Err(DmaError::InvalidAddress);
                }
            };

            // TODO: Skipping check for PCIeDevice with 32bit addressing.

            // NOTE: OpenBSD has a check here for pre-allocated bounce
            // buffers in SEV guest mode. AWKernel skips this because:
            // 1. No SEV support yet
            // 2. We use dynamic bounce buffer allocation instead

            // Compute the segment size, and adjust counts.
            let mut sgsize = PAGESIZE - (vaddr_current & (PAGESIZE - 1));
            if buflen < sgsize {
                sgsize = buflen;
            }

            // Make sure we don't cross any boundaries
            if self.tag.boundary > 0 {
                let baddr = (curaddr.as_usize() as u64 + self.tag.boundary) & bmask;
                let max_size = baddr - curaddr.as_usize() as u64;
                if sgsize > max_size as usize {
                    sgsize = max_size as usize;
                }
            }

            // Insert chunk into a segment, coalescing with
            // previous segment if possible
            if first {
                self.segments.push(DmaSegment {
                    ds_addr: curaddr,
                    ds_len: sgsize,
                });
                first = false;
            } else {
                let can_coalesce = curaddr.as_usize() == lastaddr.as_usize()
                    && (self.segments[seg].ds_len + sgsize) <= self.tag.maxsegsz
                    && (self.tag.boundary == 0
                        || (self.segments[seg].ds_addr.as_usize() as u64 & bmask)
                            == (curaddr.as_usize() as u64 & bmask));

                if can_coalesce {
                    self.segments[seg].ds_len += sgsize;
                } else {
                    seg += 1;
                    if seg >= self.tag.nsegments {
                        return self.load_with_bounce(vaddr, size);
                    }
                    self.segments.push(DmaSegment {
                        ds_addr: curaddr,
                        ds_len: sgsize,
                    });
                }
            }

            lastaddr = PhyAddr::new(curaddr.as_usize() + sgsize);
            vaddr_current += sgsize;
            buflen -= sgsize;
        }

        self.orig_vaddr = Some(vaddr);
        self.mapsize = size;
        Ok(())
    }

    fn load_with_bounce(&mut self, vaddr: VirtAddr, size: usize) -> Result<(), DmaError> {
        let pages = size.div_ceil(PAGESIZE);
        log::warn!("Allocating bounce buffer: size={size} bytes, pages={pages}");

        let bounce = DMAPool::<u8>::new(self.numa_id, pages).ok_or(DmaError::OutOfMemory)?;

        let bounce_paddr = bounce.get_phy_addr();

        // NOTE: Data copying happens in sync(), not here!
        // This matches OpenBSD's design where load only sets up mappings

        self.segments.clear();
        self.segments.push(DmaSegment {
            ds_addr: bounce_paddr,
            ds_len: size,
        });

        self.owned_memory = Some(bounce);
        self.orig_vaddr = Some(vaddr);
        self.mapsize = size;

        Ok(())
    }

    pub fn unload(&mut self) {
        self.segments.clear();
        self.owned_memory = None;
        self.orig_vaddr = None;
        self.mapsize = 0;
    }

    pub fn sync(&self, offset: usize, len: usize, op: DmaSyncOp) -> Result<(), DmaError> {
        if self.segments.is_empty() {
            return Err(DmaError::NotLoaded);
        }

        // Validate offset and length
        if offset + len > self.mapsize {
            return Err(DmaError::SizeTooLarge);
        }

        if let (Some(ref bounce), Some(orig_vaddr)) = (&self.owned_memory, self.orig_vaddr) {
            match op {
                // READ: device -> memory
                DmaSyncOp::PostRead => unsafe {
                    core::ptr::copy_nonoverlapping(
                        bounce.get_virt_addr().as_ptr::<u8>().add(offset),
                        orig_vaddr.as_mut_ptr::<u8>().add(offset),
                        len,
                    );
                },
                // WRITE: memory -> device
                DmaSyncOp::PreWrite => unsafe {
                    core::ptr::copy_nonoverlapping(
                        orig_vaddr.as_ptr::<u8>().add(offset),
                        bounce.get_virt_addr().as_mut_ptr::<u8>().add(offset),
                        len,
                    );
                },
                // PREREAD and POSTWRITE are no-ops.
                _ => (),
            }
        }

        // TODO: Implement cache operations for non-coherent devices.
        // Currently only memory barriers are implemented, which is insufficient
        // for non-coherent devices but works for cache-coherent systems.
        //
        // Note: The barrier and cache invalidation are not atomic, which could
        // theoretically allow speculative loads between them. This is mitigated
        // in practice by running in interrupt context and exclusive buffer access.

        #[cfg(any(target_arch = "riscv32", target_arch = "riscv64"))]
        if matches!(op, DmaSyncOp::PostRead) {
            crate::barrier::membar_sync();
            // TODO: cpu_dcache_inv_range(paddr, len)
        }

        #[cfg(target_arch = "aarch64")]
        if matches!(op, DmaSyncOp::PostRead) {
            crate::barrier::membar_sync();
            // TODO: cpu_dcache_inv_range(paddr, len)
        }

        Ok(())
    }

    pub fn get_segments(&self) -> &[DmaSegment] {
        &self.segments
    }

    pub fn is_bounced(&self) -> bool {
        self.owned_memory.is_some()
    }
}

impl DmaMap {
    pub fn from_dma_pool<T>(pool: DMAPool<T>, tag: DmaConstraints) -> Result<Self, DmaError> {
        let paddr = pool.get_phy_addr();
        let size = pool.get_size();
        let vaddr = pool.get_virt_addr();
        let numa_id = pool.get_numa_id();

        if size > tag.maxsize {
            return Err(DmaError::SizeTooLarge);
        }

        Ok(Self {
            tag,
            segments: alloc::vec![DmaSegment {
                ds_addr: paddr,
                ds_len: size,
            }],
            owned_memory: Some(pool.into_bytes()),
            orig_vaddr: Some(vaddr),
            mapsize: size,
            numa_id,
        })
    }
}
