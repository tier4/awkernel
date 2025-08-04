//! DMA Mapping API
//! 
//! Based on OpenBSD's bus_dma(9) framework
//! References:
//! - sys/arch/amd64/include/bus.h
//! - sys/arch/amd64/amd64/bus_dma.c

use alloc::vec::Vec;
use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    dma_pool::DMAPool,
    paging::{self, PAGESIZE},
};

/// DMA constraints for a device
/// Corresponds to OpenBSD's bus_dma_tag
#[derive(Debug, Clone, Copy)]
pub struct DmaTag {
    /// Maximum DMA address the device can access
    pub boundary: u64,
    /// Maximum size of a single DMA segment
    pub maxsegsz: usize,
    /// Maximum number of segments in a transfer
    pub nsegments: usize,
    /// Maximum total size of a DMA transfer
    pub maxsize: usize,
    /// Alignment requirements (must be power of 2)
    pub alignment: usize,
}

impl DmaTag {
    /// Create a DMA tag for 32-bit devices
    /// Corresponds to OpenBSD's bus_dma_tag_create() for 32-bit devices
    pub fn new_32bit() -> Self {
        Self {
            boundary: 0xFFFF_FFFF,
            maxsegsz: 0xFFFF_FFFF,
            nsegments: 1,
            maxsize: 0xFFFF_FFFF,
            alignment: 1,
        }
    }

    /// Create a DMA tag for 64-bit devices
    pub fn new_64bit() -> Self {
        Self {
            boundary: u64::MAX,
            maxsegsz: usize::MAX,
            nsegments: 1,
            maxsize: usize::MAX,
            alignment: 1,
        }
    }
}

/// DMA segment descriptor
/// Corresponds to OpenBSD's bus_dma_segment
#[derive(Debug, Clone, Copy)]
pub struct DmaSegment {
    pub ds_addr: PhyAddr,
    pub ds_len: usize,
}

/// DMA map structure
/// Corresponds to OpenBSD's struct bus_dmamap
pub struct DmaMap {
    /// DMA constraints
    tag: DmaTag,
    /// Memory segments for this mapping
    segments: Vec<DmaSegment>,
    /// Bounce buffer if needed
    bounce_buffer: Option<DMAPool<u8>>,
    /// Original virtual address (for sync operations)
    orig_vaddr: Option<VirtAddr>,
    /// Size of the mapped region
    mapsize: usize,
    /// NUMA node ID
    numa_id: usize,
}

/// DMA synchronization operations
/// Corresponds to OpenBSD's BUS_DMASYNC_* flags
#[derive(Debug, Clone, Copy)]
pub enum DmaSyncOp {
    /// Sync before DMA read from device
    /// OpenBSD: BUS_DMASYNC_PREREAD
    PreRead,
    /// Sync after DMA read from device
    /// OpenBSD: BUS_DMASYNC_POSTREAD
    PostRead,
    /// Sync before DMA write to device
    /// OpenBSD: BUS_DMASYNC_PREWRITE
    PreWrite,
    /// Sync after DMA write to device
    /// OpenBSD: BUS_DMASYNC_POSTWRITE
    PostWrite,
}

/// Errors that can occur during DMA operations
#[derive(Debug)]
pub enum DmaError {
    /// Address exceeds device's DMA boundary
    AddressTooHigh,
    /// Size exceeds maximum transfer size
    SizeTooLarge,
    /// Too many segments required
    TooManySegments,
    /// Alignment requirements not met
    BadAlignment,
    /// Out of memory for bounce buffer
    OutOfMemory,
    /// Map not loaded
    NotLoaded,
}

impl DmaMap {
    /// Create a new DMA map
    /// Corresponds to OpenBSD's bus_dmamap_create()
    pub fn new(tag: DmaTag, numa_id: usize) -> Result<Self, DmaError> {
        Ok(Self {
            tag,
            segments: Vec::new(),
            bounce_buffer: None,
            orig_vaddr: None,
            mapsize: 0,
            numa_id,
        })
    }

    /// Load a buffer into the DMA map
    /// Corresponds to OpenBSD's bus_dmamap_load()
    pub fn load(&mut self, vaddr: VirtAddr, size: usize) -> Result<(), DmaError> {
        if size > self.tag.maxsize {
            return Err(DmaError::SizeTooLarge);
        }

        // Check alignment
        if vaddr.as_usize() & (self.tag.alignment - 1) != 0 {
            return Err(DmaError::BadAlignment);
        }

        // Clear existing segments
        self.segments.clear();
        
        // Build scatter-gather list by checking each page
        let mut offset = 0;
        
        while offset < size {
            // Calculate size within current page
            let page_offset = (vaddr.as_usize() + offset) % PAGESIZE;
            let chunk_size = core::cmp::min(PAGESIZE - page_offset, size - offset);
            
            // Get physical address for this chunk
            let current_vaddr = VirtAddr::new(vaddr.as_usize() + offset);
            let Some(paddr) = paging::vm_to_phy(current_vaddr) else {
                // Cannot get physical address, need bounce buffer
                return self.load_with_bounce(vaddr, size);
            };
            
            // Check if address exceeds device boundary
            if paddr.as_usize() as u64 > self.tag.boundary {
                return self.load_with_bounce(vaddr, size);
            }
            
            // Check if we can coalesce with previous segment
            if let Some(last_seg) = self.segments.last_mut() {
                let expected_paddr = PhyAddr::new(last_seg.ds_addr.as_usize() + last_seg.ds_len);
                if paddr == expected_paddr && last_seg.ds_len + chunk_size <= self.tag.maxsegsz {
                    // Extend the last segment
                    last_seg.ds_len += chunk_size;
                } else {
                    // Check if adding new segment would exceed nsegments
                    if self.segments.len() >= self.tag.nsegments {
                        return self.load_with_bounce(vaddr, size);
                    }
                    
                    // Check segment size constraint
                    if chunk_size > self.tag.maxsegsz {
                        return self.load_with_bounce(vaddr, size);
                    }
                    
                    // Add new segment
                    self.segments.push(DmaSegment {
                        ds_addr: paddr,
                        ds_len: chunk_size,
                    });
                }
            } else {
                // First segment
                if chunk_size > self.tag.maxsegsz {
                    return self.load_with_bounce(vaddr, size);
                }
                
                self.segments.push(DmaSegment {
                    ds_addr: paddr,
                    ds_len: chunk_size,
                });
            }
            
            // Check boundary crossing within segment
            if let Some(last_seg) = self.segments.last() {
                let seg_start = last_seg.ds_addr.as_usize() as u64;
                let seg_end = seg_start + last_seg.ds_len as u64 - 1;
                
                // Check if segment crosses a boundary
                if self.tag.boundary != 0 && self.tag.boundary != u64::MAX {
                    let start_boundary = seg_start / (self.tag.boundary + 1);
                    let end_boundary = seg_end / (self.tag.boundary + 1);
                    if start_boundary != end_boundary {
                        // Segment crosses boundary, need bounce buffer
                        return self.load_with_bounce(vaddr, size);
                    }
                }
            }
            
            offset += chunk_size;
        }
        
        // Successfully mapped
        self.orig_vaddr = Some(vaddr);
        self.mapsize = size;
        Ok(())
    }

    /// Load buffer using bounce buffer
    /// Corresponds to OpenBSD's bounce buffer allocation in _bus_dmamap_load_buffer()
    fn load_with_bounce(&mut self, vaddr: VirtAddr, size: usize) -> Result<(), DmaError> {
        // Allocate bounce buffer
        let pages = (size + PAGESIZE - 1) / PAGESIZE;
        let bounce = DMAPool::<u8>::new(self.numa_id, pages)
            .ok_or(DmaError::OutOfMemory)?;

        let bounce_paddr = bounce.get_phy_addr();
        
        // Check if bounce buffer meets requirements
        if bounce_paddr.as_usize() as u64 > self.tag.boundary {
            return Err(DmaError::AddressTooHigh);
        }

        // NOTE: Data copying happens in sync(), not here!
        // This matches OpenBSD's design where load only sets up mappings

        self.segments.clear();
        self.segments.push(DmaSegment {
            ds_addr: bounce_paddr,
            ds_len: size,
        });
        
        self.bounce_buffer = Some(bounce);
        self.orig_vaddr = Some(vaddr);
        self.mapsize = size;

        Ok(())
    }

    /// Unload the DMA map
    /// Corresponds to OpenBSD's bus_dmamap_unload()
    pub fn unload(&mut self) {
        self.segments.clear();
        self.bounce_buffer = None;
        self.orig_vaddr = None;
        self.mapsize = 0;
    }

    /// Synchronize DMA map
    /// Corresponds to OpenBSD's bus_dmamap_sync()
    pub fn sync(&self, offset: usize, len: usize, op: DmaSyncOp) -> Result<(), DmaError> {
        if self.segments.is_empty() {
            return Err(DmaError::NotLoaded);
        }

        // Validate offset and length
        if offset + len > self.mapsize {
            return Err(DmaError::SizeTooLarge);
        }

        // If using bounce buffer, handle data copying
        if let (Some(ref bounce), Some(orig_vaddr)) = (&self.bounce_buffer, self.orig_vaddr) {
            match op {
                DmaSyncOp::PreRead => {
                    // Nothing to do - device will write to bounce buffer
                }
                DmaSyncOp::PostRead => {
                    // Copy from bounce buffer back to original
                    unsafe {
                        core::ptr::copy_nonoverlapping(
                            bounce.get_virt_addr().as_ptr::<u8>().add(offset),
                            orig_vaddr.as_mut_ptr::<u8>().add(offset),
                            len,
                        );
                    }
                }
                DmaSyncOp::PreWrite => {
                    // Copy from original to bounce buffer
                    // This is now the ONLY place where data is copied for writes
                    unsafe {
                        core::ptr::copy_nonoverlapping(
                            orig_vaddr.as_ptr::<u8>().add(offset),
                            bounce.get_virt_addr().as_mut_ptr::<u8>().add(offset),
                            len,
                        );
                    }
                }
                DmaSyncOp::PostWrite => {
                    // Nothing to do - data already written to device
                }
            }
        }

        // Memory barrier to ensure coherency
        // Corresponds to OpenBSD's bus_dmamap_sync() memory barriers
        #[cfg(target_arch = "x86_64")]
        unsafe {
            core::arch::x86_64::_mm_mfence();
        }
        #[cfg(target_arch = "aarch64")]
        unsafe {
            core::arch::asm!("dmb sy");
        }

        Ok(())
    }

    /// Get the first DMA segment
    /// Useful for simple single-segment transfers
    pub fn get_segment(&self) -> Option<&DmaSegment> {
        self.segments.first()
    }

    /// Get all DMA segments
    pub fn get_segments(&self) -> &[DmaSegment] {
        &self.segments
    }

    /// Check if using bounce buffer
    pub fn is_bounced(&self) -> bool {
        self.bounce_buffer.is_some()
    }
}

/// Integration with existing DMAPool
impl DmaMap {
    /// Create a map from existing DMAPool
    /// This provides compatibility with current AWKernel code
    pub fn from_dma_pool<T>(pool: &DMAPool<T>, tag: DmaTag) -> Result<Self, DmaError> {
        let paddr = pool.get_phy_addr();
        let size = pool.get_size();
        
        if paddr.as_usize() as u64 > tag.boundary {
            return Err(DmaError::AddressTooHigh);
        }
        
        if size > tag.maxsize {
            return Err(DmaError::SizeTooLarge);
        }

        Ok(Self {
            tag,
            segments: alloc::vec![DmaSegment {
                ds_addr: paddr,
                ds_len: size,
            }],
            bounce_buffer: None,
            orig_vaddr: Some(pool.get_virt_addr()),
            mapsize: size,
            numa_id: pool.get_numa_id(),
        })
    }
}