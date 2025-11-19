//! DMA Remapping Hardware Unit Definition Structure

use core::{marker::PhantomData, mem};

use super::{device_scope::DeviceScopeIter, EntryHeader};

/// DMA Remapping Hardware Unit Definition Structure
#[repr(C, packed)]
#[derive(Debug, Clone)]
pub struct DmarDrhd {
    pub header: EntryHeader,
    pub flags: u8,
    pub size: u8,
    pub segment_number: u16, // The PCI Segment associated with this unit.
    pub register_base_address: u64,
}

impl DmarDrhd {
    pub fn device_scopes(&self) -> DeviceScopeIter<'_> {
        DeviceScopeIter {
            pointer: unsafe {
                (self as *const DmarDrhd as *const u8).add(mem::size_of::<DmarDrhd>())
            },
            remaining_length: (self.header.length as u8)
                .saturating_sub(mem::size_of::<DmarDrhd>() as u8),
            _phantom: PhantomData,
        }
    }
}
