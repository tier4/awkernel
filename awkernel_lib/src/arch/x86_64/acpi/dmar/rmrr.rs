//! Reserved Memory Region Reporting Structure

use core::{marker::PhantomData, mem};

use super::{device_scope::DeviceScopeIter, EntryHeader};

/// Reserved Memory Region Reporting Structure
#[repr(C, packed)]
#[derive(Debug, Clone)]
pub struct DmarRmrr {
    pub header: EntryHeader,
    reserved: u16,
    pub size: u8,
    pub segment_number: u16, // The PCI Segment associated with this unit.
    pub reserved_memory_region_base_address: u64,
    pub reserved_memory_region_limit_address: u64,
}

impl DmarRmrr {
    pub fn device_scopes(&self) -> DeviceScopeIter<'_> {
        DeviceScopeIter {
            pointer: unsafe {
                (self as *const DmarRmrr as *const u8).add(mem::size_of::<DmarRmrr>())
            },
            remaining_length: (self.header.length as u8)
                .saturating_sub(mem::size_of::<DmarRmrr>() as u8),
            _phantom: PhantomData,
        }
    }
}
