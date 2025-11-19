//! SoC Integrated Device Property Reporting Structure

use core::{marker::PhantomData, mem};

use super::{device_scope::DeviceScopeIter, EntryHeader};

/// SoC Integrated Device Property Reporting Structure
#[repr(C, packed)]
#[derive(Debug, Clone)]
pub struct DmarSidp {
    pub header: EntryHeader,
    reserved: u16,
    pub segment_number: u16, // The PCI Segment associated with this unit.
}

impl DmarSidp {
    pub fn device_scopes(&self) -> DeviceScopeIter<'_> {
        DeviceScopeIter {
            pointer: unsafe {
                (self as *const DmarSidp as *const u8).add(mem::size_of::<DmarSidp>())
            },
            remaining_length: (self.header.length as u8)
                .saturating_sub(mem::size_of::<DmarSidp>() as u8),
            _phantom: PhantomData,
        }
    }
}
