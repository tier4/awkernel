//! SoC Integrated Address Translation Cache Reporting Structure

use core::{marker::PhantomData, mem};

use super::{device_scope::DeviceScopeIter, EntryHeader};

/// SoC Integrated Address Translation Cache Reporting Structure
#[repr(C, packed)]
#[derive(Debug, Clone)]
pub struct DmarSatc {
    pub header: EntryHeader,
    pub flags: u8,
    reserved: u8,
    pub segment_number: u16, // The PCI Segment associated with this unit.
}

impl DmarSatc {
    pub fn device_scopes(&self) -> DeviceScopeIter {
        DeviceScopeIter {
            pointer: unsafe {
                (self as *const DmarSatc as *const u8).add(mem::size_of::<DmarSatc>())
            },
            remaining_length: (self.header.length as u8)
                .saturating_sub(mem::size_of::<DmarSatc>() as u8),
            _phantom: PhantomData,
        }
    }
}
