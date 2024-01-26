//! Root Port ATS Capability Reporting Structure

use core::{marker::PhantomData, mem};

use super::{device_scope::DeviceScopeIter, EntryHeader};

/// Root Port ATS Capability Reporting Structure
#[repr(C, packed)]
#[derive(Debug, Clone)]
pub struct DmarAtsr {
    pub header: EntryHeader,
    pub flags: u8,
    reserved: u8,
    pub segment_number: u16, // The PCI Segment associated with this unit.
}

impl DmarAtsr {
    pub fn device_scopes(&self) -> DeviceScopeIter {
        DeviceScopeIter {
            pointer: unsafe {
                (self as *const DmarAtsr as *const u8).add(mem::size_of::<DmarAtsr>())
            },
            remaining_length: (self.header.length as u8)
                .saturating_sub(mem::size_of::<DmarAtsr>() as u8),
            _phantom: PhantomData,
        }
    }
}
