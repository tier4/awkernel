//! ACPI Name-space Device Declaration Structure

use acpi::madt::EntryHeader;

/// ACPI Name-space Device Declaration Structure
#[repr(C, packed)]
#[derive(Debug, Clone)]
pub struct DmarAndd {
    pub header: EntryHeader,
    reserved: u32,
    pub acpi_device_number: u8,
}

impl DmarAndd {
    pub fn acpi_object_name(&self) -> &[u8] {
        unsafe {
            core::slice::from_raw_parts(
                (self as *const DmarAndd as *const u8).add(core::mem::size_of::<DmarAndd>()),
                (self.header.length as usize).saturating_sub(core::mem::size_of::<DmarAndd>()),
            )
        }
    }
}
