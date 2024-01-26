//! Remapping Hardware Static Affinity Structure

use acpi::madt::EntryHeader;

/// Remapping Hardware Static Affinity Structure
#[repr(C, packed)]
#[derive(Debug, Clone)]
pub struct DmarRhsa {
    pub header: EntryHeader,
    reserved: u32,
    pub register_base_address: u64,
    pub proximity_domain: u32,
}
