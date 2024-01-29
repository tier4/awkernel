use self::{acpi::AcpiMapper, page_allocator::VecPageAllocator};
use ::acpi::AcpiTables;

pub mod acpi;
pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod interrupt;
#[allow(dead_code)] // TODO: remove this
#[allow(unused_variables)] // TODO: remove this
pub mod interrupt_remap;
pub mod page_allocator;
pub mod page_table;
pub(super) mod paging;

pub struct X86;

impl super::Arch for X86 {}

pub fn init(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut page_table::PageTable,
    page_allocator: &mut VecPageAllocator,
) {
    // Initialize timer.
    delay::init(acpi, page_table, page_allocator);
}
