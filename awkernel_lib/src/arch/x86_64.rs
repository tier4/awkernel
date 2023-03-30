use self::{acpi::AcpiMapper, page_allocator::PageAllocator};
use ::acpi::AcpiTables;
use x86_64::structures::paging::OffsetPageTable;

pub mod acpi;
pub(super) mod cpu;
pub(crate) mod delay;
pub mod mmu;
pub mod page_allocator;

pub fn init(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator,
) {
    // Initialize timer.
    acpi::init(acpi);
    delay::init(acpi, page_table, page_allocator);
}
