use self::{acpi::AcpiMapper, page_allocator::PageAllocator};
use ::acpi::AcpiTables;
use x86_64::structures::paging::{OffsetPageTable, PhysFrame};

pub mod acpi;
pub mod context;
pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod interrupt;
pub mod mmu;
pub mod page_allocator;

pub fn init<T>(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator<T>,
) where
    T: Iterator<Item = PhysFrame> + Send,
{
    // Initialize timer.
    acpi::init(acpi);
    delay::init(acpi, page_table, page_allocator);
}
