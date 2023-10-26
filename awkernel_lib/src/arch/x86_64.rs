use self::{acpi::AcpiMapper, page_allocator::PageAllocator};
use ::acpi::AcpiTables;
use x86_64::structures::paging::PhysFrame;

pub mod acpi;
pub(super) mod cpu;
pub(super) mod delay;
pub(super) mod interrupt;
pub(super) mod memory;
pub mod page_allocator;
pub mod page_table;

pub struct X86;

impl super::Arch for X86 {}

pub fn init<T>(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut page_table::PageTable,
    page_allocator: &mut PageAllocator<T>,
) where
    T: Iterator<Item = PhysFrame> + Send,
{
    // Initialize timer.
    acpi::init(acpi);
    delay::init(acpi, page_table, page_allocator);
}
