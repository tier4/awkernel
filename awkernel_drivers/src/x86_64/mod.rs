pub mod pcie;

use acpi::AcpiTables;
use awkernel_lib::arch::x86_64::acpi::AcpiMapper;

use awkernel_lib::arch::x86_64::page_allocator::PageAllocator;
use x86_64::structures::paging::{OffsetPageTable, PhysFrame};

pub fn init<T>(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator<T>,
    page_size: u64,
) where
    T: Iterator<Item = PhysFrame> + Send,
{
    // PCI Express
    pcie::init(acpi, page_table, page_allocator, page_size)
}
