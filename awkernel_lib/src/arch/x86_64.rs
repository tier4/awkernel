use self::{acpi::AcpiMapper, page_allocator::VecPageAllocator};
use ::acpi::AcpiTables;

pub mod acpi;
pub mod barrier;
pub mod cpu;
pub mod delay;
pub(super) mod dvfs;
pub mod fault;
pub(super) mod interrupt;
pub mod interrupt_remap;
pub mod kvm;
pub mod msr;
pub mod page_allocator;
pub mod page_table;
pub(super) mod paging;

pub struct X86;

impl super::Arch for X86 {}

pub fn init(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut page_table::PageTable,
    page_allocator: &mut VecPageAllocator,
) -> Result<(), &'static str> {
    // Initialize timer.
    delay::init(acpi, page_table, page_allocator)
}
