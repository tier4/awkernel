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
pub mod power;

pub struct X86;

impl super::Arch for X86 {}

pub fn init(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut page_table::PageTable,
    page_allocator: &mut VecPageAllocator,
) -> Result<(), &'static str> {
    // Initialize timer before AML-driven power initialization can invoke
    // delay-backed Stall/Sleep handlers.
    // HPET may be absent on some hardware; treat as non-fatal so boot continues.
    if let Err(e) = delay::init(acpi, page_table, page_allocator) {
        log::warn!("Timer init failed ({e}); delay functions will be inaccurate.");
    }

    if let Err(err) = power::init(acpi) {
        log::warn!("Failed to initialize x86 power control. {err}");
    }

    Ok(())
}
