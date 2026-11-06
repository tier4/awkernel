#[cfg(not(feature = "std"))]
use self::{acpi::AcpiMapper, page_allocator::VecPageAllocator};
#[cfg(not(feature = "std"))]
use ::acpi::AcpiTables;

#[cfg(not(feature = "std"))]
pub mod acpi;
pub mod barrier;
pub mod cpu;
pub mod cpuid;
#[cfg(not(feature = "std"))]
pub mod delay;
#[cfg(not(feature = "std"))]
pub mod dvfs;
pub mod fault;
pub mod hwp;
pub mod identity_map;
#[cfg(not(feature = "std"))]
pub(super) mod interrupt;
#[cfg(not(feature = "std"))]
pub mod interrupt_remap;
pub mod kvm;
pub mod msr;
#[cfg(not(feature = "std"))]
pub mod page_allocator;
#[cfg(not(feature = "std"))]
pub mod page_table;
#[cfg(not(feature = "std"))]
pub(super) mod paging;
#[cfg(not(feature = "std"))]
pub mod power;
pub mod power_profile;

pub struct X86;

#[cfg(not(feature = "std"))]
impl super::Arch for X86 {}

#[cfg(not(feature = "std"))]
pub fn init(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut page_table::PageTable,
    page_allocator: &mut VecPageAllocator,
) -> Result<(), &'static str> {
    // Initialize timer before AML-driven power initialization can invoke
    // delay-backed Stall/Sleep handlers.
    delay::init(acpi, page_table, page_allocator)?;

    if let Err(err) = power::init(acpi) {
        log::warn!("Failed to initialize x86 power control. {err}");
    }

    Ok(())
}
