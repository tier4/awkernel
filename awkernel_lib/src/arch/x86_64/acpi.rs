use acpi::{AcpiHandler, AcpiTables};
use bootloader_api::BootInfo;
use core::ptr::NonNull;
use x86_64::VirtAddr;

pub mod dmar;
pub mod srat;

#[derive(Debug, Clone)]
pub struct AcpiMapper {
    phy_offset: VirtAddr,
}

impl AcpiHandler for AcpiMapper {
    unsafe fn map_physical_region<T>(
        &self,
        physical_address: usize,
        size: usize,
    ) -> acpi::PhysicalMapping<Self, T> {
        let addr = self.phy_offset + physical_address as u64;
        let virtual_start = NonNull::new(addr.as_mut_ptr()).unwrap();

        acpi::PhysicalMapping::new(physical_address, virtual_start, size, size, self.clone())
    }

    fn unmap_physical_region<T>(_region: &acpi::PhysicalMapping<Self, T>) {}
}

impl AcpiMapper {
    pub fn new(phy_offset: VirtAddr) -> Self {
        Self { phy_offset }
    }
}

pub fn create_acpi(boot_info: &BootInfo, phy_offset: u64) -> Option<AcpiTables<AcpiMapper>> {
    if let Some(rsdp_addr) = boot_info.rsdp_addr.as_ref() {
        match unsafe {
            acpi::AcpiTables::from_rsdp(
                AcpiMapper::new(VirtAddr::new(phy_offset)),
                *rsdp_addr as usize,
            )
        } {
            Ok(acpi) => Some(acpi),
            Err(err) => {
                log::error!("Failed to create AcpiTables: err = {:?}", err);
                None
            }
        }
    } else {
        None
    }
}
