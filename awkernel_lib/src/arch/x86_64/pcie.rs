use crate::arch::x86_64::{AcpiMapper, AcpiTables, OffsetPageTable, PageAllocator};
use acpi::PciConfigRegions;

pub fn init(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator,
) {
    let pcie_info = PciConfigRegions::new(acpi).unwrap();
    for device in pcie_info.list_all() {
        log::info!("{:?}", device);
    }
}
