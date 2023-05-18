use crate::arch::x86_64::{mmu::map_to, AcpiMapper, AcpiTables, PageAllocator};
use acpi::{mcfg::McfgEntry, PciConfigRegions};
use core::ptr::read_volatile;

use x86_64::structures::paging::{OffsetPageTable, PageTableFlags, PhysFrame};

pub fn init<T>(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator<T>,
    page_size : usize,
) where
    T: Iterator<Item = PhysFrame> + Send,
{
    let pcie_info = PciConfigRegions::new(acpi).unwrap();
    for segment in pcie_info.list_all() {
        log::info!("{:?}", segment);
        let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;
        let mut pa_start = segment.base_address() as usize;
        let pa_end =  pa_start + (256 * 1024 * 1024);
        while pa_start  <  pa_end {
            unsafe {
                map_to(pa_start, pa_start, flags, page_table, page_allocator);
            }
            pa_start += page_size;
        }
        
        search_devices(&segment);
    }
}

fn search_devices(segment: &McfgEntry) {
    for bus in segment.buses() {
        for dev in 0..(1 << 5) {
            for func in 0..(1 << 3) {
                let offset = (bus as u64) << 20 | dev << 15| func << 12;
                let addr = segment.base_address() + offset;
                let id = unsafe { read_volatile(addr as *const u32) };
                if id != !0 {
                    log::info!("found device with id {:#x} at {:#x}", u32::to_be(id), addr);
                }
            }
        }
    }
}


