use crate::config::{STACK_SIZE, STACK_START};
use acpi::AcpiTables;
use alloc::collections::BTreeMap;
use awkernel_lib::{
    arch::x86_64::{acpi::AcpiMapper, page_allocator::VecPageAllocator},
    heap::InitErr,
    paging::PAGESIZE,
};
use x86_64::{
    structures::paging::{FrameAllocator, Mapper, OffsetPageTable, Page, PageTableFlags, Size4KiB},
    VirtAddr,
};

pub(super) fn map_stack(
    acpi: &AcpiTables<AcpiMapper>,
    cpu_to_numa: &BTreeMap<u32, u32>,
    page_table: &mut OffsetPageTable<'static>,
    page_allocators: &mut BTreeMap<u32, VecPageAllocator>,
) -> Result<(), InitErr> {
    let num_cpu = if let Ok(platform_info) = acpi.platform_info() {
        if let Some(processor_info) = platform_info.processor_info {
            processor_info.application_processors.len()
        } else {
            log::error!("Failed processor_info().");
            return Err(InitErr::InvalidACPI);
        }
    } else {
        log::error!("Failed platform_info().");
        return Err(InitErr::InvalidACPI);
    };

    log::info!("Found {} cores.", num_cpu + 1);

    let flags = PageTableFlags::PRESENT
        | PageTableFlags::WRITABLE
        | PageTableFlags::NO_EXECUTE
        | PageTableFlags::GLOBAL;
    for (i, numa_id) in cpu_to_numa.iter() {
        let stack_start = STACK_START + STACK_SIZE * (*i as usize) + PAGESIZE;
        let stack_end = STACK_START + STACK_SIZE * ((i + 1) as usize) - PAGESIZE;

        let page_range = {
            let stack_start_page: Page<Size4KiB> =
                Page::containing_address(VirtAddr::new(stack_start as u64));
            let stack_end_page: Page<_> = Page::containing_address(VirtAddr::new(stack_end as u64));
            Page::range_inclusive(stack_start_page, stack_end_page)
        };

        let Some(page_allocator) = page_allocators.get_mut(numa_id) else {
            continue;
        };

        for page in page_range {
            let frame = page_allocator
                .allocate_frame()
                .ok_or(InitErr::FailedToAllocateFrame)?;

            unsafe {
                page_table
                    .map_to(page, frame, flags, page_allocator)
                    .or(Err(InitErr::FailedToMapPage))?
                    .flush()
            };
        }
    }

    Ok(())
}
