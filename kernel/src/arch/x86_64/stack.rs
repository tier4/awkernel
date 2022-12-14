use super::{acpi::AcpiMapper, page_allocator::PageAllocator};
use crate::{
    config::{PAGE_SIZE, STACK_SIZE, STACK_START},
    heap::InitErr,
};
use acpi::AcpiTables;
use x86_64::{
    structures::paging::{FrameAllocator, Mapper, OffsetPageTable, Page, PageTableFlags, Size4KiB},
    VirtAddr,
};

pub(super) fn map_stack(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator,
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

    log::debug!("Map stack: num_cpu = {num_cpu}");

    let mut stack_start = STACK_START;
    for _ in 0..num_cpu {
        let page_range = {
            let stack_start = VirtAddr::new(stack_start + PAGE_SIZE);
            let stack_end = stack_start + STACK_SIZE - PAGE_SIZE - 1u64;
            let stack_start_page: Page<Size4KiB> = Page::containing_address(stack_start);
            let stack_end_page: Page<_> = Page::containing_address(stack_end);
            Page::range_inclusive(stack_start_page, stack_end_page)
        };

        for page in page_range {
            let frame = page_allocator
                .allocate_frame()
                .ok_or(InitErr::FailedToAllocateFrame)?;

            let flags =
                PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;

            unsafe {
                page_table
                    .map_to(page, frame, flags, page_allocator)
                    .or(Err(InitErr::FailedToMapPage))?
                    .flush()
            };
        }

        stack_start += STACK_SIZE;

        log::debug!("Map stack memory for non-primary CPUs: {:?}", page_range);
    }

    Ok(())
}
