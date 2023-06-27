use crate::config::{STACK_SIZE, STACK_START};
use acpi::AcpiTables;
use awkernel_lib::{
    arch::x86_64::{acpi::AcpiMapper, page_allocator::PageAllocator},
    heap::InitErr,
    memory::PAGESIZE,
};
use x86_64::{
    structures::paging::{
        FrameAllocator, Mapper, OffsetPageTable, Page, PageTableFlags, PhysFrame, Size4KiB,
    },
    VirtAddr,
};

pub(super) fn map_stack<T>(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator<T>,
) -> Result<(), InitErr>
where
    T: Iterator<Item = PhysFrame> + Send,
{
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

    let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;
    let mut stack_start = STACK_START;
    for _ in 0..num_cpu {
        let page_range = {
            let stack_start = VirtAddr::new(stack_start + PAGESIZE as u64);
            let stack_end = stack_start + STACK_SIZE - PAGESIZE as u64 - 1u64;
            let stack_start_page: Page<Size4KiB> = Page::containing_address(stack_start);
            let stack_end_page: Page<_> = Page::containing_address(stack_end);
            Page::range_inclusive(stack_start_page, stack_end_page)
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

        stack_start += STACK_SIZE;
    }

    Ok(())
}
