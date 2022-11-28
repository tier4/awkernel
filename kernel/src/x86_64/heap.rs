use bootloader::{boot_info::MemoryRegionKind, BootInfo};

use x86_64::{
    registers::control::Cr3,
    structures::paging::{
        FrameAllocator, Mapper, OffsetPageTable, Page, PageTable, PageTableFlags, PhysFrame,
        Size4KiB,
    },
    PhysAddr, VirtAddr,
};

use crate::{
    config::{HEAP_SIZE, HEAP_START},
    heap::{HeapInit, InitErr},
};

pub struct MapHeapPage;

impl HeapInit for MapHeapPage {
    fn init(boot_info: &BootInfo) -> Result<(), InitErr> {
        let phys_mem_offset = VirtAddr::new(
            *boot_info
                .physical_memory_offset
                .as_ref()
                .ok_or(InitErr::InvalidPhysicalMemoryOffset)?,
        );

        let mut page_table = unsafe { get_page_table(phys_mem_offset) };

        let page_range = {
            let heap_start = VirtAddr::new(HEAP_START);
            let heap_end = heap_start + HEAP_SIZE - 1u64;
            let heap_start_page: Page<Size4KiB> = Page::containing_address(heap_start);
            let heap_end_page: Page<_> = Page::containing_address(heap_end);
            Page::range_inclusive(heap_start_page, heap_end_page)
        };

        let mut frames = boot_info
            .memory_regions
            .iter()
            .filter(|m| m.kind == MemoryRegionKind::Usable)
            .flat_map(|m| (m.start..m.end).step_by(4096))
            .map(|addr| PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(addr)));
        let mut frame_allocator = PageAllocator::new(&mut frames);

        for page in page_range {
            let frame = frame_allocator
                .allocate_frame()
                .ok_or(InitErr::FailedToAllocateFrame)?;

            let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE;

            unsafe {
                page_table
                    .map_to(page, frame, flags, &mut frame_allocator)
                    .or(Err(InitErr::FailedToMapPage))?
                    .flush()
            };
        }

        Ok(())
    }
}

unsafe fn get_page_table(physical_memory_offset: VirtAddr) -> OffsetPageTable<'static> {
    let level_4_table = active_level_4_table(physical_memory_offset);
    OffsetPageTable::new(level_4_table, physical_memory_offset)
}

unsafe fn active_level_4_table(physical_memory_offset: VirtAddr) -> &'static mut PageTable {
    let (level_4_table_frame, _) = Cr3::read();

    let phys = level_4_table_frame.start_address();
    let virt = physical_memory_offset + phys.as_u64();
    let ptr = virt.as_mut_ptr() as *mut PageTable;

    &mut *ptr
}

struct PageAllocator<'a> {
    frames: &'a mut dyn Iterator<Item = PhysFrame>,
}

impl<'a> PageAllocator<'a> {
    fn new(frames: &'a mut dyn Iterator<Item = PhysFrame>) -> Self {
        PageAllocator { frames }
    }
}

unsafe impl<'a> FrameAllocator<Size4KiB> for PageAllocator<'a> {
    fn allocate_frame(&mut self) -> Option<PhysFrame<Size4KiB>> {
        self.frames.next()
    }
}
