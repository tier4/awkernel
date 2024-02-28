use crate::{
    addr::Addr,
    paging::PAGESIZE,
    sync::mutex::{MCSNode, Mutex},
};
use alloc::vec::Vec;
use bootloader_api::{info::MemoryRegion, BootInfo};
use core::{
    alloc::Layout,
    sync::atomic::{AtomicUsize, Ordering},
};
use x86_64::{
    registers::control::Cr3,
    structures::paging::{FrameAllocator, OffsetPageTable, PageTable, PhysFrame, Size4KiB},
    PhysAddr, VirtAddr,
};

static PHYSICAL_MEORY_OFFSET: AtomicUsize = AtomicUsize::new(0);

/// # Safety
///
/// Must be initialized at once when booting.
pub unsafe fn init(boot_info: &BootInfo) {
    let addr = boot_info.physical_memory_offset.as_ref().unwrap();
    PHYSICAL_MEORY_OFFSET.store((*addr) as usize, Ordering::Relaxed);
}

fn physical_memory_offset() -> usize {
    PHYSICAL_MEORY_OFFSET.load(Ordering::Relaxed)
}

pub struct PageAllocator<'a, T>
where
    T: Iterator<Item = PhysFrame> + Send,
{
    frames: Mutex<&'a mut T>,
}

impl<'a, T> PageAllocator<'a, T>
where
    T: Iterator<Item = PhysFrame> + Send,
{
    pub fn new(frames: &'a mut T) -> Self {
        PageAllocator {
            frames: Mutex::new(frames),
        }
    }
}

unsafe impl<'a, T> FrameAllocator<Size4KiB> for PageAllocator<'a, T>
where
    T: Iterator<Item = PhysFrame> + Send,
{
    fn allocate_frame(&mut self) -> Option<PhysFrame<Size4KiB>> {
        let mut node = MCSNode::new();
        let mut guard = self.frames.lock(&mut node);
        guard.next()
    }
}

pub struct VecPageAllocator {
    range: Vec<MemoryRegion>,
    index: usize,
    addr: usize,
}

unsafe impl FrameAllocator<Size4KiB> for VecPageAllocator {
    fn allocate_frame(&mut self) -> Option<PhysFrame<Size4KiB>> {
        loop {
            let range = self.range.get(self.index)?;
            let result = self.addr as u64;

            if (range.start..range.end).contains(&result) {
                self.addr += PAGESIZE;
                return Some(PhysFrame::containing_address(PhysAddr::new(result)));
            } else {
                self.index += 1;
                if let Some(addr) = self.range.get(self.index) {
                    self.addr = addr.start as usize;
                }
            }
        }
    }
}

impl VecPageAllocator {
    pub fn new(range: Vec<MemoryRegion>) -> Self {
        if let Some(addr) = range.first() {
            Self {
                addr: addr.start as usize,
                range,
                index: 0,
            }
        } else {
            Self {
                range,
                index: 0,
                addr: 0,
            }
        }
    }
}

#[derive(Debug, Clone)]
pub struct Frame {
    frame: PhysFrame<Size4KiB>,
}

impl crate::paging::Frame for Frame {
    fn start_address(&self) -> crate::addr::phy_addr::PhyAddr {
        crate::addr::phy_addr::PhyAddr::new(self.frame.start_address().as_u64() as usize)
    }

    fn size(&self) -> usize {
        self.frame.size() as usize
    }

    fn set_address(&mut self, addr: crate::addr::phy_addr::PhyAddr) {
        self.frame = PhysFrame::containing_address(PhysAddr::new(addr.as_usize() as u64));
    }
}

impl<'a, T> crate::paging::FrameAllocator<Frame, &'static str> for PageAllocator<'a, T>
where
    T: Iterator<Item = PhysFrame> + Send,
{
    fn allocate_frame(&mut self) -> Result<Frame, &'static str> {
        let mut node = MCSNode::new();
        let mut guard = self.frames.lock(&mut node);
        guard
            .next()
            .map(|frame| Frame { frame })
            .ok_or("no more frames")
    }
}

impl crate::paging::FrameAllocator<Frame, &'static str> for VecPageAllocator {
    fn allocate_frame(&mut self) -> Result<Frame, &'static str> {
        if let Some(frame) = FrameAllocator::allocate_frame(self) {
            Ok(Frame { frame })
        } else {
            Err("no more frames")
        }
    }
}

/// # Safety
///
/// `PHYSICAL_MEORY_OFFSET` must be initialized before calling.
pub unsafe fn get_page_table() -> Option<OffsetPageTable<'static>> {
    let physical_memory_offset = VirtAddr::new(physical_memory_offset() as u64);

    let level_4_table = active_level_4_table(physical_memory_offset);
    Some(OffsetPageTable::new(level_4_table, physical_memory_offset))
}

unsafe fn active_level_4_table(physical_memory_offset: VirtAddr) -> &'static mut PageTable {
    let (level_4_table_frame, _) = Cr3::read();

    let phys = level_4_table_frame.start_address();
    let virt = physical_memory_offset + phys.as_u64();
    let ptr = virt.as_mut_ptr();

    &mut *ptr
}

pub struct HeapPageAllocator;

unsafe impl FrameAllocator<Size4KiB> for HeapPageAllocator {
    fn allocate_frame(&mut self) -> Option<x86_64::structures::paging::PhysFrame<Size4KiB>> {
        let layout = Layout::from_size_align(PAGESIZE, PAGESIZE).ok()?;

        let ptr = unsafe {
            let ptr = crate::alloc::alloc::alloc(layout);
            if ptr.is_null() {
                return None;
            }
            ptr
        };

        let frame = PhysFrame::containing_address(PhysAddr::new(ptr as u64));
        Some(frame)
    }
}
