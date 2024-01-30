use super::address::{
    PhysAddr, PhysPageNum, VirtAddr, VirtPageNum, MEMORY_END, PAGE_SIZE, PA_WIDTH, PPN_WIDTH,
    VA_WIDTH, VPN_WIDTH,
};
use core::cell::OnceCell;

type FrameAllocatorImpl = PageAllocator;

/// Use `OnceCell` to get `lazy_static!` + `Arc` like effect
///
/// SAFETY
///
/// May not be thread_safe, Seems that `OnceLock`is better.
pub static FRAME_ALLOCATOR: OnceCell<FrameAllocatorImpl> = {
    let mut cell_allocator = OnceCell::new();
    cell_allocator.get_or_init(FrameAllocatorImpl::new());
    cell_allocator
};

pub fn init_page_allocator() {
    extern "C" {
        fn ekernel();
    }

    if let Some(ALLOCATOR_REF) = FRAME_ALLOCATOR.get_mut() {
        ALLOCATOR_REF.init(
            PhysAddr::from(ekernel as usize).ceil(),
            PhysAddr::from(MEMORY_END).floor(),
        )
    } else {
        panic!("[Error] FrameAllocator is not initialized at all! May be triggered by Race condition of multicore!")
    }
}

pub trait FrameAllocator {
    fn new() -> Self;
    fn alloc(&mut self) -> Option<PhysPageNum>;
    fn alloc_more(&mut self, pages: usize) -> Option<Vec<PhysPageNum>>;
    fn dealloc(&mut self, ppn: PhysPageNum);
}

pub struct FrameTracker {
    pub ppn: PhysPageNum,
}

impl FrameTracker {
    pub fn new(ppn: PhysPageNum) -> Self {
        let
    }
}

/// Frame range: [current, end)
pub struct PageAllocator {
    current: usize,
    end: usize,
    recycled: Vec<usize>,
}

impl FrameAllocator for PageAllocator {
    fn new() -> Self {
        Self {
            current: 0,
            end: 0,
            recycled: Vec::new(),
        }
    }

    fn alloc(&mut self) -> Option<PhysPageNum> {
        if let Some(ppn) = self.recycled.pop() {
            Some(ppn.into())
        } else {
            if self.current == self.end {
                None
            } else {
                self.current += 1;
                Some((self.current - 1).into())
            }
        }
    }

    fn alloc_more(&mut self, pages: usize) -> Option<Vec<PhysPageNum>> {
        if self.current + pages >= self.end {
            None
        } else {
            self.current += pages;
            let arr: Vec<usize> = (1..pages + 1).collect();
            let v = arr.iter().map(|x| (self.current - x).into()).collect();
            Some(v)
        }
    }

    fn dealloc(&mut self, ppn: PhysPageNum) {
        if ppn.0 >= self.current || self.recycled.iter().find(|&v| v == ppn.0).is_some() {
            panic!("Frame ppn={:#x} has not been allocated!", ppn.0)
        }
        self.recycled.push(ppn.0)
    }
}
