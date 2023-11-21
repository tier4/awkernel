use super::address::{
    PhysAddr, PhysPageNum, VirtAddr, VirtPageNum, MEMORY_END, PAGE_SIZE, PA_WIDTH, PPN_WIDTH,
    VA_WIDTH, VPN_WIDTH,
};
use crate::sync::safe_arc::SafeArc;
use lazy_static::lazy_static;

type FrameAllocatorImpl = PageAllocator;

#[global_allocator]
lazy_static! {
    pub static ref FRAME_ALLOCATOR: SafeArc<FrameAllocatorImpl> =
        unsafe { SafeArc::new(FrameAllocatorImpl::new()) };
}

pub fn init_page_allocator() {
    extern "C" {
        fn ekernel();
    }

    FRAME_ALLOCATOR.exclusive_access().init(
        PhysAddr::from(ekernel as usize).ceil(),
        PhysAddr::from(MEMORY_END).floor(),
    );
}

pub trait FrameAllocator {
    fn new() -> Self;
    fn alloc(&mut self) -> Option<PhysPageNum>;
    fn alloc_more(&mut self, pages: usize) -> Option<Vec<PhysPageNum>>;
    fn dealloc(&mut self, ppn: PhysPageNum);
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
