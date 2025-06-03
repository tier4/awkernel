use super::address::{PhysAddr, PhysPageNum, MEMORY_END};
use crate::sync::mcs::MCSNode;
use alloc::vec::Vec;

type FrameAllocatorImpl = PageAllocator;

/// Use `awkernel_lib::sync::mutex::Mutex` to get `lazy_static!` + `Arc` like effect
///
/// `OnceCell` like implementation. (OnceCell: https://doc.rust-lang.org/core/cell/struct.OnceCell.html)
///
/// SAFETY
///
/// Based on MCSLock, thread safe
pub static FRAME_ALLOCATOR: crate::sync::mutex::Mutex<Option<FrameAllocatorImpl>> =
    crate::sync::mutex::Mutex::new(None);

pub fn frame_alloc() -> Option<FrameTracker> {
    let mut node = MCSNode::new();
    let mut allocator = FRAME_ALLOCATOR.lock(&mut node);
    if let Some(allocator_ref) = allocator.as_mut() {
        allocator_ref.alloc().map(FrameTracker::new)
    } else {
        None
    }
}

pub fn frame_dealloc(ppn: PhysPageNum) {
    let mut node = MCSNode::new();
    let mut allocator = FRAME_ALLOCATOR.lock(&mut node);
    if let Some(allocator_ref) = allocator.as_mut() {
        allocator_ref.dealloc(ppn);
    }
}

pub fn init_page_allocator() {
    extern "C" {
        fn ekernel();
    }
    let mut node = MCSNode::new();
    let mut allocator = FRAME_ALLOCATOR.lock(&mut node);
    if allocator.is_none() {
        *allocator = Some(FrameAllocatorImpl::new());
    }
    if let Some(allocator_ref) = allocator.as_mut() {
        allocator_ref.init(
            PhysAddr::from(ekernel as usize).ceil(),
            PhysAddr::from(MEMORY_END as usize).floor(),
        );
    } else {
        panic!("[Error] Failed to initialize FrameAllocator!");
    }
}

pub trait FrameAllocator {
    fn new() -> Self;
    fn alloc(&mut self) -> Option<PhysPageNum>;
    #[allow(dead_code)]
    fn alloc_more(&mut self, pages: usize) -> Option<Vec<PhysPageNum>>;
    fn dealloc(&mut self, ppn: PhysPageNum);
}

/// An abstraction to use Rust's borrowchecker to guarantee safety of memory
#[derive(Debug)]
pub struct FrameTracker {
    pub ppn: PhysPageNum,
}

impl FrameTracker {
    pub fn new(ppn: PhysPageNum) -> Self {
        // page cleaning
        let bytes_array = ppn.get_bytes_array();
        bytes_array.fill(0);
        Self { ppn }
    }
}

impl Drop for FrameTracker {
    fn drop(&mut self) {
        frame_dealloc(self.ppn);
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
        } else if self.current == self.end {
            None
        } else {
            self.current += 1;
            Some((self.current - 1).into())
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
        if ppn.0 >= self.current || self.recycled.contains(&ppn.0) {
            panic!("Frame ppn={:#x} has not been allocated!", ppn.0)
        }
        self.recycled.push(ppn.0)
    }
}

impl PageAllocator {
    pub fn init(&mut self, l: PhysPageNum, r: PhysPageNum) {
        self.current = l.0;
        self.end = r.0;
    }
}
