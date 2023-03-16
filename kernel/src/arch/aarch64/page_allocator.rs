use super::{mmu::PAGESIZE, page_table::FrameAllocator};

pub struct PageAllocator {
    start: u64,
    end: u64,
}

impl FrameAllocator for PageAllocator {
    fn allocate_frame(&mut self) -> Option<u64> {
        if self.start == self.end {
            None
        } else {
            let frame = self.start;
            self.start += PAGESIZE;
            Some(frame)
        }
    }
}

impl PageAllocator {
    pub fn new(start: u64, end: u64) -> Self {
        Self { start, end }
    }
}
