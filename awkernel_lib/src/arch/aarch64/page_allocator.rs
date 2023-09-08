use crate::{addr::Addr, memory::PAGESIZE};

use super::page_table::FrameAllocator;

const NUM_RANGES: usize = 16;

pub struct PageAllocator<A: Addr> {
    range: [Option<(A, A)>; NUM_RANGES],
    idx: usize,
    current: usize,
}

impl<A: Addr> FrameAllocator<A> for PageAllocator<A> {
    fn allocate_frame(&mut self) -> Option<A> {
        let range = self.range.get_mut(self.current)?;

        let page_size = A::from_usize(PAGESIZE);

        if let Some(range) = range {
            let result = range.0;

            range.0 += page_size;

            if range.0 >= range.1 {
                self.current += 1;
            }

            Some(result)
        } else {
            None
        }
    }
}

impl<A: Addr> PageAllocator<A> {
    pub fn new() -> Self {
        PageAllocator {
            range: [None; NUM_RANGES],
            idx: 0,
            current: 0,
        }
    }

    pub fn push(&mut self, start: A, end: A) -> Result<(), &'static str> {
        if start >= end {
            return Err("start >= end");
        }

        if self.idx >= self.range.len() {
            return Err("too many heap ranges");
        }

        self.range[self.idx] = Some((start, end));
        self.idx += 1;

        Ok(())
    }
}

impl<A: Addr> Default for PageAllocator<A> {
    fn default() -> Self {
        Self::new()
    }
}
