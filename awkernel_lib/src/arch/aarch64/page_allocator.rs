use crate::memory::PAGESIZE;

use super::page_table::FrameAllocator;

const NUM_RANGES: usize = 16;

#[derive(Default)]
pub struct PageAllocator {
    range: [Option<(u64, u64)>; NUM_RANGES],
    idx: usize,
    current: usize,
}

impl FrameAllocator for PageAllocator {
    fn allocate_frame(&mut self) -> Option<u64> {
        let range = self.range.get_mut(self.current)?;

        if let Some(range) = range {
            let result = range.0;

            range.0 += PAGESIZE as u64;

            if range.0 >= range.1 {
                self.current += 1;
            }

            Some(result)
        } else {
            None
        }
    }
}

impl PageAllocator {
    pub fn new() -> Self {
        PageAllocator::default()
    }

    pub fn push(&mut self, start: u64, end: u64) -> Result<(), &'static str> {
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
