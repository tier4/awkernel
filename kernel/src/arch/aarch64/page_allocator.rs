use super::mmu::PAGESIZE;

pub static mut PALLOC: PageAllocator = PageAllocator::init();
pub struct PageAllocator {
    start: u64,
    end: u64,
    cursor: u64,
}

impl PageAllocator {
    pub const fn init() -> Self {
        Self {
            start: 0,
            end: 0,
            cursor: 0,
        }
    }

    pub fn insert(&mut self, start: u64, end: u64) {
        self.start = start;
        self.end = end;
        self.cursor = self.start;
    }

    pub fn alloc(&mut self) -> u64 {
        let prev = self.cursor;
        self.cursor += PAGESIZE;
        prev
    }
}
