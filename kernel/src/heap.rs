use crate::board_info::BoardInfo;

#[derive(Debug)]
pub enum InitErr {
    InvalidPhysicalMemoryOffset,
    FailedToAllocateFrame,
    FailedToMapPage,
}

pub trait HeapInit<Info> {
    /// Map heap memory region.
    fn init(board_info: &BoardInfo<Info>) -> Result<(), InitErr>;
}

pub fn init() {
    // Initialize memory allocator.
    unsafe {
        ALLOC.init(
            crate::config::HEAP_START as usize,
            crate::config::HEAP_SIZE as usize,
        );
    }
}

#[global_allocator]
static mut ALLOC: memac::Allocator<memac::buddy::Buddy64M> = memac::Allocator::new();
