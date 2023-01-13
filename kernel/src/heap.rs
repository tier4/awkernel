#[allow(dead_code)]
#[derive(Debug)]
pub enum InitErr {
    InvalidPhysicalMemoryOffset,
    InvalidACPI,
    FailedToAllocateFrame,
    FailedToMapPage,
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
static mut ALLOC: memac::Allocator<memac::buddy::Buddy256M> = memac::Allocator::new();
