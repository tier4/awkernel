use bootloader::BootInfo;

#[derive(Debug)]
pub enum InitErr {
    InvalidPhysicalMemoryOffset,
    FailedToAllocateFrame,
    FailedToMapPage,
}

pub trait HeapInit {
    fn init(boot_info: &BootInfo) -> Result<(), InitErr>;
}

pub fn init(boot_info: &BootInfo) -> Result<(), InitErr> {
    use crate::x86_64::heap::MapHeapPage;

    MapHeapPage::init(boot_info)?;

    unsafe {
        ALLOC.init(
            crate::config::HEAP_START as usize,
            crate::config::HEAP_SIZE as usize,
        );
    }

    Ok(())
}

#[global_allocator]
static mut ALLOC: memac::Allocator<memac::buddy::Buddy32M> = memac::Allocator::new();
