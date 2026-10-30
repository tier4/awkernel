pub const STACK_SIZE: usize = 2 * 1024 * 1024; // 2MiB
pub const STACK_START: usize = 256 * 1024 * 1024; // 256MiB

pub const DMA_START: usize = 0x40000000000;

pub const HEAP_START: usize = 0x41000000000;

/// Virtual address of the bootloader's physical memory mapping: the start of
/// the higher half, so up to 128 TiB of physical address space fits.
///
/// `Mapping::Dynamic` takes the first free run of level 4 entries, which can
/// straddle the non-canonical hole when the firmware memory map reaches the top
/// of a 46-bit physical address space; the bootloader then panics with
/// `VirtAddrNotValid(0x800000000000)` while mapping physical memory.
pub const PHYSICAL_MEMORY_OFFSET: u64 = 0xffff_8000_0000_0000;

pub const PREEMPT_IRQ: u16 = 255;
pub const WAKEUP_IRQ: u16 = 254;

pub const DMA_SIZE: usize = 128 * 1024 * 1024; // 128MiB
