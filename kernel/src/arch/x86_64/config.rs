pub const STACK_SIZE: usize = 2 * 1024 * 1024; // 2MiB
pub const STACK_START: usize = 256 * 1024 * 1024; // 256MiB

pub const DMA_START: usize = 0x40000000000; // 6 * 1024 * 1024 * 1024; // 6GiB
pub const DMA_SIZE: usize = 64 * 1024 * 1024; // 64MiB per NUMA node

pub const HEAP_START: usize = 0x41000000000; // 8 * 1024 * 1024 * 1024; // 8GiB

pub const PREEMPT_IRQ: u16 = 255;
