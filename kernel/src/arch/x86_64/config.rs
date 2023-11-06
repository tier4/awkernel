pub const STACK_SIZE: usize = 2 * 1024 * 1024; // 2MiB
pub const STACK_START: usize = 256 * 1024 * 1024; // 256MiB

pub const HEAP_START: usize = 8 * 1024 * 1024 * 1024; // 8GiB

pub const DMA_START: usize = 3 * 1024 * 1024 * 1024 * 1024; // 3TiB

pub const PREEMPT_IRQ: u16 = 32;
