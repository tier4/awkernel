pub const STACK_SIZE: usize = 2 * 1024 * 1024; // 2MiB
pub const STACK_START: usize = 256 * 1024 * 1024; // 256MiB

pub const DMA_START: usize = 0x40000000000;

pub const VT_D_START: usize = 0x40800000000;

pub const HEAP_START: usize = 0x41000000000;

pub const PREEMPT_IRQ: u16 = 255;

pub const INTERRUPT_REMAPPING_TABLE_START: usize = 128 * 1024 * 1024; // 128MiB;
