pub const UART_CLOCK: usize = 44_000_000;

pub const PREEMPT_IRQ: u16 = 0;
pub const WAKEUP_IRQ: u16 = 1;

pub const HEAP_START: usize = 0x50_0000_0000;

pub const DMA_SIZE: usize = 64 * 1024 * 1024; // 64MiB
