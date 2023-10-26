pub const STACK_SIZE: usize = 2 * 1024 * 1024; // 2MiB
pub const STACK_START: usize = 256 * 1024 * 1024; // 256MiB

pub const DEV_START: usize = 8 * 1024 * 1024 * 1024; // 4GiB
pub const HEAP_START: usize = 16 * 1024 * 1024 * 1024; // 16GiB

pub const PREEMPT_IRQ: u16 = 32;
