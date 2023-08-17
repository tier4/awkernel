use awkernel_lib::cpu::NUM_MAX_CPU;

pub const STACK_SIZE: usize = 2 * 1024 * 1024; // 2MiB
pub const STACK_START: usize = 256 * 1024 * 1024; // 256MiB

pub const HEAP_START: usize = STACK_START + STACK_SIZE * NUM_MAX_CPU;

pub const PREEMPT_IRQ: u16 = 32;
