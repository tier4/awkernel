use awkernel_lib::cpu::NUM_MAX_CPU;

pub const STACK_SIZE: u64 = 2 * 1024 * 1024; // 2MiB
pub const STACK_START: u64 = 256 * 1024 * 1024; // 256MiB

pub const HEAP_START: u64 = STACK_START + STACK_SIZE * NUM_MAX_CPU as u64;

pub const PREEMPT_IRQ: u16 = 0;
