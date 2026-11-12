use awkernel_lib::arch::rv_common::interrupt_controller::{PREEMPT_IPI_IRQ, WAKEUP_IPI_IRQ};

pub const HEAP_START: usize = 0x0008_8000_0000;

pub const PREEMPT_IRQ: u16 = PREEMPT_IPI_IRQ;
pub const WAKEUP_IRQ: u16 = WAKEUP_IPI_IRQ;
