pub const UART_CLOCK: usize = 48000000;

/// For Raspberry Pi 3, IRQ#1 is the interrupt of ARM Mailbox,
/// and for Raspberry Pi 4, IRQ#1 is a local interrupt.
pub const PREEMPT_IRQ: u16 = 1;
