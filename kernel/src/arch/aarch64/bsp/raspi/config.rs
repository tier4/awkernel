pub const UART_CLOCK: usize = 48000000;

/// For Raspberry Pi 3, IRQ#0 is an interrupt of ARM Mailbox0,
/// and for Raspberry Pi 4, IRQ#0 is a local interrupt of GICv2.
pub const PREEMPT_IRQ: u16 = 0;
