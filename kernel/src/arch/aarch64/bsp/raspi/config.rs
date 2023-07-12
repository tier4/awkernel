pub const UART_CLOCK: usize = 48000000;

#[cfg(feature = "raspi3")]
pub const PREEMPT_IRQ: u16 = !0; // TODO

#[cfg(feature = "raspi4")]
pub const PREEMPT_IRQ: u16 = 0;
