#[cfg(feature = "aarch64")]
pub mod pl011;

#[cfg(feature = "x86")]
pub mod uart_16550;
