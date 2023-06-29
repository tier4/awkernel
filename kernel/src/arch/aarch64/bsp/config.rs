#[cfg(any(feature = "raspi3", feature = "raspi4"))]
pub use super::raspi::config::*;

pub const UART_BAUDRATE: usize = 115200;
