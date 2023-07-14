#[cfg(feature = "raspi")]
pub use super::raspi::config::*;

pub const UART_BAUDRATE: usize = 115200;
