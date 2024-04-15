#[cfg(feature = "raspi")]
pub use super::raspi::config::*;

#[cfg(feature = "raspi5")]
pub use super::raspi5::config::*;

#[cfg(feature = "aarch64_virt")]
pub use super::aarch64_virt::config::*;

#[cfg(not(feature = "raspi5"))]
pub const UART_BAUDRATE: usize = 115200;
