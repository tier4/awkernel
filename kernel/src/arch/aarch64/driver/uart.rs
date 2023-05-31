#[cfg(any(feature = "raspi3", feature = "raspi4"))]
pub mod pl011;

use crate::arch::aarch64::serial::{UART_BAUDRATE, UART_CLOCK};
use awkernel_lib::serial::Serial;

#[cfg(any(feature = "raspi3", feature = "raspi4"))]
pub type DevUART = pl011::PL011;

impl DevUART where DevUART: Serial {}

pub unsafe fn init_device() {
    DevUART::init_device(UART_CLOCK, UART_BAUDRATE);
}
