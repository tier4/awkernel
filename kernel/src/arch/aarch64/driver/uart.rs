#[cfg(any(feature = "raspi3", feature = "raspi4"))]
pub mod pl011;

use crate::arch::aarch64::console::{UART_BAUDRATE, UART_CLOCK};
use awkernel_lib::console::Console;

#[cfg(any(feature = "raspi3", feature = "raspi4"))]
pub type DevUART = pl011::PL011;

impl DevUART where DevUART: Console {}

pub unsafe fn init_device() {
    DevUART::init_device(UART_CLOCK, UART_BAUDRATE);
}
