#[cfg(any(feature = "raspi3", feature = "raspi4"))]
pub mod pl011;

use crate::arch::aarch64::serial::UART_CLOCK;
use alloc::vec::Vec;
use awkernel_lib::serial::{Serial, BAUDRATE};

#[cfg(any(feature = "raspi3", feature = "raspi4"))]
pub type DevUART = pl011::PL011;

impl DevUART where DevUART: Serial {}

pub unsafe fn init_device() {
    DevUART::init_device(UART_CLOCK, BAUDRATE as usize);
}
