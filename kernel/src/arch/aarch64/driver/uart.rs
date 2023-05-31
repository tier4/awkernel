#[cfg(any(feature = "raspi3", feature = "raspi4"))]
pub mod pl011;

use crate::arch::aarch64::serial::UART_CLOCK;
use awkernel_lib::serial::{Serial, BAUDRATE};

pub trait Uart {
    fn new(base: usize) -> Self;
    fn send(&self, c: u32);
    fn recv(&self) -> u32;
    fn enable_recv_interrupt(&self);
    fn disable_recv_interrupt(&self);
    fn on(&self);
    fn off(&self);

    fn init(clock: usize, baudrate: usize);

    fn puts(&self, data: &str) {
        for c in data.bytes() {
            self.send(c as u32);
            if c == b'\n' {
                self.send(b'\r' as u32);
            }
        }
    }

    unsafe fn unsafe_puts(data: &str);
}

#[cfg(any(feature = "raspi3", feature = "raspi4"))]
pub type DevUART = pl011::PL011;

impl DevUART where DevUART: Serial {}

pub unsafe fn init_device() {
    DevUART::init_device(UART_CLOCK, BAUDRATE as usize);
}
