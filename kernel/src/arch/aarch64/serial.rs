use super::driver::uart::{DevUART, UART};
use core::fmt::Write;
use log::Log;
use synctools::mcs::{MCSLock, MCSNode};

pub static SERIAL: Serial = Serial::new();

pub const UART_CLOCK: usize = 48000000;
pub const UART_BAUD: usize = 115200;

pub struct Serial {
    port: MCSLock<Option<DevUART>>,
}

impl Serial {
    const fn new() -> Self {
        Self {
            port: MCSLock::new(None),
        }
    }

    fn init(&self) {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);
        if guard.is_none() {
            let mut port = DevUART::new(super::bsp::memory::UART0_BASE);
            let _ = port.write_str("Initialized a serial port.\n");
            *guard = Some(port);
        }
    }
}

impl Log for Serial {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        let mut node = MCSNode::new();
        let guard = self.port.lock(&mut node);
        guard.is_some()
    }

    fn log(&self, record: &log::Record) {
        if !self.enabled(record.metadata()) {
            return;
        }

        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);

        if let Some(serial) = guard.as_mut() {
            t4os_lib::logger::write_msg(serial, record);
        }
    }

    fn flush(&self) {}
}

pub fn init() {
    SERIAL.init();
    let _ = log::set_logger(&SERIAL);
    log::set_max_level(log::LevelFilter::Debug);
}
