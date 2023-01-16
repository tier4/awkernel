use core::fmt::Write;

use log::Log;
use synctools::mcs::{MCSLock, MCSNode};
use uart_16550::SerialPort;

pub static SERIAL: Serial = Serial::new();

pub struct Serial {
    port: MCSLock<uart_16550::SerialPort>,
}

impl Serial {
    const fn new() -> Self {
        let port = unsafe { uart_16550::SerialPort::new(0x3F8) };
        Self {
            port: MCSLock::new(port),
        }
    }

    fn init() {
        let mut port = unsafe { uart_16550::SerialPort::new(0x3F8) };
        port.init();
    }
}

impl Log for Serial {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        true
    }

    fn log(&self, record: &log::Record) {
        if !self.enabled(record.metadata()) {
            return;
        }

        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);

        let serial: &mut SerialPort = &mut guard;
        t4os_lib::logger::write_msg(serial, record);
    }

    fn flush(&self) {}
}

pub fn init() {
    Serial::init();
}

pub fn init_logger() {
    let _ = log::set_logger(&SERIAL);
    log::set_max_level(log::LevelFilter::Debug);
}

pub fn puts(data: &str) {
    let mut port = unsafe { uart_16550::SerialPort::new(0x3F8) };
    let _ = port.write_str(data);
}
