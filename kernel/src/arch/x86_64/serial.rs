use core::fmt::Write;

use log::Log;
use synctools::mcs::{MCSLock, MCSNode};

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

    fn init(&self) {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);
        let _ = guard.write_str("Initialized a serial port.\n");
        guard.init();
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

        let _ = guard.write_char('[');
        let _ = guard.write_str(record.level().as_str());
        let _ = guard.write_str("] ");

        if let Some(args) = record.args().as_str() {
            let _ = guard.write_str(args);
        }
        let _ = guard.write_char('\n');
    }

    fn flush(&self) {}
}

pub fn init() {
    SERIAL.init();
    let _ = log::set_logger(&SERIAL);
    log::set_max_level(log::LevelFilter::Debug);
}
