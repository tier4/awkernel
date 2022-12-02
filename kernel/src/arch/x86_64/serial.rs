use core::fmt::Write;

use log::Log;
use synctools::mcs::{MCSLock, MCSNode};

pub static SERIAL: Serial = Serial::new();

pub struct Serial {
    port: MCSLock<uart_16550::SerialPort>,
}

pub(crate) fn puts(msg: &str) {
    let mut node = MCSNode::new();
    let mut guard = SERIAL.port.lock(&mut node);
    let _ = guard.write_str(msg);
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
        guard.init();
        let _ = guard.write_str("Initialized a serial port.\n");
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

        let msg = alloc::format!("{}\n", record.args());
        let _ = guard.write_str(msg.as_str());
    }

    fn flush(&self) {}
}

pub fn init() {
    SERIAL.init();
    let _ = log::set_logger(&SERIAL);
    log::set_max_level(log::LevelFilter::Debug);
}
