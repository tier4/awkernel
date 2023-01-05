use core::fmt::Write;

use log::Log;
use synctools::mcs::MCSLock;
use uart_16550::SerialPort;

pub static SERIAL: Serial = Serial::new();

pub struct Serial {
    port: MCSLock<uart_16550::SerialPort>,
}

pub(crate) fn puts(msg: &str) {
    let mut guard = SERIAL.port.lock();
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
        let mut guard = self.port.lock();
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

        let mut guard = self.port.lock();

        let serial: &mut SerialPort = &mut guard;
        crate::logger::write_msg(serial, record);
    }

    fn flush(&self) {}
}

pub fn init() {
    SERIAL.init();
    let _ = log::set_logger(&SERIAL);
    log::set_max_level(log::LevelFilter::Debug);
}
