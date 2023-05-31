use super::driver::uart::{self, DevUART};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::fmt::Write;
use log::Log;

pub static SERIAL: Serial = Serial::new();

pub const UART_CLOCK: usize = 48000000;
pub const UART_BAUDRATE: usize = 115200;

pub struct Serial {
    port: Mutex<Option<DevUART>>,
}

impl Serial {
    const fn new() -> Self {
        Self {
            port: Mutex::new(None),
        }
    }

    fn init(&self) {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);
        if guard.is_none() {
            let mut port = DevUART::new();
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
            awkernel_lib::logger::write_msg(serial, record);
        }
    }

    fn flush(&self) {}
}

pub unsafe fn init_device() {
    uart::init_device();
}

pub fn init() {
    SERIAL.init();
    let _ = log::set_logger(&SERIAL);
    log::set_max_level(log::LevelFilter::Debug);
}
