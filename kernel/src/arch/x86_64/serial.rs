use awkernel_lib::{
    console::Console,
    sync::mutex::{MCSNode, Mutex},
};
use core::fmt::Write;
use log::Log;
use uart_16550::SerialPort;

pub static SERIAL: UART = UART::new();

pub struct UART {
    port: Mutex<uart_16550::SerialPort>,
}

impl UART {
    const fn new() -> Self {
        let port = unsafe { uart_16550::SerialPort::new(0x3F8) };
        Self {
            port: Mutex::new(port),
        }
    }

    fn init() {
        let mut port = unsafe { uart_16550::SerialPort::new(0x3F8) };
        port.init();
    }
}

impl Log for UART {
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
        awkernel_lib::logger::write_msg(serial, record);
    }

    fn flush(&self) {}
}

pub fn init() {
    UART::init();
}

pub fn init_logger() {
    let _ = log::set_logger(&SERIAL);
    log::set_max_level(log::LevelFilter::Debug);
}

impl Write for UART {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);

        let serial: &mut SerialPort = &mut guard;
        serial.write_str(s)
    }
}

impl Console for UART {
    unsafe fn raw_puts(data: &str) {
        let mut port = unsafe { uart_16550::SerialPort::new(0x3F8) };
        let _ = port.write_str(data);
    }

    fn enable(&mut self) {
        // TODO
    }

    fn disable(&mut self) {
        // TODO
    }

    fn enable_recv_interrupt(&mut self) {
        // TODO
    }

    fn disable_recv_interrupt(&mut self) {
        // TODO
    }
}
