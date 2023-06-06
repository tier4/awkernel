use awkernel_drivers::uart::uart_16550;
use awkernel_lib::{
    console::Console,
    sync::mutex::{MCSNode, Mutex},
};
use core::fmt::Write;
use log::Log;

static CONSOLE: UART = UART::new();

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

        let serial: &mut uart_16550::SerialPort = &mut guard;
        awkernel_lib::logger::write_msg(serial, record);
    }

    fn flush(&self) {}
}

pub fn init() {
    UART::init();
    awkernel_lib::console::register_unsafe_puts(unsafe_puts);
}

pub fn init_logger() {
    let _ = log::set_logger(&CONSOLE);
    log::set_max_level(log::LevelFilter::Debug);

    awkernel_lib::console::register_console(&CONSOLE);
}

impl Write for UART {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);

        let serial = &mut guard;
        serial.write_str(s)
    }
}

unsafe fn unsafe_puts(data: &str) {
    let mut port = unsafe { uart_16550::SerialPort::new(0x3F8) };
    let _ = port.write_str(data);
}

impl Console for UART {
    fn enable(&self) {
        // TODO
        log::warn!("console::enable is not yet implemented.");
    }

    fn disable(&self) {
        // TODO
        log::warn!("console::disable is not yet implemented.");
    }

    fn enable_recv_interrupt(&self) {
        // TODO
        log::warn!("console::enable_recv_interrupt is not yet implemented.");
    }

    fn disable_recv_interrupt(&self) {
        // TODO
        log::warn!("console::disable_recv_interrupt is not yet implemented.");
    }

    fn acknowledge_recv_interrupt(&self) {
        // TODO
        log::warn!("console::acknowledge_recv_interrupt is not yet implemented.");
    }

    fn irq_id(&self) -> usize {
        log::warn!("console::irq_id is not yet implemented.");
        0
    }

    fn get(&self) -> Option<u8> {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);
        guard.try_receive()
    }

    fn put(&self, data: u8) {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);
        let _ = guard.write_char(data as char);
    }

    fn print(&self, data: &str) {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);
        let _ = guard.write_str(data);
    }
}
