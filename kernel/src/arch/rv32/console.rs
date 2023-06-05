use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::{fmt::Write, ptr::write_volatile};
use log::Log;
use ns16550a::Uart;

static CONSOLE: Console = Console::new();
static mut DEVADDR: usize = 0;

pub struct Console {
    port: Mutex<Option<Uart>>,
}

impl Console {
    const fn new() -> Self {
        Self {
            port: Mutex::new(None),
        }
    }

    fn init(&self, devaddr: usize) {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);
        if guard.is_none() {
            let mut port = Uart::new(devaddr as usize);
            let _ = port.write_str("Initialized a serial port.\n");
            *guard = Some(port);
        }
    }
}

impl Log for Console {
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

unsafe fn unsafe_puts(data: &str) {
    let mut port = Uart::new(DEVADDR);
    let _ = port.write_str(data);
}

pub fn init_port(devaddr: usize) {
    let port = Uart::new(devaddr);
    port.init(
        ns16550a::WordLength::EIGHT,
        ns16550a::StopBits::ONE,
        ns16550a::ParityBit::DISABLE,
        ns16550a::ParitySelect::EVEN,
        ns16550a::StickParity::DISABLE,
        ns16550a::Break::DISABLE,
        ns16550a::DMAMode::MODE0,
        ns16550a::Divisor::BAUD115200,
    );

    unsafe { write_volatile(&mut DEVADDR, devaddr) };

    awkernel_lib::console::register_unsafe_puts(unsafe_puts);
}

pub fn init(devaddr: usize) {
    CONSOLE.init(devaddr);
    let _ = log::set_logger(&CONSOLE);
    log::set_max_level(log::LevelFilter::Debug);

    awkernel_lib::console::register_console(&CONSOLE);
}

impl awkernel_lib::console::Console for Console {
    fn enable(&self) {
        todo!()
    }

    fn disable(&self) {
        todo!()
    }

    fn enable_recv_interrupt(&self) {
        todo!()
    }

    fn disable_recv_interrupt(&self) {
        todo!()
    }

    fn acknowledge_recv_interrupt(&self) {
        todo!()
    }

    fn get(&self) -> Option<u8> {
        todo!()
    }

    fn put(&self, data: u8) {}

    fn irq_id(&self) -> usize {
        todo!()
    }

    fn print(&self, data: &str) {
        todo!()
    }
}
