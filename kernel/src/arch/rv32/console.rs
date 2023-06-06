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

    fn get(&self) -> Option<u8> {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);

        if let Some(serial) = guard.as_mut() {
            serial.get()
        } else {
            None
        }
    }

    fn put(&self, data: u8) {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);

        if let Some(serial) = guard.as_mut() {
            let _ = serial.put(data);
        }
    }

    fn irq_id(&self) -> usize {
        // TODO
        log::warn!("console::irq_id is not yet implemented.");

        0
    }

    fn print(&self, data: &str) {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);

        if let Some(serial) = guard.as_mut() {
            let _ = serial.write_str(data);
        }
    }
}
