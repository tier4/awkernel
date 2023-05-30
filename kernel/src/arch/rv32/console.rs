use core::fmt::Write;
use log::Log;
use ns16550a::Uart;
use synctools::mcs::{MCSLock, MCSNode};

pub static CONSOLE: Console = Console::new();

pub struct Console {
    port: MCSLock<Option<Uart>>,
}

impl Console {
    const fn new() -> Self {
        Self {
            port: MCSLock::new(None),
        }
    }

    fn init(&self, devaddr: u32) {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);
        if guard.is_none() {
            let mut port = Uart::new(devaddr as usize);
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

pub fn init(devaddr: u32) {
    CONSOLE.init(devaddr);
    let _ = log::set_logger(&CONSOLE);
    log::set_max_level(log::LevelFilter::Debug);
}
