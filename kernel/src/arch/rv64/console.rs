use alloc::boxed::Box;
use core::{
    fmt::Write,
    sync::atomic::{AtomicUsize, Ordering},
};
use ns16550a::Uart;

static DEVADDR: AtomicUsize = AtomicUsize::new(0);

pub struct Console {
    port: Uart,
}

impl Console {
    fn new(devaddr: usize) -> Self {
        Self {
            port: Uart::new(devaddr),
        }
    }
}

unsafe fn unsafe_puts(data: &str) {
    let mut port = Uart::new(DEVADDR.load(Ordering::Relaxed));
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

    DEVADDR.store(devaddr, Ordering::Relaxed);

    awkernel_lib::console::register_unsafe_puts(unsafe_puts);
}

pub fn init(devaddr: usize) {
    awkernel_lib::console::register_console(Box::new(Console::new(devaddr)));
}

impl Write for Console {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.port.write_str(s)
    }
}

impl awkernel_lib::console::Console for Console {
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

    fn acknowledge_recv_interrupt(&mut self) {
        // TODO
    }

    fn get(&mut self) -> Option<u8> {
        self.port.get()
    }

    fn put(&mut self, data: u8) {
        self.port.put(data);
    }

    fn irq_id(&self) -> u16 {
        // TODO
        0
    }
}