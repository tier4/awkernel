use alloc::boxed::Box;
use awkernel_drivers::uart::uart_16550;
use awkernel_lib::console::Console;
use core::fmt::Write;

pub struct Uart {
    port: uart_16550::SerialPort,
    enabled: bool,
}

const BASE: u16 = 0x3F8;

impl Uart {
    const fn new() -> Self {
        let port = unsafe { uart_16550::SerialPort::new(BASE) };
        Self {
            port,
            enabled: true,
        }
    }

    fn init() {
        let mut port = unsafe { uart_16550::SerialPort::new(BASE) };
        port.init();
    }
}

pub fn init_device() {
    Uart::init();
    awkernel_lib::console::register_unsafe_puts(unsafe_puts);
}

pub fn register_console() {
    awkernel_lib::console::register_console(Box::new(Uart::new()));
}

impl Write for Uart {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.port.write_str(s)
    }
}

unsafe fn unsafe_puts(data: &str) {
    let mut port = unsafe { uart_16550::SerialPort::new(BASE) };
    let _ = port.write_str(data);
}

impl Console for Uart {
    fn enable(&mut self) {
        self.enabled = true;
    }

    fn disable(&mut self) {
        self.enabled = false;
    }

    fn enable_recv_interrupt(&mut self) {
        self.port.enable_interrupt();
    }

    fn disable_recv_interrupt(&mut self) {
        self.port.disable_interrupt();
    }

    fn acknowledge_recv_interrupt(&mut self) {
        // nothing to do
    }

    fn irq_id(&self) -> u16 {
        36 // COM1
    }

    fn get(&mut self) -> Option<u8> {
        if self.enabled {
            self.port.try_receive()
        } else {
            None
        }
    }

    fn put(&mut self, data: u8) {
        if self.enabled {
            self.port.send(data);
        }
    }
}
