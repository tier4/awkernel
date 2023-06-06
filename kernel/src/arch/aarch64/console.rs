use super::{
    config,
    driver::uart::{self, DevUART},
};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::fmt::Write;
use log::Log;

pub static CONSOLE: Console = Console::new();

pub const UART_CLOCK: usize = 48000000;
pub const UART_BAUDRATE: usize = 115200;

pub struct Console {
    port: Mutex<Option<DevUART>>,
}

impl Console {
    const fn new() -> Self {
        Self {
            port: Mutex::new(None),
        }
    }

    fn init(&self) {
        let mut node = MCSNode::new();
        let mut guard = self.port.lock(&mut node);
        if guard.is_none() {
            let mut port = DevUART::new(config::UART_IRQ);
            let _ = port.write_str("Initialized a serial port.\n");
            *guard = Some(port);
        }
    }
}

// impl awkernel_lib::console::Console for Console {
//     fn enable(&self) {
//         let uart = DevUART::new(config::UART_IRQ);
//         uart.enable();
//     }

//     fn disable(&self) {
//         let uart = DevUART::new(config::UART_IRQ);
//         uart.disable();
//     }

//     fn enable_recv_interrupt(&self) {
//         let uart = DevUART::new(config::UART_IRQ);
//         uart.enable_recv_interrupt();
//     }

//     fn disable_recv_interrupt(&self) {
//         let uart = DevUART::new(config::UART_IRQ);
//         uart.disable_recv_interrupt();
//     }

//     fn acknowledge_recv_interrupt(&self) {
//         let uart = DevUART::new(config::UART_IRQ);
//         uart.acknowledge_recv_interrupt();
//     }

//     fn irq_id(&self) -> usize {
//         config::UART_IRQ
//     }

//     fn get(&self) -> Option<u8> {
//         let mut node = MCSNode::new();
//         let guard = self.port.lock(&mut node);
//         if let Some(console) = guard.as_ref() {
//             console.get()
//         } else {
//             None
//         }
//     }

//     fn put(&self, data: u8) {
//         let mut node = MCSNode::new();
//         let guard = self.port.lock(&mut node);
//         if let Some(console) = guard.as_ref() {
//             console.put(data);
//         }
//     }
// }

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

pub unsafe fn init_device() {
    uart::init_device();
    awkernel_lib::console::register_unsafe_puts(uart::unsafe_puts);
}

pub fn init() {
    // CONSOLE.init();
    // let _ = log::set_logger(&CONSOLE);
    // log::set_max_level(log::LevelFilter::Debug);

    // awkernel_lib::console::register_console(DevUART::new());
}
