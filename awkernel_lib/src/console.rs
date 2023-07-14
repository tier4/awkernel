use crate::sync::{mcs::MCSNode, mutex::Mutex};
use alloc::boxed::Box;
use core::{fmt::Write, ptr::write_volatile, str::from_utf8_unchecked};
use log::Log;

pub trait Console: Write + Send {
    /// Enable the serial port.
    fn enable(&mut self);

    /// Disable the serial port.
    fn disable(&mut self);

    /// Enable the reception interrupt.
    fn enable_recv_interrupt(&mut self);

    /// Disable the reception interrupt.
    fn disable_recv_interrupt(&mut self);

    /// Acknowledge to the reception interrupt.
    fn acknowledge_recv_interrupt(&mut self);

    /// Get IRQ#.
    fn irq_id(&self) -> u16;

    /// Read a byte.
    fn get(&mut self) -> Option<u8>;

    /// Write a byte.
    fn put(&mut self, data: u8);
}

static mut UNSAFE_PUTS: Option<unsafe fn(&str)> = None;

pub fn register_unsafe_puts(console: unsafe fn(&str)) {
    unsafe { write_volatile(&mut UNSAFE_PUTS, Some(console)) }
}

/// # Safety
///
/// This function do not acquire lock to print `data`,
/// and should be called for critical errors or booting.
pub unsafe fn unsafe_puts(data: &str) {
    if let Some(console) = UNSAFE_PUTS {
        console(data);
    }
}

macro_rules! unsafe_print_hex {
    ($n:expr, $result:expr) => {{
        let mut num = $n;

        let mut i = 0;
        while num > 0 {
            let n = num & 0xf;

            $result[i] = if n < 10 {
                b'0' + n as u8
            } else {
                b'a' + (n as u8 - 10)
            };

            num /= 16;
            i += 1;
        }

        let mut msg = [b'0'];

        for n in $result.iter().rev() {
            msg[0] = *n;

            let msg = from_utf8_unchecked(&msg);
            unsafe_puts(msg);
        }
    }};
}

pub unsafe fn unsafe_print_hex_u32(num: u32) {
    let mut result = [b'0'; 8];
    unsafe_print_hex!(num, result);
}

pub unsafe fn unsafe_print_hex_u64(num: u64) {
    let mut result = [b'0'; 16];
    unsafe_print_hex!(num, result);
}

pub unsafe fn unsafe_print_hex_u96(num: u128) {
    let mut result = [b'0'; 24];
    unsafe_print_hex!(num, result);
}

pub unsafe fn unsafe_print_hex_u128(num: u128) {
    let mut result = [b'0'; 32];
    unsafe_print_hex!(num, result);
}

static CONSOLE: ConsoleContainer = ConsoleContainer {
    console: Mutex::new(None),
};

struct ConsoleContainer {
    console: Mutex<Option<Box<dyn Console>>>,
}

impl Log for ConsoleContainer {
    fn enabled(&self, _metadata: &log::Metadata) -> bool {
        let mut node = MCSNode::new();
        let c = CONSOLE.console.lock(&mut node);
        c.is_some()
    }

    fn log(&self, record: &log::Record) {
        if !self.enabled(record.metadata()) {
            return;
        }

        let mut node = MCSNode::new();
        let mut guard = self.console.lock(&mut node);

        if let Some(serial) = guard.as_mut() {
            crate::logger::write_msg(serial.as_mut(), record);
        }
    }

    fn flush(&self) {}
}

pub fn register_console(console: Box<dyn Console>) {
    let mut node = MCSNode::new();
    let mut c = CONSOLE.console.lock(&mut node);

    *c = Some(console);

    let _ = log::set_logger(&CONSOLE);
    log::set_max_level(log::LevelFilter::Debug);
}

/// Enable console.
pub fn enable() {
    let mut node = MCSNode::new();
    let mut c = CONSOLE.console.lock(&mut node);

    if let Some(console) = c.as_mut() {
        console.enable();
    }
}

/// Disable console.
pub fn disable() {
    let mut node = MCSNode::new();
    let mut c = CONSOLE.console.lock(&mut node);

    if let Some(console) = c.as_mut() {
        console.disable();
    }
}

/// Enable the reception interrupt.
pub fn enable_recv_interrupt() {
    let mut node = MCSNode::new();
    let mut c = CONSOLE.console.lock(&mut node);

    if let Some(console) = c.as_mut() {
        console.enable_recv_interrupt();
    }
}

/// Disable the reception interrupt.
pub fn disable_recv_interrupt() {
    let mut node = MCSNode::new();
    let mut c = CONSOLE.console.lock(&mut node);

    if let Some(console) = c.as_mut() {
        console.disable_recv_interrupt();
    }
}

/// Acknowledge to the reception interrupt.
pub fn acknowledge_recv_interrupt() {
    let mut node = MCSNode::new();
    let mut c = CONSOLE.console.lock(&mut node);

    if let Some(console) = c.as_mut() {
        console.acknowledge_recv_interrupt();
    }
}

/// Get IRQ#.
pub fn irq_id() -> Option<u16> {
    let mut node = MCSNode::new();
    let c = CONSOLE.console.lock(&mut node);

    c.as_ref().map(|console| console.irq_id())
}

/// Read a byte.
pub fn get() -> Option<u8> {
    let mut node = MCSNode::new();
    let mut c = CONSOLE.console.lock(&mut node);

    if let Some(console) = c.as_mut() {
        console.get()
    } else {
        None
    }
}

/// Write a byte.
pub fn put(data: u8) {
    let mut node = MCSNode::new();
    let mut c = CONSOLE.console.lock(&mut node);

    if let Some(console) = c.as_mut() {
        console.put(data);
    }
}

/// Write a string.
pub fn print(data: &str) {
    let mut node = MCSNode::new();
    let mut c = CONSOLE.console.lock(&mut node);

    if let Some(console) = c.as_mut() {
        let _ = console.write_str(data);
    }
}
