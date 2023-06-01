use core::ptr::write_volatile;

pub trait Console {
    /// Enable the serial port.
    fn enable(&self);

    /// Disable the serial port.
    fn disable(&self);

    /// Enable the reception interrupt.
    fn enable_recv_interrupt(&self);

    /// Disable the reception interrupt.
    fn disable_recv_interrupt(&self);
}

static mut UNSAFE_PUTS: Option<unsafe fn(&str)> = None;

pub fn register_unsafe_puts(console: unsafe fn(&str)) {
    unsafe { write_volatile(&mut UNSAFE_PUTS, Some(console)) }
}

pub unsafe fn unsafe_puts(data: &str) {
    if let Some(console) = UNSAFE_PUTS {
        console(data);
    }
}

static mut CONSOLE: Option<&'static dyn Console> = None;

pub fn register_console(console: &'static dyn Console) {
    unsafe { write_volatile(&mut CONSOLE, Some(console)) };
}

/// Enable console.
pub fn enable() {
    if let Some(console) = unsafe { &CONSOLE } {
        console.enable();
    }
}

/// Disable console.
pub fn disable() {
    if let Some(console) = unsafe { &CONSOLE } {
        console.disable();
    }
}

/// Enable the reception interrupt.
pub fn enable_recv_interrupt() {
    if let Some(console) = unsafe { &CONSOLE } {
        console.enable_recv_interrupt();
    }
}

/// Disable the reception interrupt.
pub fn disable_recv_interrupt() {
    if let Some(console) = unsafe { &CONSOLE } {
        console.disable_recv_interrupt();
    }
}
