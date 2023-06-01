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
