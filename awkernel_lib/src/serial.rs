use core::fmt::Write;

pub const BAUDRATE: u32 = 115200;

pub trait Serial: Write {
    /// Print raw data.
    unsafe fn raw_puts(data: &str);

    /// Enable the serial port.
    fn enable(&mut self);

    /// Disable the serial port.
    fn disable(&mut self);

    /// Enable the reception interrupt.
    fn enable_recv_interrupt(&mut self);

    /// Disable the reception interrupt.
    fn disable_recv_interrupt(&mut self);
}
