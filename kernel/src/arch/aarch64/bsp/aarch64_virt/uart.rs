use awkernel_drivers::uart::pl011::PL011;
use awkernel_lib::console::register_unsafe_puts;
use core::{
    fmt::Write,
    ptr::{addr_of_mut, write_volatile},
};

use crate::arch::config::UART_BAUDRATE;

static mut UART0_BASE: usize = 0;
static mut UART_IRQ: u16 = 0;
static mut UART_CLOCK: usize = 0;

pub unsafe fn init(base: usize, irq: u16, clock: usize) {
    write_volatile(&mut *addr_of_mut!(UART0_BASE), base);
    write_volatile(&mut *addr_of_mut!(UART_IRQ), irq);
    write_volatile(&mut *addr_of_mut!(UART_CLOCK), clock);

    let pl011 = PL011::new(base, irq);
    pl011.init_device(clock, UART_BAUDRATE);

    register_unsafe_puts(unsafe_puts);
}

pub unsafe fn unsafe_puts(data: &str) {
    let mut pl011 = PL011::new(UART0_BASE, UART_IRQ);
    let _ = pl011.write_str(data);
}
