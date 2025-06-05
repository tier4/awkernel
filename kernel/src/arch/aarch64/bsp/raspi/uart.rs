use crate::{
    arch::aarch64::bsp::memory::*,
    config::{UART_BAUDRATE, UART_CLOCK},
};
use awkernel_drivers::uart::pl011::PL011;
use awkernel_lib::console::Console;
use core::{arch::asm, fmt::Write};

static mut UART0_BASE: usize = 0;
static mut UART_IRQ: u16 = 0;

pub fn init(uart_base_addr: usize, gpio_base_addr: usize, irq: u16) -> impl Console {
    let mut pl011 = PL011::new(uart_base_addr, irq);

    pl011.disable();

    // map UART1 to GPIO pins
    let mut r = GPFSEL1.read(gpio_base_addr);
    r &= !((7 << 12) | (7 << 15)); // gpio14, gpio15
    r |= (4 << 12) | (4 << 15); // alt0

    // enable pins 14 and 15
    GPFSEL1.write(r, gpio_base_addr);
    GPPUD.write(0, gpio_base_addr);

    wait_cycles(150);

    GPPUDCLK0.write((1 << 14) | (1 << 15), gpio_base_addr);

    wait_cycles(150);

    unsafe { pl011.init_device(UART_CLOCK, UART_BAUDRATE) };

    pl011.enable();

    unsafe {
        UART0_BASE = uart_base_addr;
        UART_IRQ = irq;
    }

    pl011
}

pub unsafe fn unsafe_puts(data: &str) {
    let mut pl011 = PL011::new(UART0_BASE, UART_IRQ);
    let _ = pl011.write_str(data);
}

/// Wait N CPU cycles
fn wait_cycles(n: usize) {
    if n > 0 {
        for _ in 0..n {
            unsafe { asm!("nop;") };
        }
    }
}
