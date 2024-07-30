use crate::config::{UART_BAUDRATE, UART_CLOCK};
use awkernel_drivers::uart::pl011::PL011;
use awkernel_lib::console::Console;
use core::{arch::asm, fmt::Write};

const ARM_IO_BASE: usize = 0x0010_7C00_0000;

static UART0_BASE: usize = ARM_IO_BASE + 0x0100_1000;
static UART_IRQ: u16 = 0;

pub fn init() -> impl Console {
    let mut pl011 = PL011::new(UART0_BASE, UART_IRQ);

    pl011.disable();

    wait_cycles(150);

    unsafe { pl011.init_device(UART_CLOCK, UART_BAUDRATE) };

    pl011.enable();

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
