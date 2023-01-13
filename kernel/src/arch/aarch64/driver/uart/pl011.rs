use crate::arch::aarch64::bsp::memory::*;
use core::{arch::asm, fmt::Write};
use t4os_lib::mmio_rw;

use super::UART;

pub struct RaspiUART {}

const UART0_BASE: usize = MMIO_BASE + 0x00201000;

mmio_rw!(UART0_BASE         => uart0_dr<u32>);
mmio_rw!(UART0_BASE + 0x004 => uart0_rsrecr<u32>);
mmio_rw!(UART0_BASE + 0x018 => uart0_fr<u32>);
mmio_rw!(UART0_BASE + 0x020 => uart0_ilpr<u32>);
mmio_rw!(UART0_BASE + 0x024 => uart0_ibrd<u32>);
mmio_rw!(UART0_BASE + 0x028 => uart0_fbrd<u32>);
mmio_rw!(UART0_BASE + 0x02c => uart0_lcrh<u32>);
mmio_rw!(UART0_BASE + 0x030 => uart0_cr<u32>);
mmio_rw!(UART0_BASE + 0x034 => uart0_ifls<u32>);
mmio_rw!(UART0_BASE + 0x038 => uart0_imsc<u32>);
mmio_rw!(UART0_BASE + 0x03c => uart0_ris<u32>);
mmio_rw!(UART0_BASE + 0x040 => uart0_mis<u32>);
mmio_rw!(UART0_BASE + 0x044 => uart0_icr<u32>);
mmio_rw!(UART0_BASE + 0x048 => uart0_dmacr<u32>);

const CR_RXE: u32 = 1 << 9;
const CR_TXE: u32 = 1 << 8;
const CR_EN: u32 = 1;

const ICR_ALL_CLEAR: u32 = 0x7ff;

const LCRH_WLEN_8BITS: u32 = 0b11 << 5; // Word length (8bits)
const LCRH_FEN_FIFO: u32 = 1 << 4; // Enable FIFOs

const IFLS_RXIFLSEL_1_8: u32 = 0b000;
const IFLS_RXIFLSEL_1_4: u32 = 0b001 << 3;
const IFLS_RXIFLSEL_1_2: u32 = 0b010 << 3;
const IFLS_RXIFLSEL_3_4: u32 = 0b011 << 3;
const IFLS_RXIFLSEL_7_8: u32 = 0b100 << 3;

const IMSC_RXIM: u32 = 1 << 4;

/// Wait N CPU cycles
fn wait_cycles(n: usize) {
    if n > 0 {
        for _ in 0..n {
            unsafe { asm!("nop;") };
        }
    }
}

impl RaspiUART {
    unsafe fn putc(c: u32) {
        // wait until we can send
        unsafe { asm!("nop;") };
        while uart0_fr().read() & 0x20 != 0 {
            unsafe { asm!("nop;") };
        }

        // write the character to the buffer
        uart0_dr().write(c);
    }
}

impl super::UART for RaspiUART {
    /// Initialiaze UART0 for serial console.
    /// Set baud rate and characteristics (8N1) and map to GPIO 14 (Tx) and 15 (Rx).
    /// 8N1 stands for "eight data bits, no parity, one stop bit".
    fn init(uart_clock: usize, baudrate: usize) {
        uart0_cr().write(0); // turn off UART0

        // map UART1 to GPIO pins
        let mut r = gpfsel1().read();
        r &= !((7 << 12) | (7 << 15)); // gpio14, gpio15
        r |= (4 << 12) | (4 << 15); // alt0

        // enable pins 14 and 15
        gpfsel1().write(r);
        gppud().write(0);

        wait_cycles(150);

        gppudclk0().write((1 << 14) | (1 << 15));

        wait_cycles(150);

        let bauddiv: u32 = ((1000 * uart_clock) / (16 * baudrate)) as u32;
        let ibrd: u32 = bauddiv / 1000;
        let fbrd: u32 = ((bauddiv - ibrd * 1000) * 64 + 500) / 1000;

        gppudclk0().write(0); // flush GPIO setup
        uart0_icr().write(ICR_ALL_CLEAR); // clear interrupts
        uart0_ibrd().write(ibrd);
        uart0_fbrd().write(fbrd);

        uart0_lcrh().write(LCRH_WLEN_8BITS | LCRH_FEN_FIFO); // 8n1, FIFO
        uart0_ifls().write(IFLS_RXIFLSEL_1_4); // RX FIFO fill level at 1/4
        uart0_cr().write(CR_EN | CR_RXE | CR_TXE); // enable, Rx, Tx
    }

    /// send a character to serial console
    fn send(&self, c: u32) {
        unsafe { Self::putc(c) };
    }

    fn recv(&self) -> u32 {
        // wait until something is in the buffer
        unsafe { asm!("nop;") };
        while uart0_fr().read() & 0x10 != 0 {
            unsafe { asm!("nop;") };
        }

        uart0_dr().read()
    }

    fn enable_recv_interrupt(&self) {
        //uart0_imsc().setbits(IMSC_RXIM);
    }

    fn disable_recv_interrupt(&self) {
        uart0_imsc().clrbits(IMSC_RXIM);
    }

    fn on(&self) {}
    fn off(&self) {}
    fn new(_base: usize) -> Self {
        Self {}
    }

    unsafe fn unsafe_puts(data: &str) {
        for c in data.bytes() {
            Self::putc(c as u32);
            if c == b'\n' {
                Self::putc(b'\r' as u32);
            }
        }
    }
}

impl Write for RaspiUART {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        self.puts(s);
        Ok(())
    }
}
