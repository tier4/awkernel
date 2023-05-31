use crate::arch::aarch64::bsp::memory::*;
use alloc::vec::Vec;
use awkernel_lib::{mmio_rw, serial::Serial};
use core::{arch::asm, fmt::Write};

pub struct PL011;

const UART0_BASE: usize = MMIO_BASE + 0x00201000;

mmio_rw!(UART0_BASE         => UART0_DR<u32>);
mmio_rw!(UART0_BASE + 0x004 => UART0_RSRECR<u32>);
mmio_rw!(UART0_BASE + 0x018 => UART0_FR<u32>);
mmio_rw!(UART0_BASE + 0x020 => UART0_ILPR<u32>);
mmio_rw!(UART0_BASE + 0x024 => UART0_IBRD<u32>);
mmio_rw!(UART0_BASE + 0x028 => UART0_FBRD<u32>);
mmio_rw!(UART0_BASE + 0x02c => UART0_LCHR<u32>);
mmio_rw!(UART0_BASE + 0x030 => UART0_CR<u32>);
mmio_rw!(UART0_BASE + 0x034 => UART0_IFLS<u32>);
mmio_rw!(UART0_BASE + 0x038 => UART0_IMSC<u32>);
mmio_rw!(UART0_BASE + 0x03c => UART0_RIS<u32>);
mmio_rw!(UART0_BASE + 0x040 => UART0_MIS<u32>);
mmio_rw!(UART0_BASE + 0x044 => UART0_ICR<u32>);
mmio_rw!(UART0_BASE + 0x048 => UART0_DMACR<u32>);

const CR_RXE: u32 = 1 << 9;
const CR_TXE: u32 = 1 << 8;
const CR_EN: u32 = 1;

const ICR_ALL_CLEAR: u32 = 0x7ff;

const LCRH_WLEN_8BITS: u32 = 0b11 << 5; // Word length (8bits)
const LCRH_FEN_FIFO: u32 = 1 << 4; // Enable FIFOs

const _IFLS_RXIFLSEL_1_8: u32 = 0b000;
const IFLS_RXIFLSEL_1_4: u32 = 0b001 << 3;
const _IFLS_RXIFLSEL_1_2: u32 = 0b010 << 3;
const _IFLS_RXIFLSEL_3_4: u32 = 0b011 << 3;
const _IFLS_RXIFLSEL_7_8: u32 = 0b100 << 3;

const IMSC_RXIM: u32 = 1 << 4;

/// Wait N CPU cycles
fn wait_cycles(n: usize) {
    if n > 0 {
        for _ in 0..n {
            unsafe { asm!("nop;") };
        }
    }
}

impl PL011 {
    pub fn new() -> Self {
        PL011
    }

    /// Initialiaze UART0 for serial console.
    /// Set baud rate and characteristics (8N1) and map to GPIO 14 (Tx) and 15 (Rx).
    /// 8N1 stands for "eight data bits, no parity, one stop bit".
    pub unsafe fn init_device(uart_clock: usize, baudrate: usize) {
        UART0_CR.write(0); // turn off UART0

        // map UART1 to GPIO pins
        let mut r = GPFSEL1.read();
        r &= !((7 << 12) | (7 << 15)); // gpio14, gpio15
        r |= (4 << 12) | (4 << 15); // alt0

        // enable pins 14 and 15
        GPFSEL1.write(r);
        GPPUD.write(0);

        wait_cycles(150);

        GPPUDCLK0.write((1 << 14) | (1 << 15));

        wait_cycles(150);

        let bauddiv: u32 = ((1000 * uart_clock) / (16 * baudrate)) as u32;
        let ibrd: u32 = bauddiv / 1000;
        let fbrd: u32 = ((bauddiv - ibrd * 1000) * 64 + 500) / 1000;

        GPPUDCLK0.write(0); // flush GPIO setup
        UART0_ICR.write(ICR_ALL_CLEAR); // clear interrupts
        UART0_IBRD.write(ibrd);
        UART0_FBRD.write(fbrd);

        UART0_LCHR.write(LCRH_WLEN_8BITS | LCRH_FEN_FIFO); // 8n1, FIFO
        UART0_IFLS.write(IFLS_RXIFLSEL_1_4); // RX FIFO fill level at 1/4
        UART0_CR.write(CR_EN | CR_RXE | CR_TXE); // enable, Rx, Tx
    }

    unsafe fn putc(c: u32) {
        // wait until we can send
        unsafe { asm!("nop;") };
        while UART0_FR.read() & 0x20 != 0 {
            unsafe { asm!("nop;") };
        }

        // write the character to the buffer
        UART0_DR.write(c);
    }

    fn recv(&self) -> u32 {
        // wait until something is in the buffer
        unsafe { asm!("nop;") };
        while UART0_FR.read() & 0x10 != 0 {
            unsafe { asm!("nop;") };
        }

        UART0_DR.read()
    }

    fn send(&self, c: u32) {
        unsafe { Self::putc(c) }
    }

    #[allow(clippy::same_item_push)]
    fn _read_line(&self) -> Vec<u8> {
        let mut res = Vec::new();

        loop {
            let c = self.recv() as u8;
            if c == b'\r' || c == b'\n' {
                break;
            } else if c == 0x08 || c == 0x7F {
                if !res.is_empty() {
                    self.send(0x08);
                    self.send(b' ' as u32);
                    self.send(0x08);
                    res.pop();
                }
            } else if c == b'\t' {
                let c = b' ';
                for _ in 0..8 {
                    self.send(c as u32);
                    res.push(c);
                }
            } else if c == 0x15 {
                while !res.is_empty() {
                    self.send(0x08);
                    self.send(b' ' as u32);
                    self.send(0x08);
                    res.pop();
                }
            } else {
                self.send(c as u32);
                res.push(c);
            }
        }

        self.send('\n' as u32);

        res
    }
}

impl Write for PL011 {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        unsafe { Self::raw_puts(s) };
        Ok(())
    }
}

impl Serial for PL011 {
    unsafe fn raw_puts(data: &str) {
        for c in data.bytes() {
            Self::putc(c as u32);
            if c == b'\n' {
                Self::putc(b'\r' as u32);
            }
        }
    }

    fn enable(&mut self) {
        UART0_CR.write(CR_EN | CR_RXE | CR_TXE); // enable, Rx, Tx
    }

    fn disable(&mut self) {
        UART0_CR.write(0);
    }

    fn enable_recv_interrupt(&mut self) {
        UART0_IMSC.setbits(IMSC_RXIM);
    }

    fn disable_recv_interrupt(&mut self) {
        UART0_IMSC.clrbits(IMSC_RXIM);
    }
}
