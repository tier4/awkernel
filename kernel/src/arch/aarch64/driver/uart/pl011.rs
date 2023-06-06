use crate::arch::aarch64::bsp::memory::*;
use awkernel_lib::console::Console;
use core::{arch::asm, fmt::Write};

pub struct PL011 {
    irq: usize,
}

mod registers {
    use crate::arch::aarch64::bsp::memory::UART0_BASE;
    use awkernel_lib::{mmio_r, mmio_rw, mmio_w};
    use bitflags::bitflags;

    bitflags! {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct CR: u32 {
            const EN  = 1;
            const TXE = 1 << 8;
            const RXE = 1 << 9;
        }

        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct ICR: u32 {
            const RIMIC  = 0b0000_0000_0001; // nUARTRI modem interrupt clear. Clears the UARTRIINTR interrupt
            const CTSMIC = 0b0000_0000_0010; // nUARTCTS modem interrupt clear. Clears the UARTCTSINTR interrupt
            const DCDMIC = 0b0000_0000_0100; // nUARTDCD modem interrupt clear. Clears the UARTDCDINTR interrupt
            const DSRMIC = 0b0000_0000_1000; // nUARTDSR modem interrupt clear. Clears the UARTDSRINTR interrupt
            const RXIC   = 0b0000_0001_0000; // Receive interrupt clear. Clears the UARTRXINTR interrupt
            const TXIC   = 0b0000_0010_0000; // Transmit interrupt clear. Clears the UARTTXINTR interrupt
            const RTIC   = 0b0000_0100_0000; // Receive timeout interrupt clear. Clears the UARTRTINTR interrupt
            const FEIC   = 0b0000_1000_0000; // Framing error interrupt clear. Clears the UARTFEINTR interrupt
            const PEIC   = 0b0001_0000_0000; // Parity error interrupt clear. Clears the UARTPEINTR interrupt
            const BEIC   = 0b0010_0000_0000; // Break error interrupt clear. Clears the UARTBEINTR interrupt
            const OEIC   = 0b0100_0000_0000; // Overrun error interrupt clear. Clears the UARTOEINTR interrupt
        }
    }

    pub const IFLS_RXIFLSEL_1_8: u32 = 0b000; // Receive FIFO becomes >= 1/8 full
    pub const _IFLS_RXIFLSEL_1_4: u32 = 0b001 << 3; // Receive FIFO becomes >= 1/4 full
    pub const _IFLS_RXIFLSEL_1_2: u32 = 0b010 << 3; // Receive FIFO becomes >= 1/2 full
    pub const _IFLS_RXIFLSEL_3_4: u32 = 0b011 << 3; // 011 = Receive FIFO becomes >= 3/4 full
    pub const _IFLS_RXIFLSEL_7_8: u32 = 0b100 << 3; // Receive FIFO becomes >= 7/8 full

    pub const LCR_H_WLEN_8BITS: u32 = 0b11 << 5; // Word length (8bits)
    pub const LCR_H_FEN_FIFO: u32 = 1 << 4; // Enable FIFOs

    mmio_rw!(UART0_BASE         => pub UART0_DR<u32>);
    mmio_rw!(UART0_BASE + 0x018 => pub UART0_FR<u32>);
    mmio_rw!(UART0_BASE + 0x020 => pub UART0_ILPR<u32>);
    mmio_rw!(UART0_BASE + 0x024 => pub UART0_IBRD<u32>);
    mmio_rw!(UART0_BASE + 0x028 => pub UART0_FBRD<u32>);
    mmio_rw!(UART0_BASE + 0x02c => pub UART0_LCR_H<u32>);
    mmio_rw!(UART0_BASE + 0x030 => pub UART0_CR<CR>);
    mmio_rw!(UART0_BASE + 0x034 => pub UART0_IFLS<u32>);
    mmio_rw!(UART0_BASE + 0x038 => pub UART0_IMSC<u32>);
    mmio_r! (UART0_BASE + 0x03c => pub UART0_RIS<u32>);
    mmio_r! (UART0_BASE + 0x040 => pub UART0_MIS<u32>);
    mmio_w! (UART0_BASE + 0x044 => pub UART0_ICR<ICR>);
    mmio_rw!(UART0_BASE + 0x048 => pub UART0_DMACR<u32>);
}

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
    pub fn new(irq: usize) -> Self {
        Self { irq }
    }

    pub unsafe fn unsafe_puts(data: &str) {
        for c in data.bytes() {
            Self::putc(c as u32);
            if c == b'\n' {
                Self::putc(b'\r' as u32);
            }
        }
    }

    /// Initialiaze UART0 for serial console.
    /// Set baud rate and characteristics (8N1) and map to GPIO 14 (Tx) and 15 (Rx).
    /// 8N1 stands for "eight data bits, no parity, one stop bit".
    pub unsafe fn init_device(uart_clock: usize, baudrate: usize) {
        registers::UART0_CR.write(registers::CR::empty()); // turn off UART0

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
        registers::UART0_ICR.write(registers::ICR::all()); // clear interrupts
        registers::UART0_IBRD.write(ibrd);
        registers::UART0_FBRD.write(fbrd);

        registers::UART0_LCR_H.write(registers::LCR_H_WLEN_8BITS | registers::LCR_H_FEN_FIFO); // 8n1, FIFO
        registers::UART0_IFLS.write(registers::IFLS_RXIFLSEL_1_8); // RX FIFO fill level at 1/8

        // enable, Rx, Tx
        registers::UART0_CR.write(registers::CR::EN | registers::CR::RXE | registers::CR::TXE);
    }

    unsafe fn putc(c: u32) {
        // wait until we can send
        unsafe { asm!("nop;") };
        while registers::UART0_FR.read() & 0x20 != 0 {
            unsafe { asm!("nop;") };
        }

        // write the character to the buffer
        registers::UART0_DR.write(c);
    }
}

impl Write for PL011 {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        unsafe { Self::unsafe_puts(s) };
        Ok(())
    }
}

impl Console for PL011 {
    fn enable(&mut self) {
        use registers::CR;
        registers::UART0_CR.write(CR::EN | CR::RXE | CR::TXE); // enable, Rx, Tx
    }

    fn disable(&mut self) {
        registers::UART0_CR.write(registers::CR::empty());
    }

    fn enable_recv_interrupt(&mut self) {
        registers::UART0_IMSC.setbits(IMSC_RXIM);
    }

    fn disable_recv_interrupt(&mut self) {
        registers::UART0_IMSC.clrbits(IMSC_RXIM);
    }

    fn acknowledge_recv_interrupt(&mut self) {
        registers::UART0_ICR.write(registers::ICR::RXIC);
    }

    fn irq_id(&self) -> usize {
        self.irq
    }

    fn get(&mut self) -> Option<u8> {
        if registers::UART0_FR.read() & 0x10 != 0 {
            None
        } else {
            Some(registers::UART0_DR.read() as u8)
        }
    }

    fn put(&mut self, data: u8) {
        unsafe { Self::putc(data as u32) };
    }
}
