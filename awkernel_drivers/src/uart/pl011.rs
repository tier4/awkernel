use awkernel_lib::console::Console;
use core::{arch::asm, fmt::Write};

pub struct PL011 {
    base_addr: usize,
    irq: u16,
}

mod registers {
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

    mmio_rw!(offset 0x000 => pub UART0_DR<u32>);
    mmio_rw!(offset 0x018 => pub UART0_FR<u32>);
    mmio_rw!(offset 0x020 => pub UART0_ILPR<u32>);
    mmio_rw!(offset 0x024 => pub UART0_IBRD<u32>);
    mmio_rw!(offset 0x028 => pub UART0_FBRD<u32>);
    mmio_rw!(offset 0x02c => pub UART0_LCR_H<u32>);
    mmio_rw!(offset 0x030 => pub UART0_CR<CR>);
    mmio_rw!(offset 0x034 => pub UART0_IFLS<u32>);
    mmio_rw!(offset 0x038 => pub UART0_IMSC<u32>);
    mmio_r! (offset 0x03c => pub UART0_RIS<u32>);
    mmio_r! (offset 0x040 => pub UART0_MIS<u32>);
    mmio_w! (offset 0x044 => pub UART0_ICR<ICR>);
    mmio_rw!(offset 0x048 => pub UART0_DMACR<u32>);
}

const IMSC_RXIM: u32 = 1 << 4;

impl PL011 {
    pub fn new(base_addr: usize, irq: u16) -> Self {
        Self { base_addr, irq }
    }

    pub unsafe fn unsafe_puts(&self, data: &str) {
        for c in data.bytes() {
            self.putc(c as u32);
            if c == b'\n' {
                self.putc(b'\r' as u32);
            }
        }
    }

    /// Initialiaze UART0 for serial console.
    /// Set baud rate and characteristics (8N1) and map to GPIO 14 (Tx) and 15 (Rx).
    /// 8N1 stands for "eight data bits, no parity, one stop bit".
    pub unsafe fn init_device(&self, uart_clock: usize, baudrate: usize) {
        let bauddiv: u32 = ((1000 * uart_clock) / (16 * baudrate)) as u32;
        let ibrd: u32 = bauddiv / 1000;
        let fbrd: u32 = ((bauddiv - ibrd * 1000) * 64 + 500) / 1000;

        registers::UART0_ICR.write(registers::ICR::all(), self.base_addr); // clear interrupts
        registers::UART0_IBRD.write(ibrd, self.base_addr);
        registers::UART0_FBRD.write(fbrd, self.base_addr);

        registers::UART0_LCR_H.write(
            registers::LCR_H_WLEN_8BITS | registers::LCR_H_FEN_FIFO,
            self.base_addr,
        ); // 8n1, FIFO
        registers::UART0_IFLS.write(registers::IFLS_RXIFLSEL_1_8, self.base_addr);
    }

    unsafe fn putc(&self, c: u32) {
        // wait until we can send
        unsafe { asm!("nop;") };
        while registers::UART0_FR.read(self.base_addr) & 0x20 != 0 {
            unsafe { asm!("nop;") };
        }

        // write the character to the buffer
        registers::UART0_DR.write(c, self.base_addr);
    }
}

impl Write for PL011 {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        unsafe { self.unsafe_puts(s) };
        Ok(())
    }
}

impl Console for PL011 {
    fn enable(&mut self) {
        use registers::CR;
        registers::UART0_CR.write(CR::EN | CR::RXE | CR::TXE, self.base_addr); // enable, Rx, Tx
    }

    fn disable(&mut self) {
        registers::UART0_CR.write(registers::CR::empty(), self.base_addr);
    }

    fn enable_recv_interrupt(&mut self) {
        registers::UART0_IMSC.setbits(IMSC_RXIM, self.base_addr);
    }

    fn disable_recv_interrupt(&mut self) {
        registers::UART0_IMSC.clrbits(IMSC_RXIM, self.base_addr);
    }

    fn acknowledge_recv_interrupt(&mut self) {
        registers::UART0_ICR.write(registers::ICR::RXIC, self.base_addr);
    }

    fn irq_id(&self) -> u16 {
        self.irq
    }

    fn get(&mut self) -> Option<u8> {
        if registers::UART0_FR.read(self.base_addr) & 0x10 != 0 {
            None
        } else {
            Some(registers::UART0_DR.read(self.base_addr) as u8)
        }
    }

    fn put(&mut self, data: u8) {
        unsafe { self.putc(data as u32) };
    }
}
