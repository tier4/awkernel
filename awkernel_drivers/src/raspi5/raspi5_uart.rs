use core::ptr::{read_volatile, write_volatile};

const DEFAULTBAUD: u32 = 115200;
const CLOCKRATE: u32 = 44_000_000;

pub struct Uart {
    base_addr: usize,
}

impl Uart {
    /// Creates a new `Uart` instance.
    ///
    /// # Arguments
    /// * `base_addr` - The base address of the UART hardware registers.
    ///
    /// # Returns
    /// A new instance of `Uart`.
    pub fn new(base_addr: usize) -> Self {
        Self { base_addr }
    }

    /// Initializes the UART interface.
    /// This method sets up baud rate, clock rate, and data format for UART communication.
    pub fn init(&self) {
        let n_baudrate = DEFAULTBAUD;
        let n_clock_rate = CLOCKRATE;
        let n_baud16 = n_baudrate * 16;
        let n_int_div = n_clock_rate / n_baud16;
        let n_fract_div = ((n_clock_rate % n_baud16) * 64 + n_baudrate / 2) / n_baudrate;

        unsafe {
            let cr = self.base_addr + 0x30;
            let imsc = self.base_addr + 0x38;
            let icr = self.base_addr + 0x44;
            let ibrd = self.base_addr + 0x24;
            let fbrd = self.base_addr + 0x28;
            let lcrh = self.base_addr + 0x2C;

            // Disable all interrupts.
            write_volatile(imsc as *mut u32, 0);
            // Clear all interrupt flags.
            write_volatile(icr as *mut u32, 0x7FF);
            // Set integer baud rate divisor.
            write_volatile(ibrd as *mut u32, n_int_div);
            // Set fractional baud rate divisor.
            write_volatile(fbrd as *mut u32, n_fract_div);
            // Set data format: 8 data bits, no parity bit, 1 stop bit.
            write_volatile(lcrh as *mut u32, (1 << 4) | (3 << 5));
            // Enable UART, allow sending and receiving.
            write_volatile(cr as *mut u32, (1 << 0) | (1 << 8) | (1 << 9));
        }
    }

    /// Sends a single byte of data through UART.
    ///
    /// # Arguments
    /// * `c` - The character (byte) to send.
    fn send(&self, c: u8) {
        let dr = self.base_addr;
        let fr = self.base_addr + 0x18;
        unsafe {
            // Wait for the send buffer to be empty.
            while read_volatile(fr as *const u32) & 0x20 != 0 {}
            // Send data.
            write_volatile(dr as *mut u32, c as u32);
        }
    }

    /// Receives a single byte of data through UART.
    ///
    /// # Returns
    /// The received character (byte).
    #[allow(dead_code)]
    fn recv(&self) -> u8 {
        let dr = self.base_addr;
        let fr = self.base_addr + 0x18;
        unsafe {
            // Wait to receive data.
            while read_volatile(fr as *const u32) & 0x10 != 0 {}
            // Read received data.
            read_volatile(dr as *const u32) as u8
        }
    }

    /// Sends a string of data through UART, one byte at a time.
    ///
    /// # Arguments
    /// * `s` - The string to send.
    pub fn send_string(&self, s: &str) {
        for c in s.bytes() {
            self.send(c);
        }
    }
}
