//! # UART's device driver for Raspberry Pi.
//!
//! Raspberry Pi 4 has 6 UARTs.
//! UART0 is dedicated to the console, while UART2 to UART5 are available for user applications.
//! Both UART0 and UART1 utilize GPIO14 for Tx (transmit) and GPIO15 for Rx (receive).
//! Consequently, Awkernel does not use UART1.
//!
//! The table below outlines the GPIO pins associated with each UART and their availability on the Raspberry Pi 3 and 4 models.
//!
//! | UART | Tx | Rx | Rpi3 | Rpi4 |
//! |------|----|----|------|------|
//! | 0/1  | 14 | 15 | ✓    | ✓    |
//! | 2    |  0 |  1 |      | ✓    |
//! | 3    |  4 |  5 |      | ✓    |
//! | 4    |  8 |  9 |      | ✓    |
//! | 5    | 12 | 13 |      | ✓    |
//!
//! ## Example
//!
//! The following example shows how to use UART2.
//!
//! ```
//! use awkernel_drivers::hal::raspi::uart::{Uart, Uarts};
//! use embedded_hal_nb::serial::{Read, Write};
//!
//! pub async fn test_uart2() {
//!     let mut uart2 = Uart::new(Uarts::Uart2, 230400).unwrap();
//!     let (tx2, rx2) = uart2.get_gpio_pins(); // Get the GPIO pins for UART2.
//!
//!     let write_buf = b"Hello, world!\r\n";
//!
//!     for data in write_buf.iter() {
//!         uart2.write(*data).unwrap();
//!     }
//!
//!     loop {
//!         if let Ok(data) = uart2.read() {
//!             let _ = uart2.write(data);
//!         }
//!         awkernel_async_lib::sleep(Duration::from_millis(5)).await;
//!     }
//! }
//! ```

use core::sync::atomic::{AtomicUsize, Ordering};

use awkernel_lib::{
    console::Console,
    sync::mutex::{MCSNode, Mutex},
};

use crate::{hal::raspi::gpio::GpioPin, uart::pl011::PL011};

use super::gpio::{GpioFunction, GpioPinAlt, PullMode};

#[derive(Debug)]
pub struct Uart {
    _tx: GpioPinAlt,
    _rx: GpioPinAlt,
    pl011: PL011,
    uarts: Uarts,
    pin: PinUart,
}

#[derive(Debug)]
pub enum Uarts {
    Uart2,
    Uart3,
    Uart4,
    Uart5,
}

impl From<u32> for Uarts {
    fn from(value: u32) -> Self {
        match value {
            2 => Uarts::Uart2,
            3 => Uarts::Uart3,
            4 => Uarts::Uart4,
            5 => Uarts::Uart5,
            _ => panic!("Invalid Uart"),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Pin {
    pin: u32,
    alt: GpioFunction,
    bias: PullMode,
}

impl Pin {
    pub fn new(pin: u32, alt: GpioFunction, bias: PullMode) -> Self {
        Self { pin, alt, bias }
    }
}

#[derive(Debug, Clone)]
pub struct PinUart {
    tx: Pin,
    rx: Pin,

    irq: u16,
    base_addr: usize,
}

impl PinUart {
    pub fn new(tx: Pin, rx: Pin, irq: u16, base_addr: usize) -> Self {
        Self {
            tx,
            rx,
            irq,
            base_addr,
        }
    }
}

#[derive(Debug)]
struct UartsInfo {
    uart2: Option<PinUart>,
    uart3: Option<PinUart>,
    uart4: Option<PinUart>,
    uart5: Option<PinUart>,
}

static UARTS_INFO: Mutex<UartsInfo> = Mutex::new(UartsInfo::new());
static UART_CLOCK: AtomicUsize = AtomicUsize::new(0);

impl UartsInfo {
    const fn new() -> Self {
        UartsInfo {
            uart2: None,
            uart3: None,
            uart4: None,
            uart5: None,
        }
    }
}

/// Set the UARTs pins.
///
/// # Safety
///
/// These information must be correct.
/// It means that the information must be the same as the one in the device tree.
pub unsafe fn set_uart_info(uarts: Uarts, pin: PinUart) {
    let mut node = MCSNode::new();
    let mut guard = UARTS_INFO.lock(&mut node);

    let pin = Some(pin);

    match uarts {
        Uarts::Uart2 => {
            guard.uart2 = pin;
        }
        Uarts::Uart3 => {
            guard.uart3 = pin;
        }
        Uarts::Uart4 => {
            guard.uart4 = pin;
        }
        Uarts::Uart5 => {
            guard.uart5 = pin;
        }
    }
}

/// Set UART's clock.
///
/// # Safety
///
/// This function must be called before any UART is initialized.
/// The clock must be the same as the one in the device tree.
pub unsafe fn set_uart_clock(clock: usize) {
    UART_CLOCK.store(clock, Ordering::Relaxed);
}

#[derive(Debug)]
pub enum UartError {
    InUse,
}

impl Uart {
    pub fn new(uarts: Uarts, baudrate: usize) -> Result<Self, UartError> {
        let mut node = MCSNode::new();
        let mut guard = UARTS_INFO.lock(&mut node);

        let pin = match uarts {
            Uarts::Uart2 => guard.uart2.take().ok_or(UartError::InUse)?,
            Uarts::Uart3 => guard.uart3.take().ok_or(UartError::InUse)?,
            Uarts::Uart4 => guard.uart4.take().ok_or(UartError::InUse)?,
            Uarts::Uart5 => guard.uart5.take().ok_or(UartError::InUse)?,
        };

        let tx = GpioPin::new(pin.tx.pin)
            .or(Err(UartError::InUse))?
            .into_alt(pin.tx.alt, pin.tx.bias)
            .unwrap();
        let rx = GpioPin::new(pin.rx.pin)
            .or(Err(UartError::InUse))?
            .into_alt(pin.rx.alt, pin.rx.bias)
            .unwrap();

        let mut pl011 = PL011::new(pin.base_addr, pin.irq);

        unsafe { pl011.init_device(UART_CLOCK.load(Ordering::Relaxed), baudrate) };

        pl011.enable();

        let uart = Uart {
            _tx: tx,
            _rx: rx,
            pin,
            pl011,
            uarts,
        };

        Ok(uart)
    }

    pub fn get_gpio_pins(&self) -> (u32, u32) {
        (self.pin.tx.pin, self.pin.rx.pin)
    }

    pub fn get_irq(&self) -> u16 {
        self.pin.irq
    }
}

impl Drop for Uart {
    fn drop(&mut self) {
        self.pl011.disable();

        let mut node = MCSNode::new();
        let mut guard = UARTS_INFO.lock(&mut node);

        match self.uarts {
            Uarts::Uart2 => guard.uart2 = Some(self.pin.clone()),
            Uarts::Uart3 => guard.uart3 = Some(self.pin.clone()),
            Uarts::Uart4 => guard.uart4 = Some(self.pin.clone()),
            Uarts::Uart5 => guard.uart5 = Some(self.pin.clone()),
        }
    }
}

impl embedded_hal_nb::serial::Error for UartError {
    fn kind(&self) -> embedded_hal_nb::serial::ErrorKind {
        match self {
            UartError::InUse => embedded_hal_nb::serial::ErrorKind::Other,
        }
    }
}

impl embedded_hal_nb::serial::ErrorType for Uart {
    type Error = UartError;
}

impl embedded_hal_nb::serial::Read for Uart {
    fn read(&mut self) -> embedded_hal_nb::nb::Result<u8, Self::Error> {
        self.pl011
            .get()
            .ok_or(embedded_hal_nb::nb::Error::WouldBlock)
    }
}

impl embedded_hal_nb::serial::Write for Uart {
    fn write(&mut self, word: u8) -> embedded_hal_nb::nb::Result<(), Self::Error> {
        self.pl011.put(word);
        Ok(())
    }

    fn flush(&mut self) -> embedded_hal_nb::nb::Result<(), Self::Error> {
        Ok(())
    }
}
