use core::sync::atomic::{AtomicUsize, Ordering};

use awkernel_lib::{
    console::Console,
    sync::mutex::{MCSNode, Mutex},
};

use crate::{hal::rpi::gpio::GpioPin, uart::pl011::PL011};

use super::gpio::{GpioFunction, GpioPinAlt, PullMode};

#[derive(Debug)]
pub struct Uart {
    _tx: GpioPinAlt,
    _rx: GpioPinAlt,
    pl011: PL011,
    uarts: Uarts,
    pin: Pin,
}

#[derive(Debug)]
pub enum Uarts {
    Uart2,
    Uart3,
    Uart4,
    Uart5,
}

#[derive(Debug, Clone)]
pub struct Pin {
    tx_pin: u32,
    tx_alt: super::gpio::GpioFunction,
    tx_bias: PullMode,

    rx_pin: u32,
    rx_alt: super::gpio::GpioFunction,
    rx_bias: PullMode,

    irq: u16,
    base_addr: usize,
}

#[derive(Debug)]
struct UartsInfo {
    uart2: Option<Pin>,
    uart3: Option<Pin>,
    uart4: Option<Pin>,
    uart5: Option<Pin>,
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

pub unsafe fn set_uart_info(
    uarts: Uarts,
    tx_pin: u32,
    tx_alt: GpioFunction,
    tx_bias: PullMode,
    rx_pin: u32,
    rx_alt: GpioFunction,
    rx_bias: PullMode,
    irq: u16,
    base_addr: usize,
) {
    let mut node = MCSNode::new();
    let mut guard = UARTS_INFO.lock(&mut node);

    let pin = Some(Pin {
        tx_pin,
        tx_alt,
        tx_bias,
        rx_pin,
        rx_alt,
        rx_bias,
        irq,
        base_addr,
    });

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

pub unsafe fn set_uart_clock(clock: usize) {
    UART_CLOCK.store(clock, Ordering::Relaxed);
}

#[derive(Debug)]
pub enum UartError {
    InUse,
}

impl embedded_io::Error for UartError {
    fn kind(&self) -> embedded_io::ErrorKind {
        match self {
            UartError::InUse => embedded_io::ErrorKind::AddrInUse,
        }
    }
}

impl Uart {
    fn new(uarts: Uarts, baudrate: usize) -> Result<Self, UartError> {
        let mut node = MCSNode::new();
        let mut guard = UARTS_INFO.lock(&mut node);

        let pin = match uarts {
            Uarts::Uart2 => guard.uart2.take().ok_or(UartError::InUse)?,
            Uarts::Uart3 => guard.uart3.take().ok_or(UartError::InUse)?,
            Uarts::Uart4 => guard.uart4.take().ok_or(UartError::InUse)?,
            Uarts::Uart5 => guard.uart5.take().ok_or(UartError::InUse)?,
        };

        let tx = GpioPin::new(pin.tx_pin)
            .or(Err(UartError::InUse))?
            .into_alt(pin.tx_alt, pin.tx_bias)
            .unwrap();
        let rx = GpioPin::new(pin.rx_pin)
            .or(Err(UartError::InUse))?
            .into_alt(pin.tx_alt, pin.rx_bias)
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

impl embedded_io::ErrorType for Uart {
    type Error = UartError;
}

impl embedded_io::Read for Uart {
    fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        for (i, ref_buf) in buf.iter_mut().enumerate() {
            if let Some(c) = self.pl011.get() {
                *ref_buf = c;
            } else {
                return Ok(i + 1);
            }
        }

        Ok(buf.len())
    }
}

impl embedded_io::Write for Uart {
    fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        for &c in buf.iter() {
            self.pl011.put(c);
        }

        Ok(buf.len())
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}
