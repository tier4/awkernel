/// Raspberry Pi SPI module
use super::gpio::{GpioFunction, GpioPin, GpioPinAlt, PullMode};
use core::sync::atomic::{AtomicUsize, Ordering};
use embedded_hal::spi::{Error, ErrorKind, ErrorType, SpiBus};

/// The base address of the SPI device
pub static SPI_BASE: AtomicUsize = AtomicUsize::new(0);

/// Sets the base address of the SPI device
///
/// # Safety
///
/// This function is unsafe because it writes to a mutable static
pub unsafe fn set_spi_base(base: usize) {
    SPI_BASE.store(base, Ordering::Relaxed);
}

/// SPI registers offset definitions
mod registers {
    use awkernel_lib::mmio_rw;
    use bitflags::bitflags;

    mmio_rw!(offset 0x00 => pub CS<ControlStatus>); // Control and Status
    mmio_rw!(offset 0x04 => pub FIFO<u32>); // FIFO Data
    mmio_rw!(offset 0x08 => pub CLK<u32>); // Clock
    mmio_rw!(offset 0x0c => pub DLEN<u32>); // Data Length
    mmio_rw!(offset 0x10 => pub LTOH<u32>); // LOSSI mode TOH
    mmio_rw!(offset 0x14 => pub DC<u32>); // DMA DREQ Controls

    bitflags! {
    #[derive(PartialEq)]
        pub struct ControlStatus: u32 {
            const LEN_LONG = 1 << 25; // Enable Long data word in Lossi mode if DMA_LEN is set
            const DMA_LEN = 1 << 24; // Enable DMA mode in Lossi mode
            const CSPOL2 = 1 << 23; // Chip Select 2 Polarity
            const CSPOL1 = 1 << 22; // Chip Select 1 Polarity
            const CSPOL0 = 1 << 21; // Chip Select 0 Polarity
            const RXF = 1 << 20; // RX FIFO Full
            const RXR = 1 << 19; // RX FIFO needs Reading (full)
            const TXD = 1 << 18; // TX FIFO can accept Data
            const RXD = 1 << 17; // RX FIFO contains Data
            const DONE = 1 << 16; // Transfer Done
            const TE_EN = 1 << 15; // Unused
            const LMONO = 1 << 14; // Unused
            const LEN = 1 << 13; // Enable LoSSI
            const REN = 1 << 12; // Enable Read
            const ADCS = 1 << 11; // Automatically Deassert Chip Select
            const INTR = 1 << 10; // Interrupt on RXR
            const INTD = 1 << 9; // Interrupt on Done
            const DMAEN = 1 << 8; // DMA Enable
            const TA = 1 << 7; // Transfer Active
            const CSPOL = 1 << 6; // Chip Select Polarity
            const CLEAR = 0b11 << 4; // FIFO Clear
            const CPOL = 1 << 3; // Clock Polarity
            const CPHA = 1 << 2; // Clock Phase
            const CS = 0b11; // Chip Select
        }
    }
}

/// Enumeration of possible SPI errors
#[derive(Debug, Clone, Copy)]
pub enum SpiError {
    WriteError,
    ReadError,
    OtherError,
}

/// Implementation of the `ErrorType` trait for the SPI
impl ErrorType for Spi {
    type Error = SpiError;
}

/// Maps SPI errors to their kinds
impl Error for SpiError {
    fn kind(&self) -> embedded_hal::spi::ErrorKind {
        match *self {
            SpiError::WriteError => embedded_hal::spi::ErrorKind::Other,
            SpiError::ReadError => embedded_hal::spi::ErrorKind::Other,
            SpiError::OtherError => embedded_hal::spi::ErrorKind::Other,
        }
    }
}

impl From<ErrorKind> for SpiError {
    fn from(_: ErrorKind) -> Self {
        SpiError::OtherError
    }
}

/// Representation of the SPI device
pub struct Spi {
    base: usize,
    _pin_miso: GpioPinAlt,
    _pin_mosi: GpioPinAlt,
    _pin_sclk: GpioPinAlt,
    _pin_ce0: GpioPinAlt,
}

/// Bit orders for SPI data transmission
pub enum BitOrder {
    LSBFirst,
    MSBFirst,
}

/// Modes for SPI data transmission.
pub enum DataMode {
    Mode0,
    Mode1,
    Mode2,
    Mode3,
}

/// Enumeration for chip select pins
pub enum ChipSelect {
    CS0,
    CS1,
}

/// Polarity options for chip select
pub enum Polarity {
    Low,
    High,
}

impl Spi {
    /// Creates and initializes a new SPI device
    pub fn new() -> Result<Self, &'static str> {
        let pin_miso = GpioPin::new(9)?;
        let pin_miso = pin_miso.into_alt(GpioFunction::ALTF0, PullMode::Up)?;

        let pin_mosi = GpioPin::new(10)?;
        let pin_mosi = pin_mosi.into_alt(GpioFunction::ALTF0, PullMode::Up)?;

        let pin_sclk = GpioPin::new(11)?;
        let pin_sclk = pin_sclk.into_alt(GpioFunction::ALTF0, PullMode::Up)?;

        let pin_ce0 = GpioPin::new(8)?;
        let pin_ce0 = pin_ce0.into_alt(GpioFunction::ALTF0, PullMode::Up)?;

        let base = SPI_BASE.load(Ordering::Relaxed);

        let spi = Self {
            base,
            _pin_miso: pin_miso,
            _pin_mosi: pin_mosi,
            _pin_sclk: pin_sclk,
            _pin_ce0: pin_ce0,
        };

        spi.set_bit_order(BitOrder::MSBFirst);
        spi.set_data_mode(DataMode::Mode0);
        spi.set_clock_divider(512);
        spi.set_chip_select(ChipSelect::CS0);
        spi.set_chip_select_polarity(ChipSelect::CS0, Polarity::Low);

        Ok(spi)
    }

    /// Sets the bit order for data transmission
    pub fn set_bit_order(&self, order: BitOrder) {
        let mut cs = registers::CS.read(self.base);
        match order {
            BitOrder::LSBFirst => cs |= registers::ControlStatus::LEN,
            BitOrder::MSBFirst => cs &= !registers::ControlStatus::LEN,
        }
        registers::CS.write(cs, self.base);
    }

    /// Sets the data transmission mode
    pub fn set_data_mode(&self, mode: DataMode) {
        let mut cs = registers::CS.read(self.base);
        match mode {
            DataMode::Mode0 => {
                cs &= !registers::ControlStatus::CPOL;
                cs &= !registers::ControlStatus::CPHA;
            }
            DataMode::Mode1 => {
                cs &= !registers::ControlStatus::CPOL;
                cs |= registers::ControlStatus::CPHA;
            }
            DataMode::Mode2 => {
                cs |= registers::ControlStatus::CPOL;
                cs &= !registers::ControlStatus::CPHA;
            }
            DataMode::Mode3 => {
                cs |= registers::ControlStatus::CPOL;
                cs |= registers::ControlStatus::CPHA;
            }
        }
        registers::CS.write(cs, self.base);
    }

    /// Sets the clock divider for SPI
    pub fn set_clock_divider(&self, divider: u32) {
        registers::CLK.write(divider, self.base);
    }

    /// Sets the polarity for the chip select pin
    pub fn set_chip_select_polarity(&self, cs: ChipSelect, polarity: Polarity) {
        let mut cs_reg = registers::CS.read(self.base);
        match (cs, polarity) {
            (ChipSelect::CS0, Polarity::Low) => cs_reg &= !registers::ControlStatus::CSPOL0,
            (ChipSelect::CS0, Polarity::High) => cs_reg |= registers::ControlStatus::CSPOL0,
            (ChipSelect::CS1, Polarity::Low) => cs_reg &= !registers::ControlStatus::CSPOL1,
            (ChipSelect::CS1, Polarity::High) => cs_reg |= registers::ControlStatus::CSPOL1,
        }
        registers::CS.write(cs_reg, self.base);
    }

    /// Sets the active chip select pin
    pub fn set_chip_select(&self, cs: ChipSelect) {
        let mut cs_reg = registers::CS.read(self.base);
        cs_reg &= !registers::ControlStatus::CS; // Clear current CS bits
        match cs {
            ChipSelect::CS0 => cs_reg |= registers::ControlStatus::from_bits(0b00).unwrap(),
            ChipSelect::CS1 => cs_reg |= registers::ControlStatus::from_bits(0b01).unwrap(),
        }
        registers::CS.write(cs_reg, self.base);
    }

    /// Writes data to the SPI device.
    ///
    /// # Safety
    ///
    /// Direct hardware access, ensure proper device state before use.
    unsafe fn spi_write(&self, data: u16) -> Result<(), ErrorKind> {
        // Clear TX and RX FIFOs
        let mut cs_value = registers::CS.read(self.base);
        cs_value |= registers::ControlStatus::CLEAR;
        registers::CS.write(cs_value, self.base);

        // Set TA = 1
        let mut cs_value = registers::CS.read(self.base);
        cs_value |= registers::ControlStatus::TA;
        registers::CS.write(cs_value, self.base);

        // Wait for TXD to become available
        while (registers::CS.read(self.base) & registers::ControlStatus::TXD)
            != registers::ControlStatus::TXD
        {}

        // Write to FIFO
        registers::FIFO.write((data >> 8) as u32, self.base);
        registers::FIFO.write((data & 0xFF) as u32, self.base);

        // Wait for DONE to be set
        while (registers::CS.read(self.base) & registers::ControlStatus::DONE)
            != registers::ControlStatus::DONE
        {}

        // Set TA = 0
        let mut cs_value = registers::CS.read(self.base);
        cs_value &= !registers::ControlStatus::TA;
        registers::CS.write(cs_value, self.base);

        Ok(())
    }

    /// Reads data from the SPI device.
    ///
    /// # Safety
    ///
    /// Direct hardware access, ensure proper device state before use.
    unsafe fn spi_read(&self, buffer: &mut [u8]) -> Result<(), ErrorKind> {
        for byte in buffer.iter_mut() {
            // Wait until there's data to be read
            while (registers::CS.read(self.base) & registers::ControlStatus::RXD)
                == registers::ControlStatus::RXD
            {}

            // Read a byte from the FIFO register
            *byte = registers::FIFO.read(self.base) as u8;
        }

        Ok(())
    }

    /// Sends a byte to the SPI device and simultaneously reads a byte from it.
    ///
    /// # Safety
    ///
    /// Direct hardware access, ensure proper device state before use.
    unsafe fn spi_transfer(&self, value: u8) -> Result<u8, ErrorKind> {
        // Clear TX and RX FIFOs
        let mut cs_value = registers::CS.read(self.base);
        cs_value |= registers::ControlStatus::CLEAR;
        registers::CS.write(cs_value, self.base);

        // Set TA = 1
        let mut cs_value = registers::CS.read(self.base);
        cs_value |= registers::ControlStatus::TA;
        registers::CS.write(cs_value, self.base);

        // Wait for TXD to become available
        while (registers::CS.read(self.base) & registers::ControlStatus::TXD)
            != registers::ControlStatus::TXD
        {}

        // Write to FIFO
        registers::FIFO.write(value as u32, self.base);

        // Wait for DONE to be set
        while (registers::CS.read(self.base) & registers::ControlStatus::DONE)
            != registers::ControlStatus::DONE
        {}

        // Read any byte that was sent back by the slave
        let ret = registers::FIFO.read(self.base) as u8;

        // Set TA = 0
        let mut cs_value = registers::CS.read(self.base);
        cs_value &= !registers::ControlStatus::TA;
        registers::CS.write(cs_value, self.base);

        Ok(ret)
    }
}

/// Implementing the `SpiBus`
impl SpiBus<u8> for Spi {
    fn read(&mut self, words: &mut [u8]) -> Result<(), Self::Error> {
        unsafe { self.spi_read(words).map_err(SpiError::from) }
    }

    fn write(&mut self, words: &[u8]) -> Result<(), Self::Error> {
        for word in words.chunks(2) {
            if let Some(&first_byte) = word.first() {
                let second_byte = word.get(1).cloned().unwrap_or(0);
                let combined: u16 = ((first_byte as u16) << 8) | (second_byte as u16);
                match unsafe { self.spi_write(combined) } {
                    Ok(_) => continue,
                    Err(e) => return Err(SpiError::from(e)),
                }
            }
        }
        Ok(())
    }

    fn transfer(&mut self, read: &mut [u8], write: &[u8]) -> Result<(), Self::Error> {
        for (&w, r) in write.iter().zip(read.iter_mut()) {
            match unsafe { self.spi_transfer(w) } {
                Ok(received) => *r = received,
                Err(e) => return Err(SpiError::from(e)),
            }
        }
        Ok(())
    }

    fn transfer_in_place(&mut self, words: &mut [u8]) -> Result<(), SpiError> {
        for word in words.iter_mut() {
            match unsafe { self.spi_transfer(*word) } {
                Ok(received) => *word = received,
                Err(e) => return Err(SpiError::from(e)),
            }
        }
        Ok(())
    }

    fn flush(&mut self) -> Result<(), Self::Error> {
        while (registers::CS.read(self.base) & registers::ControlStatus::DONE)
            != registers::ControlStatus::DONE
        {}

        Ok(())
    }
}
