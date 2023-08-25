use super::gpio::{GpioFunction, GpioPin, GpioPinAlt, PullMode};
use core::ptr::{read_volatile, write_volatile};
use embedded_hal::i2c::{self, Operation};

pub static mut I2C_BASE: usize = 0;

/// Sets the base address for I2C communication
///
/// # Safety
///
/// `base` must be the base address of I2C.
pub unsafe fn set_i2c_base(base: usize) {
    write_volatile(&mut I2C_BASE, base);
}

mod registers {
    use awkernel_lib::mmio_rw;
    use bitflags::bitflags;

    mmio_rw!(offset 0x00 => pub C<Control>); // Control
    mmio_rw!(offset 0x04 => pub S<Status>); // Status
    mmio_rw!(offset 0x08 => pub DLEN<u32>); // Data length
    mmio_rw!(offset 0x0c => pub A<u32>); // Save address
    mmio_rw!(offset 0x10 => pub FIFO<u32>); // Data FIFO
    mmio_rw!(offset 0x14 => pub CDIV<u32>); // clock divider register
    mmio_rw!(offset 0x18 => pub DEL<u32>); // Data Delay
    mmio_rw!(offset 0x1c => pub CLKT<u32>); // Clock Stretch Timeout

    bitflags! {
        pub struct Control: u32 {
            const I2CEN = 1 << 15; // I2C Enable
            const INTR = 1 << 10; // Interrupt on RX
            const INTT = 1 << 9; // Interrupt on TX
            const CLEAR = 0b11 << 4; // FIFO Clear
            const ST = 1 << 7; // Start Transfer
            const READ = 1; // Read Transfer
        }

        pub struct Status: u32 {
            const CLKT = 1 << 9; // Clock Stretch Timeout
            const ERR  = 1 << 8; // ACK Error
            const RXF  = 1 << 7; // FIFO Full
            const TXE  = 1 << 6; // FIFO Empty
            const RXD  = 1 << 5; // FIFO contains Data
            const TXD  = 1 << 4; // FIFO can accept Data
            const RXR  = 1 << 3; // FIFO needs Reading (3/4 full)
            const TXW  = 1 << 2; // FIFO needs Writing (1/4 full)
            const DONE = 1 << 1; // Transfer Done
            const TA   = 1 << 0; // Transfer Active
        }
    }
}

/// I2C errors
#[derive(Debug, Clone)]
pub struct I2cError {
    pub err: i2c::ErrorKind,
    pub rw: RWError,
}

#[derive(Debug, Clone)]
pub enum RWError {
    Read,
    Write,
}

pub struct I2cBus {
    base: usize,
    _pin0: GpioPinAlt,
    _pin1: GpioPinAlt,
}

impl I2cBus {
    pub fn new(core_speed: u32, fast_mode: bool) -> Result<Self, &'static str> {
        let pin0 = GpioPin::new(2)?;
        let pin0 = pin0.into_alt(GpioFunction::ALTF0, PullMode::Up)?;

        let pin1 = GpioPin::new(3)?;
        let pin1 = pin1.into_alt(GpioFunction::ALTF0, PullMode::Up)?;

        let base = unsafe { read_volatile(&I2C_BASE) };

        let clock_divisor = if fast_mode {
            core_speed / 400_000
        } else {
            core_speed / 100_000
        };

        registers::CDIV.write(clock_divisor, base);

        Ok(Self {
            base,
            _pin0: pin0,
            _pin1: pin1,
        })
    }
}

impl i2c::ErrorType for I2cBus {
    type Error = I2cError;
}

impl i2c::Error for I2cError {
    fn kind(&self) -> i2c::ErrorKind {
        self.err
    }
}

/// Trait implementation for `I2c`.
impl i2c::I2c for I2cBus {
    fn write(&mut self, addr: u8, bytes: &[u8]) -> Result<(), Self::Error> {
        use registers::{Control, Status};

        assert!(addr < 0x80);
        assert!(bytes.len() < (1 << 16));

        registers::S.write(Status::CLKT | Status::ERR | Status::DONE, self.base);
        registers::C.write(Control::CLEAR, self.base); // Clear FIFO
        registers::A.write(addr as u32, self.base); // Set address
        registers::DLEN.write(bytes.len() as u32, self.base);

        for byte in bytes.iter() {
            while !registers::S.read(self.base).contains(Status::TXD) {
                core::hint::spin_loop();
            }

            registers::FIFO.write(*byte as u32, self.base);
        }

        registers::C.write(Control::I2CEN | Control::ST, self.base);

        if let Err(err) = self.wait_i2c_done(100) {
            Err(I2cError {
                err,
                rw: RWError::Write,
            })
        } else {
            Ok(())
        }
    }

    fn read(&mut self, addr: u8, buffer: &mut [u8]) -> Result<(), Self::Error> {
        use registers::{Control, Status};

        assert!(buffer.len() < (1 << 16));

        registers::S.write(Status::CLKT | Status::ERR | Status::DONE, self.base);
        registers::C.write(Control::CLEAR, self.base); // Clear FIFO
        registers::A.write(addr as u32, self.base); // Set address
        registers::DLEN.write(buffer.len() as u32, self.base);

        registers::C.write(
            Control::I2CEN | Control::CLEAR | Control::ST | Control::READ,
            self.base,
        );

        if let Err(err) = self.wait_i2c_done(2000) {
            return Err(I2cError {
                err,
                rw: RWError::Read,
            });
        }

        for buf in buffer.iter_mut() {
            while !registers::S.read(self.base).contains(Status::RXD) {
                core::hint::spin_loop();
            }

            *buf = (registers::FIFO.read(self.base) & 0xff) as u8;
        }

        Ok(())
    }

    fn transaction(
        &mut self,
        address: u8,
        operations: &mut [i2c::Operation<'_>],
    ) -> Result<(), Self::Error> {
        for op in operations.iter_mut() {
            match op {
                Operation::Read(buf) => {
                    self.read(address, buf)?;
                }
                Operation::Write(buf) => {
                    self.write(address, buf)?;
                }
            }
        }

        Ok(())
    }
}

impl I2cBus {
    /// Wait until the current I2C operation has been finished/acknowledged.
    fn wait_i2c_done(&self, tries: u32) -> Result<(), i2c::ErrorKind> {
        use registers::Status;

        for _ in 0..tries {
            if registers::S.read(self.base).contains(Status::DONE) {
                if registers::S.read(self.base).contains(Status::ERR) {
                    return Err(i2c::ErrorKind::NoAcknowledge(
                        i2c::NoAcknowledgeSource::Address,
                    ));
                } else {
                    return Ok(());
                }
            }

            super::wait_cycles(1000);
        }

        // Timeout
        Err(i2c::ErrorKind::NoAcknowledge(
            i2c::NoAcknowledgeSource::Unknown,
        ))
    }
}
