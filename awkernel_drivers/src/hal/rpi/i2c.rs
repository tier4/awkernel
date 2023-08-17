use core::ptr::{read_volatile, write_volatile};
use embedded_hal::blocking::i2c::{Read, Write, WriteRead};

pub static mut I2C_BASE: usize = 0;

/// Sets the base address for I2C communication
///
/// # Safety
///
/// `base` must be the base address of I2C.
pub unsafe fn set_i2c_base(base: usize) {
    write_volatile(&mut I2C_BASE, base);
}

impl Default for I2C {
    fn default() -> Self {
        Self::new()
    }
}

/// Define the addresses for the different I2C operations

fn i2c_c() -> usize {
    unsafe { read_volatile(&I2C_BASE) }
}

fn i2c_s() -> usize {
    unsafe { read_volatile(&I2C_BASE) + 0x4 }
}

fn i2c_dlen() -> usize {
    unsafe { read_volatile(&I2C_BASE) + 0x8 }
}

fn i2c_a() -> usize {
    unsafe { read_volatile(&I2C_BASE) + 0xc }
}

fn i2c_fifo() -> usize {
    unsafe { read_volatile(&I2C_BASE) + 0x10 }
}

/// Enum to represent possible I2C errors
pub enum I2cError {
    WriteError,
    ReadError,
    OtherError,
}

pub struct I2C {}

impl I2C {
    pub fn new() -> Self {
        Self {}
    }
}

/// Trait implementation for writing to an I2C device
impl Write for I2C {
    type Error = I2cError;

    /// Writes the given bytes to the device at the given address
    fn write(&mut self, addr: u8, bytes: &[u8]) -> Result<(), Self::Error> {
        unsafe {
            i2c_write(
                addr,
                bytes,
                i2c_a(),
                i2c_dlen(),
                i2c_fifo(),
                i2c_c(),
                i2c_s(),
            )
        }
    }
}

/// Trait implementation for reading from an I2C device
impl Read for I2C {
    type Error = I2cError;

    /// Reads data into the given buffer from the device at the given address
    fn read(&mut self, addr: u8, buffer: &mut [u8]) -> Result<(), Self::Error> {
        unsafe {
            i2c_read(
                addr,
                buffer,
                i2c_a(),
                i2c_dlen(),
                i2c_fifo(),
                i2c_c(),
                i2c_s(),
            )
        }
    }
}

/// Trait implementation for reading from and writing to an I2C device
impl WriteRead for I2C {
    type Error = I2cError;

    /// Writes the given bytes to the device at the given address, then reads data into the given buffer
    fn write_read(&mut self, addr: u8, bytes: &[u8], buffer: &mut [u8]) -> Result<(), Self::Error> {
        self.write(addr, bytes)?;
        self.read(addr, buffer)
    }
}

/// Writes the given bytes to the device at the given address
unsafe fn i2c_write(
    addr: u8,
    bytes: &[u8],
    i2c_a: usize,
    i2c_dlen: usize,
    i2c_fifo: usize,
    i2c_c: usize,
    i2c_s: usize,
) -> Result<(), I2cError> {
    write_volatile(i2c_a as *mut u8, addr);
    write_volatile(i2c_dlen as *mut u16, bytes.len() as u16);
    for byte in bytes {
        write_volatile(i2c_fifo as *mut u8, *byte);
    }
    write_volatile(i2c_c as *mut u8, 0x80);

    if read_volatile(i2c_s as *mut u8) != 0 {
        return Err(I2cError::WriteError);
    }

    Ok(())
}

/// Reads data into the given buffer from the device at the given address
unsafe fn i2c_read(
    addr: u8,
    buffer: &mut [u8],
    i2c_a: usize,
    i2c_dlen: usize,
    i2c_fifo: usize,
    i2c_c: usize,
    i2c_s: usize,
) -> Result<(), I2cError> {
    write_volatile(i2c_a as *mut u8, addr);
    write_volatile(i2c_dlen as *mut u16, buffer.len() as u16);
    write_volatile(i2c_c as *mut u8, 0x81);
    for byte in buffer {
        *byte = read_volatile(i2c_fifo as *mut u8);
    }

    if read_volatile(i2c_s as *mut u8) != 0 {
        return Err(I2cError::ReadError);
    }

    Ok(())
}
