use core::convert::{From, Into};
use core::ptr::{read_volatile, write_volatile};
use embedded_hal::digital::v2::{InputPin, OutputPin};

/// The base address for the GPIO.
static mut GPBASE: usize = 0;

/// Set the base address of GPIO.
///
/// # Safety
///
/// The base address must be Raspberry Pi's GPIO's base.
pub unsafe fn set_gpio_base(base: usize) {
    write_volatile(&mut GPBASE, base);
}

// Define the addresses for the different GPIO operations

fn gpfsel() -> usize {
    unsafe { read_volatile(&GPBASE) }
}

fn gpfset() -> usize {
    unsafe { read_volatile(&GPBASE) + 0x1c }
}

fn gpfclr() -> usize {
    unsafe { read_volatile(&GPBASE) + 0x28 }
}

fn gplev() -> usize {
    unsafe { read_volatile(&GPBASE) + 0x34 }
}

/// Enum `PullMode` for setting the pull-up/pull-down/none configuration for a GPIO pin.
pub enum PullMode {
    PullNone,
    PullUp,
    PullDown,
}

// Provide a method to convert `PullMode` enum to corresponding bit representation
impl From<PullMode> for u32 {
    fn from(val: PullMode) -> u32 {
        match val {
            PullMode::PullDown => 0b10,
            PullMode::PullNone => 0b0,
            PullMode::PullUp => 1,
        }
    }
}

// Implement the Clone and Copy trait for `PullMode`
impl core::clone::Clone for PullMode {
    fn clone(&self) -> Self {
        *self
    }
}
impl core::marker::Copy for PullMode {}

/// Enum `GpioFunction` for setting the function of a GPIO pin.
pub enum GpioFunction {
    INPUT,
    OUTPUT,
    ALTF0,
    ALTF1,
    ALTF2,
    ALTF3,
    ALTF4,
    ALTF5,
}

// Provide a method to convert `GpioFunction` enum to corresponding bit representation
impl From<GpioFunction> for u32 {
    fn from(val: GpioFunction) -> u32 {
        match val {
            GpioFunction::INPUT => 0,
            GpioFunction::OUTPUT => 1,
            GpioFunction::ALTF0 => 0b100,
            GpioFunction::ALTF1 => 0b101,
            GpioFunction::ALTF2 => 0b110,
            GpioFunction::ALTF3 => 0b111,
            GpioFunction::ALTF4 => 0b011,
            GpioFunction::ALTF5 => 0b010,
        }
    }
}

// Implement the Clone and Copy trait for `GpioFunction`
impl core::clone::Clone for GpioFunction {
    fn clone(&self) -> Self {
        *self
    }
}
impl core::marker::Copy for GpioFunction {}

/// Structure `GpioPin` to represent a GPIO pin and its operations.
pub struct GpioPin {
    pin: u32,
}

impl GpioPin {
    /// Create a new `GpioPin`.
    pub fn new(pin: u32) -> Self {
        Self { pin }
    }

    /// Set the function of the `GpioPin`.
    pub fn set_function(&self, func: GpioFunction) {
        gpio_ctrl(self.pin, func.into(), gpfsel(), 3);
    }
}

/// Implement `OutputPin` trait for `GpioPin` to provide methods for setting the pin high and low.
impl OutputPin for GpioPin {
    type Error = core::convert::Infallible;

    /// Set the GPIO pin high.
    fn set_high(&mut self) -> Result<(), Self::Error> {
        gpio_ctrl(self.pin, 1, gpfset(), 1);
        Ok(())
    }

    /// Set the GPIO pin low.
    fn set_low(&mut self) -> Result<(), Self::Error> {
        gpio_ctrl(self.pin, 1, gpfclr(), 1);
        Ok(())
    }
}

/// Implement `InputPin` trait for `GpioPin` to provide methods for checking if the pin is high or low.
impl InputPin for GpioPin {
    type Error = core::convert::Infallible;

    /// Check if the GPIO pin is high.
    fn is_high(&self) -> Result<bool, Self::Error> {
        let state = gpio_read(self.pin, gplev(), 1) == 1;
        if state {
            log::info!("Pin is high");
        }
        Ok(state)
    }

    /// Check if the GPIO pin is low.
    fn is_low(&self) -> Result<bool, Self::Error> {
        let state = gpio_read(self.pin, gplev(), 1) == 0;
        if state {
            log::info!("Pin is low");
        }
        Ok(state)
    }
}

/// A function to perform GPIO control operation.
fn gpio_ctrl(pin_num: u32, value: u32, base: usize, width: usize) {
    let frame = 32 / width;
    let reg = (base + (pin_num as usize / frame) * 4) as *mut u32;
    let shift = ((pin_num as usize % frame) * width) as u32;
    let val = value << shift;
    let mask = ((1 << width as u32) - 1) << shift;
    unsafe {
        let tmp = read_volatile(reg); // read the previous value
        write_volatile(reg, (tmp & !mask) | val);
    }
}

/// A function to read from a GPIO pin.
fn gpio_read(pin_num: u32, base: usize, width: usize) -> u32 {
    let frame = 32 / width;
    let reg = (base + (pin_num as usize / frame) * 4) as *mut u32;
    let shift = ((pin_num as usize % frame) * width) as u32;
    let mask = ((1 << width as u32) - 1) << shift;
    unsafe {
        let tmp = read_volatile(reg); // read the previous value
        (tmp & mask) >> shift
    }
}
