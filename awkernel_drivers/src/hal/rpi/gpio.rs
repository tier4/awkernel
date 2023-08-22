use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::convert::{From, Into};
use core::ptr::{read_volatile, write_volatile};
use embedded_hal::digital::v2::{InputPin, OutputPin};

static GPIO_PINS: Mutex<[bool; 46]> = Mutex::new([
    true,  // GPIO0
    true,  // GPIO1
    true,  // GPIO2
    true,  // GPIO3
    true,  // GPIO4
    true,  // GPIO5
    true,  // GPIO6
    true,  // GPIO7
    true,  // GPIO8
    true,  // GPIO9
    true,  // GPIO10
    true,  // GPIO11
    true,  // GPIO12
    true,  // GPIO13
    false, // GPIO14 is used for UART TX
    false, // GPIO15 is used for UART RX
    true,  // GPIO16
    true,  // GPIO17
    true,  // GPIO18
    true,  // GPIO19
    true,  // GPIO20
    true,  // GPIO21
    true,  // GPIO22
    true,  // GPIO23
    true,  // GPIO24
    true,  // GPIO25
    true,  // GPIO26
    true,  // GPIO27
    true,  // GPIO28
    true,  // GPIO29
    true,  // GPIO30
    true,  // GPIO31
    true,  // GPIO32
    true,  // GPIO33
    true,  // GPIO34
    true,  // GPIO35
    true,  // GPIO36
    true,  // GPIO37
    true,  // GPIO38
    true,  // GPIO39
    true,  // GPIO40
    true,  // GPIO41
    true,  // GPIO42
    true,  // GPIO43
    true,  // GPIO44
    true,  // GPIO45
]);

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
    0
}

fn gpfset() -> usize {
    0x1c
}

fn gpfclr() -> usize {
    0x28
}

fn gplev() -> usize {
    0x34
}

mod registers {
    use awkernel_lib::mmio_rw;

    mmio_rw!(offset 0xe4 => pub GPP_PUP_DOWN<u32>);
}

/// Enum `PullMode` for setting the pull-up/pull-down/none configuration for a GPIO pin.
#[derive(Debug, Clone, Copy)]
pub enum PullMode {
    None = 0b00,
    Up = 0b01,
    Down = 0b10,
}

/// Enum `GpioFunction` for setting the function of a GPIO pin.
#[derive(Debug, Clone, Copy)]
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

/// Structure `GpioPin` to represent a GPIO pin and its operations.
#[derive(Debug)]
pub struct GpioPin {
    pin: Option<u32>,
    base: usize,
}

impl GpioPin {
    /// Create a new `GpioPin`.
    pub fn new(pin: u32) -> Result<Self, &'static str> {
        let mut node = MCSNode::new();
        let mut guard = GPIO_PINS.lock(&mut node);

        let Some(ref_pin) = guard.get_mut(pin as usize) else {
            return Err("invalid GPIO pin");
        };

        if !*ref_pin {
            return Err("The GPIO pin is already in used.");
        }

        *ref_pin = false;

        Ok(Self {
            pin: Some(pin),
            base: unsafe { read_volatile(&GPBASE) },
        })
    }

    pub fn into_output(mut self) -> GpioPinOut {
        let pin = self.pin.unwrap();
        self.pin = None;

        gpio_ctrl(pin, GpioFunction::OUTPUT.into(), gpfsel() + self.base, 3);
        GpioPinOut {
            pin,
            base: self.base,
        }
    }

    pub fn into_input(mut self, pull_up_down: PullMode) -> Result<GpioPinIn, &'static str> {
        let pin = self.pin.unwrap();

        if (pin == 2 || pin == 3) && !matches!(pull_up_down, PullMode::Up) {
            return Err("Pins GPIO2 and GPIO3 have fixed pull-up resistors.");
        }

        self.pin = None;
        self.set_pull_up_down(pin, pull_up_down);

        gpio_ctrl(pin, GpioFunction::OUTPUT.into(), gpfsel() + self.base, 3);
        Ok(GpioPinIn {
            pin,
            base: self.base,
        })
    }

    pub fn into_alt(
        mut self,
        alt: GpioFunction,
        pull_up_down: PullMode,
    ) -> Result<GpioPinAlt, &'static str> {
        if matches!(alt, GpioFunction::INPUT | GpioFunction::OUTPUT) {
            return Err("Not GpioFunction::Alt");
        }

        let pin = self.pin.unwrap();

        if (pin == 2 || pin == 3) && !matches!(pull_up_down, PullMode::Up) {
            return Err("Pins GPIO2 and GPIO3 have fixed pull-up resistors.");
        }

        self.pin = None;
        self.set_pull_up_down(pin, pull_up_down);

        gpio_ctrl(pin, alt.into(), gpfsel() + self.base, 3);

        Ok(GpioPinAlt {
            pin,
            base: self.base,
        })
    }

    fn set_pull_up_down(&self, pin: u32, pull_up_down: PullMode) {
        let offset = pin / 16;
        let shift = pin % (16 - 1);
        let mask = !(0x11 << shift);

        let base = self.base + 4 * offset as usize;
        let val_up_down = registers::GPP_PUP_DOWN.read(base);
        let val_up_down = (val_up_down & mask) | ((pull_up_down as u32) << shift);
        registers::GPP_PUP_DOWN.write(val_up_down, base);
    }
}

impl Drop for GpioPin {
    fn drop(&mut self) {
        if let Some(pin) = self.pin {
            make_pin_available(pin);
        }
    }
}

fn make_pin_available(pin: u32) {
    let mut node = MCSNode::new();
    let mut guard = GPIO_PINS.lock(&mut node);
    guard[pin as usize] = true;
}

#[derive(Debug)]
pub struct GpioPinOut {
    pin: u32,
    base: usize,
}

/// Implement `OutputPin` trait for `GpioPin` to provide methods for setting the pin high and low.
impl OutputPin for GpioPinOut {
    type Error = core::convert::Infallible;

    /// Set the GPIO pin high.
    fn set_high(&mut self) -> Result<(), Self::Error> {
        gpio_ctrl(self.pin, 1, gpfset() + self.base, 1);
        Ok(())
    }

    /// Set the GPIO pin low.
    fn set_low(&mut self) -> Result<(), Self::Error> {
        gpio_ctrl(self.pin, 1, gpfclr() + self.base, 1);
        Ok(())
    }
}

impl Drop for GpioPinOut {
    fn drop(&mut self) {
        make_pin_available(self.pin);
    }
}

#[derive(Debug)]
pub struct GpioPinIn {
    pin: u32,
    base: usize,
}

/// Implement `InputPin` trait for `GpioPin` to provide methods for checking if the pin is high or low.
impl InputPin for GpioPinIn {
    type Error = core::convert::Infallible;

    /// Check if the GPIO pin is high.
    fn is_high(&self) -> Result<bool, Self::Error> {
        let state = gpio_read(self.pin, gplev() + self.base, 1) == 1;
        Ok(state)
    }

    /// Check if the GPIO pin is low.
    fn is_low(&self) -> Result<bool, Self::Error> {
        let state = gpio_read(self.pin, gplev() + self.base, 1) == 0;
        Ok(state)
    }
}

impl Drop for GpioPinIn {
    fn drop(&mut self) {
        make_pin_available(self.pin);
    }
}

#[derive(Debug)]
pub struct GpioPinAlt {
    pin: u32,
    base: usize,
}

impl GpioPinAlt {
    pub fn get_base(&self) -> usize {
        self.base
    }
}

impl Drop for GpioPinAlt {
    fn drop(&mut self) {
        make_pin_available(self.pin);
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
