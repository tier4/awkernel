use core::ptr::{read_volatile, write_volatile};

use awkernel_lib::console::{unsafe_print_hex_u32, unsafe_print_hex_u64, unsafe_puts};
use embedded_graphics::primitives::ellipse;

// const ARM_GPIO0_IO_BASE: u64 = 0x1F000D0000;
const ARM_GPIO0_IO_BASE: u64 = 0x400D0000; // datasheet
                                           // const ARM_GPIO0_IO_BASE: u64 = 0xc0400d0000; /* "raspberrypi,rp1-gpio" io_base <- data abort */
                                           // const ARM_GPIO0_IO_BASE: u64 = 0x10001F8014;
                                        //    const ARM_GPIO0_IO_BASE: u64 = 0xffcd0000; // PCIe BAR1 + 0xd0000
                                           // const ARM_GPIO0_IO_BASE: u64 = 0x1000c0000;

// const ARM_GPIO0_PADS_BASE: u64 = 0x1F000F0000;
const ARM_GPIO0_PADS_BASE: u64 = 0x400F0000; // datasheet
                                             // const ARM_GPIO0_PADS_BASE: u64 = 0xc0400f0000; /* "raspberrypi,rp1-gpio" pads_base <- data abort */
                                             // const ARM_GPIO0_PADS_BASE: u64 = 0x1000218014;
                                            //  const ARM_GPIO0_PADS_BASE: u64 = 0xffcf0000; // PCIe BAR1 + 0xf0000
                                             // const ARM_GPIO0_PADS_BASE: u64 = 0x1000e0000;
                                             // const GPIO0_BANKS: usize = 3;
                                             // const MAX_BANK_PINS: usize = 32;

/// Masks for configuring pad control settings.
const PADS_PDE_MASK: u32 = 1 << 2; // Pull-down enable
const PADS_PUE_MASK: u32 = 1 << 3; // Pull-up enable

const PADS_OD_MASK: u32 = 1 << 7; // Open drain
const PADS_IE_MASK: u32 = 1 << 6; // Input enable
const CTRL_INOVER_MASK: u32 = 3 << 16; // Input override
const CTRL_OUTOVER_MASK: u32 = 3 << 12; // Output override
const CTRL_OEOVER_MASK: u32 = 3 << 14; // Output enable override
const CTRL_FUNCSEL_MASK: u32 = 0x1F; // Function select
const FUNCSEL_NULL: u32 = 31; // Null function select
const CTRL_FUNCSEL_SHIFT: u32 = 0; // Function select shift
const OEOVER_ENABLE: u32 = 3; // Enable override
const CTRL_OEOVER_SHIFT: u32 = 14; // Output enable override shift

const CTRL_OUTOVER_SHIFT: u32 = 12; // Output override shift
const OUTOVER_LOW: u32 = 2; // Output low
const OUTOVER_HIGH: u32 = 3; // Output high

const OEOVER_FUNCSEL: u32 = 0;
const OUTOVER_FUNCSEL: u32 = 0;

// const ARM_GPIO0_RIO_BASE: u64 = 0x1F000E0000;
const ARM_GPIO0_RIO_BASE: u64 = 0x400E0000; // datasheet
                                            // const ARM_GPIO0_RIO_BASE: u64 = 0xc0400e0000; /* "raspberrypi,rp1-gpio" rio_base <- data abort */
                                            // const ARM_GPIO0_RIO_BASE: u64 =	0xffce0000; // PCIe BAR1 + 0xe0000
const RIO_XOR_OFFSET: usize = 0x1000;
const RIO_SET_OFFSET: u32 = 0x2000;
const RIO_CLR_OFFSET: u32 = 0x3000;

/// Enumeration of GPIO pull modes.
pub enum TGPIOPullMode {
    Off,
    Down,
    Up,
    Unknown,
}
/// Enumeration of GPIO modes.
pub enum GPIOMode {
    Input,
    Output,
    InputPullUp,
    InputPullDown,
    GPIOModeAlternateFunction0,
    GPIOModeAlternateFunction1,
    GPIOModeAlternateFunction2,
    GPIOModeAlternateFunction3,
    GPIOModeAlternateFunction4,
    GPIOModeAlternateFunction5,
    GPIOModeAlternateFunction6,
    GPIOModeAlternateFunction7,
    GPIOModeAlternateFunction8,
    GPIOModeUnknown,
}

pub struct GPIOPin {
    bank: usize,
    bank_pin: usize,
    mode: GPIOMode,
}

impl GPIOPin {
    /// Constructs a new `GPIOPin`.
    ///
    /// # Arguments
    ///
    /// * `pin` - The GPIO pin number.
    ///
    /// # Returns
    ///
    /// A new instance of `GPIOPin`.
    pub fn new(pin: u32) -> Self {
        let (bank, bank_pin) = Self::pin_to_bank(pin);

        Self {
            bank,
            bank_pin,
            mode: GPIOMode::GPIOModeUnknown,
        }
    }

    pub fn init_with_mode(pin: u32, mode: GPIOMode) -> Self {
        let (bank, bank_pin) = Self::pin_to_bank(pin);

        let mut pin = Self {
            bank,
            bank_pin,
            mode: GPIOMode::GPIOModeUnknown,
        };

        pin.set_mode(mode, true);

        return pin;
    }

    /// Maps a pin number to its corresponding bank and pin within that bank.
    ///
    /// # Arguments
    ///
    /// * `pin` - The GPIO pin number.
    ///
    /// # Returns
    ///
    /// A tuple containing the bank number and pin number within that bank.
    fn pin_to_bank(pin: u32) -> (usize, usize) {
        if pin < 28 {
            (0, pin as usize)
        } else if pin < 34 {
            (1, (pin - 28) as usize)
        } else {
            assert!(pin < 54);
            (2, (pin - 34) as usize)
        }
    }

    /// Returns a pointer to the GPIO control register for a specific pin.
    ///
    /// # Arguments
    ///
    /// * `bank` - The bank number.
    /// * `pin` - The pin number within the bank.
    ///
    /// # Returns
    ///
    /// A mutable pointer to the control register.
    fn gpio0_ctrl(bank: usize, pin: usize) -> *mut u32 {
        (ARM_GPIO0_IO_BASE + (bank as u64) * 0x4000 + (pin as u64) * 8 + 4) as *mut u32
    }

    /// Returns a pointer to the pads control register for a specific pin.
    ///
    /// # Arguments
    ///
    /// * `bank` - The bank number.
    /// * `pin` - The pin number within the bank.
    ///
    /// # Returns
    ///
    /// A mutable pointer to the pads control register.
    fn pads0_ctrl(bank: usize, pin: usize) -> *mut u32 {
        (ARM_GPIO0_PADS_BASE + (bank as u64) * 0x4000 + 4 + (pin as u64) * 4) as *mut u32
    }

    /// Sets the pull-up/pull-down mode of the GPIO pin.
    ///
    /// # Arguments
    ///
    /// * `mode` - The desired pull mode as defined by `TGPIOPullMode`.
    pub fn set_pull_mode(&self, mode: TGPIOPullMode) {
        unsafe {
            let pads_ctrl = Self::pads0_ctrl(self.bank, self.bank_pin);
            let mut n_pads = read_volatile(pads_ctrl);
            n_pads &= !(PADS_PDE_MASK | PADS_PUE_MASK);

            match mode {
                TGPIOPullMode::Off => {}
                TGPIOPullMode::Down => n_pads |= PADS_PDE_MASK,
                TGPIOPullMode::Up => n_pads |= PADS_PUE_MASK,
                TGPIOPullMode::Unknown => panic!("Invalid pull mode"),
            }

            write_volatile(pads_ctrl, n_pads);
        }
    }

    /// Configures the GPIO pin to a specific alternate function.
    ///
    /// # Arguments
    ///
    /// * `function` - The function to set, as defined by the alternate function constants.
    pub fn set_alternate_function(&self, function: u32) {
        unsafe {
            let pads_reg = Self::pads0_ctrl(self.bank, self.bank_pin);
            let mut pads_val = read_volatile(pads_reg);
            pads_val &= !PADS_OD_MASK;
            pads_val |= PADS_IE_MASK;
            write_volatile(pads_reg, pads_val);

            let ctrl_reg = Self::gpio0_ctrl(self.bank, self.bank_pin);
            let mut ctrl_val = read_volatile(ctrl_reg);
            ctrl_val &= !CTRL_INOVER_MASK;
            ctrl_val |= 0 << 16;
            ctrl_val &= !CTRL_OUTOVER_MASK;
            ctrl_val |= 0 << 12;
            ctrl_val &= !CTRL_OEOVER_MASK;
            ctrl_val |= 0 << 14;
            ctrl_val &= !CTRL_FUNCSEL_MASK;
            ctrl_val |= function;
            write_volatile(ctrl_reg, ctrl_val);
        }
    }

    fn rio0_out(bank: usize, offset: u32) -> *mut u32 {
        (ARM_GPIO0_RIO_BASE + (bank as u64) * 0x4000 + (offset as u64) + 0) as *mut u32
    }

    fn rio0_oe(bank: usize, offset: u32) -> *mut u32 {
        (ARM_GPIO0_RIO_BASE + (bank as u64) * 0x4000 + (offset as u64) + 4) as *mut u32
    }

    fn rio0_in(bank: usize, offset: u32) -> *mut u32 {
        (ARM_GPIO0_RIO_BASE + (bank as u64) * 0x4000 + 8) as *mut u32
    }

    /// Sets the mode of the GPIO pin.
    ///
    /// # Arguments
    ///
    /// * `mode` - The desired mode as defined by `GPIOMode`.

    /// circle version set_mode
    // pub fn set_mode(&mut self, mode: GPIOMode, init: bool) {

    //     unsafe {

    //         match mode {
    //             GPIOMode::GPIOModeUnknown => {
    //                 let pads_reg = Self::pads0_ctrl(self.bank, self.bank_pin);
    //                 let mut pads_val = read_volatile(pads_reg);
    //                 pads_val |= PADS_OD_MASK;
    //                 pads_val &= !PADS_IE_MASK;
    //                 pads_val |= PADS_PDE_MASK;
    //                 pads_val &= !PADS_PUE_MASK;
    //                 write_volatile(pads_reg, pads_val);

    //                 let ctrl_reg = Self::gpio0_ctrl(self.bank, self.bank_pin);
    //                 let mut ctrl_val = read_volatile(ctrl_reg);
    //                 ctrl_val &= !CTRL_OUTOVER_MASK;
    //                 ctrl_val |= 0 << 12;
    //                 ctrl_val &= !CTRL_OEOVER_MASK;
    //                 ctrl_val |= 0 << 14;
    //                 ctrl_val &= !CTRL_FUNCSEL_MASK;
    //                 ctrl_val |= FUNCSEL_NULL << CTRL_FUNCSEL_SHIFT;
    //                 write_volatile(ctrl_reg, ctrl_val);
    //                 return;
    //             }
    //             _ => {},
    //         }

    //         let fsel_mode = match mode {
    //             GPIOMode::Input => 5,
    //             GPIOMode::InputPullUp => 5,
    //             GPIOMode::InputPullDown => 5,
    //             GPIOMode::Output => 5,
    //             GPIOMode::GPIOModeAlternateFunction0 => 0,
    //             GPIOMode::GPIOModeAlternateFunction1 => 1,
    //             GPIOMode::GPIOModeAlternateFunction2 => 2,
    //             GPIOMode::GPIOModeAlternateFunction3 => 3,
    //             GPIOMode::GPIOModeAlternateFunction4 => 4,
    //             GPIOMode::GPIOModeAlternateFunction5 => 5,
    //             GPIOMode::GPIOModeAlternateFunction6 => 6,
    //             GPIOMode::GPIOModeAlternateFunction7 => 7,
    //             GPIOMode::GPIOModeAlternateFunction8 => 8,
    //             GPIOMode::GPIOModeUnknown => 31,
    //         };

    //         match mode {
    //             GPIOMode::GPIOModeAlternateFunction0 | GPIOMode::GPIOModeAlternateFunction1 |
    //             GPIOMode::GPIOModeAlternateFunction2 | GPIOMode::GPIOModeAlternateFunction3 |
    //             GPIOMode::GPIOModeAlternateFunction4 | GPIOMode::GPIOModeAlternateFunction5 |
    //             GPIOMode::GPIOModeAlternateFunction6 | GPIOMode::GPIOModeAlternateFunction7 |
    //             GPIOMode::GPIOModeAlternateFunction8 | GPIOMode::GPIOModeUnknown => {
    //                 if init {
    //                     self.set_pull_mode(TGPIOPullMode::Off);
    //                 }

    //                 self.set_alternate_function(fsel_mode);

    //                 return;
    //             }
    //             _ => {},
    //         };

    //         if init {
    //             match mode {
    //                 GPIOMode::Output => self.set_pull_mode(TGPIOPullMode::Off),
    //                 _ => {},
    //             }
    //         }

    //         match self.mode {
    //             GPIOMode::Input | GPIOMode::InputPullUp | GPIOMode::InputPullDown | GPIOMode::Output => {},
    //             _ => self.set_alternate_function(5),
    //         }

    //         match mode {
    //             GPIOMode::Output => {
    //                 let rio_reg = Self::rio0_oe(self.bank, RIO_SET_OFFSET);
    //                 write_volatile(rio_reg, 1 << self.bank_pin);
    //             }
    //             _ => {
    //                 let rio_reg = Self::rio0_oe(self.bank, RIO_CLR_OFFSET);
    //                 write_volatile(rio_reg, 1 << self.bank_pin);
    //             }
    //         }

    //         if init {
    //             match mode {
    //                 GPIOMode::Input => self.set_pull_mode(TGPIOPullMode::Off),
    //                 GPIOMode::Output => self.write(false),
    //                 GPIOMode::InputPullUp => self.set_pull_mode(TGPIOPullMode::Up),
    //                 GPIOMode::InputPullDown => self.set_pull_mode(TGPIOPullMode::Down),
    //                 _ => {},
    //             }
    //         }

    //         self.mode = mode;

    //     }
    // }

    /// rppal version set_mode
    pub fn set_mode(&mut self, mode: GPIOMode, init: bool) {
        let ctrl_reg = Self::gpio0_ctrl(self.bank, self.bank_pin);

        let prev_mode = self.get_mode();

        match mode {
            GPIOMode::GPIOModeUnknown => {
                self.input_disable();
                self.output_disable();
            }
            _ => {
                self.input_enable();
                self.output_enable();
            }
        }

        unsafe {
            let mut ctrl_val = read_volatile(ctrl_reg);

            let fsel_mode = match mode {
                GPIOMode::Input => 5,
                GPIOMode::InputPullUp => 5,
                GPIOMode::InputPullDown => 5,
                GPIOMode::Output => 5,
                GPIOMode::GPIOModeAlternateFunction0 => 0,
                GPIOMode::GPIOModeAlternateFunction1 => 1,
                GPIOMode::GPIOModeAlternateFunction2 => 2,
                GPIOMode::GPIOModeAlternateFunction3 => 3,
                GPIOMode::GPIOModeAlternateFunction4 => 4,
                GPIOMode::GPIOModeAlternateFunction5 => 5,
                GPIOMode::GPIOModeAlternateFunction6 => 6,
                GPIOMode::GPIOModeAlternateFunction7 => 7,
                GPIOMode::GPIOModeAlternateFunction8 => 8,
                GPIOMode::GPIOModeUnknown => 31,
            };

            match mode {
                GPIOMode::Input
                | GPIOMode::InputPullUp
                | GPIOMode::InputPullDown
                | GPIOMode::Output => self.set_direction(mode),
                _ => {}
            }

            ctrl_val &= CTRL_OUTOVER_MASK;
            ctrl_val &= CTRL_OEOVER_MASK;
            ctrl_val &= CTRL_FUNCSEL_MASK;
            ctrl_val |= (fsel_mode as u32) << 0;

            write_volatile(ctrl_reg, ctrl_val);
        }
    }

    /// Retrieves the current alternate function of the GPIO pin.
    ///
    /// # Returns
    ///
    /// An optional containing the current function if set; otherwise `None`.
    pub fn get_alternate_function(&self) -> Option<u32> {
        unsafe {
            let ctrl_reg = Self::gpio0_ctrl(self.bank, self.bank_pin);
            let ctrl_val = read_volatile(ctrl_reg);
            let func_sel = (ctrl_val & CTRL_FUNCSEL_MASK) >> CTRL_FUNCSEL_SHIFT;

            if func_sel == FUNCSEL_NULL {
                None
            } else {
                Some(func_sel)
            }
        }
    }

    /// Retrieves the current mode of the GPIO pin.
    ///
    /// # Returns
    ///
    /// The current mode as defined by `GPIOMode`.

    /// raspi5_gpio version get_mode
    // pub fn get_mode(&self) -> GPIOMode {
    //     unsafe {
    //         let ctrl_reg = Self::gpio0_ctrl(self.bank, self.bank_pin);
    //         let pads_reg = Self::pads0_ctrl(self.bank, self.bank_pin);

    //         let ctrl_val = read_volatile(ctrl_reg);
    //         let pads_val = read_volatile(pads_reg);

    //         let func_sel = (ctrl_val & CTRL_FUNCSEL_MASK) >> CTRL_FUNCSEL_SHIFT;
    //         let oe_over = (ctrl_val & CTRL_OEOVER_MASK) >> CTRL_OEOVER_SHIFT;
    //         let is_input_enabled = pads_val & PADS_IE_MASK != 0;
    //         let is_pull_up_enabled = pads_val & PADS_PUE_MASK != 0;
    //         let is_pull_down_enabled = pads_val & PADS_PDE_MASK != 0;

    //         match func_sel {
    //             FUNCSEL_NULL => match (
    //                 is_input_enabled,
    //                 is_pull_up_enabled,
    //                 is_pull_down_enabled,
    //                 oe_over,
    //             ) {
    //                 (true, false, false, _) => GPIOMode::Input,
    //                 (true, true, false, _) => GPIOMode::InputPullUp,
    //                 (true, false, true, _) => GPIOMode::InputPullDown,
    //                 (_, false, false, OEOVER_ENABLE) => GPIOMode::Output,
    //                 _ => GPIOMode::GPIOModeUnknown,
    //             },
    //             _ => match func_sel {
    //                 0..=8 => match func_sel {
    //                     0 => GPIOMode::GPIOModeAlternateFunction0,
    //                     1 => GPIOMode::GPIOModeAlternateFunction1,
    //                     2 => GPIOMode::GPIOModeAlternateFunction2,
    //                     3 => GPIOMode::GPIOModeAlternateFunction3,
    //                     4 => GPIOMode::GPIOModeAlternateFunction4,
    //                     5 => GPIOMode::GPIOModeAlternateFunction5,
    //                     6 => GPIOMode::GPIOModeAlternateFunction6,
    //                     7 => GPIOMode::GPIOModeAlternateFunction7,
    //                     8 => GPIOMode::GPIOModeAlternateFunction8,
    //                     _ => GPIOMode::GPIOModeUnknown,
    //                 },
    //                 _ => GPIOMode::GPIOModeUnknown,
    //             },
    //         }
    //     }
    // }

    pub fn get_mode(&self) -> GPIOMode {
        unsafe {
            let ctrl_reg = Self::gpio0_ctrl(self.bank, self.bank_pin);
            let pads_reg = Self::pads0_ctrl(self.bank, self.bank_pin);

            let ctrl_val = read_volatile(ctrl_reg);
            let pads_val = read_volatile(pads_reg);

            match (ctrl_val & CTRL_FUNCSEL_MASK) as u8 {
                0 => GPIOMode::GPIOModeAlternateFunction0,
                1 => GPIOMode::GPIOModeAlternateFunction1,
                2 => GPIOMode::GPIOModeAlternateFunction2,
                3 => GPIOMode::GPIOModeAlternateFunction3,
                4 => GPIOMode::GPIOModeAlternateFunction4,
                5 => GPIOMode::GPIOModeAlternateFunction5,
                6 => GPIOMode::GPIOModeAlternateFunction6,
                7 => GPIOMode::GPIOModeAlternateFunction7,
                8 => GPIOMode::GPIOModeAlternateFunction8,
                31 => GPIOMode::GPIOModeUnknown,
                _ => GPIOMode::Input,
            }
        }
    }

    fn set_direction(&self, mode: GPIOMode) {
        let rio_reg = match mode {
            GPIOMode::Output => Self::rio0_oe(self.bank, RIO_SET_OFFSET),
            _ => Self::rio0_oe(self.bank, RIO_CLR_OFFSET),
        };

        unsafe {
            write_volatile(rio_reg, 1 << self.bank_pin);
        }
    }

    pub fn get_direction(&self) -> GPIOMode {
        let rio_reg = Self::rio0_oe(self.bank, 0);
        unsafe {
            let temp = read_volatile(rio_reg);

            unsafe_puts("\n\rRIO_OE address: ");
            unsafe_print_hex_u64(rio_reg as u64);
            unsafe_puts("\n\rRIO_OE value: ");
            unsafe_print_hex_u64(temp as u64);
            unsafe_puts("\r\n");

            let rio_val = (read_volatile(rio_reg) >> self.bank_pin) as u8 & 0b1;

            if rio_val > 0 {
                GPIOMode::Output
            } else {
                GPIOMode::Input
            }
        }
    }

    pub fn input_enable(&self) {
        unsafe {
            let pads_reg = Self::pads0_ctrl(self.bank, self.bank_pin);
            let mut pads_val = read_volatile(pads_reg);

            pads_val |= PADS_IE_MASK;

            write_volatile(pads_reg, pads_val);
        }
    }

    pub fn input_disable(&self) {
        unsafe {
            let pads_reg = Self::pads0_ctrl(self.bank, self.bank_pin);
            let mut pads_val = read_volatile(pads_reg);

            pads_val &= PADS_IE_MASK;

            write_volatile(pads_reg, pads_val);
        }
    }

    pub fn output_enable(&self) {
        unsafe {
            let pads_reg = Self::pads0_ctrl(self.bank, self.bank_pin);
            let mut pads_val = read_volatile(pads_reg);

            pads_val &= !PADS_OD_MASK;

            write_volatile(pads_reg, pads_val);
        }
    }

    pub fn output_disable(&self) {
        unsafe {
            let pads_reg = Self::pads0_ctrl(self.bank, self.bank_pin);
            let mut pads_val = read_volatile(pads_reg);

            pads_val |= PADS_OD_MASK;

            write_volatile(pads_reg, pads_val);
        }
    }

    /// Writes a value to the GPIO pin, setting it high or low.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to write to the pin (`true` for high, `false` for low).
    pub fn write(&self, value: bool) {
        // let ctrl_reg = Self::gpio0_ctrl(self.bank, self.bank_pin);

        unsafe {
            // let mut ctrl_value = core::ptr::read_volatile(ctrl_reg);

            // ctrl_value &= !CTRL_OUTOVER_MASK;
            // ctrl_value |= if value { OUTOVER_HIGH } else { OUTOVER_LOW } << CTRL_OUTOVER_SHIFT;
            // write_volatile(ctrl_reg, ctrl_value);

            let rio_reg = if value {
                Self::rio0_out(self.bank, RIO_SET_OFFSET)
            } else {
                Self::rio0_out(self.bank, RIO_CLR_OFFSET)
            };

            // let check_rio_reg = Self::rio0_out(self.bank, 0);

            // unsafe_puts("\n\rRIO_OUT address: ");
            // unsafe_print_hex_u64(check_rio_reg as u64);

            // let mut rio_base = read_volatile(ARM_GPIO0_RIO_BASE as *const u64);
            // unsafe_puts("\n\rrio_base before: ");
            // unsafe_print_hex_u64(rio_base as u64);

            // let mut rio_val = read_volatile(check_rio_reg);
            // unsafe_puts("\n\rRIO_OUT value before: ");
            // unsafe_print_hex_u64(rio_val as u64);


            // dummy address for fence operation

            // let dummy_addr = (0x12_0000 + 0xc0) as *mut u32;
            // let dummy_addr = (0x10_0012_0000 as usize + 0xc0) as *mut usize;

            // fence operation
            // maybe, this is not correct

            // write_volatile(dummy_addr, 0);
            // write_volatile(dummy_addr, 0);
            // write_volatile(dummy_addr, 0);
            // write_volatile(dummy_addr, 0);
            // write_volatile(dummy_addr, 0);
            // write_volatile(dummy_addr, 0);

            write_volatile(rio_reg, 1 << self.bank_pin);

            // rio_base = read_volatile(ARM_GPIO0_RIO_BASE as *const u64);
            // unsafe_puts("\n\rrio_base after: ");
            // unsafe_print_hex_u64(rio_base as u64);

            // rio_val = read_volatile(check_rio_reg);
            // unsafe_puts("\n\rRIO_OUT value after: ");
            // unsafe_print_hex_u64(rio_val as u64);

            // unsafe_puts("\n\r\n\r");
        }
    }
}
