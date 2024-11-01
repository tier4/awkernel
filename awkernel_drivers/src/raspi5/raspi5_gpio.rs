use core::ptr::{read_volatile, write_volatile};

// const ARM_GPIO0_IO_BASE: u64 = 0x1F000D0000;
const ARM_GPIO0_IO_BASE: u64 = 0x400D0000;
// const ARM_GPIO0_IO_BASE: u64 = 0x10001F8014;
// const ARM_GPIO0_IO_BASE: u64 = 0xffcd0000;
// const ARM_GPIO0_IO_BASE: u64 = 0x1000c0000;
// const ARM_GPIO0_PADS_BASE: u64 = 0x1F000F0000;
const ARM_GPIO0_PADS_BASE: u64 = 0x400F0000;
// const ARM_GPIO0_PADS_BASE: u64 = 0x1000218014;
// const ARM_GPIO0_PADS_BASE: u64 = 0xffcf0000;
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
const ARM_GPIO0_RIO_BASE: u64 =	0x1F000E0000;

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
        Self { bank, bank_pin }
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

    fn rio0_out(bank: usize, offset: u32) -> *mut u32{
        (ARM_GPIO0_RIO_BASE + (bank as u64) * 0x4000 + (offset as u64) + 0) as *mut u32
    }

    /// Sets the mode of the GPIO pin.
    ///
    /// # Arguments
    ///
    /// * `mode` - The desired mode as defined by `GPIOMode`.
    // pub fn set_mode(&self, mode: GPIOMode) {
    //     let pads_reg = Self::pads0_ctrl(self.bank, self.bank_pin);
    //     let ctrl_reg = Self::gpio0_ctrl(self.bank, self.bank_pin);

    //     match mode {
    //         GPIOMode::GPIOModeUnknown => {
    //             unsafe{
    //                 let mut ctrl_val = read_volatile(ctrl_reg);
    //                 let mut pads_val = read_volatile(pads_reg);

    //                 ctrl_val &= !CTRL_OUTOVER_MASK;
    //                 ctrl_val |= OUTOVER_FUNCSEL << CTRL_OUTOVER_SHIFT;
    //                 ctrl_val &= !CTRL_OEOVER_MASK;
    //                 ctrl_val |= OEOVER_FUNCSEL << CTRL_OEOVER_SHIFT;
    //                 ctrl_val &= !CTRL_FUNCSEL_MASK;
    //                 ctrl_val |= FUNCSEL_NULL << CTRL_FUNCSEL_SHIFT;

    //                 pads_val |= PADS_OD_MASK;
    //                 pads_val &= !PADS_IE_MASK;
    //                 pads_val |= PADS_PDE_MASK;
    //                 pads_val &= !PADS_PUE_MASK;

    //                 write_volatile(ctrl_reg, ctrl_val);
    //                 write_volatile(pads_reg, pads_val);
    //             }
    //         },
    //         GPIOMode::Output => {
    //             self.set_pull_mode(TGPIOPullMode::Off);
    //             unsafe{
    //                 let rio0_out = Self::rio0_out(self.bank, RIO_SET_OFFSET);
    //                 write_volatile(rio0_out, self.bank_pin as u32);
    //             }
    //         },
    //         _ => {},
    //     }

    // }
    pub fn set_mode(&self, mode: GPIOMode) {
        let pads_reg = Self::pads0_ctrl(self.bank, self.bank_pin);
        let ctrl_reg = Self::gpio0_ctrl(self.bank, self.bank_pin);

        unsafe {
            let mut ctrl_val = read_volatile(ctrl_reg);
            let mut pads_val = read_volatile(pads_reg);

            ctrl_val &= !(CTRL_FUNCSEL_MASK | CTRL_OEOVER_MASK | CTRL_INOVER_MASK);
            pads_val &= !(PADS_PDE_MASK | PADS_PUE_MASK | PADS_OD_MASK | PADS_IE_MASK);
            match mode {
                GPIOMode::Input | GPIOMode::InputPullUp | GPIOMode::InputPullDown => {
                    pads_val |= PADS_IE_MASK;
                }
                _ => {}
            }

            match mode {
                GPIOMode::Input => {
                    ctrl_val |= FUNCSEL_NULL << CTRL_FUNCSEL_SHIFT;
                }
                GPIOMode::Output => {
                    ctrl_val |= FUNCSEL_NULL << CTRL_FUNCSEL_SHIFT;
                    ctrl_val |= OEOVER_ENABLE << CTRL_OEOVER_SHIFT;
                }
                GPIOMode::InputPullUp => {
                    pads_val |= PADS_PUE_MASK;
                }
                GPIOMode::InputPullDown => {
                    pads_val |= PADS_PDE_MASK;
                }

                _ => {}
            }

            write_volatile(ctrl_reg, ctrl_val);
            write_volatile(pads_reg, pads_val);
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
    pub fn get_mode(&self) -> GPIOMode {
        unsafe {
            let ctrl_reg = Self::gpio0_ctrl(self.bank, self.bank_pin);
            let pads_reg = Self::pads0_ctrl(self.bank, self.bank_pin);

            let ctrl_val = read_volatile(ctrl_reg);
            let pads_val = read_volatile(pads_reg);

            let func_sel = (ctrl_val & CTRL_FUNCSEL_MASK) >> CTRL_FUNCSEL_SHIFT;
            let oe_over = (ctrl_val & CTRL_OEOVER_MASK) >> CTRL_OEOVER_SHIFT;
            let is_input_enabled = pads_val & PADS_IE_MASK != 0;
            let is_pull_up_enabled = pads_val & PADS_PUE_MASK != 0;
            let is_pull_down_enabled = pads_val & PADS_PDE_MASK != 0;

            match func_sel {
                FUNCSEL_NULL => match (
                    is_input_enabled,
                    is_pull_up_enabled,
                    is_pull_down_enabled,
                    oe_over,
                ) {
                    (true, false, false, _) => GPIOMode::Input,
                    (true, true, false, _) => GPIOMode::InputPullUp,
                    (true, false, true, _) => GPIOMode::InputPullDown,
                    (_, false, false, OEOVER_ENABLE) => GPIOMode::Output,
                    _ => GPIOMode::GPIOModeUnknown,
                },
                _ => match func_sel {
                    0..=8 => match func_sel {
                        0 => GPIOMode::GPIOModeAlternateFunction0,
                        1 => GPIOMode::GPIOModeAlternateFunction1,
                        2 => GPIOMode::GPIOModeAlternateFunction2,
                        3 => GPIOMode::GPIOModeAlternateFunction3,
                        4 => GPIOMode::GPIOModeAlternateFunction4,
                        5 => GPIOMode::GPIOModeAlternateFunction5,
                        6 => GPIOMode::GPIOModeAlternateFunction6,
                        7 => GPIOMode::GPIOModeAlternateFunction7,
                        8 => GPIOMode::GPIOModeAlternateFunction8,
                        _ => GPIOMode::GPIOModeUnknown,
                    },
                    _ => GPIOMode::GPIOModeUnknown,
                },
            }
        }
    }

    /// Writes a value to the GPIO pin, setting it high or low.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to write to the pin (`true` for high, `false` for low).
    pub fn write(&self, value: bool) {
        let ctrl_reg = Self::gpio0_ctrl(self.bank, self.bank_pin);

        unsafe {
            let mut ctrl_value = core::ptr::read_volatile(ctrl_reg);

            ctrl_value &= !CTRL_OUTOVER_MASK;
            ctrl_value |= if value { OUTOVER_HIGH } else { OUTOVER_LOW } << CTRL_OUTOVER_SHIFT;
            write_volatile(ctrl_reg, ctrl_value);
        }
    }
}
