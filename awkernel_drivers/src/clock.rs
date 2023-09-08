use core::{
    hint,
    ptr::{read_volatile, write_volatile},
};

/// Base address for the CLK module
pub static mut CLK_BASE: usize = 0;

/// Set the base address for the CLK module
///
/// # Safety
///
/// This function is unsafe because it modifies a static mutable variable.
pub unsafe fn set_clk_base(base: usize) {
    write_volatile(&mut CLK_BASE, base);
}

pub static mut CLOCK_FREQUENCY: usize = 0;

/// Get the clock frequency
///
/// # Safety
///
/// This function is unsafe because it modifies a static mutable variable.
pub unsafe fn get_clock_frequency(base: usize) {
    write_volatile(&mut CLOCK_FREQUENCY, base);
}

/// Registers associated with the CLK module
pub mod registers {
    use awkernel_lib::mmio_rw;
    use bitflags::bitflags;

    mmio_rw!(offset 0x70 => pub GP0CTL<GPCTL>); // General Purpose Clock 0 Control
    mmio_rw!(offset 0x74 => pub GP0DIV<u32>); // General Purpose Clock 0 Divisors
    mmio_rw!(offset 0x78 => pub GP1CTL<GPCTL>); // General Purpose Clock 1 Control
    mmio_rw!(offset 0x7c => pub GP1DIV<u32>); // General Purpose Clock 1 Divisors
    mmio_rw!(offset 0x80 => pub GP2CTL<GPCTL>); // General Purpose Clock 2 Control
    mmio_rw!(offset 0x84 => pub GP2DIV<u32>); // General Purpose Clock 2 Divisors
    mmio_rw!(offset 0xa0 => pub PWMCTL<GPCTL>); // PWM Clock Control
    mmio_rw!(offset 0xa4 => pub PWMDIV<u32>); // PWM Clock Divisors

    bitflags! {
        pub struct GPCTL: u32 {
            const PASSWD = 0x5a << 24; // Clock Manager password "5a"
            const MASH_0 = 0 << 9; // Integer division
            const MASH_1 = 1 << 9; // 1-stage MASH
            const MASH_2 = 2 << 9; // 2-stage MASH
            const MASH_3 = 3 << 9; // 3-stage MASH
            const FLIP = 1 << 8; // Invert the clock generator output
            const BUSY = 1 << 7; // Clock generator is running
            const KILL = 1 << 5; // Kill the clock generator
            const ENAB = 1 << 4; // Enable the clock generator
            const SRC_GND = 0; // GND
            const SRC_OSCILLATOR = 1; // Oscillator
            const SRC_TESTDEBUG0 = 2; // testdebug0
            const SRC_TESTDEBUG1 = 3; // testdebug1
            const SRC_PLLA_PER = 4; // PLLA per
            const SRC_PLLC_PER = 5; // PLLC per
            const SRC_PLLD_PER = 6; // PLLD per
            const SRC_HDMI_AUX = 7; // HDMI auxiliary
        }
    }
}

/// Possible sources for the clock
pub enum ClockSource {
    Oscillator,
    PLLDPer,
}

/// Possible MASH types for the clock
pub enum MashType {
    Integer,
    Stage1,
    Stage2,
    Stage3,
}

pub struct Clock {
    base: usize,
}

impl Clock {
    /// Creates a new instance of the CLK module
    pub fn new() -> Self {
        let base = unsafe { read_volatile(&CLK_BASE) };
        Self { base }
    }

    /// Enables the general-purpose clock with given configurations
    pub fn enable_gp_clock(
        &self,
        source: ClockSource,
        divi: u32,
        divf: u32,
        mash: MashType,
    ) -> Result<(), &'static str> {
        if divi > 4095 {
            return Err("Invalid divi");
        }
        if divf > 4095 {
            return Err("Invalid divf");
        }

        let mut ctl = registers::GPCTL::PASSWD | registers::GPCTL::KILL;
        registers::GP0CTL.write(ctl, self.base);

        while registers::GP0CTL
            .read(self.base)
            .contains(registers::GPCTL::BUSY)
        {
            hint::spin_loop();
        }

        let div = (registers::GPCTL::PASSWD.bits() | (divi << 12) | divf);
        registers::GP0DIV.write(div, self.base);

        ctl = registers::GPCTL::PASSWD
            | match mash {
                MashType::Integer => registers::GPCTL::MASH_0,
                MashType::Stage1 => registers::GPCTL::MASH_1,
                MashType::Stage2 => registers::GPCTL::MASH_2,
                MashType::Stage3 => registers::GPCTL::MASH_3,
            }
            | match source {
                ClockSource::Oscillator => registers::GPCTL::SRC_OSCILLATOR,
                ClockSource::PLLDPer => registers::GPCTL::SRC_PLLD_PER,
            }
            | registers::GPCTL::ENAB;
        registers::GP0CTL.write(ctl, self.base);

        Ok(())
    }

    /// Disables the general-purpose clock
    pub fn disable_gp_clock(&self) {
        let ctl = registers::GPCTL::PASSWD;
        registers::GP0CTL.write(ctl, self.base);
    }

    /// Enables the PWM clock with given configurations
    pub fn enable_pwm_clock(
        &self,
        source: ClockSource,
        divi: u32,
        divf: u32,
        mash: MashType,
    ) -> Result<(), &'static str> {
        if divi > 4095 {
            return Err("Invalid divi");
        }
        if divf > 4095 {
            return Err("Invalid divf");
        }

        // Kill the clock if busy
        let mut ctl = registers::GPCTL::PASSWD | registers::GPCTL::KILL;
        registers::PWMCTL.write(ctl, self.base);

        while registers::PWMCTL
            .read(self.base)
            .contains(registers::GPCTL::BUSY)
        {
            hint::spin_loop();
        }

        let div = (registers::GPCTL::PASSWD.bits() | (divi << 12) | divf);
        registers::PWMDIV.write(div, self.base);

        ctl = registers::GPCTL::PASSWD
            | match mash {
                MashType::Integer => registers::GPCTL::MASH_0,
                MashType::Stage1 => registers::GPCTL::MASH_1,
                MashType::Stage2 => registers::GPCTL::MASH_2,
                MashType::Stage3 => registers::GPCTL::MASH_3,
            }
            | match source {
                ClockSource::Oscillator => registers::GPCTL::SRC_OSCILLATOR,
                ClockSource::PLLDPer => registers::GPCTL::SRC_PLLD_PER,
            }
            | registers::GPCTL::ENAB;
        registers::PWMCTL.write(ctl, self.base);

        Ok(())
    }

    /// Disables the PWM clock
    pub fn disable_pwm_clock(&self) {
        let ctl = registers::GPCTL::PASSWD;
        registers::PWMCTL.write(ctl, self.base);
    }
}

impl Default for Clock {
    fn default() -> Self {
        Self::new()
    }
}