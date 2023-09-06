use core::{
    hint,
    ptr::{read_volatile, write_volatile},
};

pub static mut CLK_BASE: usize = 0;

pub unsafe fn set_clk_base(base: usize) {
    write_volatile(&mut CLK_BASE, base);
}

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
            const SRC_GND = 0 << 0; // GND
            const SRC_OSCILLATOR = 1 << 0; // Oscillator
            const SRC_TESTDEBUG0 = 2 << 0; // testdebug0
            const SRC_TESTDEBUG1 = 3 << 0; // testdebug1
            const SRC_PLLA_PER = 4 << 0; // PLLA per
            const SRC_PLLC_PER = 5 << 0; // PLLC per
            const SRC_PLLD_PER = 6 << 0; // PLLD per
            const SRC_HDMI_AUX = 7 << 0; // HDMI auxiliary
        }
    }
}

pub enum ClockSource {
    Oscillator,
    PLLDPer,
}

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
    pub fn new() -> Self {
        let base = unsafe { read_volatile(&CLK_BASE) };
        Self { base }
    }

    pub fn enable_gp_clock(
        &self,
        source: u32,
        divi: u32,
        divf: u32,
        mash: u32,
    ) -> Result<(), &'static str> {
        if source > 7 {
            return Err("Invalid source");
        }
        if divi > 4095 {
            return Err("Invalid divi");
        }
        if divf > 4095 {
            return Err("Invalid divf");
        }
        if mash > 3 {
            return Err("Invalid mash");
        }

        // Disable clock
        let password = registers::GPCTL::PASSWD;
        registers::GP0CTL.write(password, self.base);
        // Wait for clock to stop
        while registers::GP0CTL
            .read(self.base)
            .contains(registers::GPCTL::BUSY)
        {}
        // Configure clock source, MASH, divisor, and enable clock
        let mut ctl = registers::GPCTL::PASSWD | registers::GPCTL::ENAB;
        ctl |= match mash {
            1 => registers::GPCTL::MASH_1,
            2 => registers::GPCTL::MASH_2,
            3 => registers::GPCTL::MASH_3,
            _ => registers::GPCTL::MASH_0,
        };
        ctl |= match source {
            1 => registers::GPCTL::SRC_OSCILLATOR,
            2 => registers::GPCTL::SRC_TESTDEBUG0,
            3 => registers::GPCTL::SRC_TESTDEBUG1,
            4 => registers::GPCTL::SRC_PLLA_PER,
            5 => registers::GPCTL::SRC_PLLC_PER,
            6 => registers::GPCTL::SRC_PLLD_PER,
            7 => registers::GPCTL::SRC_HDMI_AUX,
            _ => registers::GPCTL::SRC_OSCILLATOR,
        };

        ctl.remove(registers::GPCTL::SRC_GND);

        let div = (registers::GPCTL::PASSWD.bits() | (divi << 12) | divf) as u32;

        registers::GP0DIV.write(div, self.base);
        registers::GP0CTL.write(ctl, self.base);
        Ok(())
    }

    pub fn disable_gp_clock(&self) {
        let password = registers::GPCTL::PASSWD;
        registers::GP0CTL.write(password, self.base);
    }

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

        // Set clock divisors
        let div = (registers::GPCTL::PASSWD.bits() | (divi << 12) | divf) as u32;
        registers::PWMDIV.write(div, self.base);

        // Configure clock source and MASH
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

    pub fn disable_pwm_clock(&self) {
        let ctl = registers::GPCTL::PASSWD;
        registers::PWMCTL.write(ctl, self.base);
    }
}
