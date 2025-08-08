//! MC146818-compatible CMOS RTC driver for x86_64, x86

use super::RtcError;
use core::arch::asm;

const _IO_RTC: u16 = 0x070;

// The registers, and the bits within each register.

const _MC_SEC: u8 = 0x00; // Time of year: seconds (0-59)
const _MC_MIN: u8 = 0x02; // Time of year: minutes (0-59)
const _MC_HOUR: u8 = 0x04; // Time of year: hour (see above)
const _MC_DOW: u8 = 0x06; // Time of year: day of week (1-7)
const _MC_DOM: u8 = 0x07; // Time of year: day of month (1-31)
const _MC_MONTH: u8 = 0x08; // Time of year: month (1-12)
const _MC_YEAR: u8 = 0x09; // Time of year: year in century (0-99)

const _MC_REGA: u8 = 0x0a; // Control register A

const _MC_REGA_RSMASK: u8 = 0x0f; // Interrupt rate select mask
const _MC_REGA_DVMASK: u8 = 0x70; // Divisor select mask
const _MC_REGA_UIP: u8 = 0x80; // Update in progress; read only

const _MC_REGB: u8 = 0x0b; // Control register B

const _MC_REGB_DSE: u8 = 0x01; // Daylight Saving Enable
const _MC_REGB_24HR: u8 = 0x02; // 24-hour mode (AM/PM mode when clear)
const _MC_REGB_DM: u8 = 0x04; // Binary mode (BCD mode when clear)
const _MC_REGB_SQWE: u8 = 0x08; // Square wave enable, ONLY in BQ3285E
const _MC_REGB_UIE: u8 = 0x10; // Update End interrupt enable
const _MC_REGB_AIE: u8 = 0x20; // Alarm interrupt enable
const _MC_REGB_PIE: u8 = 0x40; // Periodic interrupt enable
const _MC_REGB_SET: u8 = 0x80; // Allow time to be set; stops updates

const _MC_REGC: u8 = 0x0c; // Control register C

const _MC_REGC_UF: u8 = 0x10; // Update End interrupt flag
const _MC_REGC_AF: u8 = 0x20; // Alarm interrupt flag
const _MC_REGC_PF: u8 = 0x40; // Periodic interrupt flag
const _MC_REGC_IRQF: u8 = 0x80; // Interrupt request pending flag

const _MC_REGD: u8 = 0x0d; // Control register D

// MC_REGD_UNUSED 0x7f UNUSED
const _MC_REGD_VRT: u8 = 0x80; // Valid RAM and Time bit

// Number of TOD registers
const _MC_NREGS: usize = 0xe; // 14 registers; CMOS follows
const _MC_NTODREGS: usize = 0xa; // 10 of those are for TOD and alarm

type _McTodRegs = [u8; _MC_NTODREGS];

pub struct Mc146818Rtc;

impl Mc146818Rtc {
    pub fn new() -> Self {
        Self
    }
}

impl Default for Mc146818Rtc {
    fn default() -> Self {
        Self::new()
    }
}
impl Mc146818Rtc {
    fn _mc146818_read(reg: u8) -> u8 {
        unsafe {
            asm!(
                "out dx, al",
                in("dx") _IO_RTC,
                in("al") reg,
                options(nostack, preserves_flags)
            );

            awkernel_lib::delay::wait_microsec(1);

            let value: u8;
            asm!(
                "in al, dx",
                in("dx") _IO_RTC + 1,
                out("al") value,
                options(nostack, preserves_flags)
            );
            value
        }
    }

    fn _mc146818_write(reg: u8, value: u8) {
        unsafe {
            asm!(
                "out dx, al",
                in("dx") _IO_RTC,
                in("al") reg,
                options(nostack, preserves_flags)
            );

            awkernel_lib::delay::wait_microsec(1);

            asm!(
                "out dx, al",
                in("dx") _IO_RTC + 1,
                in("al") value,
                options(nostack, preserves_flags)
            );

            awkernel_lib::delay::wait_microsec(1);
        }
    }

    fn _bcdtobin(bcd: u8) -> u8 {
        (((bcd >> 4) & 0x0f) * 10) + (bcd & 0x0f)
    }

    fn _bintobcd(bin: u8) -> u8 {
        (((bin / 10) << 4) & 0xf0) | ((bin % 10) & 0x0f)
    }

    fn _rtcget() -> Result<_McTodRegs, RtcError> {
        let mut regs = [0u8; _MC_NTODREGS];

        if (Self::_mc146818_read(_MC_REGD) & _MC_REGD_VRT) == 0 {
            return Err(RtcError::HardwareError);
        }

        // update in progress; spin loop
        while (Self::_mc146818_read(_MC_REGA) & _MC_REGA_UIP) != 0 {
            continue;
        }

        loop {
            // read all of the tod/alarm regs
            for i in 0.._MC_NTODREGS {
                regs[i] = Self::_mc146818_read(i as u8);
            }

            if regs[_MC_SEC as usize] == Self::_mc146818_read(_MC_SEC) {
                break;
            }
        }

        Ok(regs)
    }

    fn _rtcput(regs: &_McTodRegs) -> Result<(), RtcError> {
        // stop updates while setting
        Self::_mc146818_write(_MC_REGB, Self::_mc146818_read(_MC_REGB) | _MC_REGB_SET);

        // write all of the tod/alarm regs
        for i in 0.._MC_NTODREGS {
            Self::_mc146818_write(i as u8, regs[i]);
        }

        // reenable updates
        Self::_mc146818_write(_MC_REGB, Self::_mc146818_read(_MC_REGB) & !_MC_REGB_SET);

        Ok(())
    }
}
