//! MC146818-compatible CMOS RTC driver for x86_64, x86

use super::{DateTime, RtcError};
use awkernel_lib::interrupt::InterruptGuard;
use core::arch::asm;

const IO_RTC: u16 = 0x070;

// The registers, and the bits within each register.

const MC_SEC: u8 = 0x00; // Time of year: seconds (0-59)
const MC_MIN: u8 = 0x02; // Time of year: minutes (0-59)
const MC_HOUR: u8 = 0x04; // Time of year: hour (see above)
const MC_DOW: u8 = 0x06; // Time of year: day of week (1-7)
const MC_DOM: u8 = 0x07; // Time of year: day of month (1-31)
const MC_MONTH: u8 = 0x08; // Time of year: month (1-12)
const MC_YEAR: u8 = 0x09; // Time of year: year in century (0-99)

const MC_REGA: u8 = 0x0a; // Control register A

const _MC_REGA_RSMASK: u8 = 0x0f; // Interrupt rate select mask
const _MC_REGA_DVMASK: u8 = 0x70; // Divisor select mask
const MC_REGA_UIP: u8 = 0x80; // Update in progress; read only

const MC_REGB: u8 = 0x0b; // Control register B

const _MC_REGB_DSE: u8 = 0x01; // Daylight Saving Enable
const MC_REGB_24HR: u8 = 0x02; // 24-hour mode (AM/PM mode when clear)
const _MC_REGB_DM: u8 = 0x04; // Binary mode (BCD mode when clear)
const _MC_REGB_SQWE: u8 = 0x08; // Square wave enable, ONLY in BQ3285E
const _MC_REGB_UIE: u8 = 0x10; // Update End interrupt enable
const _MC_REGB_AIE: u8 = 0x20; // Alarm interrupt enable
const _MC_REGB_PIE: u8 = 0x40; // Periodic interrupt enable
const MC_REGB_SET: u8 = 0x80; // Allow time to be set; stops updates

const _MC_REGC: u8 = 0x0c; // Control register C

const _MC_REGC_UF: u8 = 0x10; // Update End interrupt flag
const _MC_REGC_AF: u8 = 0x20; // Alarm interrupt flag
const _MC_REGC_PF: u8 = 0x40; // Periodic interrupt flag
const _MC_REGC_IRQF: u8 = 0x80; // Interrupt request pending flag

const MC_REGD: u8 = 0x0d; // Control register D

// MC_REGD_UNUSED 0x7f UNUSED
const MC_REGD_VRT: u8 = 0x80; // Valid RAM and Time bit

// Number of TOD registers
const _MC_NREGS: usize = 0xe; // 14 registers; CMOS follows
const MC_NTODREGS: usize = 0xa; // 10 of those are for TOD and alarm

type McTodRegs = [u8; MC_NTODREGS];

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
    fn mc146818_read(reg: u8) -> u8 {
        unsafe {
            asm!(
                "out dx, al",
                in("dx") IO_RTC,
                in("al") reg,
                options(nostack, preserves_flags)
            );

            awkernel_lib::delay::wait_microsec(1);

            let value: u8;
            asm!(
                "in al, dx",
                in("dx") IO_RTC + 1,
                out("al") value,
                options(nostack, preserves_flags)
            );
            value
        }
    }

    fn mc146818_write(reg: u8, value: u8) {
        unsafe {
            asm!(
                "out dx, al",
                in("dx") IO_RTC,
                in("al") reg,
                options(nostack, preserves_flags)
            );

            awkernel_lib::delay::wait_microsec(1);

            asm!(
                "out dx, al",
                in("dx") IO_RTC + 1,
                in("al") value,
                options(nostack, preserves_flags)
            );

            awkernel_lib::delay::wait_microsec(1);
        }
    }

    fn bcdtobin(bcd: u8) -> u8 {
        (((bcd >> 4) & 0x0f) * 10) + (bcd & 0x0f)
    }

    fn bintobcd(bin: u8) -> u8 {
        (((bin / 10) << 4) & 0xf0) | ((bin % 10) & 0x0f)
    }

    fn rtcget() -> Result<McTodRegs, RtcError> {
        let mut regs = [0u8; MC_NTODREGS];

        if (Self::mc146818_read(MC_REGD) & MC_REGD_VRT) == 0 {
            return Err(RtcError::HardwareError);
        }

        // update in progress; spin loop
        while (Self::mc146818_read(MC_REGA) & MC_REGA_UIP) != 0 {
            continue;
        }

        loop {
            // read all of the tod/alarm regs
            for (i, reg) in regs.iter_mut().enumerate().take(MC_NTODREGS) {
                *reg = Self::mc146818_read(i as u8);
            }

            if regs[MC_SEC as usize] == Self::mc146818_read(MC_SEC) {
                break;
            }
        }

        Ok(regs)
    }

    fn rtcput(regs: &McTodRegs) -> Result<(), RtcError> {
        // stop updates while setting
        Self::mc146818_write(MC_REGB, Self::mc146818_read(MC_REGB) | MC_REGB_SET);

        // write all of the tod/alarm regs
        for (i, &reg) in regs.iter().enumerate().take(MC_NTODREGS) {
            Self::mc146818_write(i as u8, reg);
        }

        // reenable updates
        Self::mc146818_write(MC_REGB, Self::mc146818_read(MC_REGB) & !MC_REGB_SET);

        Ok(())
    }

    pub fn gettime(&self) -> Result<DateTime, RtcError> {
        let regs = {
            let _guard = InterruptGuard::new();
            Self::rtcget()?
        };

        let second = Self::bcdtobin(regs[MC_SEC as usize]);
        let minute = Self::bcdtobin(regs[MC_MIN as usize]);
        let hour = Self::bcdtobin(regs[MC_HOUR as usize]);
        let day = Self::bcdtobin(regs[MC_DOM as usize]);
        let month = Self::bcdtobin(regs[MC_MONTH as usize]);
        let year = Self::bcdtobin(regs[MC_YEAR as usize]);

        // TODO: clock_expandyear()
        let full_year = 2000 + year as u16;

        Ok(DateTime::new(full_year, month, day, hour, minute, second))
    }

    pub fn settime(&self, time: &DateTime) -> Result<(), RtcError> {
        let mut regs = [0u8; MC_NTODREGS];

        regs[MC_SEC as usize] = Self::bintobcd(time.second);
        regs[MC_MIN as usize] = Self::bintobcd(time.minute);
        regs[MC_HOUR as usize] = Self::bintobcd(time.hour);
        regs[MC_DOM as usize] = Self::bintobcd(time.day);
        regs[MC_MONTH as usize] = Self::bintobcd(time.month);
        regs[MC_YEAR as usize] = Self::bintobcd((time.year % 100) as u8);

        // Day of week (1-7) - not calculated currently, just using placeholder
        // NOTE: Implement day of week calculation if needed
        regs[MC_DOW as usize] = 1;

        regs[7] = 0;
        regs[8] = 0;
        regs[9] = 0;

        {
            let _guard = InterruptGuard::new();
            Self::rtcput(&regs)?;
        }

        // TODO: century byte update

        Ok(())
    }

    pub fn init(&self) {
        Self::mc146818_write(MC_REGB, MC_REGB_24HR);
    }
}
