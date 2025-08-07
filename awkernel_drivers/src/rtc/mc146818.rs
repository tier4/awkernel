//! MC146818-compatible CMOS RTC driver for x86_64, x86

use super::{DateTime, RtcError};
use core::arch::asm;

const IO_RTC: u16 = 0x070;

// Time of year registers
const MC_SEC: u8 = 0x00; // Time of year: seconds (0-59)
const MC_MIN: u8 = 0x02; // Time of year: minutes (0-59)
const MC_HOUR: u8 = 0x04; // Time of year: hour (see above)
const MC_DOW: u8 = 0x06; // Time of year: day of week (1-7)
const MC_DOM: u8 = 0x07; // Time of year: day of month (1-31)
const MC_MONTH: u8 = 0x08; // Time of year: month (1-12)
const MC_YEAR: u8 = 0x09; // Time of year: year in century (0-99)

const MC_REGA: u8 = 0x0a; // Control register A
const MC_REGB: u8 = 0x0b; // Control register B
#[allow(dead_code)]
const MC_REGC: u8 = 0x0c; // Control register C
const MC_REGD: u8 = 0x0d; // Control register D

// Control register B bits
const MC_REGB_SET: u8 = 0x80; // Allow time to be set; stops updates
#[allow(dead_code)]
const MC_REGB_PIE: u8 = 0x40; // Periodic interrupt enable
#[allow(dead_code)]
const MC_REGB_AIE: u8 = 0x20; // Alarm interrupt enable
#[allow(dead_code)]
const MC_REGB_UIE: u8 = 0x10; // Update End interrupt enable
#[allow(dead_code)]
const MC_REGB_SQWE: u8 = 0x08; // Square wave enable, ONLY in BQ3285E
#[allow(dead_code)]
const MC_REGB_DM: u8 = 0x04; // Binary mode (BCD mode when clear)
const MC_REGB_24HR: u8 = 0x02; // 24-hour mode (AM/PM mode when clear)
#[allow(dead_code)]
const MC_REGB_DSE: u8 = 0x01; // Daylight Saving Enable

// Control register A bits
const MC_REGA_UIP: u8 = 0x80; // Update in progress; read only
#[allow(dead_code)]
const MC_REGA_RSMASK: u8 = 0x0f; // Interrupt rate select mask
#[allow(dead_code)]
const MC_REGA_DVMASK: u8 = 0x70; // Divisor select mask
#[allow(dead_code)]
const MC_BASE_32_KHZ: u8 = 0x20; // 32.768 KHz timebase

// Control register C bits (read-only, cleared by read)
#[allow(dead_code)]
const MC_REGC_IRQF: u8 = 0x80; // Interrupt request pending flag
#[allow(dead_code)]
const MC_REGC_PF: u8 = 0x40; // Periodic interrupt flag
#[allow(dead_code)]
const MC_REGC_AF: u8 = 0x20; // Alarm interrupt flag
#[allow(dead_code)]
const MC_REGC_UF: u8 = 0x10; // Update End interrupt flag

// Control register D bits
const MC_REGD_VRT: u8 = 0x80; // Valid RAM and Time bit

// NVRAM offset for century byte
#[allow(dead_code)]
const NVRAM_CENTURY: u8 = 0x32;

// Number of TOD registers
const MC_NTODREGS: usize = 0xa;

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
}
