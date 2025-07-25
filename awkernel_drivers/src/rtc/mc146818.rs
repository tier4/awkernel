//! MC146818-compatible CMOS RTC driver for x86_64
//! 
//! Based on OpenBSD's implementation in sys/arch/amd64/isa/clock.c
//! and sys/dev/ic/mc146818reg.h

use super::{DateTime, RtcError};
use core::arch::asm;

// OpenBSD: sys/dev/isa/isareg.h - IO_RTC definitions
const IO_RTC: u16 = 0x070;  // RTC I/O base address

// OpenBSD: sys/dev/ic/mc146818reg.h - MC146818 register definitions
// Time registers
const MC_SEC: u8 = 0x00;    // Seconds register
const MC_MIN: u8 = 0x02;    // Minutes register
const MC_HOUR: u8 = 0x04;   // Hours register
const MC_DOW: u8 = 0x06;    // Day of week register (1-7)
const MC_DOM: u8 = 0x07;    // Day of month register (1-31)
const MC_MONTH: u8 = 0x08;  // Month register (1-12)
const MC_YEAR: u8 = 0x09;   // Year register (0-99)

// Control registers
const MC_REGA: u8 = 0x0a;   // Control register A
const MC_REGB: u8 = 0x0b;   // Control register B
const MC_REGC: u8 = 0x0c;   // Control register C
const MC_REGD: u8 = 0x0d;   // Control register D

// Control register B bits
const MC_REGB_SET: u8 = 0x80;   // Set time bit (halt updates)
const MC_REGB_PIE: u8 = 0x40;   // Periodic interrupt enable
const MC_REGB_AIE: u8 = 0x20;   // Alarm interrupt enable
const MC_REGB_UIE: u8 = 0x10;   // Update-ended interrupt enable
const MC_REGB_SQWE: u8 = 0x08;  // Square wave enable
const MC_REGB_DM: u8 = 0x04;    // Data mode (1 = binary, 0 = BCD)
const MC_REGB_24HR: u8 = 0x02;  // 24-hour mode (1 = 24hr, 0 = 12hr)
const MC_REGB_DSE: u8 = 0x01;   // Daylight savings enable

// Control register A bits
const MC_REGA_UIP: u8 = 0x80;   // Update in progress bit

// NVRAM offset for century byte
const NVRAM_CENTURY: u8 = 0x32;

// Number of TOD registers (OpenBSD: MC_NTODREGS)
const MC_NTODREGS: usize = 0xa;

// OpenBSD: typedef u_int mc_todregs[MC_NTODREGS];
type McTodRegs = [u8; MC_NTODREGS];

/// MC146818-compatible CMOS RTC driver
pub struct Mc146818Rtc;

impl Mc146818Rtc {
    /// Create a new MC146818 RTC instance
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
    /// OpenBSD: mc146818_read() from sys/arch/amd64/isa/clock.c
    /// Read a byte from the MC146818 RTC register
    fn mc146818_read(reg: u8) -> u8 {
        unsafe {
            // outb(IO_RTC, reg);
            asm!(
                "out dx, al",
                in("dx") IO_RTC,
                in("al") reg,
                options(nostack, preserves_flags)
            );
            
            // DELAY(1) - small delay
            Self::delay();
            
            // return inb(IO_RTC+1);
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

    /// OpenBSD: mc146818_write() from sys/arch/amd64/isa/clock.c
    /// Write a byte to the MC146818 RTC register
    fn mc146818_write(reg: u8, value: u8) {
        unsafe {
            // outb(IO_RTC, reg);
            asm!(
                "out dx, al",
                in("dx") IO_RTC,
                in("al") reg,
                options(nostack, preserves_flags)
            );
            
            // DELAY(1)
            Self::delay();
            
            // outb(IO_RTC+1, datum);
            asm!(
                "out dx, al",
                in("dx") IO_RTC + 1,
                in("al") value,
                options(nostack, preserves_flags)
            );
            
            // DELAY(1)
            Self::delay();
        }
    }

    /// Small delay function (OpenBSD uses DELAY(1))
    #[inline]
    fn delay() {
        // Simple delay using nop instructions
        unsafe {
            asm!("nop; nop; nop; nop", options(nostack, preserves_flags));
        }
    }

    /// OpenBSD: bcdtobin() - Convert BCD to binary
    fn bcdtobin(bcd: u8) -> u8 {
        ((bcd >> 4) * 10) + (bcd & 0x0f)
    }

    /// OpenBSD: bintobcd() - Convert binary to BCD
    fn bintobcd(bin: u8) -> u8 {
        ((bin / 10) << 4) | (bin % 10)
    }

    /// OpenBSD: rtcget() - Read all RTC time registers atomically
    fn rtcget() -> Result<McTodRegs, RtcError> {
        let mut regs = [0u8; MC_NTODREGS];
        
        // OpenBSD: if ((mc146818_read(NULL, MC_REGD) & MC_REGD_VRT) == 0)
        // Check if battery is OK (VRT = Valid RAM and Time)
        if (Self::mc146818_read(MC_REGD) & 0x80) == 0 {
            return Err(RtcError::HardwareError);
        }
        
        // OpenBSD: MC146818_GETTOD macro implementation
        // Wait until update is not in progress
        while (Self::mc146818_read(MC_REGA) & MC_REGA_UIP) != 0 {
            // Spin loop waiting for update to complete
        }
        
        // Read all registers twice to ensure consistency
        loop {
            // Read all TOD registers
            for i in 0..MC_NTODREGS {
                regs[i] = Self::mc146818_read(i as u8);
            }
            
            // Re-read seconds register to ensure no update occurred
            if regs[MC_SEC as usize] == Self::mc146818_read(MC_SEC) {
                break;
            }
        }
        
        Ok(regs)
    }
    
    /// OpenBSD: rtcput() - Write all RTC time registers atomically
    fn rtcput(regs: &McTodRegs) -> Result<(), RtcError> {
        // OpenBSD: MC146818_PUTTOD macro implementation
        
        // Stop updates while setting
        let regb = Self::mc146818_read(MC_REGB);
        Self::mc146818_write(MC_REGB, regb | MC_REGB_SET);
        
        // Write all TOD registers
        for i in 0..MC_NTODREGS {
            Self::mc146818_write(i as u8, regs[i]);
        }
        
        // Re-enable updates
        Self::mc146818_write(MC_REGB, regb & !MC_REGB_SET);
        
        Ok(())
    }

    /// Read the current time from the RTC
    /// OpenBSD: rtcgettime()
    pub fn read_time(&self) -> Result<DateTime, RtcError> {
        // Get RTC registers
        let regs = Self::rtcget()?;
        
        // Convert BCD to binary for all time fields
        let second = Self::bcdtobin(regs[MC_SEC as usize]);
        let minute = Self::bcdtobin(regs[MC_MIN as usize]);
        let hour = Self::bcdtobin(regs[MC_HOUR as usize]);
        let day = Self::bcdtobin(regs[MC_DOM as usize]);
        let month = Self::bcdtobin(regs[MC_MONTH as usize]);
        let year = Self::bcdtobin(regs[MC_YEAR as usize]);
        
        // TODO: Implement clock_expandyear() for century handling
        // For now, assume 21st century
        let full_year = 2000 + year as u16;
        
        Ok(DateTime::new(full_year, month, day, hour, minute, second))
    }

    /// Set the RTC time
    /// OpenBSD: rtcsettime()
    pub fn set_time(&self, time: &DateTime) -> Result<(), RtcError> {
        let mut regs = [0u8; MC_NTODREGS];
        
        // Convert time to BCD and store in registers
        regs[MC_SEC as usize] = Self::bintobcd(time.second);
        regs[MC_MIN as usize] = Self::bintobcd(time.minute);
        regs[MC_HOUR as usize] = Self::bintobcd(time.hour);
        regs[MC_DOM as usize] = Self::bintobcd(time.day);
        regs[MC_MONTH as usize] = Self::bintobcd(time.month);
        regs[MC_YEAR as usize] = Self::bintobcd((time.year % 100) as u8);
        
        // Day of week - not critical, set to 1 (Sunday)
        regs[MC_DOW as usize] = 1;
        
        // Set alarm registers to 0 (disabled)
        regs[7] = 0;  // Alarm seconds
        regs[8] = 0;  // Alarm minutes
        regs[9] = 0;  // Alarm hours
        
        // Write registers to RTC
        Self::rtcput(&regs)?;
        
        // TODO: Update century byte in NVRAM if needed
        
        Ok(())
    }

    /// Initialize the RTC (OpenBSD: rtcinit())
    pub fn init(&self) -> Result<(), RtcError> {
        // Set 24-hour mode
        let regb = Self::mc146818_read(MC_REGB);
        Self::mc146818_write(MC_REGB, regb | MC_REGB_24HR);
        
        Ok(())
    }
}