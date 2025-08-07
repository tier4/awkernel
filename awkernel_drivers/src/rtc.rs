//! Real-Time Clock (RTC) driver support

#[cfg(any(target_arch = "x86", target_arch = "x86_64", feature = "x86"))]
pub mod mc146818;

#[cfg(any(target_arch = "x86", target_arch = "x86_64", feature = "x86"))]
pub use mc146818::Mc146818Rtc;

#[derive(Debug, Clone, Copy)]
pub struct DateTime {
    pub year: u16,  // Full year (e.g., 2024)
    pub month: u8,  // 1-12
    pub day: u8,    // 1-31
    pub hour: u8,   // 0-23 (24-hour format)
    pub minute: u8, // 0-59
    pub second: u8, // 0-59
}

impl DateTime {
    pub fn new(year: u16, month: u8, day: u8, hour: u8, minute: u8, second: u8) -> Self {
        Self {
            year,
            month,
            day,
            hour,
            minute,
            second,
        }
    }
}
