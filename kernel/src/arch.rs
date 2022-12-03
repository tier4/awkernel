#[cfg(feature = "aarch64")]
mod aarch64;

#[cfg(feature = "x86")]
mod x86_64;

#[cfg(feature = "linux")]
pub mod linux;

pub mod config;

// Delay.

#[cfg(feature = "aarch64")]
pub type ArchDelay = self::aarch64::delay::ArchDelay;

#[cfg(feature = "x86")]
pub type ArchDelay = self::x86_64::delay::ArchDelay;

#[cfg(feature = "linux")]
pub type ArchDelay = self::linux::delay::ArchDelay;

impl ArchDelay where ArchDelay: Delay {}

pub trait Delay {
    fn wait_interrupt();
    fn wait_forever() -> ! {
        loop {
            Self::wait_interrupt();
        }
    }
}
