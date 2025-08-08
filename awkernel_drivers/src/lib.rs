#![feature(allocator_api)]
#![cfg_attr(not(test), no_std)]

extern crate alloc;

pub mod device;
pub mod hal;
pub mod ic;
pub mod if_media;
pub mod interrupt_controller;
pub mod uart;

#[cfg(feature = "aarch64")]
pub mod psci;

#[cfg(feature = "aarch64")]
pub mod raspi5;

#[cfg(feature = "pcie")]
pub mod pcie;

#[cfg(feature = "mii")]
pub mod mii;

#[cfg(feature = "x86")]
pub mod rtc;
