#![feature(allocator_api)]
#![cfg_attr(not(test), no_std)]

extern crate alloc;

pub mod device;
pub mod framebuffer;
pub mod hal;
pub mod ic;
pub mod if_media;
pub mod interrupt_controller;
pub mod raspi5;
// pub mod mii;
pub mod uart;

#[cfg(feature = "aarch64")]
pub mod psci;

#[cfg(feature = "pcie")]
pub mod pcie;
