#![cfg_attr(not(test), no_std)]

extern crate alloc;

pub mod clock;
pub mod device;
pub mod framebuffer;
pub mod hal;
pub mod interrupt_controller;
pub mod net;
#[allow(dead_code)] // TODO: remove this.
pub mod pcie;
pub mod uart;

#[cfg(feature = "aarch64")]
pub mod psci;
