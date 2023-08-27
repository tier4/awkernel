#![cfg_attr(not(test), no_std)]

extern crate alloc;

pub mod framebuffer;
pub mod hal;
pub mod interrupt_controler;
pub mod net;
pub mod uart;

#[cfg(all(feature = "x86", not(feature = "std")))]
pub mod pcie;

#[cfg(feature = "aarch64")]
pub mod psci;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}
