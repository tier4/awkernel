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

// The xHCI driver needs DMA and MMIO, but its USB descriptor parsers and its
// buffer placement are plain computations, so their unit tests also run on the
// host.  They are `pub` like the driver's modules, so their API is not reported
// as unused.
#[cfg(all(test, not(feature = "pcie")))]
#[path = "pcie/usb/xhci"]
pub mod xhci_descriptors {
    pub mod cdc_acm;
    pub mod desc;
    pub mod trb_buffer;
}

#[cfg(feature = "mii")]
pub mod mii;

#[cfg(feature = "x86")]
pub mod rtc;
