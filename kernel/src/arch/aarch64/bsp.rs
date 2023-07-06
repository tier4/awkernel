//! Board Support Package (BSP).
//!
//! - `raspi` is for Raspberry Pi 3 (Qemu) and 4.

use awkernel_lib::{
    delay,
    device_tree::{device_tree::DeviceTree, prop::PropertyValue},
    local_heap,
};

pub mod config;
pub mod memory;

#[cfg(feature = "raspi")]
pub mod raspi;

pub fn init() {
    #[cfg(feature = "raspi")]
    raspi::init();
}

pub unsafe fn init_device(
    device_tree: &'static DeviceTree<'static, local_heap::LocalHeap<'static>>,
) {
    #[cfg(feature = "raspi")]
    raspi::init_device();
}
