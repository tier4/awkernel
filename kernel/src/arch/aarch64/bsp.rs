//! Board Support Package (BSP).
//!
//! - `raspi` is for Raspberry Pi 3 (Qemu) and 4.

use awkernel_lib::{
    device_tree::{device_tree::DeviceTree, node::DeviceTreeNode},
    local_heap,
};

pub mod config;
pub mod memory;

type DeviceTreeRef = &'static DeviceTree<'static, local_heap::LocalHeap<'static>>;
type DeviceTreeNoeRef = &'static DeviceTreeNode<'static, local_heap::LocalHeap<'static>>;

#[cfg(feature = "raspi")]
pub mod raspi;

#[cfg(feature = "raspi")]
use raspi::Raspi as SoCInit;

pub fn init() {
    #[cfg(feature = "raspi")]
    raspi::init();
}

pub unsafe fn init_device(
    device_tree: &'static DeviceTree<'static, local_heap::LocalHeap<'static>>,
) {
    #[cfg(feature = "raspi")]
    raspi::init_device();

    SoCInit::init_device(device_tree);
}

pub trait SoC {
    unsafe fn init_device(device_tree: DeviceTreeRef);

    unsafe fn init_memory_map(device_tree: DeviceTreeRef);

    unsafe fn init(device_tree: DeviceTreeRef);
}
