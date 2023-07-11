//! Board Support Package (BSP).
//!
//! - `raspi` is for Raspberry Pi 3 (Qemu) and 4.

use awkernel_lib::{
    device_tree::{
        device_tree::DeviceTree,
        node::{ArrayedNode, DeviceTreeNode},
    },
    local_heap,
};

pub mod config;
pub mod memory;

type DeviceTreeRef = &'static DeviceTree<'static, local_heap::LocalHeap<'static>>;
type DeviceTreeNodeRef = &'static DeviceTreeNode<'static, local_heap::LocalHeap<'static>>;
type StaticArrayedNode = ArrayedNode<'static, local_heap::LocalHeap<'static>>;

#[cfg(feature = "raspi")]
pub mod raspi;

#[cfg(feature = "raspi")]
use raspi::Raspi as SoCInitializer;

pub fn init() {
    #[cfg(feature = "raspi")]
    raspi::init();
}

pub unsafe fn init_device(
    device_tree: &'static DeviceTree<'static, local_heap::LocalHeap<'static>>,
) {
    // #[cfg(feature = "raspi")]
    // raspi::init_device();

    let mut soc = SoCInitializer::new();
    let _ = soc.init_device(device_tree);
}

pub trait SoC {
    /// Initialize the device first.
    /// This method will be invoked before `init_memory_map()` and `init()`.
    unsafe fn init_device(&mut self, device_tree: DeviceTreeRef) -> Result<(), &'static str>;

    /// Initialize the virtual memory.
    /// This method will be invoked after `init_device()` and before `init()`.
    unsafe fn init_virtual_memory(&self, device_tree: DeviceTreeRef);

    /// Initialize the AWkernel.
    /// This method will be invoked after `init_device()` and `init_virtual_memory()`.
    unsafe fn init(&self, device_tree: DeviceTreeRef);
}
