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
pub use raspi::Raspi as SoCInitializer;

pub fn init() {
    #[cfg(feature = "raspi")]
    raspi::init();
}

pub trait SoC {
    /// Initialize the device first.
    /// This method will be invoked before `init_memory_map()` and `init()`.
    unsafe fn init_device(&mut self) -> Result<(), &'static str>;

    /// Initialize the virtual memory.
    /// This method will be invoked after `init_device()` and before `init()`.
    ///
    /// Return the size of heap memory if the virtual memory is
    /// successfully initialized.
    unsafe fn init_virtual_memory(&self) -> Result<usize, &'static str>;

    /// Initialize the AWkernel.
    /// This method will be invoked after `init_device()` and `init_virtual_memory()`.
    unsafe fn init(&self);
}
