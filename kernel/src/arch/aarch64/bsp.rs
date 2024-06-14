//! Board Support Package (BSP).
//!
//! - `raspi` is for Raspberry Pi 3 (Qemu) and 4.
//! - `aarch64_virt` is for Qemu's AArch64 generic virtual platform.

use awkernel_lib::{
    addr::virt_addr::VirtAddr,
    device_tree::{
        node::{ArrayedNode, DeviceTreeNode},
        DeviceTree,
    },
    local_heap,
};

pub mod config;
pub mod memory;

pub(super) type DeviceTreeRef =
    &'static DeviceTree<'static, local_heap::LocalHeap<'static, 'static>>;

#[allow(dead_code)]
pub(super) type DeviceTreeNodeRef =
    &'static DeviceTreeNode<'static, local_heap::LocalHeap<'static, 'static>>;

pub(super) type StaticArrayedNode = ArrayedNode<'static, local_heap::LocalHeap<'static, 'static>>;

#[cfg(feature = "aarch64_virt")]
pub mod aarch64_virt;

#[cfg(feature = "aarch64_virt")]
pub use aarch64_virt::AArch64Virt as SoCInitializer;

#[cfg(feature = "raspi5")]
pub mod raspi5;

#[cfg(feature = "raspi5")]
pub use raspi5::Raspi5 as SoCInitializer;

#[cfg(feature = "raspi")]
pub mod raspi;

#[cfg(feature = "raspi")]
pub use raspi::Raspi as SoCInitializer;

use super::vm::VM;

pub trait SoC {
    /// Initialize the device first.
    /// This method will be invoked before `init_memory_map()` and `init()`.
    unsafe fn init_device(&mut self) -> Result<(), &'static str>;

    /// Initialize the virtual memory.
    /// This method will be invoked after `init_device()` and before `init()`.
    ///
    /// Return the size of heap memory if the virtual memory is
    /// successfully initialized.
    unsafe fn init_virtual_memory(&mut self) -> Result<VM, &'static str>;

    /// Initialize the AWkernel.
    /// This method will be invoked after `init_device()` and `init_virtual_memory()`.
    unsafe fn init(&self) -> Result<(), &'static str>;

    /// Return the segment group and the address of the DMA pool.
    #[allow(unused_variables)]
    fn get_dma_pool(&self, segment: usize) -> Option<VirtAddr> {
        None
    }

    /// Get the number of segments.
    fn get_segment_count(&self) -> usize {
        1
    }
}
