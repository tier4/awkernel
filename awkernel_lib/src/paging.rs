use crate::addr::{phy_addr::PhyAddr, virt_addr::VirtAddr};

#[cfg(not(feature = "std"))]
use crate::arch::ArchImpl;

pub trait Frame {
    fn start_address(&self) -> PhyAddr;
    fn set_address(&mut self, addr: PhyAddr);
    fn size(&self) -> usize;
}

/// Allocate a frame.
pub trait FrameAllocator<F, E>
where
    F: Frame,
{
    fn allocate_frame(&mut self) -> Result<F, E>;
}

/// Allocate a frame for NUMA node of `numa_id`.
pub trait NUMAFrameAllocator<F, E>
where
    F: Frame,
{
    fn allocate_frame(&mut self, numa_id: usize) -> Result<F, E>;
}

pub trait PageTable<F, FA, E>
where
    F: Frame,
    FA: FrameAllocator<F, E>,
{
    /// Map `virt_addr` to `phy_addr` with `flag`.
    ///
    /// # Safety
    ///
    /// - virt_addr and phy_addr must be aligned to page size.
    unsafe fn map_to(
        &mut self,
        virt_addr: VirtAddr,
        phy_addr: PhyAddr,
        flags: Flags,
        page_allocator: &mut FA,
    ) -> Result<(), E>;
}

pub const PAGESIZE: usize = 4 * 1024;

#[cfg(any(feature = "x86", feature = "aarch64"))]
pub const USER_START: usize = 0x1FFFFFF << 39;

#[cfg(feature = "rv32")]
pub const USER_START: usize = 1024 * 1024 * 1024 * 2; // 2 GiB

/// Flag for a page.
/// Note that every page is readable.
#[derive(Debug, Clone, Copy)]
pub struct Flags {
    pub execute: bool,       // executable
    pub write: bool,         // writable
    pub cache: bool,         // enable cache
    pub write_through: bool, // write back if disabled
    pub device: bool,        // this page is MMIO, ignored on x86
}

pub trait Mapper {
    /// Return the physical address of `vm_addr`.
    fn vm_to_phy(vm_addr: VirtAddr) -> Option<PhyAddr>;

    /// Map `vm_addr` to `phy_addr` with `flag`.
    ///
    /// # Safety
    ///
    /// - Virtual memory must be enabled.
    /// - `flag` must be reasonable.
    /// - `phy_addr` must be being unmapped.
    unsafe fn map(vm_addr: VirtAddr, phy_addr: PhyAddr, flags: Flags) -> bool;

    /// Unmap `vm_addr`.
    ///
    /// # Safety
    ///
    /// - Virtual memory must be enabled.
    /// - `vm_addr` must be being mapped.
    unsafe fn unmap(vm_addr: VirtAddr);
}

/// Return the physical address of `vm_addr`.
#[cfg(not(feature = "std"))]
pub fn vm_to_phy(vm_addr: VirtAddr) -> Option<PhyAddr> {
    ArchImpl::vm_to_phy(vm_addr)
}

/// Map `vm_addr` to `phy_addr` with `flag`.
///
/// # Safety
///
/// - Virtual memory must be enabled.
/// - `flag` must be reasonable.
/// - `phy_addr` must be being unmapped.
#[cfg(not(feature = "std"))]
pub unsafe fn map(vm_addr: VirtAddr, phy_addr: PhyAddr, flags: Flags) -> bool {
    ArchImpl::map(vm_addr, phy_addr, flags)
}

/// Unmap `vm_addr`.
///
/// # Safety
///
/// - Virtual memory must be enabled.
/// - `vm_addr` must be being mapped.
#[cfg(not(feature = "std"))]
pub unsafe fn unmap(vm_addr: VirtAddr) {
    ArchImpl::unmap(vm_addr)
}
