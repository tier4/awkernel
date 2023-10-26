use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr},
    arch::ArchImpl,
};

pub const PAGESIZE: usize = 4 * 1024;

#[cfg(any(feature = "x86", feature = "aarch64"))]
pub const USER_START: usize = 0x1FFFFFF << 39;

#[cfg(feature = "rv32")]
pub const USER_START: usize = 1024 * 1024 * 1024 * 2; // 2 GiB

/// Flag for a page.
/// Note that every page is readable.
#[derive(Debug, Clone, Copy)]
pub struct Flags {
    pub execute: bool,
    pub write: bool,
    pub cache: bool,
}

pub trait Memory {
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
pub unsafe fn map(vm_addr: VirtAddr, phy_addr: PhyAddr, flags: Flags) -> bool {
    ArchImpl::map(vm_addr, phy_addr, flags)
}

/// Unmap `vm_addr`.
///
/// # Safety
///
/// - Virtual memory must be enabled.
/// - `vm_addr` must be being mapped.
pub unsafe fn unmap(vm_addr: VirtAddr) {
    ArchImpl::unmap(vm_addr)
}
