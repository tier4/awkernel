pub const PAGESIZE: usize = 4 * 1024;

/// Flag for a page.
/// Note that every page is readable.
#[derive(Debug, Clone, Copy)]
pub struct Flag {
    pub execute: bool,
    pub write: bool,
}

pub trait Memory {
    /// Return the physical address of `vm_addr`.
    fn vm_to_phy(vm_addr: usize) -> Option<usize>;

    /// Map `vm_addr` to `phy_addr` with `flag`.
    ///
    /// # Safety
    ///
    /// - MMU must be enabled.
    /// - `flag` must be reasonable.
    unsafe fn map(vm_addr: usize, phy_addr: usize, flag: Flag) -> bool;

    /// Unmap `vm_addr`.
    ///
    /// # Safety
    ///
    /// - MMU must be enabled.
    /// - `vm_addr` must be being mapped.
    unsafe fn unmap(vm_addr: usize);
}
