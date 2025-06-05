# Mapper (Virtual Memory Management)

`Mapper` is a trait that provides a way to map and unmap virtual memory.
It is defined in [awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs) as follows.

```rust
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
    unsafe fn map(vm_addr: VirtAddr, phy_addr: PhyAddr, flags: Flags) -> Result<(), MapError>;

    /// Unmap `vm_addr`.
    ///
    /// # Safety
    ///
    /// - Virtual memory must be enabled.
    /// - `vm_addr` must be being mapped.
    unsafe fn unmap(vm_addr: VirtAddr);
}
```

`Mapper` uses `VirtAddr` and `PhyAddr` types to represent virtual and physical addresses.
These types are defined in [awkernel_lib/src/addr/virt_addr.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/addr/virt_addr.rs) and [awkernel_lib/src/addr/phy_addr.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/addr/phy_addr.rs).

The `Flags` type is used to represent the flags of the page table entry.
It is defined in [awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs) as follows.

```rust
/// Flag for a page.
/// Note that every page is readable.
#[derive(Debug, Clone, Copy)]
pub struct Flags {
    pub execute: bool,       // executable
    pub write: bool,         // writable
    pub cache: bool,         // enable cache
    pub write_through: bool, // write back if disabled
    pub device: bool,        // this page is for MMIO, ignored on x86
}
```

There are functions regarding the `Mapper` trait in [awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs) as follows.

|  function             | description |
|-----------------------|-------------|
| `fn vm_to_phy(vm_addr: VirtAddr) -> Option<PhyAddr>` | Return the physical address of `vm_addr`. |
| `unsafe fn map(vm_addr: VirtAddr, phy_addr: PhyAddr, flags: Flags) -> Result<(), MapError>` | Map `vm_addr` to `phy_addr` with `flag`. |
| `fn unsafe fn unmap(vm_addr: VirtAddr)` | Unmap `vm_addr`. |

Awkernel's page size is 4 KiB and it is defined by [`PAGESIZE`:awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs).

```rust
pub const PAGESIZE: usize = 4 * 1024;
```

# Implementation

## x86_64

For x86_64, the `X86` structure implements the `Mapper` trait in [awkernel_lib/src/arch/x86_64/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/x86_64/paging.rs).
To handle page tables, the `OffsetPageTable` structure defined in the [`x86_64`](https://docs.rs/x86_64/latest/x86_64/index.html) crate is used.


## AArch64

For AArch64, the `AArch64` structure implements the `Mapper` trait in [awkernel_lib/src/arch/aarch64/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/aarch64/paging.rs).
To handle page tables, the `PageTable` structure defined in the [`awkernel_lib/src/arch/aarch64/page_table.rs`](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/aarch64/page_table.rs) is used.
