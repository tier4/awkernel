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

## RISC-V 32-bit (RV32)

For RV32, the `RV32` structure implements the `Mapper` trait in
[awkernel_lib/src/arch/rv32/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/rv32/paging.rs).
Each operation reads the **currently active** page table from the `satp` register via
`get_page_table` (see [Page Table](../page_table.md)), then delegates to the Sv32
`PageTable`. The generic `Flags` are translated into RISC-V PTE flags — entries are always
valid, accessed and readable (`V | A | R`), writable pages also set `W | D`, and executable
pages set `X`.

```rust
impl crate::paging::Mapper for super::RV32 {
    unsafe fn map(
        vm_addr: VirtAddr,
        phy_addr: PhyAddr,
        flags: crate::paging::Flags,
    ) -> Result<(), MapError> {
        // Check address alignment
        if !vm_addr.aligned() || !phy_addr.aligned() {
            return Err(MapError::AddressNotAligned);
        }

        // Get current page table
        if let Some(mut page_table) = get_page_table(vm_addr) {
            let vpn = VirtPageNum::from(vm_addr);
            let ppn = phy_addr.floor();

            // Convert common flags to RV32 flags
            let mut rv_flags = Flags::V | Flags::A; // Always valid and accessed
            if flags.write {
                rv_flags |= Flags::W | Flags::D; // Writable and dirty
            }
            rv_flags |= Flags::R; // Always readable
            if flags.execute {
                rv_flags |= Flags::X;
            }

            // Try to map the page
            if page_table.map(vpn, ppn, rv_flags) {
                Ok(())
            } else {
                Err(MapError::AlreadyMapped)
            }
        } else {
            Err(MapError::InvalidPageTable)
        }
    }

    // unmap / vm_to_phy omitted
}
```

`vm_to_phy` walks the active page table for the page's virtual page number, and, if the
leaf PTE is valid, reconstructs the physical address from the entry's PPN plus the page
offset.

## RISC-V 64-bit (RV64)

For RV64, the `RV64` structure implements the `Mapper` trait in
[awkernel_lib/src/arch/rv64/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/rv64/paging.rs).
The structure mirrors RV32 but uses the Sv39 `PageTable`. Two differences are worth noting:
`map` first checks `vm_to_phy` to reject an already-mapped address, and both `map` and
`unmap` explicitly align the virtual and physical addresses down to the 4 KiB page
boundary before walking the table.

```rust
impl crate::paging::Mapper for super::RV64 {
    unsafe fn map(
        vm_addr: VirtAddr,
        phy_addr: PhyAddr,
        flags: crate::paging::Flags,
    ) -> Result<(), MapError> {
        // Check if already mapped
        if Self::vm_to_phy(vm_addr).is_some() {
            return Err(MapError::AlreadyMapped);
        }

        let vm_addr_aligned = vm_addr.as_usize() & !(PAGESIZE - 1);
        let phy_addr_aligned = phy_addr.as_usize() & !(PAGESIZE - 1);

        if let Some(mut page_table) = get_page_table(VirtAddr::from_usize(vm_addr_aligned)) {
            let vpn = VirtPageNum::from(VirtAddr::from_usize(vm_addr_aligned));
            let ppn = PhysPageNum::from(PhyAddr::from_usize(phy_addr_aligned));

            let mut rv_flags = Flags::V | Flags::A;
            rv_flags |= Flags::R; // Always readable
            if flags.write {
                rv_flags |= Flags::W | Flags::D;
            }
            if flags.execute {
                rv_flags |= Flags::X;
            }

            if page_table.map(vpn, ppn, rv_flags) {
                Ok(())
            } else {
                Err(MapError::AlreadyMapped)
            }
        } else {
            Err(MapError::InvalidPageTable)
        }
    }

    // unmap / vm_to_phy omitted
}
```
