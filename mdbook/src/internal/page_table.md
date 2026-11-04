# Page Table

`PageTable` defined in [awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs) is a trait that provides a way to abstract page tables.
It is defined as follows.

```rust
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
```

`map_to` method of `PageTable` is used to specify a page frame allocator,
which allocates physical pages for the page table, when mapping pages.
It is typically used when initializing the kernel's page tables or initializing device drivers.

`Frame` defined in [awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs) is a trait to represent a physical page frame.
It is defined as follows.

```rust
pub trait Frame {
    fn start_address(&self) -> PhyAddr;
    fn set_address(&mut self, addr: PhyAddr);
    fn size(&self) -> usize;
}
```

`FrameAllocator` defined in [awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs) is a trait to allocate physical pages.
It is used by `PageTable` as described above.

# Implementation

## x86_64

For x86_64, the `PageTable` structure
is defined in [awkernel_lib/src/arch/x86_64/page_table.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/x86_64/page_table.rs) as follows.

```rust
pub struct PageTable<'a> {
    offset_page_table: &'a mut OffsetPageTable<'static>,
}
```

The `PageTable` structure implements the [`PageTable`:awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs) trait as follows.

```rust
impl<'a> crate::paging::PageTable<super::page_allocator::Frame, VecPageAllocator, &'static str>
    for PageTable<'a>
{
    unsafe fn map_to(
        &mut self,
        virt_addr: crate::addr::virt_addr::VirtAddr,
        phy_addr: crate::addr::phy_addr::PhyAddr,
        flags: crate::paging::Flags,
        page_allocator: &mut VecPageAllocator,
    ) -> Result<(), &'static str> {
        let flags = flags_to_x86_flags(flags);

        let page = Page::containing_address(VirtAddr::new(virt_addr.as_usize() as u64));
        let frame =
            PhysFrame::<Size4KiB>::containing_address(PhysAddr::new(phy_addr.as_usize() as u64));

        match self
            .offset_page_table
            .map_to(page, frame, flags, page_allocator)
        {
            Ok(flusher) => {
                flusher.flush();
                Ok(())
            }
            Err(_) => Err("Failed to map page"),
        }
    }
}
```

## AArch64

For AArch64, the `PageTable` structure is defined in
[awkernel_lib/src/arch/aarch64/page_table.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/aarch64/page_table.rs) as follows.

```rust
/// - 3 transition levels
/// - 4KiB page
/// - up to 512GiB memory
pub struct PageTable {
    root: PageTableEntry,
}
```

The `PageTable` structure implements the [`PageTable`:awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs) trait as follows.

```rust
impl crate::paging::PageTable<Page, PageAllocator<Page>, &'static str> for PageTable {
    unsafe fn map_to(
        &mut self,
        virt_addr: VirtAddr,
        phy_addr: PhyAddr,
        flags: crate::paging::Flags,
        page_allocator: &mut PageAllocator<Page>,
    ) -> Result<(), &'static str> {
        let mut f = FLAG_L3_AF | 0b11;

        if !flags.execute {
            f |= FLAG_L3_XN | FLAG_L3_PXN;
        }

        if flags.write {
            f |= FLAG_L3_SH_RW_N;
        } else {
            f |= FLAG_L3_SH_R_N;
        }

        match (flags.device, flags.cache) {
            (true, true) => f |= FLAG_L3_ATTR_MEM | FLAG_L3_OSH,
            (true, false) => f |= FLAG_L3_ATTR_DEV | FLAG_L3_OSH,
            (false, true) => f |= FLAG_L3_ATTR_MEM | FLAG_L3_ISH,
            (false, false) => f |= FLAG_L3_NS | FLAG_L3_ISH,
        }

        self.map_to_aarch64(virt_addr, phy_addr, f, page_allocator)
    }
}
```

## RISC-V 32-bit (RV32)

For RV32, the `PageTable` structure is defined in
[awkernel_lib/src/arch/rv32/page_table.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/rv32/page_table.rs).
It implements the **Sv32** translation scheme: 32-bit virtual addresses, 4 KiB pages
and a **2-level** page table. Each page table entry (PTE) holds a physical page number
(`PPN`) and the standard RISC-V flag bits.

```rust
bitflags! {
    /// PTE Flags for RISC-V Sv32 page table
    pub struct Flags: u8 {
        const V = 1 << 0; // Valid
        const R = 1 << 1; // Readable
        const W = 1 << 2; // Writable
        const X = 1 << 3; // Executable
        const U = 1 << 4; // User-accessible
        const G = 1 << 5; // Global
        const A = 1 << 6; // Accessed
        const D = 1 << 7; // Dirty
    }
}

pub struct PageTable {
    root_ppn: PhysPageNum,
    frames: Vec<FrameTracker>,
}
```

The root page table is allocated from the physical frame allocator on `PageTable::new`,
and every intermediate table allocated while walking the tree is tracked in `frames`
so that it is kept alive for the lifetime of the address space.
The virtual page number is split into two 10-bit indices (`VirtPageNum::indexes`),
one per level of the Sv32 table.

The `PageTable` structure implements the [`PageTable`:awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs) trait as follows.
The generic `Flags` are translated into RISC-V PTE flags: entries are always made valid,
accessed and readable (`V | A | R`); writable mappings also set the dirty bit (`W | D`),
and executable mappings set `X`.

```rust
impl crate::paging::PageTable<Page, RV32PageAllocator, &'static str> for PageTable {
    unsafe fn map_to(
        &mut self,
        virt_addr: VirtAddr,
        phy_addr: PhyAddr,
        flags: crate::paging::Flags,
        _page_allocator: &mut RV32PageAllocator,
    ) -> Result<(), &'static str> {
        let vpn = VirtPageNum::from(virt_addr);
        let ppn = PhysPageNum::from(phy_addr);

        let mut rv_flags = Flags::V | Flags::A; // Always valid and accessed
        if flags.write {
            rv_flags |= Flags::W | Flags::D; // Writable and dirty
        }
        rv_flags |= Flags::R; // Always readable
        if flags.execute {
            rv_flags |= Flags::X;
        }

        if self.map(vpn, ppn, rv_flags) {
            Ok(())
        } else {
            Err("Mapping failed")
        }
    }
}
```

Translation is enabled by writing the `satp` (Supervisor Address Translation and Protection)
register. For Sv32 the `token` method returns the register value with `MODE = 1` (Sv32) in
bit 31 and the root table's PPN in the low bits.

```rust
pub fn token(&self) -> usize {
    (1usize << 31)    // MODE = 1 (Sv32 paging mode)
    | self.root_ppn.0 // PPN of the root page table
}
```

## RISC-V 64-bit (RV64)

For RV64, the `PageTable` structure is defined in
[awkernel_lib/src/arch/rv64/page_table.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/rv64/page_table.rs).
It implements the **Sv39** translation scheme: 39-bit virtual addresses, 4 KiB pages
and a **3-level** page table. The PTE layout and `Flags` definition are identical to RV32;
the differences are the number of levels and the `satp` encoding.

```rust
pub struct PageTable {
    root_ppn: PhysPageNum,
    frames: Vec<FrameTracker>,
}
```

The virtual page number is split into three 9-bit indices (`VirtPageNum::indexes`),
walked by `find_pte` / `find_pte_create`; the leaf PTE is reached at level index `2`.

The `map_to` implementation is the same as RV32 — generic `Flags` are mapped to the
RISC-V PTE flags (`V | A | R`, plus `W | D` for writable and `X` for executable pages):

```rust
impl crate::paging::PageTable<Page, RV64PageAllocator, &'static str> for PageTable {
    unsafe fn map_to(
        &mut self,
        virt_addr: VirtAddr,
        phy_addr: PhyAddr,
        flags: crate::paging::Flags,
        _page_allocator: &mut RV64PageAllocator,
    ) -> Result<(), &'static str> {
        let vpn = VirtPageNum::from(virt_addr);
        let ppn = PhysPageNum::from(phy_addr);

        let mut rv_flags = Flags::V | Flags::A;
        if flags.write {
            rv_flags |= Flags::W | Flags::D;
        }
        rv_flags |= Flags::R;
        if flags.execute {
            rv_flags |= Flags::X;
        }

        if self.map(vpn, ppn, rv_flags) {
            Ok(())
        } else {
            Err("Mapping failed")
        }
    }
}
```

For Sv39 the `token` method encodes `MODE = 8` (Sv39) in bits 63-60 and the root PPN in
the low 44 bits:

```rust
pub fn token(&self) -> usize {
    (8usize << 60)    // MODE = 8 (Sv39 paging mode)
    | self.root_ppn.0 // PPN of the root page table
}
```

The kernel address space is built in
[awkernel_lib/src/arch/rv64/vm.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/arch/rv64/vm.rs):
`new_kernel` maps the kernel sections (`.text`, `.rodata`, `.data`, `.bss`) and an
identity mapping for available RAM, and `activate` installs the table by writing `satp`
and flushing the TLB:

```rust
pub fn activate(&self) {
    let satp = self.page_table.token();
    unsafe {
        asm!("csrw satp, {}", in(reg) satp);
        asm!("sfence.vma");
    }
}
```
