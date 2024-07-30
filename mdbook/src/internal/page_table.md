# Page Table

The `PageTable` defined in [awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs) is a trait that provides a way to abstract page tables.
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

The `map_to` method of the `PageTable` is used to specify a page frame allocator,
which allocates physical pages for the page table, when mapping pages.
It is typically used when initializing the kernel's page tables or initializing device drivers.

The `Frame` defined in [awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs) is a trait to represent a physical page frame.
It is defined as follows.

```rust
pub trait Frame {
    fn start_address(&self) -> PhyAddr;
    fn set_address(&mut self, addr: PhyAddr);
    fn size(&self) -> usize;
}
```
The `FrameAllocator` defined in [awkernel_lib/src/paging.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/paging.rs) is a trait to allocate physical pages.
It is used by the `PageTable` as described above.

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
