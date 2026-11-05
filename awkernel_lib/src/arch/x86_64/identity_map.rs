//! Identity mapping of a single page that may already be identity-mapped.

use x86_64::{
    structures::paging::{
        mapper::{MapToError, MappedFrame, MapperFlush, TranslateResult, UnmapError},
        FrameAllocator, Mapper, Page, PageTableFlags, PhysFrame, Size4KiB, Translate,
    },
    VirtAddr,
};

/// Why [`identity_map`] could not map a page.
#[derive(Debug)]
pub enum IdentityMapError {
    /// Mapping failed for another reason than an existing identity mapping:
    /// no frame for a page table, a huge page in the way, or a mapping to
    /// another frame.
    Map(MapToError<Size4KiB>),
    /// The page is already mapped, but not to the frame of the same address.
    MappedElsewhere,
    /// The existing identity mapping could not be removed.
    Unmap(UnmapError),
}

/// Identity-map `frame` with `flags`.
///
/// If the page is already mapped to `frame`, the entry is replaced so that the
/// page gets exactly `flags`.  The bootloader identity-maps the page of its
/// context switch code read-only (`PRESENT` only) and still reports the page as
/// usable, so the page passed here can be one that must become writable.
/// As for a page that was not mapped, `map_to` also ORs the table flags of
/// `flags` (`PRESENT`, `WRITABLE`, `USER_ACCESSIBLE`) into the parent entries.
///
/// The returned flush invalidates the page's TLB entry, which may still hold
/// the old read-only translation.  The caller must call it.
///
/// # Safety
///
/// Same as [`Mapper::map_to`]: nothing may rely on the existing mapping of
/// the page, and accessing `frame` through the new mapping must be safe.
pub unsafe fn identity_map<M, A>(
    mapper: &mut M,
    frame: PhysFrame<Size4KiB>,
    flags: PageTableFlags,
    allocator: &mut A,
) -> Result<MapperFlush<Size4KiB>, IdentityMapError>
where
    M: Mapper<Size4KiB> + Translate,
    A: FrameAllocator<Size4KiB> + ?Sized,
{
    let page = Page::containing_address(VirtAddr::new(frame.start_address().as_u64()));

    match unsafe { mapper.map_to(page, frame, flags, allocator) } {
        // `PageAlreadyMapped` carries the requested frame, not the mapped one.
        Err(MapToError::PageAlreadyMapped(_)) => (),
        result => return result.map_err(IdentityMapError::Map),
    }
    match mapper.translate(page.start_address()) {
        TranslateResult::Mapped {
            frame: MappedFrame::Size4KiB(mapped),
            ..
        } if mapped == frame => (),
        _ => return Err(IdentityMapError::MappedElsewhere),
    }

    // The INVLPG of the flush returned below also drops the stale translation,
    // so this one can be skipped.
    let (_, flush) = mapper.unmap(page).map_err(IdentityMapError::Unmap)?;
    flush.ignore();

    unsafe { mapper.map_to(page, frame, flags, allocator) }.map_err(IdentityMapError::Map)
}

#[cfg(test)]
mod tests {
    use super::*;
    use x86_64::{
        structures::paging::{OffsetPageTable, PageTable},
        PhysAddr,
    };

    /// Flags the AP trampoline page needs: writable, executable, uncached.
    const RWX: PageTableFlags = PageTableFlags::PRESENT
        .union(PageTableFlags::WRITABLE)
        .union(PageTableFlags::NO_CACHE);

    /// Hands out zeroed, leaked heap pages as page-table frames.  With a
    /// physical memory offset of 0, a frame's address is its host address, so
    /// the mapper walks these tables without touching the CPU's.
    struct HeapFrames;

    unsafe impl FrameAllocator<Size4KiB> for HeapFrames {
        fn allocate_frame(&mut self) -> Option<PhysFrame<Size4KiB>> {
            let table: *mut PageTable = Box::leak(Box::new(PageTable::new()));
            Some(PhysFrame::containing_address(PhysAddr::new(table as u64)))
        }
    }

    fn new_mapper() -> OffsetPageTable<'static> {
        let l4 = Box::leak(Box::new(PageTable::new()));
        // SAFETY: with offset 0, every table frame comes from `HeapFrames` and
        // is a live host allocation.
        unsafe { OffsetPageTable::new(l4, VirtAddr::new(0)) }
    }

    fn frame(addr: u64) -> PhysFrame<Size4KiB> {
        PhysFrame::containing_address(PhysAddr::new(addr))
    }

    fn page_of(frame: PhysFrame<Size4KiB>) -> Page<Size4KiB> {
        Page::containing_address(VirtAddr::new(frame.start_address().as_u64()))
    }

    /// The frame and leaf flags `page` translates to.
    fn leaf(
        mapper: &OffsetPageTable,
        page: Page<Size4KiB>,
    ) -> (PhysFrame<Size4KiB>, PageTableFlags) {
        match mapper.translate(page.start_address()) {
            TranslateResult::Mapped {
                frame: MappedFrame::Size4KiB(frame),
                flags,
                ..
            } => (frame, flags),
            other => panic!("unexpected translation: {other:?}"),
        }
    }

    /// Flags of the P4, P3 and P2 entries on the walk to `page`.
    fn parent_flags(mapper: &mut OffsetPageTable, page: Page<Size4KiB>) -> [PageTableFlags; 3] {
        let p4 = &mapper.level_4_table()[page.p4_index()];
        // SAFETY: the tables are host allocations from `HeapFrames`.
        let p3 = unsafe { &*(p4.addr().as_u64() as *const PageTable) }[page.p3_index()].clone();
        let p2 = unsafe { &*(p3.addr().as_u64() as *const PageTable) }[page.p2_index()].clone();
        [p4.flags(), p3.flags(), p2.flags()]
    }

    #[test]
    fn maps_a_free_page() {
        let mut mapper = new_mapper();
        let f = frame(0x8000);

        unsafe { identity_map(&mut mapper, f, RWX, &mut HeapFrames) }
            .unwrap()
            .ignore();

        assert_eq!(leaf(&mapper, page_of(f)), (f, RWX));
    }

    /// The bootloader's context switch page: identity-mapped `PRESENT` only.
    /// Here the parent entries are read-only too.
    #[test]
    fn makes_a_read_only_identity_mapping_writable_and_executable() {
        let mut mapper = new_mapper();
        let f = frame(0x8000);
        let page = page_of(f);
        unsafe {
            mapper.map_to_with_table_flags(
                page,
                f,
                PageTableFlags::PRESENT,
                PageTableFlags::PRESENT,
                &mut HeapFrames,
            )
        }
        .unwrap()
        .ignore();
        assert_eq!(leaf(&mapper, page), (f, PageTableFlags::PRESENT));

        unsafe { identity_map(&mut mapper, f, RWX, &mut HeapFrames) }
            .unwrap()
            .ignore();

        let (mapped, flags) = leaf(&mapper, page);
        assert_eq!(mapped, f);
        assert_eq!(flags, RWX);
        for parent in parent_flags(&mut mapper, page) {
            assert!(parent.contains(PageTableFlags::PRESENT | PageTableFlags::WRITABLE));
        }
    }

    #[test]
    fn rejects_a_mapping_to_another_frame() {
        let mut mapper = new_mapper();
        let f = frame(0x8000);
        let other = frame(0x9000);
        unsafe { mapper.map_to(page_of(f), other, PageTableFlags::PRESENT, &mut HeapFrames) }
            .unwrap()
            .ignore();

        let result = unsafe { identity_map(&mut mapper, f, RWX, &mut HeapFrames) };

        assert!(matches!(result, Err(IdentityMapError::MappedElsewhere)));
        assert_eq!(leaf(&mapper, page_of(f)), (other, PageTableFlags::PRESENT));
    }
}
