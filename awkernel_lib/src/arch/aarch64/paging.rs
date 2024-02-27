use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    arch::aarch64::{
        page_allocator::HeapPageAllocator,
        page_table::{flags::*, PageTable},
    },
    paging::{MapError, PAGESIZE},
};

const TTBR1_ADDR: usize = 0xffff_ff80_0000_0000;

impl crate::paging::Mapper for super::AArch64 {
    unsafe fn map(
        vm_addr: VirtAddr,
        phy_addr: PhyAddr,
        flags: crate::paging::Flags,
    ) -> Result<(), MapError> {
        if Self::vm_to_phy(vm_addr).is_some() {
            return Err(MapError::AlreadyMapped);
        }

        let vm_addr = vm_addr.as_usize() & !(PAGESIZE - 1);
        let phy_addr = phy_addr.as_usize() & !(PAGESIZE - 1);

        let mut page_table = get_page_table(VirtAddr::new(vm_addr));

        let mut f = FLAG_L3_AF | FLAG_L3_ISH | FLAG_L3_ATTR_MEM | 0b11;

        if !flags.execute {
            f |= FLAG_L3_XN | FLAG_L3_PXN;
        }

        if flags.write {
            f |= FLAG_L3_SH_RW_N;
        } else {
            f |= FLAG_L3_SH_R_N;
        }

        let mut allocator = HeapPageAllocator;

        page_table
            .map_to_aarch64(VirtAddr::new(vm_addr), PhyAddr::new(phy_addr), f, &mut allocator)
            .or(Err(MapError::OutOfMemory))
    }

    unsafe fn unmap(vm_addr: VirtAddr) {
        let vm_addr = VirtAddr::new(vm_addr.as_usize() & !(PAGESIZE - 1));
        let mut page_table = get_page_table(vm_addr);
        page_table.unmap(vm_addr);
    }

    fn vm_to_phy(vm_addr: VirtAddr) -> Option<PhyAddr> {
        let higher = vm_addr.as_usize() & !(PAGESIZE - 1);
        let lower = vm_addr.as_usize() & (PAGESIZE - 1);
        let page_table = get_page_table(VirtAddr::new(higher));

        page_table
            .translate(VirtAddr::new(higher))
            .map(|phy| PhyAddr::new(phy.as_usize() | lower))
    }
}

fn get_page_table(vm_addr: VirtAddr) -> PageTable {
    let ttbr = if vm_addr.as_usize() >= TTBR1_ADDR {
        awkernel_aarch64::ttbr1_el1::get() & !1
    } else {
        awkernel_aarch64::ttbr0_el1::get() & !1
    };

    unsafe { PageTable::with_root(PhyAddr::new(ttbr as usize)) }
}
