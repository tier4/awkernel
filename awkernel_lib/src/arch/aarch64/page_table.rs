use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    paging::{Frame, FrameAllocator, PAGESIZE},
};
use alloc::slice;
use core::ptr::{read_volatile, write_volatile};

use self::flags::{
    FLAG_L3_AF, FLAG_L3_ATTR_DEV, FLAG_L3_ATTR_MEM, FLAG_L3_ISH, FLAG_L3_NS, FLAG_L3_OSH,
    FLAG_L3_PXN, FLAG_L3_SH_RW_N, FLAG_L3_SH_R_N, FLAG_L3_XN,
};

use super::page_allocator::{Page, PageAllocator};

pub mod flags {
    pub const FLAG_L3_XN: u64 = 1 << 54; // execute never
    pub const FLAG_L3_PXN: u64 = 1 << 53; // privileged execute never
    pub const FLAG_L3_CONT: u64 = 1 << 52; // contiguous
    pub const FLAG_L3_DBM: u64 = 1 << 51; // dirty bit modifier
    pub const FLAG_L3_AF: u64 = 1 << 10; // access flag
    pub const FLAG_L3_NS: u64 = 1 << 5; // non secure

    // [9:8]: Shareability attribute, for Normal memory
    //    | Shareability
    // ---|------------------
    // 00 | non sharedable
    // 01 | reserved
    // 10 | outer sharedable
    // 11 | inner sharedable
    pub const FLAG_L3_OSH: u64 = 0b10 << 8;
    pub const FLAG_L3_ISH: u64 = 0b11 << 8;

    // [7:6]: access permissions
    //    | Access from            |
    //    | higher Exception level | Access from EL0
    // ---|------------------------|-----------------
    // 00 | read/write             | none
    // 01 | read/write             | read/write
    // 10 | read-only              | none
    // 11 | read-only              | read-only
    pub const FLAG_L3_SH_RW_N: u64 = 0;
    pub const FLAG_L3_SH_RW_RW: u64 = 1 << 6;
    pub const FLAG_L3_SH_R_N: u64 = 0b10 << 6;
    pub const FLAG_L3_SH_R_R: u64 = 0b11 << 6;

    // [4:2]: AttrIndx
    // defined in MAIR register
    // see get_mair()
    pub const FLAG_L3_ATTR_MEM: u64 = 0; // normal memory
    pub const FLAG_L3_ATTR_DEV: u64 = 1 << 2; // device MMIO
    pub const FLAG_L3_ATTR_NC: u64 = 2 << 2; // non-cachable
}

const ENTRY_COUNT: usize = PAGESIZE / 8;

#[repr(align(4096))] // 4KiB
#[repr(C)]
struct PageTableEntry {
    entries: &'static mut [u64],
}

impl PageTableEntry {
    fn new<F, FA>(allocator: &mut FA) -> Result<Self, &'static str>
    where
        F: Frame,
        FA: FrameAllocator<F, &'static str>,
    {
        let ptr = allocator.allocate_frame()?.start_address().as_usize() as *mut u64;

        let entries = unsafe { slice::from_raw_parts_mut(ptr, ENTRY_COUNT) };
        for e in entries.iter_mut() {
            *e = 0;
        }

        Ok(Self { entries })
    }

    fn from_addr(addr: PhyAddr) -> Self {
        let ptr = addr.as_usize() as *mut u64;
        let entries = unsafe { slice::from_raw_parts_mut(ptr, ENTRY_COUNT) };
        Self { entries }
    }
}

enum PageTableLevel {
    Lv1,
    Lv2,
    Lv3,
}

/// - 3 transition levels
/// - 4KiB page
/// - up to 512GiB memory
pub struct PageTable {
    root: PageTableEntry,
}

impl PageTable {
    const IDX_MASK: u64 = (ENTRY_COUNT - 1) as u64;
    const ADDR_MASK: u64 = 0xFFFFFFFFF << 12; // [47:12]

    pub fn new<F, FA>(allocator: &mut FA) -> Result<Self, &'static str>
    where
        F: Frame,
        FA: FrameAllocator<F, &'static str>,
    {
        let root = PageTableEntry::new(allocator)?;
        Ok(Self { root })
    }

    /// # Safety
    ///
    /// `addr` must be the root of a page table.
    pub unsafe fn with_root(addr: PhyAddr) -> Self {
        let root = PageTableEntry::from_addr(addr);
        Self { root }
    }

    pub fn addr(&self) -> u64 {
        self.root.entries.as_ptr() as u64
    }

    fn get_idx(addr: VirtAddr, level: PageTableLevel) -> usize {
        match level {
            PageTableLevel::Lv1 => ((addr.as_usize() as u64 >> 30) & Self::IDX_MASK) as usize,
            PageTableLevel::Lv2 => ((addr.as_usize() as u64 >> 21) & Self::IDX_MASK) as usize,
            PageTableLevel::Lv3 => ((addr.as_usize() as u64 >> 12) & Self::IDX_MASK) as usize,
        }
    }

    pub fn map_to_aarch64<F, FA>(
        &mut self,
        vm_addr: VirtAddr,
        phy_addr: PhyAddr,
        flags: u64,
        allocator: &mut FA,
    ) -> Result<(), &'static str>
    where
        F: Frame,
        FA: FrameAllocator<F, &'static str>,
    {
        let lv1_table = &mut self.root.entries;
        let lv1_idx = Self::get_idx(vm_addr, PageTableLevel::Lv1);
        let lv2_table;

        if lv1_table[lv1_idx] == 0 {
            lv2_table = PageTableEntry::new(allocator)?.entries;
            lv1_table[lv1_idx] = (lv2_table.as_ptr()) as u64 | 0b11;
        } else {
            let addr = lv1_table[lv1_idx] & Self::ADDR_MASK;
            lv2_table = PageTableEntry::from_addr(PhyAddr::new(addr as usize)).entries;
        }

        let lv2_idx = Self::get_idx(vm_addr, PageTableLevel::Lv2);
        let lv3_table;

        if lv2_table[lv2_idx] == 0 {
            lv3_table = PageTableEntry::new(allocator)?.entries;
            lv2_table[lv2_idx] = (lv3_table.as_ptr()) as u64 | 0b11;
        } else {
            let addr = lv2_table[lv2_idx] & Self::ADDR_MASK;
            lv3_table = PageTableEntry::from_addr(PhyAddr::new(addr as usize)).entries;
        }

        let lv3_idx = Self::get_idx(vm_addr, PageTableLevel::Lv3);
        let e = phy_addr.as_usize() as u64 & !0xfff | flags;
        let ptr = &mut lv3_table[lv3_idx];

        unsafe { write_volatile(ptr, e) };

        Ok(())
    }

    /// # Safety
    ///
    /// The unmapped address must not be used after calling this function.
    pub unsafe fn unmap(&mut self, vm_addr: VirtAddr) {
        let lv1_table = &mut self.root.entries;
        let lv1_idx = Self::get_idx(vm_addr, PageTableLevel::Lv1);

        if lv1_table[lv1_idx] == 0 {
            return;
        }

        let lv2_addr = lv1_table[lv1_idx] & Self::ADDR_MASK;
        let lv2_table = PageTableEntry::from_addr(PhyAddr::new(lv2_addr as usize)).entries;
        let lv2_idx = Self::get_idx(vm_addr, PageTableLevel::Lv2);

        if lv2_table[lv2_idx] == 0 {
            return;
        }

        let lv3_addr = lv2_table[lv2_idx] & Self::ADDR_MASK;
        let lv3_table = PageTableEntry::from_addr(PhyAddr::new(lv3_addr as usize)).entries;
        let lv3_idx = Self::get_idx(vm_addr, PageTableLevel::Lv3);
        let ptr = &mut lv3_table[lv3_idx];

        unsafe { write_volatile(ptr, 0) };
    }

    pub fn translate(&self, vm_addr: VirtAddr) -> Option<PhyAddr> {
        let lv1_table = &self.root.entries;
        let lv1_idx = Self::get_idx(vm_addr, PageTableLevel::Lv1);

        if lv1_table[lv1_idx] == 0 {
            return None;
        }

        let lv2_addr = lv1_table[lv1_idx] & Self::ADDR_MASK;
        let lv2_table = PageTableEntry::from_addr(PhyAddr::new(lv2_addr as usize)).entries;
        let lv2_idx = Self::get_idx(vm_addr, PageTableLevel::Lv2);

        if lv2_table[lv2_idx] == 0 {
            return None;
        }

        let lv3_addr = lv2_table[lv2_idx] & Self::ADDR_MASK;
        let lv3_table = PageTableEntry::from_addr(PhyAddr::new(lv3_addr as usize)).entries;
        let lv3_idx = Self::get_idx(vm_addr, PageTableLevel::Lv3);
        let ptr = &lv3_table[lv3_idx];
        let val = unsafe { read_volatile(ptr) };

        if val & FLAG_L3_AF == 0 {
            return None;
        }

        let high = val & (0xfffffff) << 12; // PA[39:12]
        let low = vm_addr.as_usize() as u64 & 0xfff; // PA[11:0]

        Some(PhyAddr::new((high | low) as usize))
    }
}

impl crate::paging::PageTable<Page, PageAllocator<Page>, &'static str> for PageTable {
    unsafe fn map_to(
        &mut self,
        virt_addr: VirtAddr,
        phy_addr: PhyAddr,
        flags: crate::paging::Flags,
        page_allocator: &mut PageAllocator<Page>,
    ) -> Result<(), &'static str> {
        let lv1_table = &mut self.root.entries;
        let lv1_idx = Self::get_idx(virt_addr, PageTableLevel::Lv1);
        let lv2_table;

        if lv1_table[lv1_idx] == 0 {
            lv2_table = PageTableEntry::new(page_allocator)?.entries;
            lv1_table[lv1_idx] = (lv2_table.as_ptr()) as u64 | 0b11;
        } else {
            let addr = lv1_table[lv1_idx] & Self::ADDR_MASK;
            lv2_table = PageTableEntry::from_addr(PhyAddr::new(addr as usize)).entries;
        }

        let lv2_idx = Self::get_idx(virt_addr, PageTableLevel::Lv2);
        let lv3_table;

        if lv2_table[lv2_idx] == 0 {
            lv3_table = PageTableEntry::new(page_allocator)?.entries;
            lv2_table[lv2_idx] = (lv3_table.as_ptr()) as u64 | 0b11;
        } else {
            let addr = lv2_table[lv2_idx] & Self::ADDR_MASK;
            lv3_table = PageTableEntry::from_addr(PhyAddr::new(addr as usize)).entries;
        }

        let lv3_idx = Self::get_idx(virt_addr, PageTableLevel::Lv3);

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

        let e = phy_addr.as_usize() as u64 & !0xfff | f;
        let ptr = &mut lv3_table[lv3_idx];

        unsafe { write_volatile(ptr, e) };

        Ok(())
    }
}
