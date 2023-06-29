use crate::{delay::wait_forever, memory::PAGESIZE};
use alloc::slice;
use core::ptr::{read_volatile, write_volatile};

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

pub trait FrameAllocator {
    fn allocate_frame(&mut self) -> Option<u64>;
}

const ENTRY_COUNT: usize = PAGESIZE / 8;

#[repr(align(4096))] // 4KiB
#[repr(C)]
struct PageTableEntry {
    entries: &'static mut [u64],
}

impl PageTableEntry {
    fn new<A>(allocator: &mut A) -> Self
    where
        A: FrameAllocator,
    {
        let ptr = if let Some(page) = allocator.allocate_frame() {
            page as *mut u64
        } else {
            wait_forever();
        };

        let entries = unsafe { slice::from_raw_parts_mut(ptr, ENTRY_COUNT) };
        for e in entries.iter_mut() {
            *e = 0;
        }
        Self { entries }
    }

    fn from_addr(addr: u64) -> Self {
        let ptr = addr as *mut u64;
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

    pub fn new<A>(allocator: &mut A) -> Self
    where
        A: FrameAllocator,
    {
        let root = PageTableEntry::new(allocator);
        Self { root }
    }

    /// # Safety
    ///
    /// `addr` must be the root of a page table.
    pub unsafe fn with_root(addr: usize) -> Self {
        let root = PageTableEntry::from_addr(addr as u64);
        Self { root }
    }

    pub fn addr(&self) -> u64 {
        self.root.entries.as_ptr() as u64
    }

    fn get_idx(addr: u64, level: PageTableLevel) -> usize {
        match level {
            PageTableLevel::Lv1 => ((addr >> 30) & Self::IDX_MASK) as usize,
            PageTableLevel::Lv2 => ((addr >> 21) & Self::IDX_MASK) as usize,
            PageTableLevel::Lv3 => ((addr >> 12) & Self::IDX_MASK) as usize,
        }
    }

    pub fn map_to<A>(&mut self, vm_addr: u64, phy_addr: u64, flag: u64, allocator: &mut A)
    where
        A: FrameAllocator,
    {
        let lv1_table = &mut self.root.entries;
        let lv1_idx = Self::get_idx(vm_addr, PageTableLevel::Lv1);
        let lv2_table;

        if lv1_table[lv1_idx] == 0 {
            lv2_table = PageTableEntry::new(allocator).entries;
            lv1_table[lv1_idx] = (lv2_table.as_ptr()) as u64 | 0b11;
        } else {
            let addr = lv1_table[lv1_idx] & Self::ADDR_MASK;
            lv2_table = PageTableEntry::from_addr(addr).entries;
        }

        let lv2_idx = Self::get_idx(vm_addr, PageTableLevel::Lv2);
        let lv3_table;

        if lv2_table[lv2_idx] == 0 {
            lv3_table = PageTableEntry::new(allocator).entries;
            lv2_table[lv2_idx] = (lv3_table.as_ptr()) as u64 | 0b11;
        } else {
            let addr = lv2_table[lv2_idx] & Self::ADDR_MASK;
            lv3_table = PageTableEntry::from_addr(addr).entries;
        }

        let lv3_idx = Self::get_idx(vm_addr, PageTableLevel::Lv3);
        let e = phy_addr & !0xfff | flag;
        let ptr = &mut lv3_table[lv3_idx];

        unsafe { write_volatile(ptr, e) };
    }

    /// # Safety
    ///
    /// Ensure that the page tables regarding the virtual address must be allocated before calling this function.
    pub unsafe fn unsafe_map(&mut self, vm_addr: u64, phy_addr: u64, flag: u64) -> bool {
        let lv1_table = &mut self.root.entries;
        let lv1_idx = Self::get_idx(vm_addr, PageTableLevel::Lv1);
        let lv2_table = if lv1_table[lv1_idx] == 0 {
            return false;
        } else {
            let addr = lv1_table[lv1_idx] & Self::ADDR_MASK;
            PageTableEntry::from_addr(addr).entries
        };

        let lv2_idx = Self::get_idx(vm_addr, PageTableLevel::Lv2);
        let lv3_table = if lv2_table[lv2_idx] == 0 {
            return false;
        } else {
            let addr = lv2_table[lv2_idx] & Self::ADDR_MASK;
            PageTableEntry::from_addr(addr).entries
        };

        let lv3_idx = Self::get_idx(vm_addr, PageTableLevel::Lv3);
        let e = phy_addr & !0xfff | flag;
        let ptr = &mut lv3_table[lv3_idx];

        unsafe { write_volatile(ptr, e) };

        true
    }

    /// # Safety
    ///
    /// The unmapped address must not be used after calling this function.
    pub unsafe fn unmap(&mut self, vm_addr: u64) {
        let lv1_table = &mut self.root.entries;
        let lv1_idx = Self::get_idx(vm_addr, PageTableLevel::Lv1);

        if lv1_table[lv1_idx] == 0 {
            return;
        }

        let lv2_addr = lv1_table[lv1_idx] & Self::ADDR_MASK;
        let lv2_table = PageTableEntry::from_addr(lv2_addr).entries;
        let lv2_idx = Self::get_idx(vm_addr, PageTableLevel::Lv2);

        if lv2_table[lv2_idx] == 0 {
            return;
        }

        let lv3_addr = lv2_table[lv2_idx] & Self::ADDR_MASK;
        let lv3_table = PageTableEntry::from_addr(lv3_addr).entries;
        let lv3_idx = Self::get_idx(vm_addr, PageTableLevel::Lv3);
        let ptr = &mut lv3_table[lv3_idx];

        unsafe { write_volatile(ptr, 0) };
    }

    pub fn translate(&self, vm_addr: u64) -> Option<u64> {
        let lv1_table = &self.root.entries;
        let lv1_idx = Self::get_idx(vm_addr, PageTableLevel::Lv1);

        if lv1_table[lv1_idx] == 0 {
            return None;
        }

        let lv2_addr = lv1_table[lv1_idx] & Self::ADDR_MASK;
        let lv2_table = PageTableEntry::from_addr(lv2_addr).entries;
        let lv2_idx = Self::get_idx(vm_addr, PageTableLevel::Lv2);

        if lv2_table[lv2_idx] == 0 {
            return None;
        }

        let lv3_addr = lv2_table[lv2_idx] & Self::ADDR_MASK;
        let lv3_table = PageTableEntry::from_addr(lv3_addr).entries;
        let lv3_idx = Self::get_idx(vm_addr, PageTableLevel::Lv3);
        let ptr = &lv3_table[lv3_idx];
        let val = unsafe { read_volatile(ptr) };
        let high = (val >> 12) & 0xfffffff; // PA[39:12]
        let low = vm_addr & 0xfff; // PA[11:0]

        Some(high << 16 | low)
    }
}
