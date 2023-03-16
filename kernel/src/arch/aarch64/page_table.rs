use super::{
    driver::uart::{DevUART, Uart},
    mmu::PAGESIZE,
};
use alloc::slice;
use awkernel_lib::delay::wait_forever;
use core::ptr::{read_volatile, write_volatile};

pub trait FrameAllocator {
    fn allocate_frame(&mut self) -> Option<u64>;
}

const ENTRY_COUNT: usize = PAGESIZE as usize / 8;

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
            unsafe { DevUART::unsafe_puts("failed to allocate page\n") };
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

    pub fn unmap(&mut self, vm_addr: u64) {
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

    // function for debugging
    fn _translate(&self, vm_addr: u64) -> Option<u64> {
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
