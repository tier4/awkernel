use super::address::{PhysAddr, PhysPageNum, VirtAddr, VirtPageNum, PAGE_SIZE, PPN_WIDTH};
use super::frame_allocator::{frame_alloc, FrameTracker};
use alloc::vec;
use alloc::vec::Vec;
use bitflags::*;

/// PTE Flags of RISC V SV39 page table
///  V - Valid
///  R - Read
///  W - Write
///  X - eXecute
///  U - User
///  G - Global
///  A - Accessed
///  D - Dirty
bitflags! {
    #[derive(PartialEq)]
    pub struct Flags: u8 {
        const V = 1 << 0;
        const R = 1 << 1;
        const W = 1 << 2;
        const X = 1 << 3;
        const U = 1 << 4;
        const G = 1 << 5;
        const A = 1 << 6;
        const D = 1 << 7;
    }
}

#[derive(Copy, Clone)]
#[repr(C)]
pub struct PageTableEntry {
    pub bits: usize,
}

impl PageTableEntry {
    pub fn new(ppn: PhysPageNum, flags: Flags) -> Self {
        Self {
            bits: ppn.0 << 10 | flags.bits() as usize,
        }
    }

    pub fn empty() -> Self {
        PageTableEntry { bits: 0 }
    }

    pub fn ppn(&self) -> PhysPageNum {
        (self.bits >> 10 & ((1usize << PPN_WIDTH) - 1)).into()
    }

    pub fn flags(&self) -> Flags {
        Flags::from_bits(self.bits as u8).unwrap()
    }

    pub fn is_valid(&self) -> bool {
        (self.flags() & Flags::V) != Flags::empty()
    }

    pub fn is_readable(&self) -> bool {
        (self.flags() & Flags::R) != Flags::empty()
    }

    pub fn is_writable(&self) -> bool {
        (self.flags() & Flags::W) != Flags::empty()
    }

    pub fn is_executable(&self) -> bool {
        (self.flags() & Flags::X) != Flags::empty()
    }
}

pub struct PageTable {
    root_ppn: PhysPageNum,
    frames: Vec<FrameTracker>,
}

impl PageTable {
    pub fn new() -> Self {
        let frame = frame_alloc().unwrap();
        Self {
            root_ppn: frame.ppn,
            frames: vec![frame],
        }
    }

    fn find_pte(&mut self, vpn: VirtPageNum) -> Option<&mut PageTableEntry> {
        let idxs = vpn.indexes();
        let mut ppn = self.root_ppn;
        for (i, idx) in idxs.iter().enumerate() {
            let pte = &mut ppn.get_pte_array()[*idx];
            if i == 2 {
                // Level 0 (leaf level) - changed from 1 to 2
                return Some(pte);
            }
            if !pte.is_valid() {
                return None;
            }
            ppn = pte.ppn();
        }
        None
    }

    fn find_pte_create(&mut self, vpn: VirtPageNum) -> Option<&mut PageTableEntry> {
        let idxs = vpn.indexes();
        let mut ppn = self.root_ppn;
        for (i, idx) in idxs.iter().enumerate() {
            let pte = &mut ppn.get_pte_array()[*idx];
            if i == 2 {
                // Level 0 (leaf level) - changed from 1 to 2
                return Some(pte);
            }
            if !pte.is_valid() {
                let frame = frame_alloc().unwrap();
                *pte = PageTableEntry::new(frame.ppn, Flags::V);
                self.frames.push(frame);
            }
            ppn = pte.ppn();
        }
        None
    }

    pub fn map(&mut self, vpn: VirtPageNum, ppn: PhysPageNum, flags: Flags) -> bool {
        let pte = self.find_pte_create(vpn).unwrap();
        if pte.is_valid() {
            // Page already mapped
            return false;
        }
        *pte = PageTableEntry::new(ppn, flags | Flags::V);
        true
    }

    pub fn unmap(&mut self, vpn: VirtPageNum) {
        let pte = self.find_pte(vpn).unwrap();
        assert!(pte.is_valid(), "vpn{:?} is invalid before unmapping", vpn);
        *pte = PageTableEntry::empty();
    }

    pub fn translate(&mut self, vpn: VirtPageNum) -> Option<PageTableEntry> {
        self.find_pte(vpn).map(|pte| *pte)
    }

    pub fn translate_va(&mut self, va: VirtAddr) -> Option<PageTableEntry> {
        let vpn: VirtPageNum = va.into();
        self.translate(vpn)
    }
}

pub fn get_page_table(_va: VirtAddr) -> Option<PageTable> {
    // TODO: Read actual SATP register when riscv crate is available
    // For now, create a new page table
    if let Some(tracker) = frame_alloc() {
        let page_table = PageTable {
            root_ppn: tracker.ppn,
            frames: vec![tracker],
        };
        Some(page_table)
    } else {
        None
    }
}

// Frame type for integration with common paging interface
pub struct Page {
    addr: PhysAddr,
}

impl crate::paging::Frame for Page {
    fn start_address(&self) -> crate::addr::phy_addr::PhyAddr {
        crate::addr::phy_addr::PhyAddr::new(self.addr.0)
    }

    fn set_address(&mut self, addr: crate::addr::phy_addr::PhyAddr) {
        use crate::addr::Addr;
        self.addr = PhysAddr(addr.as_usize());
    }

    fn size(&self) -> usize {
        PAGE_SIZE
    }
}

// Page allocator for integration with common paging interface
pub struct RV64PageAllocator;

impl crate::paging::FrameAllocator<Page, &'static str> for RV64PageAllocator {
    fn allocate_frame(&mut self) -> Result<Page, &'static str> {
        if let Some(tracker) = frame_alloc() {
            let addr = PhysAddr((tracker.ppn.0) << 12); // Convert PPN to physical address
            core::mem::forget(tracker); // Transfer ownership to Page
            Ok(Page { addr })
        } else {
            Err("Out of memory")
        }
    }
}

impl crate::paging::PageTable<Page, RV64PageAllocator, &'static str> for PageTable {
    unsafe fn map_to(
        &mut self,
        virt_addr: crate::addr::virt_addr::VirtAddr,
        phy_addr: crate::addr::phy_addr::PhyAddr,
        flags: crate::paging::Flags,
        _page_allocator: &mut RV64PageAllocator,
    ) -> Result<(), &'static str> {
        use crate::addr::Addr;
        let vpn = VirtPageNum::from(VirtAddr(virt_addr.as_usize()));
        let ppn = PhysPageNum::from(PhysAddr(phy_addr.as_usize()));

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
