use super::address::{PhysPageNum, VirtPageNum, PAGE_SIZE, PPN_WIDTH};
use super::frame_allocator::{frame_alloc, FrameTracker};
use crate::addr::{phy_addr::PhyAddr, virt_addr::VirtAddr};
use alloc::vec;
use alloc::vec::Vec;
use bitflags::*;

bitflags! {
    /// PTE Flags for RISC-V Sv32 page table
    /// Based on RISC-V Privileged Architecture Specification
    ///
    /// V - Valid: The PTE is valid
    /// R - Read: Supervisor/User can read the page
    /// W - Write: Supervisor/User can write the page
    /// X - Execute: Supervisor/User can execute instructions on the page
    /// U - User: Page is accessible to user mode
    /// G - Global: Mapping exists in all address spaces
    /// A - Accessed: Page has been accessed since A bit was cleared
    /// D - Dirty: Page has been written since D bit was cleared
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
        let mut result: Option<&mut PageTableEntry> = None;
        for (i, idx) in idxs.iter().enumerate() {
            let pte = &mut ppn.get_pte_array()[*idx];
            if i == 1 {
                result = Some(pte);
                break;
            }
            if !pte.is_valid() {
                return None;
            }
            ppn = pte.ppn();
        }
        result
    }

    fn find_pte_create(&mut self, vpn: VirtPageNum) -> Option<&mut PageTableEntry> {
        let idxs = vpn.indexes();
        let mut ppn = self.root_ppn;
        let mut result: Option<&mut PageTableEntry> = None;
        for (i, idx) in idxs.iter().enumerate() {
            let pte = &mut ppn.get_pte_array()[*idx];
            if i == 1 {
                result = Some(pte);
                break;
            }
            if !pte.is_valid() {
                let frame = frame_alloc().unwrap();
                *pte = PageTableEntry::new(frame.ppn, Flags::V);
                self.frames.push(frame);
            }
            ppn = pte.ppn();
        }
        result
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
        assert!(pte.is_valid(), "vpn{vpn:?} is invalid before unmapping");
        *pte = PageTableEntry::empty();
    }

    pub fn translate(&mut self, vpn: VirtPageNum) -> Option<PageTableEntry> {
        self.find_pte(vpn).map(|pte| *pte)
    }

    #[allow(dead_code)]
    pub fn translate_va(&mut self, va: VirtAddr) -> Option<PageTableEntry> {
        let vpn: VirtPageNum = va.into();
        self.translate(vpn)
    }

    /// Generate SATP (Supervisor Address Translation and Protection) register value
    ///
    /// RISC-V SATP register format for RV32 (Sv32):
    /// Bits 31: MODE field (1 bit)
    ///   - 0: Bare (no translation)
    ///   - 1: Sv32 (32-bit virtual addressing, 2-level page tables)
    ///     Bits 30-22: ASID (Address Space Identifier, 9 bits)
    ///     Bits 21-0: PPN (Physical Page Number of root page table, 22 bits)
    ///
    /// For Sv32, MODE=1 enables virtual memory translation with 2-level page tables
    /// and supports 32-bit virtual addresses with 4KB pages.
    pub fn token(&self) -> usize {
        (1usize << 31)        // MODE = 1 (Sv32 paging mode)
        | self.root_ppn.0 // PPN = Physical Page Number of the root page table
    }
}

/// Get the current page table from SATP register
pub fn get_page_table(_va: VirtAddr) -> Option<PageTable> {
    use core::arch::asm;

    // Read SATP register
    let satp: usize;
    unsafe {
        asm!("csrr {}, satp", out(reg) satp);
    }

    // Extract PPN from SATP (bits 21:0 for Sv32)
    let root_ppn = PhysPageNum(satp & ((1usize << 22) - 1));

    // Check if paging is enabled (MODE field in bit 31)
    let mode = (satp >> 31) & 0x1;
    if mode == 0 {
        // Bare mode - no translation
        return None;
    }

    // Return page table with current root
    Some(PageTable {
        root_ppn,
        frames: vec![], // Don't manage frames for current page table
    })
}

// Frame type for integration with common paging interface
pub struct Page {
    addr: PhyAddr,
}

impl crate::paging::Frame for Page {
    fn start_address(&self) -> PhyAddr {
        self.addr
    }

    fn set_address(&mut self, addr: PhyAddr) {
        self.addr = addr;
    }

    fn size(&self) -> usize {
        PAGE_SIZE
    }
}

// Page allocator for integration with common paging interface
pub struct RV32PageAllocator;

impl crate::paging::FrameAllocator<Page, &'static str> for RV32PageAllocator {
    fn allocate_frame(&mut self) -> Result<Page, &'static str> {
        if let Some(tracker) = frame_alloc() {
            let addr = PhyAddr::new((tracker.ppn.0) << 12); // Convert PPN to physical address
            core::mem::forget(tracker); // Transfer ownership to Page
            Ok(Page { addr })
        } else {
            Err("Out of memory")
        }
    }
}

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
