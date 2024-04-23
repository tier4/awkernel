use super::address::{
    PhysAddr, PhysPageNum, VirtAddr, VirtPageNum, PAGE_SIZE, PA_WIDTH, PPN_WIDTH, VA_WIDTH,
    VPN_WIDTH,
};
use super::frame_allocator::{FrameTracker, frame_alloc};
use crate::{delay::wait_forever, memory::PAGESIZE};
use bitflags::*;
use x86_64::structures::paging::page_table::PageTableEntry;

use super::frame_allocator::*;

/// PTE Flags of RISC V SV32 page table
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
    pub fn new(ppn: PhysAddr, flags: Flags) -> Self {
        Self {
            bits: ppn.0 << 10 | flags.bits() as usize,
        }
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
        let mut result = Option<&mut PageTableEntry> = None;
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
        let mut result = Option<&mut PageTableEntry> = None;
        for (i, idx) in idxs.iter().enumerate() {
            let pte = &mut ppn.get_pte_array()[*idx];
            if i == 1 {
                result = Some(pte);
                break;
            }
            if !pte.is_valid() {
                let frame = frame_alloc().unwrap();
                *pte = PageTableEntry::new(frame.ppn, PTEFlags::V);
                self.frames.push(frame);
            }
            ppn = pte.ppn();
        }
        result
    }
    
    pub fn map(&mut self, vpn: VirtPageNum, ppn: PhysPageNum, flags: PTEFlags) {
        let pte = self.find_pte_create(vpn).unwrap();
        assert!(!pte.is_valid(), "vpn{:?} is mapped before mapping", vpn);
        *pte = PageTableEntry::new(ppn, flags | PTEFlags::V);
    }
    
    pub fn unmap(&mut self, vpn: VirtPageNum) {
        let pte = self.find_pte(vpn).unwrap();
        assert!(pte.is_valid(), "vpn{:?} is invalid before unmapping", vpn);
        *pte = PageTableEntry::empty();
    }
}
