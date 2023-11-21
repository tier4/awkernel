use super::address::{
    PhysAddr, PhysPageNum, VirtAddr, VirtPageNum, PAGE_SIZE, PA_WIDTH, PPN_WIDTH, VA_WIDTH,
    VPN_WIDTH,
};
use crate::{delay::wait_forever, memory::PAGESIZE};
use bitflags::*;

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
            bits: ppn.0 << 10 | flags.bits as usize,
        }
    }

    pub fn ppn(&self) -> PhysPageNum {
        (self.bits >> 10 & ((1usize << PPN_WIDTH) - 1)).into()
    }

    pub fn flags(&self) -> Flags {
        Flags::from_bits(self.bits as u8).unwrap()
    }

    pub fn is_valid(&self) -> bool {
        (self.bits() & Flags::V) != Flags::empty()
    }

    pub fn is_readable(&self) -> bool {
        (self.bits() & Flags::R) != Flags::empty()
    }

    pub fn is_writable(&self) -> bool {
        (self.bits() & Flags::W) != Flags::empty()
    }

    pub fn is_executable(&self) -> bool {
        (self.bits() & Flags::X) != Flags::empty()
    }
}

pub struct PageTable {
    root_ppn: PhysPageNum,
}

impl PageTable {}
