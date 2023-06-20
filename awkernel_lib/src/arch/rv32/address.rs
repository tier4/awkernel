use super::PageTableEntry;
use core::fmt::{self, Debug, Formatter};
pub const PAGE_SIZE: usize = 0x1000; // 4 KiB
pub const PAGE_OFFSET: usize = 0xc; // 12 bits 

/// Design abstraction struct: 
/// PhysAddr, VirtAddr, PhysPageNum, VirtPageNum 
/// to guarantee memory safty by borrow check in compilation


const PA_WIDTH: usize = 34; // SV32 Physical Address Length
const VA_WIDTH: usize = 32; // SV32 Virtual Address Length
const PPN_WIDTH: usize = PA_WIDTH - PAGE_OFFSET; // SV32 Physical Page Number Range
const VPN_WIDTH: usize = VA_WIDTH - PAGE_OFFSET; // SV32 Virtual Page Number Range

#[repr(C)]
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct PhysAddr(pub usize);

#[repr(C)]
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct VirtAddr(pub usize);

#[repr(C)]
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct PhysPageNum(pub usize);

#[repr(C)]
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct VirtPageNum(pub usize);

// implete Debugging trait for debug

impl Debug for PhysAddr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("PA: {:#x}", self.0))
    }
}

impl Debug for VirtAddr {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("VA: {:#x}", self.0))
    }
}

impl Debug for PhysPageNum {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("PPN: {:#x}", self.0))
    }
}

impl Debug for VirtPageNum {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("VPN: {:#x}", self.0))
    }
}

