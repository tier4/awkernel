use super::PageTableEntry;
use core::{
    self,
    fmt::{self, Debug, Formatter},
};
pub const PAGE_SIZE: usize = 0x1000; // 4 KiB
pub const PAGE_OFFSET: usize = 0xc; // 12 bits

pub const MEMORY_END: u64 = 0x8800_0000;

/// Design abstraction struct:
/// PhysAddr, VirtAddr, PhysPageNum, VirtPageNum
/// to guarantee memory safty by borrow check in compilation
pub const PA_WIDTH: usize = 34; // SV32 Physical Address Length
pub const VA_WIDTH: usize = 32; // SV32 Virtual Address Length
pub const PPN_WIDTH: usize = PA_WIDTH - PAGE_OFFSET; // SV32 Physical Page Number Range
pub const VPN_WIDTH: usize = VA_WIDTH - PAGE_OFFSET; // SV32 Virtual Page Number Range

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

/// From<usize> trait
impl From<usize> for PhysAddr {
    fn from(v: usize) -> Self {
        Self(v & ((1 << PA_WIDTH) - 1))
    }
}

impl From<usize> for VirtAddr {
    fn from(v: usize) -> Self {
        Self(v & ((1 << VA_WIDTH) - 1))
    }
}

impl From<usize> for PhysPageNum {
    fn from(v: usize) -> Self {
        Self(v & ((1 << PPN_WIDTH) - 1))
    }
}

impl From<usize> for VirtPageNum {
    fn from(v: usize) -> Self {
        Self(v & ((1 << VPN_WIDTH) - 1))
    }
}

impl From<PhysAddr> for usize {
    fn from(v: PhysAddr) -> Self {
        v.0
    }
}

impl From<VirtAddr> for usize {
    fn from(v: VirtAddr) -> Self {
        if v.0 >= ((1 << VPN_WIDTH) - 1) {
            v.0 | (!((1 << VPN_WIDTH) - 1))
        } else {
            v.0
        }
    }
}

impl From<PhysPageNum> for usize {
    fn from(v: PhysPageNum) -> Self {
        v.0
    }
}

impl From<VirtPageNum> for usize {
    fn from(v: VirtPageNum) -> Self {
        v.0
    }
}

impl VirtAddr {
    pub fn floor(&self) -> VirtPageNum {
        VirtPageNum(self.0 / PAGE_SIZE)
    }

    pub fn ceil(&self) -> VirtPageNum {
        if self.0 == 0 {
            VirtPageNum(0)
        } else {
            VirtPageNum((self.0 - 1 + PAGE_SIZE) / PAGE_SIZE)
        }
    }

    pub fn page_offset(&self) -> usize {
        self.0 & (PAGE_SIZE - 1)
    }

    pub fn aligned(&self) -> bool {
        self.page_offset() == 0
    }
}

impl PhysPageNum {
    pub fn get_pte_array(&self) -> &'static mut [PageTableEntry] {
        let pa: PhysAddr = (*self).into();
        unsafe { core::slice::from_raw_parts_mut(pa.0 as *mut PageTableEntry, 512) }
    }
    pub fn get_bytes_array(&self) -> &'static mut [u8] {
        let pa: PhysAddr = (*self).into();
        unsafe { core::slice::from_raw_parts_mut(pa.0 as *mut u8, 4096) }
    }
    pub fn get_mut<T>(&self) -> &'static mut T {
        let pa: PhysAddr = (*self).into();
        pa.get_mut()
    }
}
