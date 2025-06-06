use super::page_table::PageTableEntry;
use crate::addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr};
use core::{
    self,
    fmt::{self, Debug, Formatter},
};

pub const PAGE_SIZE: usize = 0x1000;
// 4 KiB
pub const PAGE_OFFSET: usize = 0xc; // 12 bits

pub const MEMORY_END: u64 = 0x8800_0000;

/// Design abstraction struct:
/// PhysAddr, VirtAddr, PhysPageNum, VirtPageNum
/// to guarantee memory safty by borrow check in compilation
// SV32 Physical Address Length
pub const PA_WIDTH: usize = 34;

// SV32 Virtual Address Length
pub const VA_WIDTH: usize = 32;

// SV32 Physical Page Number Range
pub const PPN_WIDTH: usize = PA_WIDTH - PAGE_OFFSET;

// SV32 Virtual Page Number Range
pub const VPN_WIDTH: usize = VA_WIDTH - PAGE_OFFSET;

#[repr(C)]
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct PhysPageNum(pub usize);

#[repr(C)]
#[derive(Copy, Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct VirtPageNum(pub usize);

// implete Debugging trait for debug

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

impl From<VirtAddr> for VirtPageNum {
    fn from(v: VirtAddr) -> Self {
        assert_eq!(v.page_offset(), 0);
        v.floor()
    }
}

impl From<VirtPageNum> for VirtAddr {
    fn from(v: VirtPageNum) -> Self {
        VirtAddr::new(v.0 << PAGE_OFFSET)
    }
}

impl From<PhyAddr> for PhysPageNum {
    fn from(v: PhyAddr) -> Self {
        assert_eq!(v.page_offset(), 0);
        v.floor()
    }
}

impl From<PhysPageNum> for PhyAddr {
    fn from(v: PhysPageNum) -> Self {
        PhyAddr::new(v.0 << PAGE_OFFSET)
    }
}

impl VirtAddr {
    pub fn floor(&self) -> VirtPageNum {
        VirtPageNum(self.as_usize() / PAGE_SIZE)
    }

    pub fn ceil(&self) -> VirtPageNum {
        if self.as_usize() == 0 {
            VirtPageNum(0)
        } else {
            VirtPageNum((self.as_usize() - 1 + PAGE_SIZE) / PAGE_SIZE)
        }
    }

    pub fn page_offset(&self) -> usize {
        self.as_usize() & (PAGE_SIZE - 1)
    }

    pub fn aligned(&self) -> bool {
        self.page_offset() == 0
    }
}

impl PhysPageNum {
    pub fn get_pte_array(&self) -> &'static mut [PageTableEntry] {
        let pa: PhyAddr = (*self).into();
        unsafe { core::slice::from_raw_parts_mut(pa.as_usize() as *mut PageTableEntry, 1024) }
    }
    pub fn get_bytes_array(&self) -> &'static mut [u8] {
        let pa: PhyAddr = (*self).into();
        unsafe { core::slice::from_raw_parts_mut(pa.as_usize() as *mut u8, 4096) }
    }
    pub fn get_mut<T>(&self) -> &'static mut T {
        let pa: PhyAddr = (*self).into();
        pa.get_mut()
    }
}

impl VirtPageNum {
    pub fn indexes(&self) -> [usize; 2] {
        let mut vpn = self.0;
        let mut idx = [0usize; 2];
        for i in (0..2).rev() {
            idx[i] = vpn & 1023;
            vpn >>= 10;
        }
        idx
    }
}

impl PhyAddr {
    pub fn floor(&self) -> PhysPageNum {
        PhysPageNum(self.as_usize() / PAGE_SIZE)
    }

    pub fn ceil(&self) -> PhysPageNum {
        if self.as_usize() == 0 {
            PhysPageNum(0)
        } else {
            PhysPageNum((self.as_usize() - 1 + PAGE_SIZE) / PAGE_SIZE)
        }
    }

    pub fn page_offset(&self) -> usize {
        self.as_usize() & (PAGE_SIZE - 1)
    }

    pub fn aligned(&self) -> bool {
        self.page_offset() == 0
    }

    pub fn get_ref<T>(&self) -> &'static T {
        unsafe { (self.as_usize() as *const T).as_ref().unwrap() }
    }

    pub fn get_mut<T>(&self) -> &'static mut T {
        unsafe { (self.as_usize() as *mut T).as_mut().unwrap() }
    }
}
