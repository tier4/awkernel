use core::fmt;

pub fn ceiling_div(size: usize, units: usize) -> usize {
    (size / units) + (!size.is_multiple_of(units) as usize)
}

pub fn align_up(length: usize, alignment: usize) -> usize {
    ceiling_div(length, alignment) * alignment
}

pub fn align_down(length: usize, alignment: usize) -> usize {
    length & !(alignment - 1)
}

pub fn offset_from_align(length: usize, alignment: usize) -> usize {
    length & (alignment - 1)
}

#[inline(always)]
const fn kernel_virtual_base_addr() -> u64 {
    0xffff_0000_0000_0000
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct PhysicalAddress(u64);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct VirtualAddress(u64);

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct KernelVirtualAddress(u64);

impl From<u64> for PhysicalAddress {
    fn from(addr: u64) -> Self {
        if addr & kernel_virtual_base_addr() != 0 {
            panic!("physical address is using kernel space: {:x}", addr);
        }
        Self(addr)
    }
}

impl From<PhysicalAddress> for u64 {
    fn from(paddr: PhysicalAddress) -> Self {
        paddr.0
    }
}

impl From<PhysicalAddress> for usize {
    fn from(paddr: PhysicalAddress) -> usize {
        paddr.0 as usize
    }
}

impl fmt::Debug for PhysicalAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "PhysicalAddress({:#x})", self.0)
    }
}

impl PhysicalAddress {
    pub fn add(self, offset: usize) -> Self {
        Self(self.0 + offset as u64)
    }

    pub fn to_kernel_addr(self) -> KernelVirtualAddress {
        KernelVirtualAddress::from(self)
    }

    pub fn align_up(self, align: usize) -> Self {
        Self(align_up(self.0 as usize, align) as u64)
    }
}

impl From<u64> for VirtualAddress {
    fn from(addr: u64) -> Self {
        Self(addr)
    }
}

impl From<VirtualAddress> for u64 {
    fn from(vaddr: VirtualAddress) -> Self {
        vaddr.0
    }
}

impl From<VirtualAddress> for usize {
    fn from(vaddr: VirtualAddress) -> Self {
        vaddr.0 as usize
    }
}

impl fmt::Debug for VirtualAddress {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "VirtualAddress({:#x})", self.0)
    }
}

impl VirtualAddress {
    pub fn add(self, offset: usize) -> Self {
        Self(self.0 + offset as u64)
    }

    pub fn sub(self, offset: usize) -> Self {
        Self(self.0 - offset as u64)
    }

    pub fn align_down(self, align: usize) -> Self {
        Self(align_down(self.0 as usize, align) as u64)
    }

    pub fn align_up(self, align: usize) -> Self {
        Self(align_up(self.0 as usize, align) as u64)
    }

    pub fn offset_from_align(self, align: usize) -> usize {
        offset_from_align(self.0 as usize, align)
    }
}

impl From<PhysicalAddress> for KernelVirtualAddress {
    fn from(addr: PhysicalAddress) -> Self {
        Self(addr.0 | kernel_virtual_base_addr())
    }
}

impl From<KernelVirtualAddress> for PhysicalAddress {
    fn from(addr: KernelVirtualAddress) -> Self {
        Self(addr.0 & !kernel_virtual_base_addr())
    }
}

impl KernelVirtualAddress {
    pub const fn new(addr: u64) -> Self {
        Self(addr | kernel_virtual_base_addr())
    }

    pub fn add(self, offset: usize) -> Self {
        Self(self.0 + offset as u64)
    }

    pub unsafe fn as_ptr<T>(self) -> *const T {
        self.0 as *const T
    }

    pub unsafe fn as_mut<T>(self) -> *mut T {
        self.0 as *mut T
    }
}
