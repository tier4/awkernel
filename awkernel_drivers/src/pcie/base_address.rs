use core::ptr::{read_volatile, write_volatile};

use awkernel_lib::addr::{virt_addr::VirtAddr, Addr};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AddressType {
    T32B, // 32 bit address space
    T64B, // 64 bit address space
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BaseAddress {
    IO {
        reg_addr: Option<VirtAddr>,
        addr: u32,
        size: usize,
    },
    Mmio {
        reg_addr: Option<VirtAddr>,
        addr: usize,
        size: usize,
        address_type: AddressType,
        prefetchable: bool,
        mapped: bool,
    },
    None,
}

impl BaseAddress {
    pub fn is_64bit_memory(&self) -> bool {
        matches!(
            self,
            Self::Mmio {
                address_type: AddressType::T64B,
                ..
            }
        )
    }

    pub fn is_32bit_memory(&self) -> bool {
        matches!(
            self,
            Self::Mmio {
                address_type: AddressType::T32B,
                ..
            }
        )
    }

    pub fn is_io(&self) -> bool {
        matches!(self, Self::IO { .. })
    }

    pub unsafe fn set_base_address(&mut self, addr: usize) {
        match self {
            Self::IO {
                reg_addr: Some(reg_addr),
                ..
            } => {
                write_volatile(reg_addr.as_mut_ptr(), addr as u32);
            }
            Self::Mmio {
                reg_addr: Some(reg_addr),
                address_type,
                ..
            } => {
                if *address_type == AddressType::T32B {
                    write_volatile(reg_addr.as_mut_ptr(), addr as u32);
                } else {
                    let dst = reg_addr.as_mut_ptr::<u32>();
                    write_volatile(dst, ((addr as u64) & 0xffff_ffff) as u32);
                    write_volatile(dst.add(1), ((addr as u64) >> 32) as u32);
                }
            }
            _ => (),
        }
    }

    pub fn read8(&self, offset: usize) -> Option<u8> {
        match self {
            #[cfg(feature = "x86")]
            BaseAddress::IO { addr, size, .. } => {
                if offset >= *size {
                    return None;
                }

                let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                let mut port2 = x86_64::instructions::port::PortReadOnly::new(0xCFC);

                let addr = *addr | ((offset as u32) & 0xfc);
                let val = unsafe {
                    port1.write(addr);
                    let tmp: u32 = port2.read();
                    (tmp >> ((offset as u32 & 3) * 8)) as u8
                };

                Some(val)
            }
            BaseAddress::Mmio { addr, size, .. } => {
                let dst = *addr + offset;
                assert!(dst + 1 < *addr + *size);
                unsafe { Some(read_volatile(dst as *const u8)) }
            }
            _ => None,
        }
    }

    pub fn read16(&self, offset: usize) -> Option<u16> {
        assert_eq!(offset & 1, 0);
        match self {
            #[cfg(feature = "x86")]
            BaseAddress::IO { addr, size, .. } => {
                if offset >= *size {
                    return None;
                }

                let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                let mut port2 = x86_64::instructions::port::PortReadOnly::new(0xCFC);

                let addr = *addr | ((offset as u32) & 0xfc);
                let val = unsafe {
                    port1.write(addr);
                    let tmp: u32 = port2.read();
                    (tmp >> ((offset as u32 & 2) * 8)) as u16
                };

                Some(val)
            }
            BaseAddress::Mmio { addr, size, .. } => {
                let dst = *addr + offset;
                assert!(dst + 2 < *addr + *size);
                unsafe { Some(read_volatile(dst as *const u16)) }
            }
            _ => None,
        }
    }

    pub fn read32(&self, offset: usize) -> Option<u32> {
        assert_eq!(offset & 0b11, 0);
        match self {
            #[cfg(feature = "x86")]
            BaseAddress::IO { addr, size, .. } => {
                if offset >= *size {
                    return None;
                }

                unsafe {
                    let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                    let mut port2 = x86_64::instructions::port::PortReadOnly::new(0xCFC);
                    port1.write(*addr + ((offset as u32) & 0xfc));
                    Some(port2.read())
                }
            }
            BaseAddress::Mmio { addr, size, .. } => {
                let dst = *addr + offset;
                assert!(dst + 4 < *addr + *size);
                unsafe { Some(read_volatile(dst as *const u32)) }
            }
            _ => None,
        }
    }

    pub fn write8(&mut self, offset: usize, val: u8) {
        match self {
            #[cfg(feature = "x86")]
            BaseAddress::IO { addr, size, .. } => {
                if offset >= *size {
                    return;
                }

                unsafe {
                    let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                    let mut port2 = x86_64::instructions::port::Port::new(0xCFC);

                    let addr = *addr + ((offset as u32) & 0xfc);
                    port1.write(addr);
                    let reg: u32 = port2.read();

                    let mask = !(0xff << ((offset & 3) * 8));

                    port1.write(addr);
                    port2.write((reg & mask) | (val as u32) << ((offset & 3) * 8));
                }
            }
            BaseAddress::Mmio { addr, size, .. } => unsafe {
                let dst = *addr + offset;
                assert!(dst + 1 < *addr + *size);
                write_volatile(dst as *mut u8, val);
            },
            _ => (),
        }
    }

    pub fn write16(&mut self, offset: usize, val: u16) {
        assert_eq!(offset & 1, 0);
        match self {
            #[cfg(feature = "x86")]
            BaseAddress::IO { addr, size, .. } => {
                if offset >= *size {
                    return;
                }

                unsafe {
                    let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                    let mut port2 = x86_64::instructions::port::Port::new(0xCFC);

                    let addr = *addr + ((offset as u32) & 0xfc);
                    port1.write(addr);
                    let reg: u32 = port2.read();

                    let mask = !(0xffff << ((offset & 2) * 8));

                    port1.write(addr);
                    port2.write((reg & mask) | (val as u32) << ((offset & 2) * 8));
                }
            }
            BaseAddress::Mmio { addr, size, .. } => unsafe {
                let dst = *addr + offset;
                assert!(dst + 2 < *addr + *size);
                write_volatile(dst as *mut u16, val);
            },
            _ => (),
        }
    }

    pub fn write32(&mut self, offset: usize, val: u32) {
        assert_eq!(offset & 0b11, 0);
        match self {
            #[cfg(feature = "x86")]
            BaseAddress::IO { addr, size, .. } => {
                if offset >= *size {
                    return;
                }

                unsafe {
                    let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                    let mut port2 = x86_64::instructions::port::PortWriteOnly::new(0xCFC);
                    port1.write(*addr + ((offset as u32) & 0xfc));
                    port2.write(val);
                }
            }
            BaseAddress::Mmio { addr, size, .. } => unsafe {
                let dst = *addr + offset;
                assert!(dst + 4 < *addr + *size);
                write_volatile(dst as *mut u32, val);
            },
            _ => (),
        }
    }
}
