use core::ptr::{read_volatile, write_volatile};

use awkernel_lib::addr::{virt_addr::VirtAddr, Addr};

#[derive(Debug, Clone)]
pub enum ConfigSpace {
    #[allow(dead_code)]
    IO(u32),

    Mmio(VirtAddr),
}

impl ConfigSpace {
    #[cfg(feature = "x86")]
    pub fn new_io(bus_number: u8, device_number: u8, function_number: u8) -> Self {
        let base = 0x80000000
            | (bus_number as u32) << 16
            | (device_number as u32) << 11
            | (function_number as u32) << 8;
        Self::IO(base)
    }

    pub fn new_memory(base: VirtAddr) -> Self {
        Self::Mmio(base)
    }

    pub fn addr(&self, offset: usize) -> Option<VirtAddr> {
        let ConfigSpace::Mmio(base) = self else {
            return None;
        };

        Some(*base + offset)
    }

    pub fn read_u16(&self, offset: usize) -> u16 {
        match self {
            #[allow(unused_variables)]
            Self::IO(base) => {
                #[cfg(feature = "x86")]
                {
                    let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                    let mut port2 = x86_64::instructions::port::PortReadOnly::new(0xCFC);

                    let addr = *base | ((offset as u32) & 0xfc);
                    unsafe {
                        port1.write(addr);
                        let tmp: u32 = port2.read();
                        (tmp >> (((offset as u32 & 2) * 8) & 0xffff)) as u16
                    }
                }

                #[cfg(not(feature = "x86"))]
                {
                    unreachable!()
                }
            }
            Self::Mmio(base) => {
                let addr = *base + offset;
                unsafe { read_volatile(addr.as_ptr()) }
            }
        }
    }

    pub fn read_u32(&self, offset: usize) -> u32 {
        match self {
            #[allow(unused_variables)]
            Self::IO(base) => {
                #[cfg(feature = "x86")]
                {
                    let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                    let mut port2 = x86_64::instructions::port::PortReadOnly::new(0xCFC);

                    let addr = *base | ((offset as u32) & 0xfc);
                    unsafe {
                        port1.write(addr);
                        port2.read()
                    }
                }

                #[cfg(not(feature = "x86"))]
                {
                    unreachable!()
                }
            }
            Self::Mmio(base) => {
                let addr = *base + offset;
                unsafe { read_volatile(addr.as_ptr()) }
            }
        }
    }

    pub fn write_u32(&self, data: u32, offset: usize) {
        match self {
            #[allow(unused_variables)]
            Self::IO(base) => {
                log::info!("mmio!");
                #[cfg(feature = "x86")]
                {
                    let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                    let mut port2 = x86_64::instructions::port::PortWriteOnly::new(0xCFC);

                    let addr = *base | ((offset as u32) & 0xfc);
                    unsafe {
                        port1.write(addr);
                        port2.write(data);
                    }
                }

                #[cfg(not(feature = "x86"))]
                {
                    unreachable!()
                }
            }
            Self::Mmio(base) => {
                let addr = *base + offset;
                unsafe { write_volatile(addr.as_mut_ptr(), data) }
            }
        }
    }
}
