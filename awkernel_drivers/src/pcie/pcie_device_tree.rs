use awkernel_lib::addr::phy_addr::PhyAddr;

use super::base_address::{AddressType, BaseAddress};

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum RangeCode {
    Config,
    IOSpace,
    Memory32,
    Memory64,
}

#[derive(Debug, Clone)]
pub struct PCIeRange {
    prefetchable: bool,
    code: RangeCode,
    bus_number: u8,
    device_number: u8,
    function_number: u8,
    device_addr: usize,
    cpu_addr: usize,
    size: usize,
    allocated_size: usize,
}

pub struct AllocatedRange {
    pub device_addr: usize,
    pub cpu_addr: BaseAddress,
}

impl PCIeRange {
    pub fn new(head: u32, device_addr: usize, cpu_addr: usize, size: usize) -> Self {
        // https://elinux.org/Device_Tree_Usage#PCI_Address_Translation
        let prefetchable = head & (1 << 30) != 0;

        let code = match (head >> 24) & 0b11 {
            0b00 => RangeCode::Config,
            0b01 => RangeCode::IOSpace,
            0b10 => RangeCode::Memory32,
            0b11 => RangeCode::Memory64,
            _ => unreachable!(),
        };

        let bus_number = ((head >> 16) & 0xff) as u8;
        let device_number = ((head >> 11) & 0b11111) as u8;
        let function_number = ((head >> 8) & 0b111) as u8;

        Self {
            prefetchable,
            code,
            bus_number,
            device_number,
            function_number,
            device_addr,
            cpu_addr,
            size,
            allocated_size: 0,
        }
    }

    pub fn get_cpu_mem(&self) -> PhyAddr {
        PhyAddr::new(self.cpu_addr)
    }

    pub fn get_size(&self) -> usize {
        self.size
    }

    pub fn allocate(
        &mut self,
        addr: &BaseAddress,
        bridge_bus_number: u8,
        bridge_device_number: u8,
        bridge_function_number: u8,
    ) -> Option<AllocatedRange> {
        if self.bus_number != bridge_bus_number
            || self.device_number != bridge_device_number
            || self.function_number != bridge_function_number
        {
            return None;
        }

        // TODO: align memory

        match addr {
            BaseAddress::IO { reg_addr, size, .. } => {
                if self.code != RangeCode::IOSpace {
                    return None;
                }

                let allocated_size = align_addr(self.allocated_size, *size) + size;
                if allocated_size > self.size {
                    return None;
                }

                let allocated = AllocatedRange {
                    device_addr: self.device_addr + allocated_size,
                    cpu_addr: BaseAddress::Mmio {
                        reg_addr: *reg_addr,
                        addr: self.cpu_addr + allocated_size,
                        size: *size,
                        address_type: AddressType::T32B,
                        prefetchable: self.prefetchable,
                        mapped: true,
                    },
                };

                self.allocated_size = allocated_size;

                Some(allocated)
            }
            BaseAddress::Mmio {
                reg_addr,
                size,
                address_type,
                prefetchable,
                ..
            } => {
                if self.prefetchable != *prefetchable {
                    return None;
                }

                let allocated_size = align_addr(self.allocated_size, *size) + size;
                if allocated_size > self.size {
                    return None;
                }

                let address_type = match address_type {
                    AddressType::T32B => {
                        if self.code != RangeCode::Memory32 {
                            return None;
                        }
                        AddressType::T32B
                    }
                    AddressType::T64B => {
                        if self.code != RangeCode::Memory64 {
                            return None;
                        }
                        AddressType::T64B
                    }
                };

                let result = AllocatedRange {
                    device_addr: self.device_addr + allocated_size,
                    cpu_addr: BaseAddress::Mmio {
                        reg_addr: *reg_addr,
                        addr: self.cpu_addr + allocated_size,
                        size: *size,
                        address_type,
                        prefetchable: self.prefetchable,
                        mapped: true,
                    },
                };

                self.allocated_size = allocated_size;

                Some(result)
            }
            BaseAddress::None => None,
        }
    }

    pub fn translate(
        &self,
        addr: &BaseAddress,
        bridge_bus_number: u8,
        bridge_device_number: u8,
        bridge_function_number: u8,
    ) -> Option<BaseAddress> {
        if self.bus_number != bridge_bus_number
            || self.device_number != bridge_device_number
            || self.function_number != bridge_function_number
        {
            return None;
        }

        match addr {
            BaseAddress::IO {
                reg_addr,
                addr,
                size,
            } => {
                if self.code != RangeCode::IOSpace {
                    return None;
                }

                let addr = *addr as usize;

                if (self.device_addr..(self.device_addr + self.size)).contains(&addr)
                    && (self.device_addr..(self.device_addr + self.size))
                        .contains(&(addr + size - 1))
                {
                    Some(BaseAddress::Mmio {
                        reg_addr: *reg_addr,
                        addr: self.cpu_addr + (addr - self.device_addr),
                        size: self.size - (addr - self.device_addr),
                        address_type: AddressType::T64B,
                        prefetchable: self.prefetchable,
                        mapped: true,
                    })
                } else {
                    None
                }
            }
            BaseAddress::Mmio {
                reg_addr,
                addr,
                size,
                address_type,
                prefetchable,
                mapped,
            } => {
                match address_type {
                    AddressType::T32B => {
                        if self.code != RangeCode::Memory32 {
                            return None;
                        }
                    }
                    AddressType::T64B => {
                        if self.code != RangeCode::Memory64 {
                            return None;
                        }
                    }
                };

                if self.prefetchable != *prefetchable {
                    return None;
                }

                let range = self.device_addr..(self.device_addr + self.size);

                if range.contains(addr) && range.contains(&(*addr + *size - 1)) {
                    Some(BaseAddress::Mmio {
                        reg_addr: *reg_addr,
                        addr: self.cpu_addr + (addr - self.device_addr),
                        size: *size,
                        address_type: AddressType::T64B,
                        prefetchable: self.prefetchable,
                        mapped: *mapped,
                    })
                } else {
                    None
                }
            }
            BaseAddress::None => None,
        }
    }
}

#[inline]
fn align_addr(addr: usize, align: usize) -> usize {
    addr.wrapping_add(align - 1) & !(align - 1)
}
