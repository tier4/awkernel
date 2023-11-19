use array_macro::array;
use awkernel_lib::paging::{Frame, FrameAllocator, PageTable, PAGESIZE};
use core::{
    fmt::{self, Debug},
    ptr::{read_volatile, write_volatile},
};

#[cfg(feature = "x86")]
use awkernel_lib::arch::x86_64::acpi::AcpiMapper;

#[cfg(feature = "x86")]
use acpi::{AcpiTables, PciConfigRegions};

mod capability;
pub mod msi;
mod msix;
pub mod pcie_id;

#[derive(Debug, Clone)]
pub enum BaseAddress {
    IO(u32),
    MMIO {
        addr: usize,
        size: usize,
        address_type: AddressType,
        prefetchable: bool,
    },
    None,
}

impl BaseAddress {
    pub fn is_64bit_memory(&self) -> bool {
        matches!(
            self,
            Self::MMIO {
                address_type: AddressType::T64B,
                ..
            }
        )
    }

    pub fn read(&self, offset: usize) -> Option<u32> {
        match self {
            #[cfg(feature = "x86")]
            BaseAddress::IO(addr) => unsafe {
                let mut val;
                let port = *addr + offset as u32;
                core::arch::asm!("in eax, dx",
                        out("eax") val,
                        in("dx") port,
                        options(nomem, nostack, preserves_flags));
                Some(val)
            },
            BaseAddress::MMIO { addr, size, .. } => {
                assert!(*addr & 0b11 == 0 && offset + 4 < *size);
                unsafe { Some(read_volatile((*addr + offset) as *const u32)) }
            }
            _ => None,
        }
    }

    pub fn write(&mut self, offset: usize, val: u32) {
        match self {
            #[cfg(feature = "x86")]
            BaseAddress::IO(addr) => unsafe {
                let port = *addr + offset as u32;
                core::arch::asm!("out dx, eax",
                        in("eax") val,
                        in("dx") port,
                        options(nomem, nostack, preserves_flags));
            },
            BaseAddress::MMIO { addr, size, .. } => unsafe {
                assert!(*addr & 0b11 == 0 && offset + 4 < *size);
                write_volatile((*addr + offset) as *mut u32, val);
            },
            _ => (),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum AddressType {
    T32B, // 32 bit address space
    T64B, // 64 bit address space
}

#[derive(Debug)]
pub enum PCIeDeviceErr {
    InitFailure,
    PageTableFailure,
    UnRecognizedDevice { bus: u8, device: u16, vendor: u16 },
}

impl fmt::Display for PCIeDeviceErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InitFailure => {
                write!(f, "Failed to initialize the device driver.")
            }
            Self::PageTableFailure => {
                write!(f, "Failed to map memory regions of MMIO.")
            }
            Self::UnRecognizedDevice {
                bus,
                device,
                vendor,
            } => {
                write!(
                    f,
                    "Unregistered PCIe device: bus = {bus}, device = {device}, vendor = {vendor}"
                )
            }
        }
    }
}

pub(crate) mod registers {
    use awkernel_lib::{mmio_r, mmio_rw};
    use bitflags::bitflags;

    bitflags! {
        #[derive(Copy, Clone, Debug)]
        pub struct StatusCommand: u32 {
            // Status register
            const DETECTED_PARITY_ERROR = 1 << 31;
            const SIGNALED_SYSTEM_ERROR = 1 << 30;
            const RECEIVED_MASTER_ABORT = 1 << 29;
            const RECEIVED_TARGET_ABORT = 1 << 28;
            const SIGNALED_TARGET_ABORT = 1 << 27;

            const DEVSEL_TIMING_SLOW = 0b10 << 25;
            const DEVSEL_TIMING_MEDIUM = 0b01 << 25;
            const DEVSEL_TIMING_FAST = 0b00 << 25;

            const MASTER_DATA_PARITY_ERROR = 1 << 24;
            const FAST_BACK_TO_BACK_CAPABLE = 1 << 23;
            const CAPABLE_66MHZ = 1 << 21;
            const CAPABILITIES_LIST = 1 << 20;
            const INTERRUPT_STATUS = 1 << 19;

            // Command register
            const INTERRUPT_DISABLE = 1 << 10;
            const FAST_BACK_TO_BACK_ENABLE = 1 << 9;
            const SERR_ENABLE = 1 << 8;
            const PARITY_ERROR_RESPONSE = 1 << 6;
            const VGA_PALETTE_SNOOP = 1 << 5;
            const MEMORY_WRITE_AND_INVALIDATE_ENABLE = 1 << 4;
            const SPECIAL_CYCLES = 1 << 3;
            const BUS_MASTER = 1 << 2; // Enable DMA
            const MEMORY_SPACE = 1 << 1;
            const IO_SPACE = 1 << 0;
        }
    }

    pub const HEADER_TYPE_GENERAL_DEVICE: u8 = 0;
    pub const HEADER_TYPE_PCI_TO_PCI_BRIDGE: u8 = 1;
    pub const HEADER_TYPE_PCI_TO_CARDBUS_BRIDGE: u8 = 2;

    mmio_r!(offset 0x00 => pub DEVICE_VENDOR_ID<u32>);
    mmio_rw!(offset 0x04 => pub STATUS_COMMAND<StatusCommand>);
    mmio_r!(offset 0x08 => pub CLASS_CODE_REVISION_ID<u32>);
    mmio_r!(offset 0x0c => pub BIST_HEAD_LAT_CACH<u32>);
    mmio_r!(offset 0x34 => pub CAPABILITY_POINTER<u32>); // for Type 0 and 1
    mmio_r!(offset 0x00 => pub MESSAGE_CONTROL_NEXT_PTR_CAP_ID<u32>);

    pub const BAR0: usize = 0x10;
}

/// Initialize the PCIe for ACPI
#[cfg(feature = "x86")]
pub fn init_with_acpi<F, FA, PT, E>(
    dma_offset: usize,
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut PT,
    page_allocator: &mut FA,
) where
    F: Frame,
    FA: FrameAllocator<F, E>,
    PT: PageTable<F, FA, E>,
    E: Debug,
{
    use awkernel_lib::{
        addr::{phy_addr::PhyAddr, virt_addr::VirtAddr},
        paging::Flags,
    };

    const CONFIG_SPACE_SIZE: usize = 256 * 1024 * 1024; // 256 MiB

    let pcie_info = PciConfigRegions::new(acpi).unwrap();
    for segment in pcie_info.list_all() {
        let flags = Flags {
            write: true,
            execute: false,
            cache: false,
            write_through: false,
            device: true,
        };

        let mut config_start = segment.base_address() as usize;
        let config_end = config_start + CONFIG_SPACE_SIZE;

        while config_start < config_end {
            let phy_addr = PhyAddr::new(config_start);
            let virt_addr = VirtAddr::new(config_start);

            if unsafe {
                page_table
                    .map_to(virt_addr, phy_addr, flags, page_allocator)
                    .is_err()
            } {
                log::error!("Failed to map the PCIe config space.");
                return;
            }

            config_start += PAGESIZE;
        }

        let base_address = segment.base_address();
        for bus in segment.buses() {
            scan_devices(
                dma_offset,
                bus,
                base_address as usize,
                page_table,
                page_allocator,
            );
        }
    }
}

pub fn init_with_addr<F, FA, PT, E>(
    dma_offset: usize,
    base_address: usize,
    page_table: &mut PT,
    page_allocator: &mut FA,
    starting_bus: u8,
) where
    F: Frame,
    FA: FrameAllocator<F, E>,
    PT: PageTable<F, FA, E>,
    E: Debug,
{
    for bus in (starting_bus as u32)..256 {
        scan_devices(
            dma_offset,
            bus as u8,
            base_address,
            page_table,
            page_allocator,
        );
    }
}

/// Scan and initialize the PICe devices
fn scan_devices<F, FA, PT, E>(
    dma_offset: usize,
    bus: u8,
    base_address: usize,
    page_table: &mut PT,
    page_allocator: &mut FA,
) where
    F: Frame,
    FA: FrameAllocator<F, E>,
    PT: PageTable<F, FA, E>,
    E: Debug,
{
    for dev in 0..(1 << 5) {
        for func in 0..(1 << 3) {
            let offset = (bus as usize) << 20 | dev << 15 | func << 12;
            let addr = base_address + offset;
            if let Ok(device) = PCIeInfo::from_addr(bus, addr) {
                let multiple_functions = device.multiple_functions;

                let _ = device.attach(dma_offset, page_table, page_allocator);

                if func == 0 && !multiple_functions {
                    break;
                }
            }
        }
    }
}

/// Information necessary for initializing the device
#[derive(Debug)]
pub struct PCIeInfo {
    pub(crate) addr: usize,
    bus: u8,
    id: u16,
    vendor: u16,
    revision_id: u8,
    device_name: Option<pcie_id::PCIeID>,
    multiple_functions: bool,
    pub(crate) header_type: u8,
    base_addresses: [BaseAddress; 6],
    msi: Option<msi::MSI>,
    msix: Option<msix::MSIX>,
}

impl fmt::Display for PCIeInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "id: {:#x}, vendor: {:#x}, header type: {:#x}",
            self.id, self.vendor, self.header_type
        )
    }
}

impl PCIeInfo {
    /// Get the information for PCIe device
    fn from_addr(bus: u8, addr: usize) -> Result<PCIeInfo, PCIeDeviceErr> {
        let ids = registers::DEVICE_VENDOR_ID.read(addr);
        let vendor = (ids & 0xffff) as u16;
        let id = (ids >> 16) as u16;
        let header_type = (registers::BIST_HEAD_LAT_CACH.read(addr) >> 16 & 0xff) as u8;
        let multiple_functions = header_type & 0x80 == 0x80;
        let header_type = header_type & 0x7f;

        let cls_rev_id = registers::CLASS_CODE_REVISION_ID.read(addr);
        let revision_id = (cls_rev_id & 0xff) as u8;

        if id == !0 || vendor == !0 {
            Err(PCIeDeviceErr::InitFailure)
        } else {
            Ok(PCIeInfo {
                addr,
                bus,
                id,
                vendor,
                revision_id,
                device_name: None,
                multiple_functions,
                header_type,
                base_addresses: array![_ => BaseAddress::None; 6],
                msi: None,
                msix: None,
            })
        }
    }

    pub fn get_id(&self) -> u16 {
        self.id
    }

    pub fn get_revision_id(&self) -> u8 {
        self.revision_id
    }

    pub fn set_revision_id(&mut self, revision_id: u8) {
        self.revision_id = revision_id;
    }

    pub fn get_msi_mut(&mut self) -> Option<&mut msi::MSI> {
        self.msi.as_mut()
    }

    pub fn get_msix_mut(&mut self) -> Option<&mut msix::MSIX> {
        self.msix.as_mut()
    }

    pub fn read_status_command(&self) -> registers::StatusCommand {
        registers::STATUS_COMMAND.read(self.addr)
    }

    pub fn write_status_command(&mut self, csr: registers::StatusCommand) {
        registers::STATUS_COMMAND.write(csr, self.addr);
    }

    pub fn read_config_space(&self, offset: usize) -> u32 {
        unsafe { read_volatile((self.addr + offset) as *const u32) }
    }

    pub(crate) fn read_capability(&mut self) {
        capability::read(self);
    }

    pub(crate) fn map_bar<F, FA, PT, E>(
        &mut self,
        page_table: &mut PT,
        page_allocator: &mut FA,
    ) -> Result<(), E>
    where
        F: Frame,
        FA: FrameAllocator<F, E>,
        PT: PageTable<F, FA, E>,
        E: Debug,
    {
        let num_reg = match self.header_type {
            registers::HEADER_TYPE_GENERAL_DEVICE => 6,
            registers::HEADER_TYPE_PCI_TO_PCI_BRIDGE
            | registers::HEADER_TYPE_PCI_TO_CARDBUS_BRIDGE => 2,
            _ => panic!("Unrecognized header type: {:#x}", self.header_type),
        };

        let mut csr = registers::STATUS_COMMAND.read(self.addr);

        // Disable the device
        csr.set(registers::StatusCommand::MEMORY_SPACE, false);
        csr.set(registers::StatusCommand::IO_SPACE, false);
        registers::STATUS_COMMAND.write(csr, self.addr);

        if self.header_type == registers::HEADER_TYPE_PCI_TO_CARDBUS_BRIDGE {
        } else {
            let mut i = 0;
            while i < num_reg {
                let bar = read_bar(self.addr + registers::BAR0 + i * 4);

                let is_64bit = bar.is_64bit_memory();
                self.base_addresses[i] = bar;

                if is_64bit {
                    i += 2;
                } else {
                    i += 1;
                }
            }
        }

        // Enable the device
        csr.set(registers::StatusCommand::MEMORY_SPACE, true);
        csr.set(registers::StatusCommand::IO_SPACE, true);
        registers::STATUS_COMMAND.write(csr, self.addr);

        // map MMIO regions
        for bar in self.base_addresses.iter() {
            if let BaseAddress::MMIO {
                addr,
                size,
                prefetchable,
                ..
            } = bar
            {
                if *size == 0 {
                    continue;
                }

                let flags = awkernel_lib::paging::Flags {
                    write: true,
                    execute: false,
                    cache: *prefetchable,
                    write_through: *prefetchable,
                    device: true,
                };

                let mut addr = *addr;
                let end = addr + *size;

                let mask = !(PAGESIZE - 1);
                while addr < end {
                    let phy_addr = awkernel_lib::addr::phy_addr::PhyAddr::new(addr & mask);
                    let virt_addr = awkernel_lib::addr::virt_addr::VirtAddr::new(addr & mask);

                    unsafe { page_table.map_to(virt_addr, phy_addr, flags, page_allocator)? };

                    addr += PAGESIZE;
                }
            }
        }

        Ok(())
    }

    pub fn get_bar(&self, i: usize) -> Option<BaseAddress> {
        self.base_addresses.get(i).cloned()
    }

    /// Initialize the PCIe device based on the information
    fn attach<F, FA, PT, E>(
        self,
        dma_offset: usize,
        page_table: &mut PT,
        page_allocator: &mut FA,
    ) -> Result<(), PCIeDeviceErr>
    where
        F: Frame,
        FA: FrameAllocator<F, E>,
        PT: PageTable<F, FA, E>,
        E: Debug,
    {
        match self.vendor {
            pcie_id::INTEL_VENDOR_ID => {
                if crate::net::e1000::match_device(self.vendor, self.id) {
                    return crate::net::e1000::attach(self, dma_offset, page_table, page_allocator);
                }
            }
            _ => (),
        }

        Err(PCIeDeviceErr::UnRecognizedDevice {
            bus: self.bus,
            device: self.id,
            vendor: self.vendor,
        })
    }

    pub fn disable_legacy_interrupt(&mut self) {
        registers::STATUS_COMMAND.setbits(registers::StatusCommand::INTERRUPT_DISABLE, self.addr);
    }
}

pub trait PCIeDevice {
    /// Each PCIe device has a register space,
    const REG_SPACE_SIZE: u64;

    /// Initialize the device hardware.
    fn init(&mut self) -> Result<(), PCIeDeviceErr>;
}

/// Read the base address of `addr`.
fn read_bar(addr: usize) -> BaseAddress {
    let bar = unsafe { read_volatile::<u32>(addr as *const u32) };

    const BAR_IO: u32 = 0b1;
    const BAR_TYPE_MASK: u32 = 0b110;
    const BAR_TYPE_32: u32 = 0b000;
    const BAR_TYPE_64: u32 = 0b100;
    const BAR_PREFETCHABLE: u32 = 0b1000;
    const BAR_IO_ADDR_MASK: u32 = !0b11;
    const BAR_MEM_ADDR_MASK: u32 = !0b1111;

    if (bar & BAR_IO) == 1 {
        // I/O space
        BaseAddress::IO(bar & BAR_IO_ADDR_MASK)
    } else {
        // Memory space

        let bar_type = bar & BAR_TYPE_MASK;
        if bar_type == BAR_TYPE_32 {
            let size = unsafe {
                write_volatile(addr as *mut u32, !0);
                let size = read_volatile::<u32>(addr as *const u32);
                write_volatile(addr as *mut u32, bar);
                (!size).wrapping_add(1) as usize
            };

            if size == 0 {
                BaseAddress::None
            } else {
                BaseAddress::MMIO {
                    addr: (bar & BAR_MEM_ADDR_MASK) as usize,
                    size,
                    address_type: AddressType::T32B,
                    prefetchable: (bar & BAR_PREFETCHABLE) > 1,
                }
            }
        } else if bar_type == BAR_TYPE_64 {
            let high_addr = addr + 4;
            let high_bar = unsafe { read_volatile::<u32>(high_addr as *const u32) };

            let size = unsafe {
                let high_bar = read_volatile::<u32>(high_addr as *const u32);

                write_volatile(addr as *mut u32, !0);
                write_volatile(high_addr as *mut u32, !0);

                let low_size = read_volatile::<u32>(addr as *const u32);
                let high_size = read_volatile::<u32>(high_addr as *const u32);

                write_volatile(addr as *mut u32, bar);
                write_volatile(high_addr as *mut u32, high_bar);

                (!((high_size as u64) << 32 | (low_size as u64)) + 1) as usize
            };

            let addr = (((high_bar as u64) << 32) | (bar & BAR_MEM_ADDR_MASK) as u64) as usize;

            if size == 0 {
                BaseAddress::None
            } else {
                BaseAddress::MMIO {
                    addr,
                    size,
                    address_type: AddressType::T64B,
                    prefetchable: (bar & BAR_PREFETCHABLE) > 1,
                }
            }
        } else {
            BaseAddress::None
        }
    }
}
