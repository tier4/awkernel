use alloc::{borrow::Cow, format, string::String};
use array_macro::array;
use awkernel_lib::{
    addr::{virt_addr::VirtAddr, Addr},
    paging::{self, MapError, PAGESIZE},
};
use core::{
    fmt::{self, Debug},
    ptr::{read_volatile, write_volatile},
};

#[cfg(feature = "x86")]
use awkernel_lib::arch::x86_64::acpi::AcpiMapper;

#[cfg(feature = "x86")]
use acpi::{AcpiTables, PciConfigRegions};

mod capability;
pub mod net;
pub mod pcie_class;
pub mod pcie_id;

#[derive(Debug, Clone)]
pub enum ConfigSpace {
    IO(u32),
    MMIO(VirtAddr),
}

impl ConfigSpace {
    #[cfg(feature = "x86")]
    fn new_io(bus_number: u8, device_number: u8, function_number: u8) -> Self {
        let base = 0x80000000
            | (bus_number as u32) << 16
            | (device_number as u32) << 11
            | (function_number as u32) << 8;
        Self::IO(base)
    }

    fn new_memory(base: VirtAddr) -> Self {
        Self::MMIO(base)
    }

    fn read_u16(&self, offset: usize) -> u16 {
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
            Self::MMIO(base) => {
                let addr = *base + offset;
                unsafe { read_volatile(addr.as_ptr()) }
            }
        }
    }

    fn read_u32(&self, offset: usize) -> u32 {
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
            Self::MMIO(base) => {
                let addr = *base + offset;
                unsafe { read_volatile(addr.as_ptr()) }
            }
        }
    }

    fn write_u32(&self, data: u32, offset: usize) {
        match self {
            #[allow(unused_variables)]
            Self::IO(base) => {
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
            Self::MMIO(base) => {
                let addr = *base + offset;
                unsafe { write_volatile(addr.as_mut_ptr(), data) }
            }
        }
    }
}

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

    pub fn read16(&self, offset: usize) -> Option<u16> {
        assert_eq!(offset & 1, 0);
        match self {
            #[cfg(feature = "x86")]
            BaseAddress::IO(addr) => {
                let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                let mut port2 = x86_64::instructions::port::PortReadOnly::new(0xCFC);

                let addr = *addr | ((offset as u32) & 0xfc);
                let val = unsafe {
                    port1.write(addr);
                    let tmp: u32 = port2.read();
                    (tmp >> (((offset as u32 & 2) * 8) & 0xffff)) as u16
                };

                Some(val)
            }
            BaseAddress::MMIO { addr, size, .. } => {
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
            BaseAddress::IO(addr) => unsafe {
                let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                let mut port2 = x86_64::instructions::port::PortReadOnly::new(0xCFC);
                port1.write(*addr + ((offset as u32) & 0xfc));
                Some(port2.read())
            },
            BaseAddress::MMIO { addr, size, .. } => {
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
            BaseAddress::IO(addr) => unsafe {
                let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                let mut port2 = x86_64::instructions::port::Port::new(0xCFC);

                let addr = *addr + ((offset as u32) & 0xfc);
                port1.write(addr);
                let reg: u32 = port2.read();

                let mask = !(0xff << ((offset & 3) * 8));

                port1.write(addr);
                port2.write((reg & mask) | (val as u32) << ((offset & 3) * 8));
            },
            BaseAddress::MMIO { addr, size, .. } => unsafe {
                let dst = *addr + offset;
                assert!(dst + 4 < *addr + *size);
                write_volatile(dst as *mut u8, val);
            },
            _ => (),
        }
    }

    pub fn write16(&mut self, offset: usize, val: u16) {
        assert_eq!(offset & 1, 0);
        match self {
            #[cfg(feature = "x86")]
            BaseAddress::IO(addr) => unsafe {
                let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                let mut port2 = x86_64::instructions::port::Port::new(0xCFC);

                let addr = *addr + ((offset as u32) & 0xfc);
                port1.write(addr);
                let reg: u32 = port2.read();

                let mask = !(0xffff << ((offset & 2) * 8));

                port1.write(addr);
                port2.write((reg & mask) | (val as u32) << ((offset & 2) * 8));
            },
            BaseAddress::MMIO { addr, size, .. } => unsafe {
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
            BaseAddress::IO(addr) => unsafe {
                let mut port1 = x86_64::instructions::port::PortWriteOnly::new(0xCF8);
                let mut port2 = x86_64::instructions::port::PortWriteOnly::new(0xCFC);
                port1.write(*addr + ((offset as u32) & 0xfc));
                port2.write(val);
            },
            BaseAddress::MMIO { addr, size, .. } => unsafe {
                let dst = *addr + offset;
                assert!(dst + 4 < *addr + *size);
                write_volatile(dst as *mut u32, val);
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

#[derive(Debug, Clone)]
pub enum PCIeDeviceErr {
    InitFailure,
    ReadFailure,
    PageTableFailure,
    CommandFailure,
    UnRecognizedDevice { bus: u8, device: u16, vendor: u16 },
    InvalidClass,
    Interrupt,
    NotImplemented,
    BARFailure,
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
            Self::InvalidClass => {
                write!(f, "Invalid PCIe class.")
            }
            Self::NotImplemented => {
                write!(f, "Not implemented.")
            }
            Self::ReadFailure => {
                write!(f, "Failed to read the device register.")
            }
            Self::Interrupt => {
                write!(f, "Failed to initialize interrupt.")
            }
            Self::CommandFailure => {
                write!(f, "Failed to execute the command.")
            }
            Self::BARFailure => {
                write!(f, "Failed to read the base address register.")
            }
        }
    }
}

pub(crate) mod registers {
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

    // Type 0 and 1
    pub const DEVICE_VENDOR_ID: usize = 0x00;
    pub const STATUS_COMMAND: usize = 0x04;
    pub const CLASS_CODE_REVISION_ID: usize = 0x08;
    pub const BIST_HEAD_LAT_CACH: usize = 0x0c;

    pub const CAPABILITY_POINTER: usize = 0x34;
    pub const INTERRUPT_LINE: usize = 0x3c;

    // Type 1 (PCI-to-PCI bridge)
    pub const _SECONDARY_LATENCY_TIMER_BUS_NUMBER: usize = 0x18;

    // Capability
    pub const MESSAGE_CONTROL_NEXT_PTR_CAP_ID: usize = 0x00;

    pub const BAR0: usize = 0x10;
}

/// Initialize the PCIe with ACPI.
#[cfg(feature = "x86")]
pub fn init_with_acpi(acpi: &AcpiTables<AcpiMapper>) -> Result<(), PCIeDeviceErr> {
    use awkernel_lib::{addr::phy_addr::PhyAddr, paging::Flags};

    const CONFIG_SPACE_SIZE: usize = 256 * 1024 * 1024; // 256 MiB

    let pcie_info = PciConfigRegions::new(acpi).or(Err(PCIeDeviceErr::InitFailure))?;
    for segment in pcie_info.iter() {
        let flags = Flags {
            write: true,
            execute: false,
            cache: false,
            write_through: false,
            device: true,
        };

        let mut config_start = segment.physical_address;
        let config_end = config_start + CONFIG_SPACE_SIZE;

        while config_start < config_end {
            let phy_addr = PhyAddr::new(config_start);
            let virt_addr = VirtAddr::new(config_start);

            unsafe {
                paging::map(virt_addr, phy_addr, flags).or(Err(PCIeDeviceErr::PageTableFailure))?
            };

            config_start += PAGESIZE;
        }

        let base_address = segment.physical_address;

        for bus in segment.bus_range {
            // Config space must be mapped to the same address space.
            scan_devices(segment.segment_group, bus, VirtAddr::new(base_address));
        }
    }

    Ok(())
}

/// Initialize the PCIe with IO port.
#[cfg(feature = "x86")]
pub fn init_with_io() {
    for bus in 0..=255 {
        for device in 0..32 {
            for func_num in 0..8 {
                if let Ok(info) = PCIeInfo::from_io(bus, device, func_num) {
                    let multiple_functions = info.multiple_functions;

                    let _ = info.attach();

                    if func_num == 0 && !multiple_functions {
                        break;
                    }
                } else if func_num == 0 {
                    break;
                }
            }
        }
    }
}

pub fn init_with_addr(segment_group: u16, base_address: VirtAddr, starting_bus: u8) {
    for bus in (starting_bus as u32)..256 {
        scan_devices(segment_group, bus as u8, base_address);
    }
}

/// Scan and initialize the PICe devices
fn scan_devices(segment_group: u16, bus: u8, base_address: VirtAddr) {
    for dev in 0..(1 << 5) {
        for func in 0..(1 << 3) {
            let offset = (bus as usize) << 20 | dev << 15 | func << 12;
            let addr = base_address + offset;
            if let Ok(device) = PCIeInfo::from_addr(segment_group, bus, dev as u8, func as u8, addr)
            {
                let multiple_functions = device.multiple_functions;

                let _ = device.attach();

                if func == 0 && !multiple_functions {
                    break;
                }
            } else if func == 0 {
                break;
            }
        }
    }
}

/// Information necessary for initializing the device
#[derive(Debug)]
pub struct PCIeInfo {
    pub(crate) config_space: ConfigSpace,
    segment_group: u16,
    bus_number: u8,
    device_number: u8,
    function_number: u8,
    id: u16,
    vendor: u16,
    revision_id: u8,
    interrupt_pin: u8,
    pcie_class: pcie_class::PCIeClass,
    device_name: Option<pcie_id::PCIeID>,
    multiple_functions: bool,
    pub(crate) header_type: u8,
    base_addresses: [BaseAddress; 6],
    msi: Option<capability::msi::Msi>,
    msix: Option<capability::msix::Msix>,
    pcie_cap: Option<capability::pcie_cap::PCIeCap>,
}

impl fmt::Display for PCIeInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{:04x}:{:02x}:{:02x}.{:01x}, Device ID = {:04x}, PCIe Class = {:?}",
            self.segment_group,
            self.bus_number,
            self.device_number,
            self.function_number,
            self.id,
            self.pcie_class,
        )
    }
}

impl PCIeInfo {
    #[cfg(feature = "x86")]
    fn from_io(
        bus_number: u8,
        device_number: u8,
        function_number: u8,
    ) -> Result<PCIeInfo, PCIeDeviceErr> {
        let config_space = ConfigSpace::new_io(bus_number, device_number, function_number);
        Self::new(config_space, 0, bus_number, device_number, function_number)
    }

    /// Get the information for PCIe device
    fn from_addr(
        segment_group: u16,
        bus_number: u8,
        device_number: u8,
        function_number: u8,
        addr: VirtAddr,
    ) -> Result<PCIeInfo, PCIeDeviceErr> {
        let config_space = ConfigSpace::new_memory(addr);
        Self::new(
            config_space,
            segment_group,
            bus_number,
            device_number,
            function_number,
        )
    }

    /// Get the information for PCIe device
    fn new(
        config_space: ConfigSpace,
        segment_group: u16,
        bus_number: u8,
        device_number: u8,
        function_number: u8,
    ) -> Result<PCIeInfo, PCIeDeviceErr> {
        let ids = config_space.read_u32(registers::DEVICE_VENDOR_ID);

        let vendor = (ids & 0xffff) as u16;
        let id = (ids >> 16) as u16;

        if id == !0 || vendor == !0 {
            return Err(PCIeDeviceErr::InitFailure);
        }

        let header_type = (config_space.read_u32(registers::BIST_HEAD_LAT_CACH) >> 16 & 0xff) as u8;
        let multiple_functions = header_type & 0x80 == 0x80;
        let header_type = header_type & 0x7f;

        let cls_rev_id = config_space.read_u32(registers::CLASS_CODE_REVISION_ID);
        let revision_id = (cls_rev_id & 0xff) as u8;

        let pcie_class = pcie_class::PCIeClass::from_u8(
            (cls_rev_id >> 24) as u8,
            ((cls_rev_id >> 16) & 0xff) as u8,
        )
        .ok_or(PCIeDeviceErr::InvalidClass)?;

        let interrupt_pin_line = config_space.read_u16(registers::INTERRUPT_LINE);

        let result = PCIeInfo {
            config_space,
            segment_group,
            bus_number,
            device_number,
            function_number,
            id,
            vendor,
            revision_id,
            interrupt_pin: (interrupt_pin_line >> 8) as u8,
            pcie_class,
            device_name: None,
            multiple_functions,
            header_type,
            base_addresses: array![_ => BaseAddress::None; 6],
            msi: None,
            msix: None,
            pcie_cap: None,
        };

        Ok(result)
    }

    /// Get the information for PCIe device as BFD format.
    pub fn get_bfd(&self) -> String {
        format!(
            "{:04x}:{:02x}:{:02x}.{:01x}",
            self.segment_group, self.bus_number, self.device_number, self.function_number
        )
    }

    pub fn get_device_name(&self) -> Option<pcie_id::PCIeID> {
        self.device_name
    }

    pub fn get_class(&self) -> pcie_class::PCIeClass {
        self.pcie_class
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

    pub fn get_msi_mut(&mut self) -> Option<&mut capability::msi::Msi> {
        self.msi.as_mut()
    }

    pub fn get_msix_mut(&mut self) -> Option<&mut capability::msix::Msix> {
        self.msix.as_mut()
    }

    pub fn get_pcie_cap_mut(&mut self) -> Option<&mut capability::pcie_cap::PCIeCap> {
        self.pcie_cap.as_mut()
    }

    pub fn read_status_command(&self) -> registers::StatusCommand {
        let val = self.config_space.read_u32(registers::STATUS_COMMAND);
        registers::StatusCommand::from_bits_truncate(val)
    }

    pub fn write_status_command(&mut self, csr: registers::StatusCommand) {
        self.config_space
            .write_u32(csr.bits(), registers::STATUS_COMMAND);
    }

    pub fn get_segment_group(&self) -> u16 {
        self.segment_group
    }

    pub fn get_interrupt_line(&self) -> u8 {
        (self.config_space.read_u16(registers::INTERRUPT_LINE) & 0xff) as u8
    }

    pub fn set_interrupt_line(&mut self, irq: u8) {
        let reg = self.config_space.read_u32(registers::INTERRUPT_LINE);
        self.config_space
            .write_u32((reg & !0xff) | irq as u32, registers::INTERRUPT_LINE);
    }

    pub fn get_interrupt_pin(&self) -> u8 {
        self.interrupt_pin
    }

    pub(crate) fn read_capability(&mut self) {
        capability::read(self);
    }

    pub(crate) fn map_bar(&mut self) -> Result<(), MapError> {
        let num_reg = match self.header_type {
            registers::HEADER_TYPE_GENERAL_DEVICE => 6,
            registers::HEADER_TYPE_PCI_TO_PCI_BRIDGE
            | registers::HEADER_TYPE_PCI_TO_CARDBUS_BRIDGE => 2,
            _ => panic!("Unrecognized header type: {:#x}", self.header_type),
        };

        let mut csr = self.read_status_command();

        // Disable the device
        csr.set(registers::StatusCommand::MEMORY_SPACE, false);
        csr.set(registers::StatusCommand::IO_SPACE, false);
        self.write_status_command(csr);

        if self.header_type == registers::HEADER_TYPE_PCI_TO_CARDBUS_BRIDGE {
        } else {
            let mut i = 0;
            while i < num_reg {
                let bar = read_bar(&self.config_space, registers::BAR0 + i * 4);

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
        self.write_status_command(csr);

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

                    unsafe {
                        paging::map(virt_addr, phy_addr, flags)?;
                    }

                    addr += PAGESIZE;
                }
            }
        }

        Ok(())
    }

    #[inline(always)]
    pub fn get_bar(&self, i: usize) -> Option<BaseAddress> {
        self.base_addresses.get(i).cloned()
    }

    /// Initialize the PCIe device based on the information
    fn attach(self) -> Result<(), PCIeDeviceErr> {
        #[allow(clippy::single_match)] // TODO: To be removed
        match self.vendor {
            pcie_id::INTEL_VENDOR_ID =>
            {
                #[cfg(feature = "igb")]
                if net::igb::match_device(self.vendor, self.id) {
                    return net::igb::attach(self);
                }
            }
            _ => (),
        }

        Err(PCIeDeviceErr::UnRecognizedDevice {
            bus: self.bus_number,
            device: self.id,
            vendor: self.vendor,
        })
    }

    pub fn disable_legacy_interrupt(&mut self) {
        let reg = self.read_status_command();
        self.write_status_command(reg | registers::StatusCommand::INTERRUPT_DISABLE);
    }

    pub fn enable_legacy_interrupt(&mut self) {
        let reg = self.read_status_command();
        self.write_status_command(reg & !registers::StatusCommand::INTERRUPT_DISABLE);
    }
}

pub trait PCIeDevice {
    fn device_name(&self) -> Cow<'static, str>;
}

const BAR_IO: u32 = 0b1;
const BAR_TYPE_MASK: u32 = 0b110;
const BAR_TYPE_32: u32 = 0b000;
const BAR_TYPE_64: u32 = 0b100;
const BAR_PREFETCHABLE: u32 = 0b1000;
const BAR_IO_ADDR_MASK: u32 = !0b11;
const BAR_MEM_ADDR_MASK: u32 = !0b1111;

/// Read the base address of `addr`.
fn read_bar(config_space: &ConfigSpace, offset: usize) -> BaseAddress {
    let bar = config_space.read_u32(offset);

    if (bar & BAR_IO) == 1 {
        // I/O space
        BaseAddress::IO(bar & BAR_IO_ADDR_MASK)
    } else {
        // Memory space

        let bar_type = bar & BAR_TYPE_MASK;
        if bar_type == BAR_TYPE_32 {
            let size = {
                config_space.write_u32(!0, offset);
                let size = config_space.read_u32(offset);
                config_space.write_u32(bar, offset);
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
            let high_offset = offset + 4;
            let high_bar = config_space.read_u32(high_offset);

            let size = {
                let high_bar = config_space.read_u32(high_offset);

                config_space.write_u32(!0, offset);
                config_space.write_u32(!0, high_offset);

                let low_size = config_space.read_u32(offset);
                let high_size = config_space.read_u32(high_offset);

                config_space.write_u32(bar, offset);
                config_space.write_u32(high_bar, high_offset);

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
