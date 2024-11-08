use alloc::{
    borrow::Cow,
    boxed::Box,
    collections::{BTreeMap, BTreeSet},
    format,
    string::String,
    sync::Arc,
    vec::Vec,
};
use array_macro::array;
use awkernel_lib::{
    addr::virt_addr::VirtAddr,
    paging::{self, MapError, PAGESIZE},
    sync::{mcs::MCSNode, mutex::Mutex},
};
use core::fmt::{self, Debug};

#[cfg(feature = "x86")]
use awkernel_lib::arch::x86_64::acpi::AcpiMapper;

#[cfg(feature = "x86")]
use acpi::{AcpiTables, PciConfigRegions};

use crate::pcie::pcie_class::{PCIeBridgeSubClass, PCIeClass};

use self::{
    base_address::{AddressType, BaseAddress},
    config_space::ConfigSpace,
    pcie_device_tree::PCIeRange,
};

pub mod pcie_device_tree;

mod base_address;
pub mod broadcom;
mod capability;
mod config_space;
pub mod intel;
pub mod pcie_class;
pub mod pcie_id;
pub mod raspi;

static PCIE_TREES: Mutex<BTreeMap<u16, Arc<PCIeTree>>> = Mutex::new(BTreeMap::new());

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
    RevisionIDMismatch,
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
            Self::RevisionIDMismatch => {
                write!(f, "Revision ID mismatch.")
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

    // Type 1 (Bridge)
    pub const SECONDARY_LATENCY_TIMER_BUS_NUMBER: usize = 0x18;

    // Capability
    pub const MESSAGE_CONTROL_NEXT_PTR_CAP_ID: usize = 0x00;

    pub const BAR0: usize = 0x10;
    pub const BAR1: usize = 0x14;
}

/// Initialize the PCIe with ACPI.
#[cfg(feature = "x86")]
pub fn init_with_acpi(
    acpi: &AcpiTables<AcpiMapper>,
    max_bus: u8,
    max_device: u8,
) -> Result<(), PCIeDeviceErr> {
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
        init_with_addr(
            segment.segment_group,
            VirtAddr::new(base_address),
            None,
            max_bus,
            max_device,
        );
    }

    Ok(())
}

/// Initialize the PCIe with IO port.
#[cfg(feature = "x86")]
pub fn init_with_io(max_bus: u8, max_device: u8) {
    init(0, None, PCIeInfo::from_io, None, max_bus, max_device);
}

/// Structure representing a PCIe device after it has been attached.
struct UnknownDevice {
    segment_group: u16,
    bus_number: u8,
    device_number: u8,
    function_number: u8,
    vendor: u16,
    id: u16,
    pcie_class: pcie_class::PCIeClass,
}

impl PCIeDevice for UnknownDevice {
    fn device_name(&self) -> Cow<'static, str> {
        let bfd = format!(
            "{:04x}:{:02x}:{:02x}.{:01x}",
            self.segment_group, self.bus_number, self.device_number, self.function_number
        );

        let name = format!(
            "{bfd}: Vendor ID = {:04x}, Device ID = {:04x}, PCIe Class = {:?}",
            self.vendor, self.id, self.pcie_class,
        );
        name.into()
    }

    fn children(&self) -> Option<&Vec<ChildDevice>> {
        // UnknownDevice represents a terminal device and always returns None.
        None
    }
}

struct PCIeTree {
    // - Key: Bus number
    // - Value: PCIeBus
    tree: BTreeMap<u8, Box<PCIeBus>>,
}

impl PCIeTree {
    fn update_bridge_info(
        &mut self,
        bridge_bus_number: u8,
        bridge_device_number: u8,
        bridge_function_number: u8,
    ) {
        for (_, bus) in self.tree.iter_mut() {
            bus.update_bridge_info(
                bridge_bus_number,
                bridge_device_number,
                bridge_function_number,
            );
        }
    }

    fn attach(&mut self) {
        for (_, bus) in self.tree.iter_mut() {
            bus.attach();
        }
    }

    fn init_base_address(&mut self, ranges: &mut [PCIeRange]) {
        for (_, bus) in self.tree.iter_mut() {
            bus.init_base_address(ranges);
        }
    }
}

impl fmt::Display for PCIeTree {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (_, bus) in self.tree.iter() {
            if !bus.devices.is_empty() {
                write!(f, "{}", bus)?;
            }
        }

        Ok(())
    }
}

pub enum ChildDevice {
    Bus(Box<PCIeBus>),
    Attached(Arc<dyn PCIeDevice + Sync + Send>),
    Attaching,
    Unattached(Box<PCIeInfo>),
}

impl ChildDevice {
    fn attach(&mut self) {
        let attaching = ChildDevice::Attaching;

        if let ChildDevice::Bus(bus) = self {
            bus.attach();
            return;
        };

        // Return if the device has already been attached.
        let ChildDevice::Unattached(info) = core::mem::replace(self, attaching) else {
            return;
        };

        if let Ok(device) = info.attach() {
            *self = ChildDevice::Attached(device);
        }
    }

    fn init_base_address(&mut self, ranges: &mut [PCIeRange]) {
        match self {
            ChildDevice::Bus(bus) => {
                if let Some(info) = bus.info.as_mut() {
                    info.init_base_address(ranges);
                }
            }
            ChildDevice::Unattached(info) => {
                info.init_base_address(ranges);
            }
            _ => (),
        }
    }
}

pub struct PCIeBus {
    segment_group: u16,
    bus_number: u8,
    base_address: Option<VirtAddr>,
    info: Option<PCIeInfo>,
    devices: Vec<ChildDevice>,
}

impl PCIeBus {
    fn new(
        segment_group: u16,
        bus_number: u8,
        base_address: Option<VirtAddr>,
        info: Option<PCIeInfo>,
    ) -> Self {
        PCIeBus {
            segment_group,
            bus_number,
            base_address,
            info,
            devices: Vec::new(),
        }
    }

    fn update_bridge_info(
        &mut self,
        mut bridge_bus_number: u8,
        mut bridge_device_number: u8,
        mut bridge_function_number: u8,
    ) {
        if let Some(info) = self.info.as_mut() {
            info.bridge_bus_number = Some(bridge_bus_number);
            info.bridge_device_number = Some(bridge_device_number);
            info.bridge_function_number = Some(bridge_function_number);

            bridge_bus_number = info.bus_number;
            bridge_device_number = info.device_number;
            bridge_function_number = info.function_number;
        }

        for device in self.devices.iter_mut() {
            match device {
                ChildDevice::Bus(bus) => {
                    bus.update_bridge_info(
                        bridge_bus_number,
                        bridge_device_number,
                        bridge_function_number,
                    );
                }
                ChildDevice::Unattached(info) => {
                    info.bridge_bus_number = Some(bridge_bus_number);
                    info.bridge_device_number = Some(bridge_device_number);
                    info.bridge_function_number = Some(bridge_function_number);
                }
                _ => (),
            }
        }
    }

    fn attach(&mut self) {
        for device in self.devices.iter_mut() {
            device.attach();
        }
    }

    fn init_base_address(&mut self, ranges: &mut [PCIeRange]) {
        for device in self.devices.iter_mut() {
            device.init_base_address(ranges);
        }
    }
}

impl PCIeDevice for PCIeBus {
    fn device_name(&self) -> Cow<'static, str> {
        if let Some(info) = self.info.as_ref() {
            let bfd = info.get_bfd();
            let name = format!("{bfd}: Bridge, Bus #{:02x}", self.bus_number);
            name.into()
        } else {
            let name = format!("Bus #{:02x}", self.bus_number);
            name.into()
        }
    }

    fn children(&self) -> Option<&Vec<ChildDevice>> {
        Some(&self.devices)
    }
}

impl fmt::Display for PCIeBus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        print_pcie_devices(self, f, 0)
    }
}

fn print_pcie_devices(device: &dyn PCIeDevice, f: &mut fmt::Formatter, indent: u8) -> fmt::Result {
    let indent_str = " ".repeat(indent as usize * 4);
    write!(f, "{}{}\r\n", indent_str, device.device_name())?;

    if let Some(children) = device.children() {
        for child in children.iter() {
            match child {
                ChildDevice::Attached(child) => {
                    print_pcie_devices(child.as_ref(), f, indent + 1)?;
                }
                ChildDevice::Unattached(info) => {
                    let name = format!(
                        "{}: Vendor ID = {:04x}, Device ID = {:04x}, PCIe Class = {:?}, bridge = {:?}-{:?}-{:?}",
                        info.get_bfd(),
                        info.vendor,
                        info.id,
                        info.pcie_class,
                        info.bridge_bus_number,
                        info.bridge_device_number,
                        info.bridge_function_number,
                    );

                    let indent_str = " ".repeat((indent as usize + 1) * 4);
                    write!(f, "{}{}\r\n", indent_str, name)?;
                }
                ChildDevice::Bus(bus) => {
                    print_pcie_devices(bus.as_ref(), f, indent + 1)?;
                }
                _ => (),
            }
        }
    }

    Ok(())
}

/// Scan for devices on the physical PCIe bus.
#[inline]
fn check_bus<F>(
    bus: &mut PCIeBus,
    bus_tree: &mut PCIeTree,
    visited: &mut BTreeSet<u8>,
    f: &F,
    max_device: u8,
) where
    F: Fn(u16, u8, u8, u8, VirtAddr) -> Result<PCIeInfo, PCIeDeviceErr>,
{
    for device in 0..max_device {
        check_device(bus, device, bus_tree, visited, f, max_device);
    }
}

#[inline]
fn check_device<F>(
    bus: &mut PCIeBus,
    device: u8,
    bus_tree: &mut PCIeTree,
    visited: &mut BTreeSet<u8>,
    f: &F,
    max_device: u8,
) where
    F: Fn(u16, u8, u8, u8, VirtAddr) -> Result<PCIeInfo, PCIeDeviceErr>,
{
    for function in 0..8 {
        check_function(bus, device, function, bus_tree, visited, f, max_device);
    }
}

fn check_function<F>(
    bus: &mut PCIeBus,
    device: u8,
    function: u8,
    bus_tree: &mut PCIeTree,
    visited: &mut BTreeSet<u8>,
    f: &F,
    max_device: u8,
) -> bool
where
    F: Fn(u16, u8, u8, u8, VirtAddr) -> Result<PCIeInfo, PCIeDeviceErr>,
{
    let offset =
        (bus.bus_number as usize) << 20 | (device as usize) << 15 | (function as usize) << 12;

    let addr = if let Some(base_address) = bus.base_address {
        base_address + offset
    } else {
        VirtAddr::new(0)
    };

    if let Ok(info) = f(bus.segment_group, bus.bus_number, device, function, addr) {
        if matches!(
            info.pcie_class,
            PCIeClass::BridgeDevice(PCIeBridgeSubClass::PCItoPCI)
        ) {
            let secondary_bus = info.get_secondary_bus().unwrap();

            if secondary_bus < bus.bus_number {
                // If the secondary bus number is less than the current bus number,
                // it means that the bus has already been visited.
                if let Some(grandchild) = bus_tree.tree.remove(&secondary_bus) {
                    let mut bus_child = PCIeBus::new(
                        bus.segment_group,
                        secondary_bus,
                        bus.base_address,
                        Some(info),
                    );
                    bus_child.devices.push(ChildDevice::Bus(grandchild));
                    bus.devices.push(ChildDevice::Bus(Box::new(bus_child)));
                }
            } else if secondary_bus == bus.bus_number {
                log::warn!("PCIe: Secondary bus number is same as the current bus number.");
            } else if !visited.contains(&secondary_bus) {
                // If the secondary bus number is greater than the current bus number,
                // it means that the bus may has not been visited yet.
                let mut bus_child = PCIeBus::new(
                    bus.segment_group,
                    secondary_bus,
                    bus.base_address,
                    Some(info),
                );

                // Recursively check the bus
                visited.insert(secondary_bus);

                check_bus(&mut bus_child, bus_tree, visited, f, max_device);

                bus.devices.push(ChildDevice::Bus(Box::new(bus_child)));
            }
        } else {
            bus.devices.push(ChildDevice::Unattached(Box::new(info)));
        }

        true
    } else {
        false
    }
}

/// If `ranges` is not None, the base address registers of the device will be initialized
/// by using `ranges`.
pub fn init_with_addr(
    segment_group: u16,
    base_address: VirtAddr,
    ranges: Option<&mut [PCIeRange]>,
    max_bus: u8,
    max_device: u8,
) {
    init(
        segment_group,
        Some(base_address),
        PCIeInfo::from_addr,
        ranges,
        max_bus,
        max_device,
    );
}

fn init<F>(
    segment_group: u16,
    base_address: Option<VirtAddr>,
    f: F,
    ranges: Option<&mut [PCIeRange]>,
    max_bus: u8,
    mut max_device: u8,
) where
    F: Fn(u16, u8, u8, u8, VirtAddr) -> Result<PCIeInfo, PCIeDeviceErr>,
{
    if max_device > 32 {
        max_device = 32;
    }

    let mut visited = BTreeSet::new();

    let mut bus_tree = PCIeTree {
        tree: BTreeMap::new(),
    };

    let mut host_bridge_bus = 0;

    for bus_number in 0..=max_bus {
        if visited.contains(&bus_number) {
            continue;
        }

        let offset = (bus_number as usize) << 20;

        let addr = if let Some(base_address) = base_address {
            base_address + offset
        } else {
            VirtAddr::new(0)
        };

        // Search for the host bridge.
        if let Ok(info) = f(segment_group, bus_number, 0, 0, addr) {
            if info.pcie_class == PCIeClass::BridgeDevice(PCIeBridgeSubClass::HostBridge) {
                host_bridge_bus = bus_number;
            }
        } else {
            continue;
        };

        let mut bus = PCIeBus::new(segment_group, bus_number, base_address, None);

        visited.insert(bus_number);

        check_bus(&mut bus, &mut bus_tree, &mut visited, &f, max_device);

        bus_tree.tree.insert(bus_number, Box::new(bus));
    }

    bus_tree.update_bridge_info(host_bridge_bus, 0, 0);

    if let Some(ranges) = ranges {
        // 'ranges' is a property of the PCIe node in the device tree.
        // This property contains information for mapping the address space of a PCIe device to the address space of the host system.
        bus_tree.init_base_address(ranges);
    }

    bus_tree.attach();

    log::info!("PCIe: segment_group = {segment_group:04x}\r\n{}", bus_tree);

    let mut node = MCSNode::new();
    let mut pcie_trees = PCIE_TREES.lock(&mut node);
    pcie_trees.insert(segment_group, Arc::new(bus_tree));
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
    pub(crate) header_type: u8,
    base_addresses: [BaseAddress; 6],
    msi: Option<capability::msi::Msi>,
    msix: Option<capability::msix::Msix>,
    pcie_cap: Option<capability::pcie_cap::PCIeCap>,

    // The bridge having this device.
    bridge_bus_number: Option<u8>,
    bridge_device_number: Option<u8>,
    bridge_function_number: Option<u8>,
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
        _get_segment_group: u16,
        bus_number: u8,
        device_number: u8,
        function_number: u8,
        _addr: VirtAddr,
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
        let header_type = header_type & 0x7f;

        let cls_rev_id = config_space.read_u32(registers::CLASS_CODE_REVISION_ID);
        let revision_id = (cls_rev_id & 0xff) as u8;

        let pcie_class = pcie_class::PCIeClass::from_u8(
            (cls_rev_id >> 24) as u8,
            ((cls_rev_id >> 16) & 0xff) as u8,
        )
        .ok_or(PCIeDeviceErr::InvalidClass)?;

        let interrupt_pin_line = config_space.read_u16(registers::INTERRUPT_LINE);

        let mut result = PCIeInfo {
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
            header_type,
            base_addresses: array![_ => BaseAddress::None; 6],
            msi: None,
            msix: None,
            pcie_cap: None,
            bridge_bus_number: None,
            bridge_device_number: None,
            bridge_function_number: None,
        };

        result.read_bar()?;

        Ok(result)
    }

    fn init_base_address(&mut self, ranges: &mut [PCIeRange]) {
        let Some(bridge_bus_number) = self.bridge_bus_number else {
            return;
        };

        let Some(bridge_device_number) = self.bridge_device_number else {
            return;
        };

        let Some(bridge_function_number) = self.bridge_function_number else {
            return;
        };

        for addr in self.base_addresses.iter_mut() {
            for range in ranges.iter_mut() {
                if let Some(allocated) = range.allocate(
                    addr,
                    bridge_bus_number,
                    bridge_device_number,
                    bridge_function_number,
                ) {
                    unsafe { addr.set_base_address(allocated.device_addr) };
                    *addr = allocated.cpu_addr;
                    break;
                }
            }
        }
    }

    /// Get the information for PCIe device as BFD format.
    pub fn get_bfd(&self) -> String {
        format!(
            "{:04x}:{:02x}:{:02x}.{:01x}",
            self.segment_group, self.bus_number, self.device_number, self.function_number
        )
    }

    pub fn get_secondary_bus(&self) -> Option<u8> {
        if matches!(self.pcie_class, pcie_class::PCIeClass::BridgeDevice(_)) {
            let val = self
                .config_space
                .read_u32(registers::SECONDARY_LATENCY_TIMER_BUS_NUMBER);
            Some((val >> 8) as u8)
        } else {
            None
        }
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

    /// Read PCIe device extension functionality settings and initialize MSI, MSI-X, and other extensions.
    pub(crate) fn read_capability(&mut self) {
        capability::read(self);
    }

    fn read_bar(&mut self) -> Result<(), PCIeDeviceErr> {
        let num_reg = match self.header_type {
            registers::HEADER_TYPE_GENERAL_DEVICE => 6,
            registers::HEADER_TYPE_PCI_TO_PCI_BRIDGE
            | registers::HEADER_TYPE_PCI_TO_CARDBUS_BRIDGE => 2,
            _ => return Err(PCIeDeviceErr::ReadFailure),
        };

        if self.header_type != registers::HEADER_TYPE_PCI_TO_CARDBUS_BRIDGE {
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

        Ok(())
    }

    pub(crate) fn map_bar(&mut self) -> Result<(), MapError> {
        let mut csr = self.read_status_command();

        // Disable the device
        csr.set(registers::StatusCommand::MEMORY_SPACE, false);
        csr.set(registers::StatusCommand::IO_SPACE, false);
        self.write_status_command(csr);

        // Enable the device
        csr.set(registers::StatusCommand::MEMORY_SPACE, true);
        csr.set(registers::StatusCommand::IO_SPACE, true);
        self.write_status_command(csr);

        // map MMIO regions
        for bar in self.base_addresses.iter() {
            if let BaseAddress::Mmio {
                addr,
                size,
                prefetchable,
                mapped,
                ..
            } = bar
            {
                if *size == 0 || *mapped {
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
    fn attach(self) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
        let segment_group = self.segment_group;
        let bus_number = self.bus_number;
        let device_number = self.device_number;
        let function_number = self.function_number;
        let vendor = self.vendor;
        let id = self.id;

        match self.vendor {
            pcie_id::INTEL_VENDOR_ID => {
                #[cfg(feature = "igb")]
                if intel::igb::match_device(self.vendor, self.id) {
                    return intel::igb::attach(self);
                }

                #[cfg(feature = "ixgbe")]
                if intel::ixgbe::match_device(self.vendor, self.id) {
                    return intel::ixgbe::attach(self);
                }

                // Example of the driver for Intel E1000e.
                if intel::e1000e_example::match_device(self.vendor, self.id) {
                    return intel::e1000e_example::attach(self);
                }
            }
            pcie_id::RASPI_VENDOR_ID => {
                if raspi::rp1::match_device(self.vendor, self.id) {
                    return raspi::rp1::attach(self);
                }
            }
            pcie_id::BROADCOM_VENDOR_ID => {
                if broadcom::bcm2712::match_device(self.vendor, self.id) {
                    return broadcom::bcm2712::attach(self);
                }
            }
            _ => (),
        }

        Ok(Arc::new(UnknownDevice {
            segment_group,
            bus_number,
            device_number,
            function_number,
            vendor,
            id,
            pcie_class: self.pcie_class,
        }))
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

    fn children(&self) -> Option<&Vec<ChildDevice>> {
        None
    }
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

        // To determine the size of the memory space, the PCIe specification prescribes writing 1 to all bits of the base address register and then reading back the value.
        let size = {
            config_space.write_u32(!0, offset);
            let size = config_space.read_u32(offset);
            config_space.write_u32(bar, offset);
            (!(size & BAR_IO_ADDR_MASK)).wrapping_add(1) as usize
        };

        BaseAddress::IO {
            reg_addr: config_space.addr(offset),
            addr: bar & BAR_IO_ADDR_MASK,
            size,
        }
    } else {
        // Memory space

        let bar_type = bar & BAR_TYPE_MASK;
        if bar_type == BAR_TYPE_32 {
            let size = {
                config_space.write_u32(!0, offset);
                let size = config_space.read_u32(offset);
                config_space.write_u32(bar, offset);
                (!(size & BAR_MEM_ADDR_MASK)).wrapping_add(1) as usize
            };

            if size == 0 {
                BaseAddress::None
            } else {
                BaseAddress::Mmio {
                    reg_addr: config_space.addr(offset),
                    addr: (bar & BAR_MEM_ADDR_MASK) as usize,
                    size,
                    address_type: AddressType::T32B,
                    prefetchable: (bar & BAR_PREFETCHABLE) > 1,
                    mapped: false,
                }
            }
        } else if bar_type == BAR_TYPE_64 {
            let high_offset = offset + 4;
            let high_bar = config_space.read_u32(high_offset);

            let size = {
                let high_bar = config_space.read_u32(high_offset);

                config_space.write_u32(4, 0x04);
                config_space.write_u32(!0, offset);
                config_space.write_u32(!0, high_offset);

                let low_size = config_space.read_u32(offset);
                let high_size = config_space.read_u32(high_offset);

                config_space.write_u32(bar, offset);
                config_space.write_u32(high_bar, high_offset);
                config_space.write_u32(6, 0x04);

                (!((high_size as u64) << 32 | ((low_size & BAR_MEM_ADDR_MASK) as u64)) + 1) as usize
            };

            let addr = (((high_bar as u64) << 32) | (bar & BAR_MEM_ADDR_MASK) as u64) as usize;

            if size == 0 {
                BaseAddress::None
            } else {
                BaseAddress::Mmio {
                    reg_addr: config_space.addr(offset),
                    addr,
                    size,
                    address_type: AddressType::T64B,
                    prefetchable: (bar & BAR_PREFETCHABLE) > 1,
                    mapped: false,
                }
            }
        } else {
            BaseAddress::None
        }
    }
}
