use alloc::{
    boxed::Box,
    collections::{btree_map::Entry, BTreeMap},
};
use array_macro::array;
use awkernel_lib::{
    paging::{Frame, FrameAllocator, PageTable, PAGESIZE},
    sync::mutex::{MCSNode, Mutex},
};
use core::{
    fmt::{self, Debug},
    ptr::{read_volatile, write_volatile},
    sync::atomic::{AtomicU16, Ordering},
};

#[cfg(feature = "x86")]
use awkernel_lib::arch::x86_64::acpi::AcpiMapper;

#[cfg(feature = "x86")]
use acpi::{AcpiTables, PciConfigRegions};

mod capability;
pub mod net;
pub mod pcie_class;
pub mod pcie_id;

#[cfg(feature = "x86")]
const LEGARCY_INTERRUPT_IRQ: u16 = 42;

#[cfg(not(feature = "x86"))]
const LEGARCY_INTERRUPT_IRQ: u16 = 0; // TODO: must be set for other architectures

static LEGACY_INTERRUPTS: Mutex<BTreeMap<u16, Box<dyn FnMut() + Sync + Send>>> =
    Mutex::new(BTreeMap::new());

static LEGACY_INTERRUPT_ID: AtomicU16 = AtomicU16::new(0);

#[derive(Debug, Clone, Copy)]
pub struct LegacyInterrupt {
    irq: u16,
    handler_id: u16,
}

impl LegacyInterrupt {
    pub fn get_irq(&self) -> u16 {
        self.irq
    }
}

/// Register a legacy interrupt handler,
/// and return the ID of the handler.
/// The ID is not the IRQ number.
pub fn register_legacy_interrupt<F>(f: F) -> LegacyInterrupt
where
    F: FnMut() + Sync + Send + 'static,
{
    let f = Box::new(f);

    let id = loop {
        let id = LEGACY_INTERRUPT_ID.fetch_add(1, Ordering::Relaxed);
        let mut node = MCSNode::new();
        let mut guard = LEGACY_INTERRUPTS.lock(&mut node);
        if let Entry::Vacant(e) = guard.entry(id) {
            e.insert(f);
            break id;
        }
    };

    let _ = awkernel_lib::interrupt::register_handler(
        LEGARCY_INTERRUPT_IRQ,
        "PCIe Legacy Interrupt",
        Box::new(|_irq| {
            let mut node = MCSNode::new();
            for (_, f) in LEGACY_INTERRUPTS.lock(&mut node).iter_mut() {
                f();
            }
        }),
    );

    if id == 0 {
        awkernel_lib::interrupt::enable_irq(LEGARCY_INTERRUPT_IRQ);
    }

    LegacyInterrupt {
        irq: LEGARCY_INTERRUPT_IRQ,
        handler_id: id,
    }
}

/// Unregister a legacy interrupt handler.
pub fn unregister_legacy_interrupt(legacy_interrupt: LegacyInterrupt) {
    let mut node = MCSNode::new();
    LEGACY_INTERRUPTS
        .lock(&mut node)
        .remove(&legacy_interrupt.handler_id);
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
                let dst = *addr + offset;
                assert!(dst + 2 < *addr + *size);
                unsafe { Some(read_volatile(dst as *const u16)) }
            }
            _ => None,
        }
    }

    pub fn read32(&self, offset: usize) -> Option<u32> {
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
                let port = *addr + offset as u32;
                core::arch::asm!("out dx, al",
                        in("al") val,
                        in("dx") port,
                        options(nomem, nostack, preserves_flags));
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
        match self {
            #[cfg(feature = "x86")]
            BaseAddress::IO(addr) => unsafe {
                let port = *addr + offset as u32;
                core::arch::asm!("out dx, ax",
                        in("ax") val,
                        in("dx") port,
                        options(nomem, nostack, preserves_flags));
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
    UnRecognizedDevice { bus: u8, device: u16, vendor: u16 },
    InvalidClass,
    NotImplemented,
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

    // Type 0 and 1
    mmio_r!(offset 0x00 => pub DEVICE_VENDOR_ID<u32>);
    mmio_rw!(offset 0x04 => pub STATUS_COMMAND<StatusCommand>);
    mmio_r!(offset 0x08 => pub CLASS_CODE_REVISION_ID<u32>);
    mmio_r!(offset 0x0c => pub BIST_HEAD_LAT_CACH<u32>);
    mmio_r!(offset 0x34 => pub CAPABILITY_POINTER<u32>);
    mmio_rw!(offset 0x3c => pub INTERRUPT_LINE<u8>);

    // Type 1 (PCI-to-PCI bridge)
    mmio_r!(offset 0x18 => pub SECONDARY_LATENCY_TIMER_BUS_NUMBER<u32>);

    // Capability
    mmio_r!(offset 0x00 => pub MESSAGE_CONTROL_NEXT_PTR_CAP_ID<u32>);

    pub const BAR0: usize = 0x10;
}

/// Initialize the PCIe for ACPI
#[cfg(feature = "x86")]
pub fn init_with_acpi<F, FA, PT, E>(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut PT,
    page_allocators: &mut BTreeMap<u32, FA>,
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

        let Some(page_allocator) = page_allocators.get_mut(&(segment.segment_group as u32)) else {
            continue;
        };

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

        let base_address = segment.physical_address;

        for bus in segment.bus_range {
            scan_devices(
                segment.segment_group,
                bus,
                base_address,
                page_table,
                page_allocator,
            );
        }
    }
}

pub fn init_with_addr<F, FA, PT, E>(
    segment_group: u16,
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
            segment_group,
            bus as u8,
            base_address,
            page_table,
            page_allocator,
        );
    }
}

/// Scan and initialize the PICe devices
fn scan_devices<F, FA, PT, E>(
    segment_group: u16,
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
            if let Ok(device) = PCIeInfo::from_addr(segment_group, bus, addr) {
                let multiple_functions = device.multiple_functions;

                let _ = device.attach(page_table, page_allocator);

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
    segment_group: u16,
    bus: u8,
    id: u16,
    vendor: u16,
    revision_id: u8,
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
            "bus: {:#x}, vendor: {:#x}, device: {:#x}, header type: {:#x}",
            self.bus, self.vendor, self.id, self.header_type
        )
    }
}

impl PCIeInfo {
    /// Get the information for PCIe device
    fn from_addr(segment_group: u16, bus: u8, addr: usize) -> Result<PCIeInfo, PCIeDeviceErr> {
        let ids = registers::DEVICE_VENDOR_ID.read(addr);
        let vendor = (ids & 0xffff) as u16;
        let id = (ids >> 16) as u16;
        let header_type = (registers::BIST_HEAD_LAT_CACH.read(addr) >> 16 & 0xff) as u8;
        let multiple_functions = header_type & 0x80 == 0x80;
        let header_type = header_type & 0x7f;

        let cls_rev_id = registers::CLASS_CODE_REVISION_ID.read(addr);
        let revision_id = (cls_rev_id & 0xff) as u8;

        let pcie_class = pcie_class::PCIeClass::from_u8(
            (cls_rev_id >> 24) as u8,
            ((cls_rev_id >> 16) & 0xff) as u8,
        )
        .ok_or(PCIeDeviceErr::InvalidClass)?;

        if id == !0 || vendor == !0 {
            Err(PCIeDeviceErr::InitFailure)
        } else {
            Ok(PCIeInfo {
                addr,
                segment_group,
                bus,
                id,
                vendor,
                revision_id,
                pcie_class,
                device_name: None,
                multiple_functions,
                header_type,
                base_addresses: array![_ => BaseAddress::None; 6],
                msi: None,
                msix: None,
                pcie_cap: None,
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
        registers::STATUS_COMMAND.read(self.addr)
    }

    pub fn write_status_command(&mut self, csr: registers::StatusCommand) {
        registers::STATUS_COMMAND.write(csr, self.addr);
    }

    pub fn read_config_space_u32(&self, offset: usize) -> u32 {
        unsafe { read_volatile((self.addr + offset) as *const u32) }
    }

    pub fn read_config_space_u16(&self, offset: usize) -> u16 {
        unsafe { read_volatile((self.addr + offset) as *const u16) }
    }

    pub fn get_segment_group(&self) -> u16 {
        self.segment_group
    }

    pub fn get_interrupt_line(&mut self) -> u8 {
        registers::INTERRUPT_LINE.read(self.addr)
    }

    pub fn set_interrupt_line(&mut self, irq: u8) {
        registers::INTERRUPT_LINE.write(irq, self.addr);
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
    #[allow(unused_variables)]
    fn attach<F, FA, PT, E>(
        self,
        page_table: &mut PT,
        page_allocator: &mut FA,
    ) -> Result<(), PCIeDeviceErr>
    where
        F: Frame,
        FA: FrameAllocator<F, E>,
        PT: PageTable<F, FA, E>,
        E: Debug,
    {
        #[allow(clippy::single_match)] // TODO: To be removed
        match self.vendor {
            pcie_id::INTEL_VENDOR_ID =>
            {
                #[cfg(feature = "igb")]
                if net::igb::match_device(self.vendor, self.id) {
                    return net::igb::attach(self, page_table, page_allocator);
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

    pub fn enable_legacy_interrupt(&mut self) {
        registers::STATUS_COMMAND.clrbits(registers::StatusCommand::INTERRUPT_DISABLE, self.addr);
    }
}

pub trait PCIeDevice {
    fn device_name(&self) -> &'static str;
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
