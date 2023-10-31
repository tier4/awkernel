use alloc::{boxed::Box, sync::Arc};
use awkernel_lib::sync::mutex::Mutex;
use awkernel_lib::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr},
    net::NET_MANAGER,
    paging::{Flags, Frame, FrameAllocator, PageTable},
    sync::mutex::MCSNode,
};
use core::{fmt, ptr::read_volatile};

#[cfg(feature = "x86")]
use awkernel_lib::arch::x86_64::acpi::AcpiMapper;

#[cfg(feature = "x86")]
use acpi::{AcpiTables, PciConfigRegions};

use crate::net::e1000e::E1000E;

const CONFIG_SPACE_SIZE: usize = 256 * 1024 * 1024; // 256 MiB

pub enum PCIeDeviceErr {
    InitFailure,
    UnRecognizedDevice(DeviceInfo),
}

impl fmt::Display for PCIeDeviceErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::InitFailure => {
                write!(f, "Failed to initialize the device driver.")
            }
            Self::UnRecognizedDevice(device_info) => {
                write!(f, "Unregistered PCIe device with {}", device_info)
            }
        }
    }
}

/// Initialize the PCIe for ACPI
#[cfg(feature = "x86")]
pub fn init_with_acpi<F, FA, PT>(
    phys_offset: usize,
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut PT,
    page_allocator: &mut FA,
    page_size: u64,
) where
    F: Frame,
    FA: FrameAllocator<F, ()>,
    PT: PageTable<F, FA, ()>,
{
    let pcie_info = PciConfigRegions::new(acpi).unwrap();
    for segment in pcie_info.list_all() {
        log::info!("{:?}", segment);

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
                    .map_to(phy_addr, virt_addr, flags, page_allocator)
                    .is_err()
            } {
                log::error!("Failed to map the PCIe config space.");
                return;
            }

            config_start += page_size as usize;
        }

        let base_address = segment.base_address();
        for bus in segment.buses() {
            scan_devices(
                phys_offset,
                bus,
                base_address as usize,
                page_table,
                page_allocator,
                page_size,
            );
        }
    }
}

pub fn init_with_addr<F, FA, PT>(
    phys_offset: usize,
    base_address: usize,
    page_table: &mut PT,
    page_allocator: &mut FA,
    page_size: u64,
    starting_bus: u8,
) where
    F: Frame,
    FA: FrameAllocator<F, ()>,
    PT: PageTable<F, FA, ()>,
{
    for bus in (starting_bus as u32)..256 {
        scan_devices(
            phys_offset,
            bus as u8,
            base_address,
            page_table,
            page_allocator,
            page_size,
        );
    }
}

/// Scan and initialize the PICe devices
fn scan_devices<F, FA, PT>(
    phys_offset: usize,
    bus: u8,
    base_address: usize,
    page_table: &mut PT,
    page_allocator: &mut FA,
    page_size: u64,
) where
    F: Frame,
    FA: FrameAllocator<F, ()>,
    PT: PageTable<F, FA, ()>,
{
    for dev in 0..(1 << 5) {
        for func in 0..(1 << 3) {
            let offset = (bus as u64) << 20 | dev << 15 | func << 12;
            let addr = base_address as u64 + offset;
            if let Some(device) = DeviceInfo::from_addr(addr) {
                let _ = device.init(phys_offset, page_table, page_allocator, page_size);
            }
        }
    }
}

/// Information necessary for initializing the device
#[derive(Debug, Clone, Copy)]
pub struct DeviceInfo {
    pub(crate) addr: u64,
    id: u16,
    vendor: u16,
    pub(crate) header_type: u8,
}

impl fmt::Display for DeviceInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "id: {:#x}, vendor: {:#x}, header type: {:#x}",
            self.id, self.vendor, self.header_type
        )
    }
}

impl DeviceInfo {
    /// Get the information for PCIe device
    fn from_addr(addr: u64) -> Option<DeviceInfo> {
        let vendor = unsafe { read_volatile(addr as *const u16) };
        let id = unsafe { read_volatile((addr + 0x02) as *const u16) };
        let header_type = unsafe { read_volatile((addr + 0x0e) as *const u8) };

        if id == !0 || vendor == !0 {
            None
        } else {
            Some(DeviceInfo {
                addr,
                id,
                vendor,
                header_type,
            })
        }
    }

    /// Initialize the PCIe device based on the information
    fn init<F, FA, PT>(
        &self,
        phys_offset: usize,
        page_table: &mut PT,
        page_allocator: &mut FA,
        page_size: u64,
    ) -> Result<(), PCIeDeviceErr>
    where
        F: Frame,
        FA: FrameAllocator<F, ()>,
        PT: PageTable<F, FA, ()>,
    {
        match (self.id, self.vendor) {
            //  Intel 82574 GbE Controller
            (0x10d3, 0x8086) => {
                let mut e1000e =
                    E1000E::new(self, phys_offset, page_table, page_allocator, page_size)?;
                e1000e.init()?;
                let node = &mut MCSNode::new();
                let mut net_master = NET_MANAGER.lock(node);
                net_master.add_driver(Arc::new(Mutex::new(Box::new(e1000e))));
                Ok(())
            }
            _ => Err(PCIeDeviceErr::UnRecognizedDevice(*self)),
        }
    }
}

pub trait PCIeDevice {
    /// Each PCIe device has a register space,
    const REG_SPACE_SIZE: u64;

    /// Initialize the device hardware.
    fn init(&mut self) -> Result<(), PCIeDeviceErr>;
}
