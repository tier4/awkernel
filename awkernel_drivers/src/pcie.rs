use acpi::AcpiTables;
use alloc::boxed::Box;
use alloc::sync::Arc;
use awkernel_lib::net::NETMASTER;
use awkernel_lib::sync::mutex::MCSNode;
use awkernel_lib::{arch::x86_64::acpi::AcpiMapper, sync::mutex::Mutex};

use awkernel_lib::arch::x86_64::page_allocator::PageAllocator;
use x86_64::structures::paging::{OffsetPageTable, PageTableFlags, PhysFrame};

use acpi::{mcfg::McfgEntry, PciConfigRegions};
use awkernel_lib::arch::x86_64::mmu::map_to;
use core::ptr::read_volatile;

use crate::net::e1000e::E1000E;

const CONFIG_SPACE_SIZE: usize = 256 * 1024 * 1024; // 256 MiB

pub fn init<T>(
    acpi: &AcpiTables<AcpiMapper>,
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator<T>,
    page_size: u64,
) where
    T: Iterator<Item = PhysFrame> + Send,
{
    let pcie_info = PciConfigRegions::new(acpi).unwrap();
    for segment in pcie_info.list_all() {
        log::info!("{:?}", segment);
        let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;
        let mut config_start = segment.base_address() as usize;
        let config_end = config_start + CONFIG_SPACE_SIZE;
        while config_start < config_end {
            unsafe {
                map_to(
                    config_start,
                    config_start,
                    flags,
                    page_table,
                    page_allocator,
                );
            }
            config_start += page_size as usize;
        }

        scan_devices(&segment, page_table, page_allocator, page_size);
    }
}

/// scan and initialize the PICe devices
fn scan_devices<T>(
    segment: &McfgEntry,
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator<T>,
    page_size: u64,
) where
    T: Iterator<Item = PhysFrame> + Send,
{
    for bus in segment.buses() {
        for dev in 0..(1 << 5) {
            for func in 0..(1 << 3) {
                let offset = (bus as u64) << 20 | dev << 15 | func << 12;
                let addr = segment.base_address() + offset;
                if let Some(device) = DeviceInfo::from_addr(addr) {
                    log::info!("Load {:x?} at {:#x} ", device, addr);
                    device.init(page_table, page_allocator, page_size);
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct DeviceInfo {
    pub(crate) addr: u64,
    id: u16,
    vendor: u16,
    pub(crate) header_type: u8,
}

impl DeviceInfo {
    fn from_addr(addr: u64) -> Option<DeviceInfo> {
        let vendor = unsafe { read_volatile(addr as *const u16) };
        let id = unsafe { read_volatile((addr + 0x2) as *const u16) };
        let header_type = unsafe { read_volatile((addr + 0xF) as *const u8) };

        if id == !0 || vendor == !0 {
            return None;
        } else {
            return Some(DeviceInfo {
                addr,
                id,
                vendor,
                header_type,
            });
        }
    }

    fn init<T>(
        &self,
        page_table: &mut OffsetPageTable<'static>,
        page_allocator: &mut PageAllocator<T>,
        page_size: u64,
    ) -> Option<()>
    where
        T: Iterator<Item = PhysFrame> + Send,
    {
        match (self.id, self.vendor) {
            //  Intel 82574 GbE Controller
            (0x10d3, 0x8086) => {
                let mut e1000e = E1000E::new(&self, page_table, page_allocator, page_size);
                e1000e.init();
                let node = &mut MCSNode::new();
                let mut net_master = NETMASTER.lock(node);
                net_master.add_driver(Arc::new(Mutex::new(Box::new(e1000e))));
                Some(())
            }
            _ => None,
        }
    }
}

// TODO : design error handling ( should not panic )
pub trait PCIeDevice {
    const ADDR_SPACE_SIZE: u64;
    fn new<T>(
        info: &DeviceInfo,
        page_table: &mut OffsetPageTable<'static>,
        page_allocator: &mut PageAllocator<T>,
        page_size: u64,
    ) -> Self
    where
        T: Iterator<Item = PhysFrame> + Send,
        Self: Sized;
    fn init(&mut self);
}
