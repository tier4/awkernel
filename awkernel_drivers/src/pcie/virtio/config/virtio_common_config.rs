use super::VirtioDriverErr;
use crate::pcie::capability::virtio::VirtioCap;
use crate::pcie::BaseAddress;
use crate::pcie::PCIeInfo;

// Common configuration structure layout
// struct virtio_pci_common_cfg {
//     // About the whole device.
//     device_feature_select: u32, // read-write
//     device_feature: u32,        // read-only for driver
//     driver_feature_select: u32, // read-write
//     driver_feature: u32,        // read-write
//     config_msix_vector: u16,    // read-write
//     num_queues: u16,            // read-only for driver
//     device_status: u8,          // read-write
//     config_generation: u8,      // read-only for driver
//
//     // About a specific virtqueue.
//     queue_select: u16,            // read-write
//     queue_size: u16,              // read-write
//     queue_msix_vector: u16,       // read-write
//     queue_enable: u16,            // read-write
//     queue_notify_off: u16,        // read-only for driver
//     queue_desc: u64,              // read-write
//     queue_driver: u64,            // read-write
//     queue_device: u64,            // read-write
//     queue_notif_config_data: u16, // read-only for driver
//     queue_reset: u16,             // read-write
//
//     // About the administration virtqueue.
//     admin_queue_index: u16, // read-only for driver
//     admin_queue_num: u16,   // read-only for driver
// }

const VIRTIO_PCI_COMMON_CFG_DEVICE_FEATURE_SELECT: usize = 0x00;
const VIRTIO_PCI_COMMON_CFG_DEVICE_FEATURE: usize = 0x04;
const VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE_SELECT: usize = 0x08;
const VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE: usize = 0x0c;
const VIRTIO_PCI_COMMON_CFG_DEVICE_STATUS: usize = 0x14;

pub struct VirtioCommonConfig {
    bar: BaseAddress,
    offset: usize,
}

impl VirtioCommonConfig {
    pub fn new(info: &PCIeInfo, cap: VirtioCap) -> Self {
        let bar = info
            .get_bar(cap.get_bar() as usize)
            .ok_or(VirtioDriverErr::NoBar)
            .unwrap();

        Self {
            bar,
            offset: cap.get_offset() as usize,
        }
    }

    pub fn virtio_get_device_features(&mut self) -> u64 {
        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_DEVICE_FEATURE_SELECT, 0);
        let low = self
            .bar
            .read32(self.offset + VIRTIO_PCI_COMMON_CFG_DEVICE_FEATURE)
            .ok_or(VirtioDriverErr::ReadFailure)
            .unwrap() as u64;

        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_DEVICE_FEATURE_SELECT, 1);
        let high = self
            .bar
            .read32(self.offset + VIRTIO_PCI_COMMON_CFG_DEVICE_FEATURE)
            .ok_or(VirtioDriverErr::ReadFailure)
            .unwrap() as u64;

        (high << 32) | low
    }

    pub fn virtio_get_driver_features(&mut self) -> u64 {
        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE_SELECT, 0);
        let low = self
            .bar
            .read32(self.offset + VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE)
            .ok_or(VirtioDriverErr::ReadFailure)
            .unwrap() as u64;

        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE_SELECT, 1);
        let high = self
            .bar
            .read32(self.offset + VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE)
            .ok_or(VirtioDriverErr::ReadFailure)
            .unwrap() as u64;

        (high << 32) | low
    }

    pub fn virtio_set_driver_features(&mut self, features: u64) {
        let low = (features & 0xffffffff) as u32;
        let high = (features >> 32) as u32;

        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE_SELECT, 0);
        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE, low);

        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE_SELECT, 1);
        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE, high);
    }

    pub fn virtio_get_device_status(&self) -> u8 {
        self.bar
            .read8(self.offset + VIRTIO_PCI_COMMON_CFG_DEVICE_STATUS)
            .ok_or(VirtioDriverErr::ReadFailure)
            .unwrap()
    }

    pub fn virtio_set_device_status(&mut self, status: u8) {
        self.bar.write8(
            self.offset + VIRTIO_PCI_COMMON_CFG_DEVICE_STATUS,
            self.virtio_get_device_status() | status,
        );
    }
}
