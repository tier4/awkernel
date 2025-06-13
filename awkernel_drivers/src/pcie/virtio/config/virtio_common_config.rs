use crate::pcie::{capability::virtio::VirtioCap, virtio::VirtioDriverErr, BaseAddress, PCIeInfo};

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
const VIRTIO_PCI_COMMON_CFG_CONFIG_MSIX_VECTOR: usize = 0x10;
const VIRTIO_PCI_COMMON_CFG_DEVICE_STATUS: usize = 0x14;
const VIRTIO_PCI_COMMON_CFG_QUEUE_SELECT: usize = 0x16;
const VIRTIO_PCI_COMMON_CFG_QUEUE_SIZE: usize = 0x18;
const VIRTIO_PCI_COMMON_CFG_QUEUE_MSIX_VECTOR: usize = 0x1a;
const VIRTIO_PCI_COMMON_CFG_QUEUE_ENABLE: usize = 0x1c;
const VIRTIO_PCI_COMMON_CFG_QUEUE_NOTIFY_OFF: usize = 0x1e;
const VIRTIO_PCI_COMMON_CFG_QUEUE_DESC: usize = 0x20;
const VIRTIO_PCI_COMMON_CFG_QUEUE_DRIVER: usize = 0x28;
const VIRTIO_PCI_COMMON_CFG_QUEUE_DEVICE: usize = 0x30;

pub struct VirtioCommonConfig {
    bar: BaseAddress,
    offset: usize,
}

impl Default for VirtioCommonConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl VirtioCommonConfig {
    pub fn new() -> Self {
        Self {
            bar: BaseAddress::None,
            offset: 0,
        }
    }

    pub fn init(&mut self, info: &PCIeInfo, cap: VirtioCap) -> Result<(), VirtioDriverErr> {
        self.bar = info
            .get_bar(cap.get_bar() as usize)
            .ok_or(VirtioDriverErr::NoBar)?;

        self.offset = cap.get_offset() as usize;

        log::info!("virtio-common: bar: {:?}", self.bar);
        log::info!("virtio-common: offset: {:?}", self.offset);

        Ok(())
    }

    pub fn virtio_get_device_features(&mut self) -> Result<u64, VirtioDriverErr> {
        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_DEVICE_FEATURE_SELECT, 0);
        let low = self
            .bar
            .read32(self.offset + VIRTIO_PCI_COMMON_CFG_DEVICE_FEATURE)
            .ok_or(VirtioDriverErr::ReadFailure)? as u64;

        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_DEVICE_FEATURE_SELECT, 1);
        let high = self
            .bar
            .read32(self.offset + VIRTIO_PCI_COMMON_CFG_DEVICE_FEATURE)
            .ok_or(VirtioDriverErr::ReadFailure)? as u64;

        Ok((high << 32) | low)
    }

    pub fn virtio_get_driver_features(&mut self) -> Result<u64, VirtioDriverErr> {
        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE_SELECT, 0);
        let low = self
            .bar
            .read32(self.offset + VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE)
            .ok_or(VirtioDriverErr::ReadFailure)? as u64;

        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE_SELECT, 1);
        let high = self
            .bar
            .read32(self.offset + VIRTIO_PCI_COMMON_CFG_DRIVER_FEATURE)
            .ok_or(VirtioDriverErr::ReadFailure)? as u64;

        Ok((high << 32) | low)
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

    pub fn virtio_set_config_msix_vector(&mut self, vector: u16) -> Result<(), VirtioDriverErr> {
        self.bar.write16(
            self.offset + VIRTIO_PCI_COMMON_CFG_CONFIG_MSIX_VECTOR,
            vector,
        );

        Ok(())
    }

    pub fn virtio_get_device_status(&self) -> Result<u8, VirtioDriverErr> {
        let status = self
            .bar
            .read8(self.offset + VIRTIO_PCI_COMMON_CFG_DEVICE_STATUS)
            .ok_or(VirtioDriverErr::ReadFailure)?;

        Ok(status)
    }

    pub fn virtio_set_device_status(&mut self, status: u8) -> Result<(), VirtioDriverErr> {
        let current_status = self.virtio_get_device_status()?;

        self.bar.write8(
            self.offset + VIRTIO_PCI_COMMON_CFG_DEVICE_STATUS,
            current_status | status,
        );

        Ok(())
    }

    pub fn virtio_set_queue_select(&mut self, idx: u16) -> Result<(), VirtioDriverErr> {
        self.bar
            .write16(self.offset + VIRTIO_PCI_COMMON_CFG_QUEUE_SELECT, idx);

        Ok(())
    }

    pub fn virtio_get_queue_size(&self) -> Result<u16, VirtioDriverErr> {
        let size = self
            .bar
            .read16(self.offset + VIRTIO_PCI_COMMON_CFG_QUEUE_SIZE)
            .ok_or(VirtioDriverErr::ReadFailure)?;

        Ok(size)
    }

    pub fn virtio_set_queue_msix_vector(&mut self, vector: u16) -> Result<(), VirtioDriverErr> {
        self.bar.write16(
            self.offset + VIRTIO_PCI_COMMON_CFG_QUEUE_MSIX_VECTOR,
            vector,
        );

        Ok(())
    }

    pub fn virtio_set_queue_enable(&mut self, enable: u16) -> Result<(), VirtioDriverErr> {
        self.bar
            .write16(self.offset + VIRTIO_PCI_COMMON_CFG_QUEUE_ENABLE, enable);

        Ok(())
    }

    pub fn virtio_get_queue_notify_off(&self) -> Result<u16, VirtioDriverErr> {
        let off = self
            .bar
            .read16(self.offset + VIRTIO_PCI_COMMON_CFG_QUEUE_NOTIFY_OFF)
            .ok_or(VirtioDriverErr::ReadFailure)?;

        Ok(off)
    }

    pub fn virtio_set_queue_desc(&mut self, addr: u64) -> Result<(), VirtioDriverErr> {
        let addr_low = addr as u32;
        let addr_high = (addr >> 32) as u32;

        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_QUEUE_DESC, addr_low);
        self.bar.write32(
            self.offset + VIRTIO_PCI_COMMON_CFG_QUEUE_DESC + 4,
            addr_high,
        );

        Ok(())
    }

    // Note: driver area means available ring
    pub fn virtio_set_queue_avail(&mut self, addr: u64) -> Result<(), VirtioDriverErr> {
        let addr_low = addr as u32;
        let addr_high = (addr >> 32) as u32;

        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_QUEUE_DRIVER, addr_low);
        self.bar.write32(
            self.offset + VIRTIO_PCI_COMMON_CFG_QUEUE_DRIVER + 4,
            addr_high,
        );

        Ok(())
    }

    // Note: device area means used ring
    pub fn virtio_set_queue_used(&mut self, addr: u64) -> Result<(), VirtioDriverErr> {
        let addr_low = addr as u32;
        let addr_high = (addr >> 32) as u32;

        self.bar
            .write32(self.offset + VIRTIO_PCI_COMMON_CFG_QUEUE_DEVICE, addr_low);
        self.bar.write32(
            self.offset + VIRTIO_PCI_COMMON_CFG_QUEUE_DEVICE + 4,
            addr_high,
        );

        Ok(())
    }
}
