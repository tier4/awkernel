use crate::pcie::{capability::virtio::VirtioCap, virtio::VirtioDriverErr, BaseAddress, PCIeInfo};

// Notification structure layout
// struct virtio_pci_notify_cfg {
//     cap: struct virtio_pci_cap, (16 bytes)
//     notify_off_multiplier: u8,
// }

const VIRTIO_PCI_NOTIFY_CFG_NOTIFY_OFF_MULTIPLIER: usize = 0x10;

pub struct VirtioNotifyCap {
    bar: BaseAddress,
    offset: usize,
}

impl Default for VirtioNotifyCap {
    fn default() -> Self {
        Self::new()
    }
}

impl VirtioNotifyCap {
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

        Ok(())
    }

    pub fn virtio_get_notify_off_multiplier(&self) -> Result<u8, VirtioDriverErr> {
        let multiplier = self
            .bar
            .read32(self.offset + VIRTIO_PCI_NOTIFY_CFG_NOTIFY_OFF_MULTIPLIER)
            .ok_or(VirtioDriverErr::ReadFailure)? as u8;

        Ok(multiplier)
    }
}
