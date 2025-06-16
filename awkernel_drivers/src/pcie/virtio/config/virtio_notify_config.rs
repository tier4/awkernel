use crate::pcie::{capability::virtio::VirtioCap, virtio::VirtioDriverErr, BaseAddress, PCIeInfo};

// Notification structure layout
// struct virtio_pci_notify_cfg {
//     cap: struct virtio_pci_cap, (16 bytes)
//     notify_off_multiplier: u32,
// }

pub struct VirtioNotifyConfig {
    bar: BaseAddress,
    offset: usize,
}

impl Default for VirtioNotifyConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl VirtioNotifyConfig {
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

    pub fn virtio_set_notify(&mut self, offset: usize, idx: u16) -> Result<(), VirtioDriverErr> {
        self.bar.write16(self.offset + offset, idx);

        Ok(())
    }
}
