use crate::pcie::{ConfigSpace, PCIeInfo};

// Virtio Structure PCI Capabilities
//
// struct virtio_pci_cap {
//     cap_vndr: u8,     // Generic PCI field: PCI_CAP_ID_VNDR
//     cap_next: u8,     // Generic PCI field: next ptr.
//     cap_len: u8,      // Generic PCI field: capability length
//     cfg_type: u8,     // Identifies the structure.
//     bar: u8,          // Where to find it.
//     id: u8,           // Multiple capabilities of the same type
//     padding: [u8; 2], // Pad to full dword.
//     offset: u32,      // Offset within bar.
//     length: u32,      // Length of the structure, in bytes.
// }
//
// struct virtio_pci_notify_cap {
//     cap: struct virtio_pci_cap,
//     notify_off_multiplier: u32, // Multiplier for queue_notify_off.
// }

const VIRTIO_PCI_CAP_CFG_TYPE: usize = 0x03;
const VIRTIO_PCI_CAP_BAR: usize = 0x04;
const VIRTIO_PCI_CAP_OFFSET: usize = 0x08;
const VIRTIO_PCI_CAP_NOTIFY_OFF_MULTIPLIER: usize = 0x10;

#[derive(Debug, Clone)]
pub struct VirtioCap {
    config_space: ConfigSpace,
    cap_ptr: usize,
    cfg_type: u8,
    bar: u8,
    offset: u32,
}

impl VirtioCap {
    pub fn new(info: &PCIeInfo, cap_ptr: usize) -> Self {
        let cfg_type = info.config_space.read_u8(cap_ptr + VIRTIO_PCI_CAP_CFG_TYPE);
        let bar = info.config_space.read_u8(cap_ptr + VIRTIO_PCI_CAP_BAR);
        let offset = info.config_space.read_u32(cap_ptr + VIRTIO_PCI_CAP_OFFSET);

        Self {
            config_space: info.config_space.clone(),
            cap_ptr,
            cfg_type,
            bar,
            offset,
        }
    }

    #[inline(always)]
    pub fn get_cfg_type(&self) -> u8 {
        self.cfg_type
    }

    #[inline(always)]
    pub fn get_bar(&self) -> u8 {
        self.bar
    }

    #[inline(always)]
    pub fn get_offset(&self) -> u32 {
        self.offset
    }

    #[inline(always)]
    pub fn get_notify_off_multiplier(&self) -> u32 {
        self.config_space
            .read_u32(self.cap_ptr + VIRTIO_PCI_CAP_NOTIFY_OFF_MULTIPLIER)
    }
}
