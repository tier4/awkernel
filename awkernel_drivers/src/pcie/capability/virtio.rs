use crate::pcie::PCIeInfo;

// Virtio Structure PCI Capabilities
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

const VIRTIO_PCI_CAP_CFG_TYPE: usize = 0x03;
const VIRTIO_PCI_CAP_BAR: usize = 0x04;
const VIRTIO_PCI_CAP_OFFSET: usize = 0x08;

#[derive(Debug)]
pub struct VirtioCap {
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
            cfg_type,
            bar,
            offset,
        }
    }

    pub fn get_cfg_type(&self) -> u8 {
        self.cfg_type
    }

    pub fn get_bar(&self) -> u8 {
        self.bar
    }

    pub fn get_offset(&self) -> u32 {
        self.offset
    }
}
