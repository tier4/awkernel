#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PCIeID {
    // Intel
    Intel82574GbE, // 82574 Gb Ethernet Controller
}

pub const INTEL_VENDOR_ID: u16 = 0x8086;
pub const RASPI_VENDOR_ID: u16 = 0x1DE4;
pub const BROADCOM_VENDOR_ID: u16 = 0x14E4;
pub const VIRTIO_VENDOR_ID: u16 = 0x1AF4;
