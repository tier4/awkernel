#[derive(Debug, Clone)]
pub enum PCIeID {
    // Intel
    Intel82574GbE, // 82574 Gb Ethernet Controller
}

pub const INTEL_VENDOR_ID: u16 = 0x8086;

pub const INTEL_82574GBE_DEVICE_ID: u16 = 0x10d3;
pub const INTEL_I219_LM3_DEVICE_ID: u16 = 0x15b9;
