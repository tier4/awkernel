#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PCIeID {
    // Intel
    Intel82574GbE, // 82574 Gb Ethernet Controller
}

pub const INTEL_VENDOR_ID: u16 = 0x8086;
