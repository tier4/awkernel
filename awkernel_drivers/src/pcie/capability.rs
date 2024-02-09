pub mod msi;
pub mod msix;
pub mod pcie_cap;

use super::PCIeInfo;

pub const _NULL: u8 = 0x00;
pub const _PCI_POWER_MANAGEMENT_INTERFACE: u8 = 0x01;
pub const _AGP: u8 = 0x02;
pub const _VPD: u8 = 0x03;
pub const _SLOT_IDENTIFICATION: u8 = 0x04;
pub const MSI: u8 = 0x05;
pub const _HOT_SWAP: u8 = 0x06;
pub const _PCIX: u8 = 0x07;
pub const _HYPER_TRANSPORT: u8 = 0x08;
pub const _VENDOR_SPECIFIC: u8 = 0x09;
pub const _DEBUG_PORT: u8 = 0x0a;
pub const _COMPACT_PCI: u8 = 0x0b;
pub const _PCI_HOT_PLUG: u8 = 0x0c;
pub const _PCI_BRIDGE_SUBSYSTEM_VENDOR_ID: u8 = 0x0d;
pub const _AGP_8X: u8 = 0x0e;
pub const _SECURE_DEVICE: u8 = 0x0f;
pub const PCI_EXPRESS: u8 = 0x10;
pub const MSIX: u8 = 0x11;
pub const _SATA_DATA_INDEX_CONF: u8 = 0x12;
pub const _ADVANCED_FEATURES: u8 = 0x13;
pub const _ENHANCED_ALLOCATION: u8 = 0x14;
pub const _FLATTENING_PORTAL_BRIDGE: u8 = 0x15;

pub fn read(info: &mut PCIeInfo) {
    use super::registers;

    if info.header_type == registers::HEADER_TYPE_PCI_TO_CARDBUS_BRIDGE
        || !info
            .read_status_command()
            .contains(registers::StatusCommand::CAPABILITIES_LIST)
    {
        return;
    }

    let mut cap_ptr =
        (info.read_config_space_u32(registers::CAPABILITY_POINTER) & 0b1111_1100) as usize;

    while cap_ptr != 0 {
        let base = info.config_base + cap_ptr;
        let msg_ctl_next_id = super::pci_read_config_space_u32(
            info.is_memory_space,
            base + registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID,
        );

        let cap_id = msg_ctl_next_id & 0xff;
        cap_ptr = ((msg_ctl_next_id >> 8) & 0b1111_1100) as usize;

        match cap_id as u8 {
            MSIX => {
                log::debug!("MSI-X capability found.");
                info.msix = msix::Msix::new(info, base);
            }
            MSI => {
                log::debug!("MSI capability found.");
                let msi = msi::Msi::new(base);
                info.msi = Some(msi);
            }
            PCI_EXPRESS => {
                log::debug!("PCIe capability found.");
                let pcie_cap = pcie_cap::PCIeCap::new(base);
                info.pcie_cap = Some(pcie_cap);
            }
            _ => (),
        }
    }
}
