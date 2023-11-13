use super::DeviceInfo;

pub const NULL: u8 = 0x00;
pub const PCI_POWER_MANAGEMENT_INTERFACE: u8 = 0x01;
pub const AGP: u8 = 0x02;
pub const VPD: u8 = 0x03;
pub const SLOT_IDENTIFICATION: u8 = 0x04;
pub const MSI: u8 = 0x05;
pub const HOT_SWAP: u8 = 0x06;
pub const PCIX: u8 = 0x07;
pub const HYPER_TRANSPORT: u8 = 0x08;
pub const VENDOR_SPECIFIC: u8 = 0x09;
pub const DEBUG_PORT: u8 = 0x0a;
pub const COMPACT_PCI: u8 = 0x0b;
pub const PCI_HOT_PLUG: u8 = 0x0c;
pub const PCI_BRIDGE_SUBSYSTEM_VENDOR_ID: u8 = 0x0d;
pub const AGP_8X: u8 = 0x0e;
pub const SECURE_DEVICE: u8 = 0x0f;
pub const PCI_EXPRESS: u8 = 0x10;
pub const MSIX: u8 = 0x11;
pub const SATA_DATA_INDEX_CONF: u8 = 0x12;
pub const ADVANCED_FEATURES: u8 = 0x13;
pub const ENHANCED_ALLOCATION: u8 = 0x14;
pub const FLATTENING_PORTAL_BRIDGE: u8 = 0x15;

pub fn read(info: &mut DeviceInfo) {
    use super::registers;

    if info.header_type == registers::HEADER_TYPE_PCI_TO_CARDBUS_BRIDGE
        || !info
            .read_status_command()
            .contains(registers::StatusCommand::CAPABILITIES_LIST)
    {
        return;
    }

    let mut cap_ptr = (registers::CAPABILITY_POINTER.read(info.addr) & 0b1111_1100) as usize;
    while cap_ptr != 0 {
        let msg_ctl_next_id = registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.read(info.addr + cap_ptr);

        let cap_id = msg_ctl_next_id & 0xff;
        cap_ptr = ((msg_ctl_next_id >> 8) & 0b1111_1100) as usize;

        match cap_id as u8 {
            MSI => read_msi(info, cap_ptr),
            MSIX => read_msix(info, cap_ptr),
            _ => log::warn!(
                "Unknown PCIe capability: device = {}, capability = 0x{cap_id:02x}",
                info.id
            ),
        }

        log::debug!("PCIe capability: {:#x}", cap_id);
    }
}

fn read_msix(info: &mut DeviceInfo, cap_ptr: usize) {
    let msix = super::msix::MSIX::new(cap_ptr);
    info.msix = Some(msix);
}

fn read_msi(info: &mut DeviceInfo, cap_ptr: usize) {
    let msi = super::msi::MSI::new(cap_ptr);
    info.msi = Some(msi);
}
