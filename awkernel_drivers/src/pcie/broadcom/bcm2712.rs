use crate::pcie::{pcie_id, registers, PCIeDevice, PCIeDeviceErr, PCIeInfo};
use alloc::{borrow::Cow, sync::Arc, vec::Vec};

const BCM2712_ID: u16 = 0x2712;

const MEM_PCIE_RANGE_PCIE_START: u64 = 0x0000000000;
const PCI_BASE_ADDRESS_MEM_TYPE_64: u32 = 0x04;
const PCI_SECONDARY_BUS: usize = 0x19;
const PCI_SUBORDINATE_BUS: usize = 0x1a;
const PCI_MEMORY_BASE: usize = 0x20;
const PCI_MEMORY_LIMIT: usize = 0x22;
const PCI_BRIDGE_CTL_PARITY: u8 = 0x01;
const PCI_BRIDGE_CONTROL: usize = 0x3e;

const BRCM_PCIE_CAP_REGS: usize = 0x00ac;
const PCI_EXP_RTCTL: usize = 28;
const PCI_EXP_RTCTL_CRSSVE: u16 = 0x0010;

pub fn match_device(vendor: u16, id: u16) -> bool {
    vendor == pcie_id::BROADCOM_VENDOR_ID && id == BCM2712_ID
}

pub fn attach(mut info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    // Map the memory regions of MMIO.
    if let Err(e) = info.map_bar() {
        log::warn!("Failed to map the memory regions of MMIO: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }

    // Read capabilities of PCIe.
    info.read_capability();

    if info.get_revision_id() as u32 != 0x060400 {
        return Err(PCIeDeviceErr::RevisionIDMismatch);
    }

    let bcm2712 = BCM2712::new(info);
    let result = Arc::new(bcm2712);

    Ok(result)
}

fn pci_bus2(n: u8) -> u8 {
    n
}

pub struct BCM2712 {
    _info: PCIeInfo,
    // Add more fields if needed.
}

impl BCM2712 {
    pub fn new(mut info: PCIeInfo) -> Self {
        info.config_space
            .write_u8(64 / 4, registers::BIST_HEAD_LAT_CACH);

        info.config_space.write_u8(pci_bus2(1), PCI_SECONDARY_BUS);
        info.config_space.write_u8(pci_bus2(1), PCI_SECONDARY_BUS);

        info.config_space
            .write_u16((MEM_PCIE_RANGE_PCIE_START >> 16) as u16, PCI_MEMORY_BASE);
        info.config_space
            .write_u16((MEM_PCIE_RANGE_PCIE_START >> 16) as u16, PCI_MEMORY_LIMIT);

        info.config_space
            .write_u8(PCI_BRIDGE_CTL_PARITY, PCI_BRIDGE_CONTROL);

        info.config_space.write_u8(
            PCI_EXP_RTCTL_CRSSVE as u8,
            BRCM_PCIE_CAP_REGS + PCI_EXP_RTCTL,
        );

        let mut csr = info.read_status_command();
        csr.set(registers::StatusCommand::MEMORY_SPACE, true);
        csr.set(registers::StatusCommand::BUS_MASTER, true);
        csr.set(registers::StatusCommand::SERR_ENABLE, true);
        csr.set(registers::StatusCommand::PARITY_ERROR_RESPONSE, true);

        info.write_status_command(csr);

        Self { _info: info }
    }
}

impl PCIeDevice for BCM2712 {
    fn device_name(&self) -> Cow<'static, str> {
        "RASPI5 BCM2712".into()
    }
}
