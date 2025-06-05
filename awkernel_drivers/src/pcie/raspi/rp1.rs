use crate::pcie::{pcie_id, registers, PCIeDevice, PCIeDeviceErr, PCIeInfo};
use alloc::{borrow::Cow, sync::Arc};

const RP1_ID: u16 = 0x0001;

const MEM_PCIE_RANGE_PCIE_START: u64 = 0x0000000000;
const PCI_BASE_ADDRESS_MEM_TYPE_64: u32 = 0x04;
const PCI_INTERRUPT_PIN: u32 = 0x3d;

fn lower_32_bits(value: u64) -> u32 {
    (value & 0xFFFFFFFF) as u32
}

fn upper_32_bits(val: u64) -> u32 {
    (val >> 32) as u32
}

pub fn match_device(vendor: u16, id: u16) -> bool {
    vendor == pcie_id::RASPI_VENDOR_ID && id == RP1_ID
}

pub fn attach(mut info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    // Map the memory regions of MMIO.
    if let Err(e) = info.map_bar() {
        log::warn!("Failed to map the memory regions of MMIO: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }

    // Read capabilities of PCIe.
    info.read_capability();

    if info.get_revision_id() as u32 != 0x20000 {
        return Err(PCIeDeviceErr::RevisionIDMismatch);
    }

    let rp1 = RP1::new(info);
    let result = Arc::new(rp1);
    Ok(result)
}

pub struct RP1 {
    _info: PCIeInfo,
    // Add more fields if needed.
}

impl RP1 {
    pub fn new(mut info: PCIeInfo) -> Self {
        info.config_space
            .write_u8(64 / 4, registers::BIST_HEAD_LAT_CACH);

        info.config_space.write_u32(
            lower_32_bits(MEM_PCIE_RANGE_PCIE_START) | PCI_BASE_ADDRESS_MEM_TYPE_64,
            registers::BAR0,
        );

        info.config_space
            .write_u32(upper_32_bits(MEM_PCIE_RANGE_PCIE_START), registers::BAR1);

        let uch_int_pin = info.get_interrupt_pin();
        if uch_int_pin != 0 {
            info.config_space.write_u8(1, PCI_INTERRUPT_PIN as usize);
        }

        let mut csr = info.read_status_command();
        csr.set(registers::StatusCommand::MEMORY_SPACE, true);
        csr.set(registers::StatusCommand::BUS_MASTER, true);
        csr.set(registers::StatusCommand::SERR_ENABLE, true);
        csr.set(registers::StatusCommand::PARITY_ERROR_RESPONSE, true);

        info.write_status_command(csr);

        Self { _info: info }
    }
}

impl PCIeDevice for RP1 {
    fn device_name(&self) -> Cow<'static, str> {
        "RASPI5 RP1".into()
    }
}
