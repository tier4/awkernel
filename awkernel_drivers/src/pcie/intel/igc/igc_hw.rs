use awkernel_lib::net::ether::ETHER_ADDR_LEN;

use crate::pcie::{
    intel::igc::{igc_defines::*, igc_regs::*, read_reg, write_reg, write_reg_array},
    pcie_id::INTEL_VENDOR_ID,
    PCIeInfo,
};

use super::{write_flush, IgcDriverErr};

pub(super) const IGC_FUNC_1: u16 = 1;

pub(super) const IGC_ALT_MAC_ADDRESS_OFFSET_LAN1: u16 = 3;

pub(super) const PCI_PRODUCT_INTEL_I220_V: u16 = 0x15f7; // I220-V
pub(super) const PCI_PRODUCT_INTEL_I221_V: u16 = 0x125e; // I221-V
pub(super) const PCI_PRODUCT_INTEL_I225_BLANK_NVM: u16 = 0x15fd; // I225
pub(super) const PCI_PRODUCT_INTEL_I225_I: u16 = 0x15f8; // I225-I
pub(super) const PCI_PRODUCT_INTEL_I225_IT: u16 = 0x0d9f; // I225-IT
pub(super) const PCI_PRODUCT_INTEL_I225_K: u16 = 0x3100; // I225-K
pub(super) const PCI_PRODUCT_INTEL_I225_K2: u16 = 0x3101; // I225-K2
pub(super) const PCI_PRODUCT_INTEL_I225_LM: u16 = 0x15f2; // I225-LM
pub(super) const PCI_PRODUCT_INTEL_I225_LMVP: u16 = 0x5502; // I225-LMvP
pub(super) const PCI_PRODUCT_INTEL_I225_V: u16 = 0x15f3; // I225-V
pub(super) const PCI_PRODUCT_INTEL_I226_BLANK_NVM: u16 = 0x125f; // I226
pub(super) const PCI_PRODUCT_INTEL_I226_IT: u16 = 0x125d; // I226-IT
pub(super) const PCI_PRODUCT_INTEL_I226_LM: u16 = 0x125b; // I226-LM
pub(super) const PCI_PRODUCT_INTEL_I226_K: u16 = 0x5504; // I226-K
pub(super) const PCI_PRODUCT_INTEL_I226_V: u16 = 0x125c; // I226-V

pub const IGC_DEVICES: [(u16, u16); 15] = [
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I220_V),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I221_V),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I225_BLANK_NVM),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I225_I),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I225_IT),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I225_K),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I225_K2),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I225_LM),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I225_LMVP),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I225_V),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I226_BLANK_NVM),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I226_IT),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I226_LM),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I226_K),
    (INTEL_VENDOR_ID, PCI_PRODUCT_INTEL_I226_V),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum IgcMacType {
    Undefined,
    I225,
}

#[derive(Debug)]
pub(super) struct IgcMacInfo {
    addr: [u8; ETHER_ADDR_LEN],
    perm_addr: [u8; ETHER_ADDR_LEN],

    pub(super) mac_type: IgcMacType,

    mc_filter_type: u32,

    current_ifs_val: u16,
    ifs_max_val: u16,
    ifs_min_val: u16,
    ifs_ratio: u16,
    ifs_step_size: u16,
    mta_reg_count: u16,
    uta_reg_count: u16,

    mta_shadow: [u32; 128],
    rar_entry_count: u16,

    forced_speed_duplex: u8,

    asf_firmware_present: bool,
    autoneg: bool,
    get_link_status: bool,
    max_frame_size: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IgcFcMode {
    None,
    RxPause,
    TxPause,
    Full,
    Default,
}

#[derive(Debug)]
struct IgcFcInfo {
    high_water: u32,           // Flow control high-water mark
    low_water: u32,            // Flow control low-water mark
    pause_time: u16,           // Flow control pause timer
    refresh_time: u16,         // Flow control refresh timer
    send_xon: bool,            // Flow control send XON
    strict_ieee: bool,         // Strict IEEE mode
    current_mode: IgcFcMode,   // FC mode in effect
    requested_mode: IgcFcMode, // FC mode requested by caller
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IgcPhyType {
    Unknown,
    None,
    I225,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IgcSmartSpeed {
    Default,
    On,
    Off,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IgcMediaType {
    Unknown,
    Copper,
}

#[derive(Debug)]
struct IgcPhyInfo {
    phy_type: IgcPhyType,

    smart_speed: IgcSmartSpeed,

    addr: u32,
    id: u32,
    reset_delay_us: u32,
    revision: u32,

    media_type: IgcMediaType,

    autoneg_advertised: u16,
    autoneg_mask: u16,

    mdix: u8,

    polarity_correction: bool,
    speed_downgraded: bool,
    autoneg_wait_to_complete: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IgcNvmType {
    Unknown,
    EepromSpi,
    FlashHw,
    Invm,
}

#[derive(Debug)]
struct IgcNvmInfo {
    nvm_type: IgcNvmType,

    word_size: u16,
    delay_usec: u16,
    address_bits: u16,
    opcode_bits: u16,
    page_size: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IgcBusType {
    Unknown,
    Pci,
    PciX,
    PciExpress,
    Reserved,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IgcBusSpeed {
    Unknown,
    Speed33,
    Speed66,
    Speed100,
    Speed120,
    Speed133,
    Speed2500,
    Speed5000,
    Reserved,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IgcBusWidth {
    Unknown = 0,
    PcieX1,
    PcieX2,
    PcieX4 = 4,
    PcieX8 = 8,
    Width32,
    Width64,
    Reserved,
}

#[derive(Debug)]
pub(super) struct IgcBusInfo {
    bus_type: IgcBusType,
    speed: IgcBusSpeed,
    width: IgcBusWidth,

    pub(super) func: u16,
    pci_cmd_word: u16,
}

#[derive(Debug)]
struct IgcDevSpecI225 {
    eee_disable: bool,
    clear_semaphore_once: bool,
    mtu: u32,
}

#[derive(Debug)]
pub(super) struct IgcHw {
    pub(super) mac: IgcMacInfo,
    fc: IgcFcInfo,
    phy: IgcPhyInfo,
    nvm: IgcNvmInfo,
    pub(super) bus: IgcBusInfo,

    dev_spec: IgcDevSpecI225,

    pub(super) device_id: u16,
    subsystem_vendor_id: u16,
    subsystem_deice_id: u16,
    vendor_id: u16,

    revision_id: u8,
}

pub(super) trait IgcMacOperations {
    fn init_params(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        Ok(())
    }

    fn check_for_link(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn get_link_up_info(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn update_mc_addr_list(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
    ) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn reset_hw(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn init_hw(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn setup_link(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn setup_physical_interface(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
    ) -> Result<(), IgcDriverErr> {
        todo!()
    }

    /// Writes value at the given offset in the register array which stores
    /// the VLAN filter table.
    fn write_vfta(
        &self,
        info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        offset: usize,
        value: u32,
    ) -> Result<(), IgcDriverErr> {
        write_reg_array(info, IGC_VFTA, offset, value)?;
        write_flush(info)?;
        Ok(())
    }

    ///  Configures the collision distance to the default value and is used
    ///  during link setup.
    fn config_collision_dist(
        &self,
        info: &mut PCIeInfo,
        _hw: &mut IgcHw,
    ) -> Result<(), IgcDriverErr> {
        let mut tctl = read_reg(info, IGC_TCTL)?;

        tctl &= !IGC_TCTL_COLD;
        tctl |= IGC_COLLISION_DISTANCE << IGC_COLD_SHIFT;

        write_reg(info, IGC_TCTL, tctl)?;
        write_flush(info)?;

        Ok(())
    }

    /// Sets the receive address array register at index to the address passed
    /// in by addr.
    fn rar_set(
        &self,
        info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        addr: &[u8],
        index: usize,
    ) -> Result<(), IgcDriverErr> {
        // HW expects these in little endian so we reverse the byte order
        // from network order (big endian) to little endian
        let rar_low = (addr[0] as u32)
            | ((addr[1] as u32) << 8)
            | ((addr[2] as u32) << 16)
            | ((addr[3] as u32) << 24);

        let mut rar_high = (addr[4] as u32) | (addr[5] as u32) << 8;

        // If MAC address zero, no need to set the AV bit
        if rar_low != 0 || rar_high != 0 {
            rar_high |= IGC_RAH_AV;
        }

        // Some bridges will combine consecutive 32-bit writes into
        // a single burst write, which will malfunction on some parts.
        // The flushes avoid this.
        write_reg(info, IGC_RAL(index), rar_low)?;
        write_flush(info)?;
        write_reg(info, IGC_RAH(index), rar_high)?;
        write_flush(info)?;

        Ok(())
    }

    /// Reads the device MAC address from the EEPROM and stores the value.
    /// Since devices with two ports use the same EEPROM, we increment the
    /// last bit in the MAC address for the second port.
    fn read_mac_addr(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        let rar_high = read_reg(info, IGC_RAH(0))?;
        let rar_low = read_reg(info, IGC_RAL(0))?;

        for i in 0..IGC_RAL_MAC_ADDR_LEN {
            hw.mac.perm_addr[i] = (rar_low >> (i * 8)) as u8;
        }

        for i in 0..IGC_RAH_MAC_ADDR_LEN {
            hw.mac.perm_addr[i + 4] = (rar_high >> (i * 8)) as u8;
        }

        for i in 0..ETHER_ADDR_LEN {
            hw.mac.addr[i] = hw.mac.perm_addr[i];
        }

        Ok(())
    }
    fn acquire_swfw_sync(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn release_swfw_sync(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
}

pub(super) trait IgcPhyOperations {
    fn init_params(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn acquire(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn check_reset_block(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn force_speed_duplex(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
    ) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn get_info(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn set_page(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        _page: u16,
    ) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn read_reg(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        _offset: u32,
    ) -> Result<u16, IgcDriverErr> {
        todo!()
    }
    fn read_reg_locked(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        _offset: u32,
    ) -> Result<u16, IgcDriverErr> {
        todo!()
    }
    fn read_reg_page(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        _offset: u32,
    ) -> Result<u16, IgcDriverErr> {
        todo!()
    }
    fn release(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn reset(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn set_d0_lplu_state(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        _active: bool,
    ) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn set_d3_lplu_state(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        _active: bool,
    ) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn write_reg(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        _offset: u32,
        _data: u32,
    ) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn write_reg_locked(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        _offset: u32,
        _data: u32,
    ) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn write_reg_page(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        _offset: u32,
        _data: u32,
    ) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn power_up(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn power_down(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
}

pub(super) trait IgcNvmOperations {
    fn init_params(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn acquire(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn read(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        _offset: u16,
        _words: u16,
        _data: &mut [u16],
    ) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn release(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn reload(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn update(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn validate(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn write(
        &self,
        _info: &mut PCIeInfo,
        _hw: &mut IgcHw,
        _offset: u16,
        _words: u16,
        _data: &[u16],
    ) -> Result<(), IgcDriverErr> {
        todo!()
    }
}

pub(super) trait IgcOperations:
    IgcMacOperations + IgcPhyOperations + IgcNvmOperations
{
}
