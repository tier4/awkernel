use awkernel_lib::net::ether::ETHER_ADDR_LEN;
use bitflags::bitflags;

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(super) enum IgcMacType {
    #[default]
    Undefined,
    I225,
}

/// Because Rust does not support default derives for [u32, 128],
/// we prepare a struct to hold the array and implement `Default`.
#[derive(Debug)]
struct MtaShadow([u32; 128]);

impl Default for MtaShadow {
    fn default() -> Self {
        Self([0; 128])
    }
}

#[derive(Debug, Default)]
pub(super) struct IgcMacInfo {
    pub(super) addr: [u8; ETHER_ADDR_LEN],
    perm_addr: [u8; ETHER_ADDR_LEN],

    pub(super) mac_type: IgcMacType,

    mc_filter_type: u32,

    current_ifs_val: u16,
    ifs_max_val: u16,
    ifs_min_val: u16,
    ifs_ratio: u16,
    ifs_step_size: u16,
    pub(super) mta_reg_count: u16,
    uta_reg_count: u16,

    mta_shadow: MtaShadow,
    pub(super) rar_entry_count: u16,

    forced_speed_duplex: u8,

    pub(super) asf_firmware_present: bool,
    pub(super) autoneg: bool,
    get_link_status: bool,
    pub(super) max_frame_size: u32,
}

bitflags! {
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub(super) struct IgcFcMode: u8 {
        const None = 0;
        const RxPause = 1;
        const TxPause = 1 << 1;
        const Full = IgcFcMode::RxPause.bits() | IgcFcMode::TxPause.bits();
        const Default = 0xff;
    }
}

impl Default for IgcFcMode {
    fn default() -> Self {
        IgcFcMode::Default
    }
}

#[derive(Debug, Default)]
pub(super) struct IgcFcInfo {
    pub(super) high_water: u32,           // Flow control high-water mark
    pub(super) low_water: u32,            // Flow control low-water mark
    pub(super) pause_time: u16,           // Flow control pause timer
    refresh_time: u16,                    // Flow control refresh timer
    pub(super) send_xon: bool,            // Flow control send XON
    strict_ieee: bool,                    // Strict IEEE mode
    pub(super) current_mode: IgcFcMode,   // FC mode in effect
    pub(super) requested_mode: IgcFcMode, // FC mode requested by caller
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(super) enum IgcPhyType {
    #[default]
    Unknown,
    None,
    I225,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum IgcSmartSpeed {
    #[default]
    Default,
    On,
    Off,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(super) enum IgcMediaType {
    #[default]
    Unknown,
    Copper,
}

#[derive(Debug, Default)]
pub(super) struct IgcPhyInfo {
    pub(super) phy_type: IgcPhyType,

    smart_speed: IgcSmartSpeed,

    pub(super) addr: u32,
    pub(super) id: u32,
    pub(super) reset_delay_us: u32,
    pub(super) revision: u32,

    pub(super) media_type: IgcMediaType,

    pub(super) autoneg_advertised: u16,
    pub(super) autoneg_mask: u16,

    pub(super) mdix: u8,

    polarity_correction: bool,
    speed_downgraded: bool,
    pub(super) autoneg_wait_to_complete: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub(super) enum IgcNvmType {
    #[default]
    Unknown,
    EepromSpi,
    FlashHw,
    Invm,
}

#[derive(Debug, Default)]
pub(super) struct IgcNvmInfo {
    pub(super) nvm_type: IgcNvmType,

    pub(super) word_size: u16,
    pub(super) delay_usec: u16,
    pub(super) address_bits: u16,
    pub(super) opcode_bits: u16,
    pub(super) page_size: u16,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum IgcBusType {
    #[default]
    Unknown,
    Pci,
    PciX,
    PciExpress,
    Reserved,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum IgcBusSpeed {
    #[default]
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
enum IgcBusWidth {
    #[default]
    Unknown = 0,
    PcieX1,
    PcieX2,
    PcieX4 = 4,
    PcieX8 = 8,
    Width32,
    Width64,
    Reserved,
}

#[derive(Debug, Default)]
pub(super) struct IgcBusInfo {
    bus_type: IgcBusType,
    speed: IgcBusSpeed,
    width: IgcBusWidth,

    pub(super) func: u16,
    pci_cmd_word: u16,
}

#[derive(Debug, Default)]
pub(super) struct IgcDevSpecI225 {
    pub(super) eee_disable: bool,
    pub(super) clear_semaphore_once: bool,
    mtu: u32,
}

#[derive(Debug, Default)]
pub(super) struct IgcHw {
    pub(super) mac: IgcMacInfo,
    pub(super) fc: IgcFcInfo,
    pub(super) phy: IgcPhyInfo,
    pub(super) nvm: IgcNvmInfo,
    pub(super) bus: IgcBusInfo,

    pub(super) dev_spec: IgcDevSpecI225,

    pub(super) device_id: u16,
    subsystem_vendor_id: u16,
    subsystem_deice_id: u16,
    vendor_id: u16,

    revision_id: u8,
}

pub(super) trait IgcMacOperations {
    fn init_params(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;

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

    fn setup_link(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;

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

    /// acquire SW_FW sync
    fn acquire_swfw_sync(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        mask: u16,
    ) -> Result<(), IgcDriverErr>;

    /// release SW_FW sync
    fn release_swfw_sync(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        mask: u16,
    ) -> Result<(), IgcDriverErr>;
}

pub(super) trait IgcPhyOperations {
    fn init_params(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;

    fn acquire(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn release(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;

    /// Read the PHY management control register and check whether a PHY reset
    /// is blocked.  If a reset is not blocked return Ok(()), otherwise
    /// return Err(IgcDriverErr::BlkPhyReset).
    fn check_reset_block(&self, info: &mut PCIeInfo) -> Result<(), IgcDriverErr> {
        let manc = read_reg(info, IGC_MANC)?;

        if manc & IGC_MANC_BLK_PHY_RST_ON_IDE != 0 {
            Err(IgcDriverErr::BlkPhyReset)
        } else {
            Ok(())
        }
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
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        offset: u32,
    ) -> Result<u16, IgcDriverErr>;

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

    fn reset(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;

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
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        offset: u32,
        data: u16,
    ) -> Result<(), IgcDriverErr>;

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
    fn power_up(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn power_down(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
}

#[allow(unused_variables)]
pub(super) trait IgcNvmOperations {
    fn init_params(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;

    /// Acquire the necessary semaphores for exclusive access to the EEPROM.
    fn acquire(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;

    /// Release the semaphores acquired.
    fn release(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;

    fn read(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        offset: u16,
        words: u16,
        data: &mut [u16],
    ) -> Result<(), IgcDriverErr> {
        Ok(())
    }

    fn reload(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }
    fn update(&self, _info: &mut PCIeInfo, _hw: &mut IgcHw) -> Result<(), IgcDriverErr> {
        todo!()
    }

    fn validate(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;

    fn write(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
        offset: u16,
        words: u16,
        data: &[u16],
    ) -> Result<(), IgcDriverErr> {
        Ok(())
    }
}

pub(super) trait IgcOperations:
    IgcMacOperations + IgcPhyOperations + IgcNvmOperations
{
}
