use awkernel_lib::net::ether::ETHER_ADDR_LEN;

use crate::pcie::{pcie_id::INTEL_VENDOR_ID, PCIeInfo};

use super::IgcDriverErr;

const PCI_PRODUCT_INTEL_I220_V: u16 = 0x15f7; // I220-V
const PCI_PRODUCT_INTEL_I221_V: u16 = 0x125e; // I221-V
const PCI_PRODUCT_INTEL_I225_BLANK_NVM: u16 = 0x15fd; // I225
const PCI_PRODUCT_INTEL_I225_I: u16 = 0x15f8; // I225-I
const PCI_PRODUCT_INTEL_I225_IT: u16 = 0x0d9f; // I225-IT
const PCI_PRODUCT_INTEL_I225_K: u16 = 0x3100; // I225-K
const PCI_PRODUCT_INTEL_I225_K2: u16 = 0x3101; // I225-K2
const PCI_PRODUCT_INTEL_I225_LM: u16 = 0x15f2; // I225-LM
const PCI_PRODUCT_INTEL_I225_LMVP: u16 = 0x5502; // I225-LMvP
const PCI_PRODUCT_INTEL_I225_V: u16 = 0x15f3; // I225-V
const PCI_PRODUCT_INTEL_I226_BLANK_NVM: u16 = 0x125f; // I226
const PCI_PRODUCT_INTEL_I226_IT: u16 = 0x125d; // I226-IT
const PCI_PRODUCT_INTEL_I226_LM: u16 = 0x125b; // I226-LM
const PCI_PRODUCT_INTEL_I226_K: u16 = 0x5504; // I226-K
const PCI_PRODUCT_INTEL_I226_V: u16 = 0x125c; // I226-V

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
enum IgcMacType {
    Undefined,
    I225,
}

#[derive(Debug)]
struct IgcMacInfo {
    addr: [u8; ETHER_ADDR_LEN],
    perm_addr: [u8; ETHER_ADDR_LEN],

    mac_type: IgcMacType,

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
    Unknown,
    PcieX1,
    PcieX2,
    PcieX4,
    PcieX8,
    Width32,
    Width64,
    Reserved,
}

#[derive(Debug)]
struct IgcBusInfo {
    bus_type: IgcBusType,
    speed: IgcBusSpeed,
    width: IgcBusWidth,

    func: u16,
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
    mac: IgcMacInfo,
    fc: IgcFcInfo,
    phy: IgcPhyInfo,
    nvm: IgcNvmInfo,
    bus: IgcBusInfo,

    dev_spec: IgcDevSpecI225,

    device_id: u16,
    subsystem_vendor_id: u16,
    subsystem_deice_id: u16,
    vendor_id: u16,

    revision_id: u8,
}

pub(super) trait IgcMacOperations {
    fn init_params(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn check_for_link(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn clear_hw_cntrs(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn clear_vfta(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn get_bus_info(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn set_lan_id(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn get_link_up_info(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn update_mc_addr_list(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn reset_hw(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn init_hw(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn setup_link(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn setup_physical_interface(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
    ) -> Result<(), IgcDriverErr>;
    fn write_vfta(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn config_collision_dist(
        &self,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
    ) -> Result<(), IgcDriverErr>;
    fn rar_set(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn read_mac_addr(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn validate_mdi_setting(&self, info: &mut PCIeInfo, hw: &mut IgcHw)
        -> Result<(), IgcDriverErr>;
    fn acquire_sffw_sync(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
    fn release_sffw_sync(&self, info: &mut PCIeInfo, hw: &mut IgcHw) -> Result<(), IgcDriverErr>;
}
