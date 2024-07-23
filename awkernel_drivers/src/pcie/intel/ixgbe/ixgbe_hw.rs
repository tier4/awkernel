use crate::pcie::{pcie_id::IXGBE_INTEL_VENDOR_ID, PCIeInfo};

use alloc::boxed::Box;

use super::{
    ixgbe_82599, ixgbe_operations::IxgbeOperations, ixgbe_regs::*, ixgbe_x540, ixgbe_x550,
    IxgbeDriverErr,
};

pub const IXGBE_DEVICES: [(u16, u16); 74] = [
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598_BX),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598AF_DUAL_PORT),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598AF_SINGLE_PORT),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598AT),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598AT2),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598AT_DUAL_PORT),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598EB_SFP_LOM),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598EB_CX4),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598_CX4_DUAL_PORT),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598_DA_DUAL_PORT),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598_SR_DUAL_PORT_EM),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82598EB_XF_LR),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_KX4),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_KX4_MEZZ),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_KR),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_COMBO_BACKPLANE),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599_KX4_KR_MEZZ),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_CX4),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_SFP),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599_SFP),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599_SFP_WOL0),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599_RNDC),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599_560FLR),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599_ECNA_DP),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599_SP_560FLR),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599_LOM_SNAP6),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599_SFP_1OCP),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599_SFP_2OCP),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599_SFP_LOM_OEM1),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599_SFP_LOM_OEM2),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_BACKPLANE_FCOE),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_SFP_FCOE),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_SFP_EM),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_SFP_SF2),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_SFP_SF_QP),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_QSFP_SF_QP),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599EN_SFP),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_SUBDEV_ID_82599EN_SFP_OCP1),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_XAUI_LOM),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_T3_LOM),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_VF),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_VF_HV),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_82599_BYPASS),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X540T),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X540_VF),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X540_VF_HV),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X540_BYPASS),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X540T1),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550T),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550T1),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_KR),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_KR_L),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_SFP_N),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_SGMII),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_SGMII_L),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_10G_T),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_QSFP),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_QSFP_N),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_SFP),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_1G_T),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_1G_T_L),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_X_KX4),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_X_KR),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_X_SFP),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_X_10G_T),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_X_1G_T),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_X_XFI),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550_VF_HV),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550_VF),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_VF),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_A_VF_HV),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_X_VF),
    (IXGBE_INTEL_VENDOR_ID, IXGBE_DEV_ID_X550EM_X_VF_HV),
];

pub fn get_mac_type(device: u16) -> Result<MacType, IxgbeDriverErr> {
    use MacType::*;

    let result = match device {
        IXGBE_DEV_ID_82598
        | IXGBE_DEV_ID_82598_BX
        | IXGBE_DEV_ID_82598AF_SINGLE_PORT
        | IXGBE_DEV_ID_82598AF_DUAL_PORT
        | IXGBE_DEV_ID_82598AT
        | IXGBE_DEV_ID_82598AT2
        | IXGBE_DEV_ID_82598EB_CX4
        | IXGBE_DEV_ID_82598_CX4_DUAL_PORT
        | IXGBE_DEV_ID_82598_DA_DUAL_PORT
        | IXGBE_DEV_ID_82598_SR_DUAL_PORT_EM
        | IXGBE_DEV_ID_82598EB_XF_LR
        | IXGBE_DEV_ID_82598EB_SFP_LOM => IxgbeMac82598EB,
        IXGBE_DEV_ID_82599_KX4
        | IXGBE_DEV_ID_82599_KX4_MEZZ
        | IXGBE_DEV_ID_82599_XAUI_LOM
        | IXGBE_DEV_ID_82599_COMBO_BACKPLANE
        | IXGBE_DEV_ID_82599_KR
        | IXGBE_DEV_ID_82599_SFP
        | IXGBE_DEV_ID_82599_BACKPLANE_FCOE
        | IXGBE_DEV_ID_82599_SFP_FCOE
        | IXGBE_DEV_ID_82599_SFP_EM
        | IXGBE_DEV_ID_82599_SFP_SF2
        | IXGBE_DEV_ID_82599_SFP_SF_QP
        | IXGBE_DEV_ID_82599_QSFP_SF_QP
        | IXGBE_DEV_ID_82599EN_SFP
        | IXGBE_DEV_ID_82599_CX4
        | IXGBE_DEV_ID_82599_BYPASS
        | IXGBE_DEV_ID_82599_T3_LOM => IxgbeMac82599EB,
        IXGBE_DEV_ID_82599_VF | IXGBE_DEV_ID_82599_VF_HV => IxgbeMac82599Vf,
        IXGBE_DEV_ID_X540_VF | IXGBE_DEV_ID_X540_VF_HV => IxgbeMacX540Vf,
        IXGBE_DEV_ID_X540T | IXGBE_DEV_ID_X540T1 | IXGBE_DEV_ID_X540_BYPASS => IxgbeMacX540,
        IXGBE_DEV_ID_X550T | IXGBE_DEV_ID_X550T1 => IxgbeMacX550,
        IXGBE_DEV_ID_X550EM_X_KX4
        | IXGBE_DEV_ID_X550EM_X_KR
        | IXGBE_DEV_ID_X550EM_X_10G_T
        | IXGBE_DEV_ID_X550EM_X_1G_T
        | IXGBE_DEV_ID_X550EM_X_SFP
        | IXGBE_DEV_ID_X550EM_X_XFI => IxgbeMacX550EMX,
        IXGBE_DEV_ID_X550EM_A_KR
        | IXGBE_DEV_ID_X550EM_A_KR_L
        | IXGBE_DEV_ID_X550EM_A_SFP_N
        | IXGBE_DEV_ID_X550EM_A_SGMII
        | IXGBE_DEV_ID_X550EM_A_SGMII_L
        | IXGBE_DEV_ID_X550EM_A_1G_T
        | IXGBE_DEV_ID_X550EM_A_1G_T_L
        | IXGBE_DEV_ID_X550EM_A_10G_T
        | IXGBE_DEV_ID_X550EM_A_QSFP
        | IXGBE_DEV_ID_X550EM_A_QSFP_N
        | IXGBE_DEV_ID_X550EM_A_SFP => IxgbeMacX550EMA,
        IXGBE_DEV_ID_X550_VF | IXGBE_DEV_ID_X550_VF_HV => IxgbeMacX550Vf,
        IXGBE_DEV_ID_X550EM_X_VF | IXGBE_DEV_ID_X550EM_X_VF_HV => IxgbeMacX550EMXVf,
        IXGBE_DEV_ID_X550EM_A_VF | IXGBE_DEV_ID_X550EM_A_VF_HV => IxgbeMacX550EMAVf,
        _ => {
            log::debug!("ixgbe: get_mac_type UnknownDeviceId");
            return Err(IxgbeDriverErr::UnknownDeviceID);
        }
    };
    Ok(result)
}

pub const IXGBE_MAX_MTA: usize = 128;

#[derive(Debug, Clone, Copy)]
pub struct IxgbeMacInfo {
    pub mac_type: MacType,
    pub addr: [u8; IXGBE_ETH_LENGTH_OF_ADDRESS],
    pub perm_addr: [u8; IXGBE_ETH_LENGTH_OF_ADDRESS],
    pub mc_filter_type: i32,
    pub mta_shadow: [u32; IXGBE_MAX_MTA],
    pub mcft_size: u32,
    pub vft_size: u32,
    pub num_rar_entries: u32,
    pub rx_pb_size: u32,
    pub max_rx_queues: u32,
    pub max_tx_queues: u32,
    pub orig_autoc: u32,
    pub orig_autoc2: u32,
    pub max_msix_vectors: u16,
    pub arc_subsystem_valid: bool,
    pub orig_link_settings_stored: bool,
    pub autotry_restart: bool,
    pub flags: u8,
    pub set_lben: bool,
    pub max_link_up_time: u32,
}

pub struct IxgbeAddrFilterInfo {
    pub num_mc_addrs: u32,
    pub rar_used_count: u32,
    pub mta_in_use: u32,
    pub overflow_promisc: u32,
    pub user_set_promisc: bool,
}

pub struct IxgbeFcInfo {
    pub high_water: [u32; IXGBE_DCB_MAX_TRAFFIC_CLASS], // Flow Ctrl High-water
    pub low_water: [u32; IXGBE_DCB_MAX_TRAFFIC_CLASS],  // Flow Ctrl Low-water
    pub pause_time: u16,                                // Flow Control Pause timer
    pub send_xon: bool,                                 // Flow control send XON
    pub strict_ieee: bool,                              // Strict IEEE mode
    pub disable_fc_autoneg: bool,                       // Do not autonegotiate FC
    pub fc_was_autonegged: bool, // Is current_mode the result of autonegging?
    pub current_mode: FcMode,    // FC mode in effect
    pub requested_mode: FcMode,  // FC mode requested by caller
}

pub struct IxgbePhyInfo {
    pub phy_type: PhyType,
    pub addr: u32,
    pub id: u32,
    pub sfp_type: SfpType,
    pub sfp_setup_needed: bool,
    pub revision: u32,
    pub media_type: MediaType,
    pub phy_semaphore_mask: u32,
    // pub reset_disable: bool, Unused in OpenBSD/FreeBSD
    pub autoneg_advertised: u32,
    pub speeds_supported: u32,
    pub smart_speed: SmartSpeed,
    pub smart_speed_active: bool,
    pub multispeed_fiber: bool,
    pub qsfp_shared_i2c_bus: bool,
    pub nw_mng_if_sel: u32,
    // pub reset_if_overtemp: bool, Unused in OpenBSD/FreeBSD
    pub no_reset: bool,
}

#[derive(Debug, Clone, Copy)]
pub struct IxgbeEepromInfo {
    pub eeprom_type: EepromType,
    pub semaphore_delay: u32,
    pub word_size: u16,
    pub address_bits: u16,
    pub word_page_size: u16,
    pub ctrl_word_3: u16,
}

pub struct IxgbeBusInfo {
    pub speed: BusSpeed,
    pub width: BusWidth,
    pub bus_type: BusType,
    pub func: u16,
    pub lan_id: u8,
    pub instance_id: u16,
}

pub struct IxgbeHw {
    pub mac: IxgbeMacInfo,
    pub addr_ctrl: IxgbeAddrFilterInfo,
    pub fc: IxgbeFcInfo,
    pub phy: IxgbePhyInfo,
    pub eeprom: IxgbeEepromInfo,
    pub bus: IxgbeBusInfo,
    pub adapter_stopped: bool,
    // pub force_full_reset: bool, Unused in OpenBSD/FreeBSD
    // pub wol_enabled: bool, Unused in OpenBSD/FreeBSD
    pub crosstalk_fix: bool,
}

impl IxgbeHw {
    pub fn new(info: &mut PCIeInfo) -> Result<(Self, Box<dyn IxgbeOperations>), IxgbeDriverErr> {
        use MacType::*;

        let mac_type = get_mac_type(info.get_id())?;

        // Doesn't seem to require check_pci_express since all the ixgbe devices support PCI Express
        // https://github.com/openbsd/src/blob/82673a188a32931f4005a3ede8f05d97542feb17/sys/dev/pci/ixgbe.c#L715

        // TODO: Need to set ixgbe_smart_speed for 82599EB
        // ⇔ OpenBSD ixgbe_identify_hardware()

        // TODO: sc->mta = mallocarray() : Allocate multicast array memory -> IxgbeInner new()?

        // let hardware know driver is loaded
        let mut ctrl_ext = read_reg(info, IXGBE_CTRL_EXT)?;
        ctrl_ext |= IXGBE_CTRL_EXT_DRV_LOAD;
        write_reg(info, IXGBE_CTRL_EXT, ctrl_ext)?;

        let ops = get_operations(&mac_type)?; // init_shared_code();
        let (
            mcft_size,
            vft_size,
            num_rar_entries,
            rx_pb_size,
            max_rx_queues,
            max_tx_queues,
            max_msix_vectors,
            arc_subsystem_valid,
        ) = match mac_type {
            IxgbeMac82599EB => ixgbe_82599::set_mac_val(info)?,
            IxgbeMacX540 => ixgbe_x540::set_mac_val(info)?,
            IxgbeMacX550 => ixgbe_x550::set_mac_val(info)?,
            _ => (0, 0, 0, 0, 0, 0, 0, false),
        };
        let max_link_up_time = IXGBE_LINK_UP_TIME;

        let eeprom = ops.eeprom_validate_checksum(info)?;

        log::debug!("validate_checksum done!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");

        Ok((
            Self {
                mac: IxgbeMacInfo {
                    mac_type,
                    addr: [0; IXGBE_ETH_LENGTH_OF_ADDRESS],
                    perm_addr: [0; IXGBE_ETH_LENGTH_OF_ADDRESS],
                    mta_shadow: [0; IXGBE_MAX_MTA],
                    mc_filter_type: 0,
                    mcft_size,
                    vft_size,
                    num_rar_entries,
                    rx_pb_size,
                    max_rx_queues,
                    max_tx_queues,
                    orig_autoc: 0, //TODO: Need to check if this is initialized in FreeBSD
                    orig_autoc2: 0,
                    max_msix_vectors,
                    arc_subsystem_valid,
                    orig_link_settings_stored: false,
                    autotry_restart: false,
                    flags: 0,
                    set_lben: false,
                    max_link_up_time,
                },
                addr_ctrl: IxgbeAddrFilterInfo {
                    num_mc_addrs: 0,
                    rar_used_count: 0,
                    mta_in_use: 0,
                    overflow_promisc: 0,
                    user_set_promisc: false,
                },
                fc: IxgbeFcInfo {
                    // TODO: Need to check if this is initialized in OpenBSD
                    high_water: [0; IXGBE_DCB_MAX_TRAFFIC_CLASS],
                    low_water: [0; IXGBE_DCB_MAX_TRAFFIC_CLASS],
                    pause_time: 0,
                    send_xon: false,
                    strict_ieee: false, // TODO: Need to check if this is initialized in OpenBSD
                    disable_fc_autoneg: false,
                    fc_was_autonegged: false,
                    current_mode: FcMode::IxgbeFcNone,
                    requested_mode: FcMode::IxgbeFcNone, // TODO: Need to check if this is initialized in OpenB
                },
                phy: IxgbePhyInfo {
                    phy_type: PhyType::IxgbePhyUnknown,
                    addr: 0,
                    id: 0,
                    sfp_type: SfpType::IxgbeSfpTypeUnknown,
                    sfp_setup_needed: false,
                    revision: 0,
                    media_type: MediaType::IxgbeMediaTypeUnknown,
                    phy_semaphore_mask: 0,
                    autoneg_advertised: IXGBE_LINK_SPEED_UNKNOWN,
                    speeds_supported: IXGBE_LINK_SPEED_UNKNOWN,
                    smart_speed: SmartSpeed::IxgbeSmartSpeedAuto,
                    smart_speed_active: false,
                    multispeed_fiber: false,
                    qsfp_shared_i2c_bus: false,
                    nw_mng_if_sel: 0, // TODO: Need to check if this is initialized in OpenBSD
                    no_reset: false,
                },
                eeprom,
                bus: IxgbeBusInfo {
                    speed: BusSpeed::IxgbeBusSpeedUnknown,
                    width: BusWidth::IxgbeBusWidthUnknown,
                    bus_type: BusType::IxgbeBusTypeUnknown,
                    func: 0,
                    lan_id: 0,
                    instance_id: 0,
                }, // TODO: Need to check if this is initialized in OpenBSD
                adapter_stopped: false,
                crosstalk_fix: false,
            },
            ops,
        ))
    }

    #[inline(always)]
    pub fn get_mac_type(&self) -> MacType {
        self.mac.mac_type
    }

    pub fn get_mac_addr(&self) -> [u8; IXGBE_ETH_LENGTH_OF_ADDRESS] {
        self.mac.addr
    }

    pub fn get_media_type(&self) -> MediaType {
        self.phy.media_type
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum EepromType {
    IxgbeEepromUninitialized = 0,
    IxgbeEepromSpi,
    IxgbeFlash,
    IxgbeEepromNone, /* No NVM support */
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum MacType {
    IxgbeMac82598EB = 0,
    IxgbeMac82599EB,
    IxgbeMac82599Vf,
    IxgbeMacX540,
    IxgbeMacX540Vf,
    IxgbeMacX550,
    IxgbeMacX550EMX,
    IxgbeMacX550EMA,
    IxgbeMacX550Vf,
    IxgbeMacX550EMXVf,
    IxgbeMacX550EMAVf,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum PhyType {
    IxgbePhyUnknown = 0,
    IxgbePhyNone,
    IxgbePhyTn,
    IxgbePhyAq,
    IxgbePhyX550emKr,
    IxgbePhyX550emKx4,
    IxgbePhyX550emXfi,
    IxgbePhyX550emExtT,
    IxgbePhyExt1gT,
    IxgbePhyCuUnknown,
    IxgbePhyQt,
    IxgbePhyXaui,
    IxgbePhyNl,
    IxgbePhySfpPassiveTyco,
    IxgbePhySfpPassiveUnknown,
    IxgbePhySfpActiveUnknown,
    IxgbePhySfpAvago,
    IxgbePhySfpFtl,
    IxgbePhySfpFtlActive,
    IxgbePhySfpUnknown,
    IxgbePhySfpIntel,
    IxgbePhyQsfpPassiveUnknown,
    IxgbePhyQsfpActiveUnknown,
    IxgbePhyQsfpIntel,
    IxgbePhyQsfpUnknown,
    IxgbePhySfpUnsupported, /*Enforce bit set with unsupported module*/
    IxgbePhySgmii,
    IxgbePhyFw,
    IxgbePhyGeneric,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum SfpType {
    IxgbeSfpTypeDaCu = 0,
    IxgbeSfpTypeSr = 1,
    IxgbeSfpTypeLr = 2,
    IxgbeSfpTypeDaCuCore0 = 3,
    IxgbeSfpTypeDaCuCore1 = 4,
    IxgbeSfpTypeSrlrCore0 = 5,
    IxgbeSfpTypeSrlrCore1 = 6,
    IxgbeSfpTypeDaActLmtCore0 = 7,
    IxgbeSfpTypeDaActLmtCore1 = 8,
    IxgbeSfpType1gCuCore0 = 9,
    IxgbeSfpType1gCuCore1 = 10,
    IxgbeSfpType1gSxCore0 = 11,
    IxgbeSfpType1gSxCore1 = 12,
    IxgbeSfpType1gLxCore0 = 13,
    IxgbeSfpType1gLxCore1 = 14,
    IxgbeSfpTypeNotPresent = 0xFFFE,
    IxgbeSfpTypeUnknown = 0xFFFF,
}

impl TryFrom<u16> for SfpType {
    type Error = IxgbeDriverErr;

    fn try_from(value: u16) -> Result<SfpType, IxgbeDriverErr> {
        use SfpType::*;

        match value {
            0 => Ok(IxgbeSfpTypeDaCu),
            1 => Ok(IxgbeSfpTypeSr),
            2 => Ok(IxgbeSfpTypeLr),
            3 => Ok(IxgbeSfpTypeDaCuCore0),
            4 => Ok(IxgbeSfpTypeDaCuCore1),
            5 => Ok(IxgbeSfpTypeSrlrCore0),
            6 => Ok(IxgbeSfpTypeSrlrCore1),
            7 => Ok(IxgbeSfpTypeDaActLmtCore0),
            8 => Ok(IxgbeSfpTypeDaActLmtCore1),
            9 => Ok(IxgbeSfpType1gCuCore0),
            10 => Ok(IxgbeSfpType1gCuCore1),
            11 => Ok(IxgbeSfpType1gSxCore0),
            12 => Ok(IxgbeSfpType1gSxCore1),
            13 => Ok(IxgbeSfpType1gLxCore0),
            14 => Ok(IxgbeSfpType1gLxCore1),
            0xFFFE => Ok(IxgbeSfpTypeNotPresent),
            0xFFFF => Ok(IxgbeSfpTypeUnknown),
            _ => Err(IxgbeDriverErr::NotSupported),
        }
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum MediaType {
    IxgbeMediaTypeUnknown = 0,
    IxgbeMediaTypeFiber,
    IxgbeMediaTypeFiberFixed,
    IxgbeMediaTypeFiberQsfp,
    IxgbeMediaTypeCopper,
    IxgbeMediaTypeBackplane,
    IxgbeMediaTypeCx4,
    IxgbeMediaTypeVirtual,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum SmartSpeed {
    IxgbeSmartSpeedAuto = 0,
    IxgbeSmartSpeedOn,
    IxgbeSmartSpeedOff,
}

// Flow Control Settings
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum FcMode {
    IxgbeFcNone = 0,
    IxgbeFcRxPause,
    IxgbeFcTxPause,
    IxgbeFcFull,
    IxgbeFcDefault,
}

// PCI bus types
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum BusType {
    IxgbeBusTypeUnknown = 0,
    IxgbeBusTypePci,
    IxgbeBusTypePcix,
    IxgbeBusTypePciExpress,
    IxgbeBusTypeInternal,
    IxgbeBusTypeReserved,
}

// PCI bus speeds
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum BusSpeed {
    IxgbeBusSpeedUnknown = 0,
    IxgbeBusSpeed33 = 33,
    IxgbeBusSpeed66 = 66,
    IxgbeBusSpeed100 = 100,
    IxgbeBusSpeed120 = 120,
    IxgbeBusSpeed133 = 133,
    IxgbeBusSpeed2500 = 2500,
    IxgbeBusSpeed5000 = 5000,
    IxgbeBusSpeed8000 = 8000,
    IxgbeBusSpeedReserved,
}

// PCI bus widths
#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum BusWidth {
    IxgbeBusWidthUnknown = 0,
    IxgbeBusWidthPcieX1 = 1,
    IxgbeBusWidthPcieX2 = 2,
    IxgbeBusWidthPcieX4 = 4,
    IxgbeBusWidthPcieX8 = 8,
    IxgbeBusWidth32 = 32,
    IxgbeBusWidth64 = 64,
    IxgbeBusWidthReserved,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd)]
pub enum LinkState {
    LinkStateUnown = 0,  /* link unknown */
    LinkStateInvalid,    /* link invalid */
    LinkStateDown,       /* link is down */
    LinkStateKaliveDown, /* keepalive reports down */
    LinkStateUp,         /* link is up */
    LinkStateHalfDuplex, /* link is up and half duplex */
    LinkStateFullDuplex, /* link is up and full duplex */
}

#[inline(always)]
pub fn write_reg(info: &PCIeInfo, offset: usize, value: u32) -> Result<(), IxgbeDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IxgbeDriverErr::NoBar0)?;
    bar0.write32(offset, value);
    Ok(())
}

#[inline(always)]
pub fn write_reg_array(
    info: &PCIeInfo,
    offset: usize,
    index: usize,
    value: u32,
) -> Result<(), IxgbeDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IxgbeDriverErr::NoBar0)?;
    bar0.write32(offset + (index << 2), value);
    Ok(())
}
#[inline(always)]
pub fn read_reg(info: &PCIeInfo, offset: usize) -> Result<u32, IxgbeDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IxgbeDriverErr::NoBar0)?;
    bar0.read32(offset).ok_or(IxgbeDriverErr::ReadFailure)
}

#[inline(always)]
pub fn read_reg_array(info: &PCIeInfo, offset: usize, index: usize) -> Result<u32, IxgbeDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IxgbeDriverErr::NoBar0)?;
    bar0.read32(offset + (index << 2))
        .ok_or(IxgbeDriverErr::ReadFailure)
}

#[inline(always)]
pub fn write_flush(info: &PCIeInfo) -> Result<(), IxgbeDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IxgbeDriverErr::NoBar0)?;
    bar0.read32(IXGBE_STATUS)
        .ok_or(IxgbeDriverErr::ReadFailure)?;
    Ok(())
}

fn get_operations(mac_type: &MacType) -> Result<Box<dyn IxgbeOperations>, IxgbeDriverErr> {
    match mac_type {
        MacType::IxgbeMac82599EB => Ok(ixgbe_82599::get_self()),
        MacType::IxgbeMacX540 => Ok(ixgbe_x540::get_self()),
        MacType::IxgbeMacX550 => Ok(ixgbe_x550::get_self()),
        _ => Err(IxgbeDriverErr::NotImplemented),
    }
}

pub fn get_num_queues(mac_type: &MacType) -> usize {
    match mac_type {
        MacType::IxgbeMac82598EB => 8,
        _ => 16,
    }
}
