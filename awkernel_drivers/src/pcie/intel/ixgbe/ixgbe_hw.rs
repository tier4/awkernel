use awkernel_lib::{
    addr::{virt_addr::VirtAddr, Addr},
    net::ether::{ETHER_CRC_LEN, ETHER_MAX_LEN, ETHER_MIN_LEN, MAX_JUMBO_FRAME_SIZE},
};
use bitflags::bitflags;

use crate::pcie::{pcie_id::IXGBE_INTEL_VENDOR_ID, BaseAddress, PCIeInfo};

use alloc::boxed::Box;

use super::{
    ixgbe_operations::IxgbeOperations, ixgbe_regs::*, ixgbe_x540, ixgbe_x540::IxgbeX540,
    IxgbeDriverErr,
};

const IXGBE_DEV_ID_82598: u16 = 0x10B6;
const IXGBE_DEV_ID_82598_BX: u16 = 0x1508;
const IXGBE_DEV_ID_82598AF_DUAL_PORT: u16 = 0x10C6;
const IXGBE_DEV_ID_82598AF_SINGLE_PORT: u16 = 0x10C7;
const IXGBE_DEV_ID_82598AT: u16 = 0x10C8;
const IXGBE_DEV_ID_82598AT2: u16 = 0x150B;
const IXGBE_DEV_ID_82598AT_DUAL_PORT: u16 = 0x10D7;
const IXGBE_DEV_ID_82598EB_SFP_LOM: u16 = 0x10DB;
const IXGBE_DEV_ID_82598EB_CX4: u16 = 0x10DD;
const IXGBE_DEV_ID_82598_CX4_DUAL_PORT: u16 = 0x10EC;
const IXGBE_DEV_ID_82598_DA_DUAL_PORT: u16 = 0x10F1;
const IXGBE_DEV_ID_82598_SR_DUAL_PORT_EM: u16 = 0x10E1;
const IXGBE_DEV_ID_82598EB_XF_LR: u16 = 0x10F4;
const IXGBE_DEV_ID_82599_KX4: u16 = 0x10F7;
const IXGBE_DEV_ID_82599_KX4_MEZZ: u16 = 0x1514;
const IXGBE_DEV_ID_82599_KR: u16 = 0x1517;
const IXGBE_DEV_ID_82599_COMBO_BACKPLANE: u16 = 0x10F8;
const IXGBE_SUBDEV_ID_82599_KX4_KR_MEZZ: u16 = 0x000C;
const IXGBE_DEV_ID_82599_CX4: u16 = 0x10F9;
const IXGBE_DEV_ID_82599_SFP: u16 = 0x10FB;
const IXGBE_SUBDEV_ID_82599_SFP: u16 = 0x11A9;
const IXGBE_SUBDEV_ID_82599_SFP_WOL0: u16 = 0x1071;
const IXGBE_SUBDEV_ID_82599_RNDC: u16 = 0x1F72;
const IXGBE_SUBDEV_ID_82599_560FLR: u16 = 0x17D0;
const IXGBE_SUBDEV_ID_82599_ECNA_DP: u16 = 0x0470;
const IXGBE_SUBDEV_ID_82599_SP_560FLR: u16 = 0x211B;
const IXGBE_SUBDEV_ID_82599_LOM_SNAP6: u16 = 0x2159;
const IXGBE_SUBDEV_ID_82599_SFP_1OCP: u16 = 0x000D;
const IXGBE_SUBDEV_ID_82599_SFP_2OCP: u16 = 0x0008;
const IXGBE_SUBDEV_ID_82599_SFP_LOM_OEM1: u16 = 0x8976;
const IXGBE_SUBDEV_ID_82599_SFP_LOM_OEM2: u16 = 0x06EE;
const IXGBE_DEV_ID_82599_BACKPLANE_FCOE: u16 = 0x152A;
const IXGBE_DEV_ID_82599_SFP_FCOE: u16 = 0x1529;
const IXGBE_DEV_ID_82599_SFP_EM: u16 = 0x1507;
const IXGBE_DEV_ID_82599_SFP_SF2: u16 = 0x154D;
const IXGBE_DEV_ID_82599_SFP_SF_QP: u16 = 0x154A;
const IXGBE_DEV_ID_82599_QSFP_SF_QP: u16 = 0x1558;
const IXGBE_DEV_ID_82599EN_SFP: u16 = 0x1557;
const IXGBE_SUBDEV_ID_82599EN_SFP_OCP1: u16 = 0x0001;
const IXGBE_DEV_ID_82599_XAUI_LOM: u16 = 0x10FC;
const IXGBE_DEV_ID_82599_T3_LOM: u16 = 0x151C;
const IXGBE_DEV_ID_82599_VF: u16 = 0x10ED;
const IXGBE_DEV_ID_82599_VF_HV: u16 = 0x152E;
const IXGBE_DEV_ID_82599_BYPASS: u16 = 0x155D;
const IXGBE_DEV_ID_X540T: u16 = 0x1528;
const IXGBE_DEV_ID_X540_VF: u16 = 0x1515;
const IXGBE_DEV_ID_X540_VF_HV: u16 = 0x1530;
const IXGBE_DEV_ID_X540_BYPASS: u16 = 0x155C;
const IXGBE_DEV_ID_X540T1: u16 = 0x1560;
const IXGBE_DEV_ID_X550T: u16 = 0x1563;
const IXGBE_DEV_ID_X550T1: u16 = 0x15D1;
const IXGBE_DEV_ID_X550EM_A_KR: u16 = 0x15C2;
const IXGBE_DEV_ID_X550EM_A_KR_L: u16 = 0x15C3;
const IXGBE_DEV_ID_X550EM_A_SFP_N: u16 = 0x15C4;
const IXGBE_DEV_ID_X550EM_A_SGMII: u16 = 0x15C6;
const IXGBE_DEV_ID_X550EM_A_SGMII_L: u16 = 0x15C7;
const IXGBE_DEV_ID_X550EM_A_10G_T: u16 = 0x15C8;
const IXGBE_DEV_ID_X550EM_A_QSFP: u16 = 0x15CA;
const IXGBE_DEV_ID_X550EM_A_QSFP_N: u16 = 0x15CC;
const IXGBE_DEV_ID_X550EM_A_SFP: u16 = 0x15CE;
const IXGBE_DEV_ID_X550EM_A_1G_T: u16 = 0x15E4;
const IXGBE_DEV_ID_X550EM_A_1G_T_L: u16 = 0x15E5;
const IXGBE_DEV_ID_X550EM_X_KX4: u16 = 0x15AA;
const IXGBE_DEV_ID_X550EM_X_KR: u16 = 0x15AB;
const IXGBE_DEV_ID_X550EM_X_SFP: u16 = 0x15AC;
const IXGBE_DEV_ID_X550EM_X_10G_T: u16 = 0x15AD;
const IXGBE_DEV_ID_X550EM_X_1G_T: u16 = 0x15AE;
const IXGBE_DEV_ID_X550EM_X_XFI: u16 = 0x15B0;
const IXGBE_DEV_ID_X550_VF_HV: u16 = 0x1564;
const IXGBE_DEV_ID_X550_VF: u16 = 0x1565;
const IXGBE_DEV_ID_X550EM_A_VF: u16 = 0x15C5;
const IXGBE_DEV_ID_X550EM_A_VF_HV: u16 = 0x15B4;
const IXGBE_DEV_ID_X550EM_X_VF: u16 = 0x15A8;
const IXGBE_DEV_ID_X550EM_X_VF_HV: u16 = 0x15A9;

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

fn get_mac_type(device: u16, info: &PCIeInfo) -> Result<MacType, IxgbeDriverErr> {
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
        _ => return Err(IxgbeDriverErr::UnknownDeviceID),
    };
    Ok(result)
}

#[derive(Debug, Clone, Copy)]
pub struct IxgbeMacInfo {
    pub mac_type: MacType,
    pub addr: [u8; IXGBE_ETH_LENGTH_OF_ADDRESS],
    pub perm_addr: [u8; IXGBE_ETH_LENGTH_OF_ADDRESS],
    pub mc_filter_type: i32,
    pub mcft_size: u32,
    pub vft_size: u32,
    pub num_rar_entries: u32,
    pub rx_pb_size: u32,
    pub max_rx_queues: u32,
    pub max_tx_queues: u32,
    pub max_msix_vectors: u16,
    pub arc_subsystem_valid: bool,
    pub flags: u8,
    pub set_lben: bool,
}

pub struct IxgbePhyInfo {
    pub phy_semaphore_mask: u32,
    pub media_type: MediaType,
    //pub addr: u32,
}

pub struct IxgbeEepromInfo {
    pub eeprom_type: EepromType,
    pub semaphore_delay: u32,
    pub word_size: u16,
    pub address_bits: u16,
    pub word_page_size: u16,
    pub ctrl_word_3: u16,
}

pub struct IxgbeAddrFilterInfo {
    pub num_mc_addrs: u32,
    pub rar_used_count: u32,
    pub mta_in_use: u32,
    pub overflow_promisc: u32,
    pub user_set_promisc: bool,
}

pub struct IxgbeHw {
    //pub ops: Box<dyn IxgbeOperations>,
    pub mac: IxgbeMacInfo,
    pub phy: IxgbePhyInfo,
    pub eeprom: IxgbeEepromInfo,
    pub addr_ctrl: IxgbeAddrFilterInfo,
    pub adapter_stopped: bool,
}

impl IxgbeHw {
    pub fn new(info: &mut PCIeInfo) -> Result<(Self, Box<dyn IxgbeOperations>), IxgbeDriverErr> {
        use MacType::*;

        let mac_type = get_mac_type(info.get_id(), info)?;
        let ops;

        // Doesn't seem to require check_pci_express since all the ixgbe devices support PCI Express
        // https://github.com/openbsd/src/blob/82673a188a32931f4005a3ede8f05d97542feb17/sys/dev/pci/ixgbe.c#L715

        // TODO? : get_hw_info() swfwhw_semaphore_present, swfw_sync_present, eeprom_semaphore_presentのbool値の取得

        // TODO: Might need to set ixgbe_smart_speed as in https://github.com/openbsd/src/blob/82673a188a32931f4005a3ede8f05d97542feb17/sys/dev/pci/if_ix.c#L1703
        // ⇔ OpenBSD ixgbe_identify_hardware()

        // set the number of the descriptors allocated by the driver DEFAULT_TXD, DEFAULT_RXD

        // ixgbe_allocate_pci_resources()
        // pci_conf_read() pci_mapreg_map()はinfo.map_bar()？ hw.hw_addrはいらなそう. sc->num_queuesやsc->hw.backはどこで利用する? msi,msixの設定 -> IxgbeInner new()

        // ixgbe_allocate_queues(): -> IxgbeInner new()

        // TODO: sc->mta = mallocarray() : Allocate multicast array memory -> IxgbeInner new()?

        ops = get_operations(&mac_type)?; // init_shared_code();
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
            IxgbeMacX540 => ixgbe_x540::set_mac_val(info)?,
            _ => (0, 0, 0, 0, 0, 0, 0, false),
        };

        let eeprom = ops.validate_eeprom_checksum(info)?;

        // TODO: ixgbe_allocate_msix() or ixgbe_allocate_legacy()

        // TODO: hw.mac.ops.enable_tx_laser() for 82599 SFP+ fiber

        // ixgbe_setup_interface(): -> IxgbeInner new()

        // hw->mac.ops.get_bus_info(hw)

        // sc->fc = ixgbe_fc_full; Do we really need this?

        // ctrl_ext = IXGBE_READ_REG()....WRITE_REG(): -> IxgbeInner new()

        Ok((
            Self {
                mac: IxgbeMacInfo {
                    mac_type,
                    addr: [0; IXGBE_ETH_LENGTH_OF_ADDRESS],
                    perm_addr: [0; IXGBE_ETH_LENGTH_OF_ADDRESS],
                    mc_filter_type: 0,
                    mcft_size,
                    vft_size,
                    num_rar_entries,
                    rx_pb_size,
                    max_rx_queues,
                    max_tx_queues,
                    max_msix_vectors,
                    arc_subsystem_valid,
                    flags: 0,
                    set_lben: false,
                },
                phy: IxgbePhyInfo {
                    phy_semaphore_mask: 0,
                    media_type: MediaType::IxgbeMediaTypeUnknown,
                    //addr: phy_addr,
                },
                eeprom,
                addr_ctrl: IxgbeAddrFilterInfo {
                    num_mc_addrs: 0,
                    rar_used_count: 0,
                    mta_in_use: 0,
                    overflow_promisc: 0,
                    user_set_promisc: false,
                },
                adapter_stopped: false,
            },
            ops,
        ))
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
        MacType::IxgbeMacX540 => Ok(ixgbe_x540::get_self()),
        _ => Err(IxgbeDriverErr::NotImplemented),
    }
}

pub fn get_num_queues(hw: &IxgbeHw) -> usize {
    1
}

// set_phy_power()
//hw.phy.phy_semaphore_mask, hw.phy.addr
//let mut phy_semaphore_mask = IXGBE_GSSR_PHY1_SM;
//let mut phy_id_high = 0;
//let mut phy_addr = 0;
//let mut flag = 0;
//for try_phy_addr in 0..IXGBE_MAX_PHY_ADDR {
//phy_id_high = ops.phy_read_reg(
//info,
//try_phy_addr,
//phy_semaphore_mask,
//IXGBE_MDIO_PHY_ID_HIGH,
//IXGBE_MDIO_PMA_PMD_DEV_TYPE,
//)?;
//if phy_id_high != 0xFFFF && phy_id_high != 0x0 {
//phy_addr = try_phy_addr;
//flag = 1;
//break;
//}
//}

//if flag == 0 {
//log::error!("phy_addr1 not found!!!!");
//} else {
//log::info!("phy_addr1 found!!!!:{}", phy_addr);
//log::info!("phy_id_high1 found!!!!:{}", phy_id_high);
//}

//phy_semaphore_mask = IXGBE_GSSR_PHY0_SM;
//phy_id_high = 0;
//phy_addr = 0;
//flag = 0;
//for try_phy_addr in 0..IXGBE_MAX_PHY_ADDR {
//phy_id_high = ops.phy_read_reg(
//info,
//try_phy_addr,
//phy_semaphore_mask,
//IXGBE_MDIO_PHY_ID_HIGH,
//IXGBE_MDIO_PMA_PMD_DEV_TYPE,
//)?;
//if phy_id_high != 0xFFFF && phy_id_high != 0x0 {
//phy_addr = try_phy_addr;
//flag = 1;
//break;
//}
//}

//if flag == 0 {
//log::error!("phy_addr0 not found!!!!");
//} else {
//log::info!("phy_addr0 found!!!!:{}", phy_addr);
//log::info!("phy_id_high0 found!!!!:{}", phy_id_high);
//}
//ops.set_phy_power(info, &mac_type, phy_addr, phy_semaphore_mask, true)?; //- ixgbe_set_copper_phy_power() Do we really need this?(for min impl)
