use super::ixgbe_hw::{get_mac_type, MacType};
use super::IxgbeDriverErr;

pub const DEFAULT_TXD: usize = 256;
pub const PERFORM_TXD: usize = 4096;
pub const MAX_TXD: usize = 4096;
pub const DEFAULT_RXD: usize = 256;
pub const PERFORM_RXD: usize = 256;
pub const MIN_RXD: usize = 256;

pub const IXGBE_MAX_FRAME_SIZE: usize = 9216;

// Flow control constants
pub const IXGBE_FC_PAUSE: u16 = 0xFFFF;
pub const IXGBE_FC_HI: u32 = 0x20000;
pub const IXGBE_FC_LO: u32 = 0x10000;

/* Defines for printing debug information */
pub const DEBUG_INIT: u32 = 0;
pub const DEBUG_IOCTL: u32 = 0;
pub const DEBUG_HW: u32 = 0;

pub const MAX_NUM_MULTICAST_ADDRESSES: u16 = 128;
pub const IXGBE_82598_SCATTER: u16 = 100;
pub const IXGBE_82599_SCATTER: u16 = 32;
pub const MSIX_82598_BAR: u16 = 3;
pub const MSIX_82599_BAR: u16 = 4;
pub const IXGBE_TSO_SIZE: u32 = 262140;
pub const IXGBE_TX_BUFFER_SIZE: u32 = 1514;
pub const IXGBE_RX_HDR: u16 = 128;
pub const IXGBE_VFTA_SIZE: usize = 128;
pub const IXGBE_BR_SIZE: usize = 4096;
pub const IXGBE_QUEUE_MIN_FREE: u16 = 32;

// Interrupt Moderation parameters
pub const IXGBE_INTS_PER_SEC: u32 = 8000;
pub const IXGBE_LINK_ITR: u32 = 1000;

pub const IXGBE_DEV_ID_82598: u16 = 0x10B6;
pub const IXGBE_DEV_ID_82598_BX: u16 = 0x1508;
pub const IXGBE_DEV_ID_82598AF_DUAL_PORT: u16 = 0x10C6;
pub const IXGBE_DEV_ID_82598AF_SINGLE_PORT: u16 = 0x10C7;
pub const IXGBE_DEV_ID_82598AT: u16 = 0x10C8;
pub const IXGBE_DEV_ID_82598AT2: u16 = 0x150B;
pub const IXGBE_DEV_ID_82598AT_DUAL_PORT: u16 = 0x10D7;
pub const IXGBE_DEV_ID_82598EB_SFP_LOM: u16 = 0x10DB;
pub const IXGBE_DEV_ID_82598EB_CX4: u16 = 0x10DD;
pub const IXGBE_DEV_ID_82598_CX4_DUAL_PORT: u16 = 0x10EC;
pub const IXGBE_DEV_ID_82598_DA_DUAL_PORT: u16 = 0x10F1;
pub const IXGBE_DEV_ID_82598_SR_DUAL_PORT_EM: u16 = 0x10E1;
pub const IXGBE_DEV_ID_82598EB_XF_LR: u16 = 0x10F4;
pub const IXGBE_DEV_ID_82599_KX4: u16 = 0x10F7;
pub const IXGBE_DEV_ID_82599_KX4_MEZZ: u16 = 0x1514;
pub const IXGBE_DEV_ID_82599_KR: u16 = 0x1517;
pub const IXGBE_DEV_ID_82599_COMBO_BACKPLANE: u16 = 0x10F8;
pub const IXGBE_SUBDEV_ID_82599_KX4_KR_MEZZ: u16 = 0x000C;
pub const IXGBE_DEV_ID_82599_CX4: u16 = 0x10F9;
pub const IXGBE_DEV_ID_82599_SFP: u16 = 0x10FB;
pub const IXGBE_SUBDEV_ID_82599_SFP: u16 = 0x11A9;
pub const IXGBE_SUBDEV_ID_82599_SFP_WOL0: u16 = 0x1071;
pub const IXGBE_SUBDEV_ID_82599_RNDC: u16 = 0x1F72;
pub const IXGBE_SUBDEV_ID_82599_560FLR: u16 = 0x17D0;
pub const IXGBE_SUBDEV_ID_82599_ECNA_DP: u16 = 0x0470;
pub const IXGBE_SUBDEV_ID_82599_SP_560FLR: u16 = 0x211B;
pub const IXGBE_SUBDEV_ID_82599_LOM_SNAP6: u16 = 0x2159;
pub const IXGBE_SUBDEV_ID_82599_SFP_1OCP: u16 = 0x000D;
pub const IXGBE_SUBDEV_ID_82599_SFP_2OCP: u16 = 0x0008;
pub const IXGBE_SUBDEV_ID_82599_SFP_LOM_OEM1: u16 = 0x8976;
pub const IXGBE_SUBDEV_ID_82599_SFP_LOM_OEM2: u16 = 0x06EE;
pub const IXGBE_DEV_ID_82599_BACKPLANE_FCOE: u16 = 0x152A;
pub const IXGBE_DEV_ID_82599_SFP_FCOE: u16 = 0x1529;
pub const IXGBE_DEV_ID_82599_SFP_EM: u16 = 0x1507;
pub const IXGBE_DEV_ID_82599_SFP_SF2: u16 = 0x154D;
pub const IXGBE_DEV_ID_82599_SFP_SF_QP: u16 = 0x154A;
pub const IXGBE_DEV_ID_82599_QSFP_SF_QP: u16 = 0x1558;
pub const IXGBE_DEV_ID_82599EN_SFP: u16 = 0x1557;
pub const IXGBE_SUBDEV_ID_82599EN_SFP_OCP1: u16 = 0x0001;
pub const IXGBE_DEV_ID_82599_XAUI_LOM: u16 = 0x10FC;
pub const IXGBE_DEV_ID_82599_T3_LOM: u16 = 0x151C;
pub const IXGBE_DEV_ID_82599_VF: u16 = 0x10ED;
pub const IXGBE_DEV_ID_82599_VF_HV: u16 = 0x152E;
pub const IXGBE_DEV_ID_82599_BYPASS: u16 = 0x155D;
pub const IXGBE_DEV_ID_X540T: u16 = 0x1528;
pub const IXGBE_DEV_ID_X540_VF: u16 = 0x1515;
pub const IXGBE_DEV_ID_X540_VF_HV: u16 = 0x1530;
pub const IXGBE_DEV_ID_X540_BYPASS: u16 = 0x155C;
pub const IXGBE_DEV_ID_X540T1: u16 = 0x1560;
pub const IXGBE_DEV_ID_X550T: u16 = 0x1563;
pub const IXGBE_DEV_ID_X550T1: u16 = 0x15D1;
pub const IXGBE_DEV_ID_X550EM_A_KR: u16 = 0x15C2;
pub const IXGBE_DEV_ID_X550EM_A_KR_L: u16 = 0x15C3;
pub const IXGBE_DEV_ID_X550EM_A_SFP_N: u16 = 0x15C4;
pub const IXGBE_DEV_ID_X550EM_A_SGMII: u16 = 0x15C6;
pub const IXGBE_DEV_ID_X550EM_A_SGMII_L: u16 = 0x15C7;
pub const IXGBE_DEV_ID_X550EM_A_10G_T: u16 = 0x15C8;
pub const IXGBE_DEV_ID_X550EM_A_QSFP: u16 = 0x15CA;
pub const IXGBE_DEV_ID_X550EM_A_QSFP_N: u16 = 0x15CC;
pub const IXGBE_DEV_ID_X550EM_A_SFP: u16 = 0x15CE;
pub const IXGBE_DEV_ID_X550EM_A_1G_T: u16 = 0x15E4;
pub const IXGBE_DEV_ID_X550EM_A_1G_T_L: u16 = 0x15E5;
pub const IXGBE_DEV_ID_X550EM_X_KX4: u16 = 0x15AA;
pub const IXGBE_DEV_ID_X550EM_X_KR: u16 = 0x15AB;
pub const IXGBE_DEV_ID_X550EM_X_SFP: u16 = 0x15AC;
pub const IXGBE_DEV_ID_X550EM_X_10G_T: u16 = 0x15AD;
pub const IXGBE_DEV_ID_X550EM_X_1G_T: u16 = 0x15AE;
pub const IXGBE_DEV_ID_X550EM_X_XFI: u16 = 0x15B0;
pub const IXGBE_DEV_ID_X550_VF_HV: u16 = 0x1564;
pub const IXGBE_DEV_ID_X550_VF: u16 = 0x1565;
pub const IXGBE_DEV_ID_X550EM_A_VF: u16 = 0x15C5;
pub const IXGBE_DEV_ID_X550EM_A_VF_HV: u16 = 0x15B4;
pub const IXGBE_DEV_ID_X550EM_X_VF: u16 = 0x15A8;
pub const IXGBE_DEV_ID_X550EM_X_VF_HV: u16 = 0x15A9;

// General Registers
pub const IXGBE_CTRL: usize = 0x00000;
pub const IXGBE_STATUS: usize = 0x00008;
pub const IXGBE_CTRL_EXT: usize = 0x00018;
pub const IXGBE_ESDP: usize = 0x00020;
pub const IXGBE_EODSDP: usize = 0x00028;
pub const IXGBE_I2CCTL_82599: usize = 0x00028;
pub const IXGBE_I2CCTL: usize = IXGBE_I2CCTL_82599;
pub const IXGBE_I2CCTL_X540: usize = IXGBE_I2CCTL_82599;
pub const IXGBE_I2CCTL_X550: usize = 0x15F5C;
pub const IXGBE_I2CCTL_X550EM_X: usize = IXGBE_I2CCTL_X550;
pub const IXGBE_I2CCTL_X550EM_A: usize = IXGBE_I2CCTL_X550;
pub const IXGBE_PHY_GPIO: usize = 0x00028;
pub const IXGBE_MAC_GPIO: usize = 0x00030;
pub const IXGBE_PHYINT_STATUS0: usize = 0x00100;
pub const IXGBE_PHYINT_STATUS1: usize = 0x00104;
pub const IXGBE_PHYINT_STATUS2: usize = 0x00108;
pub const IXGBE_LEDCTL: usize = 0x00200;
pub const IXGBE_FRTIMER: usize = 0x00048;
pub const IXGBE_TCPTIMER: usize = 0x0004C;
pub const IXGBE_CORESPARE: usize = 0x00600;
pub const IXGBE_EXVET: usize = 0x05078;

// NVM Registers
pub const IXGBE_EEC: usize = 0x10010;
pub const IXGBE_EEC_X540: usize = IXGBE_EEC;
pub const IXGBE_EEC_X550: usize = IXGBE_EEC;
pub const IXGBE_EEC_X550EM_X: usize = IXGBE_EEC;
pub const IXGBE_EEC_X550EM_A: usize = 0x15FF8;
pub const IXGBE_EERD: usize = 0x10014;
pub const IXGBE_EEWR: usize = 0x10018;
pub const IXGBE_FLA: usize = 0x1001C;
pub const IXGBE_FLA_X540: usize = IXGBE_FLA;
pub const IXGBE_FLA_X550: usize = IXGBE_FLA;
pub const IXGBE_FLA_X550EM_X: usize = IXGBE_FLA;
pub const IXGBE_FLA_X550EM_A: usize = 0x15F68;
pub const IXGBE_EEMNGCTL: usize = 0x10110;
pub const IXGBE_EEMNGDATA: usize = 0x10114;
pub const IXGBE_FLMNGCTL: usize = 0x10118;
pub const IXGBE_FLMNGDATA: usize = 0x1011C;
pub const IXGBE_FLMNGCNT: usize = 0x10120;
pub const IXGBE_FLOP: usize = 0x1013C;
pub const IXGBE_GRC: usize = 0x10200;
pub const IXGBE_GRC_X540: usize = IXGBE_GRC;
pub const IXGBE_GRC_X550: usize = IXGBE_GRC;
pub const IXGBE_GRC_X550EM_X: usize = IXGBE_GRC;
pub const IXGBE_GRC_X550EM_A: usize = 0x15F64;
pub const IXGBE_SRAMREL: usize = 0x10210;
pub const IXGBE_SRAMREL_X540: usize = IXGBE_SRAMREL;
pub const IXGBE_SRAMREL_X550: usize = IXGBE_SRAMREL;
pub const IXGBE_SRAMREL_X550EM_X: usize = IXGBE_SRAMREL;
pub const IXGBE_SRAMREL_X550EM_A: usize = 0x15F6C;
pub const IXGBE_PHYDBG: usize = 0x10218;

// General Receive Control
pub const IXGBE_GRC_MNG: usize = 0x00000001; // Manageability Enable
pub const IXGBE_GRC_APME: usize = 0x00000002; // APM enabled in EEPROM

// I2CCTL Bit Masks
pub const IXGBE_I2C_CLK_IN: usize = 0x00000001;
pub const IXGBE_I2C_CLK_IN_X540: usize = IXGBE_I2C_CLK_IN;
pub const IXGBE_I2C_CLK_IN_X550: usize = 0x00004000;
pub const IXGBE_I2C_CLK_IN_X550EM_X: usize = IXGBE_I2C_CLK_IN_X550;
pub const IXGBE_I2C_CLK_IN_X550EM_A: usize = IXGBE_I2C_CLK_IN_X550;
pub const IXGBE_I2C_CLK_OUT: usize = 0x00000002;
pub const IXGBE_I2C_CLK_OUT_X540: usize = IXGBE_I2C_CLK_OUT;
pub const IXGBE_I2C_CLK_OUT_X550: usize = 0x00000200;
pub const IXGBE_I2C_CLK_OUT_X550EM_X: usize = IXGBE_I2C_CLK_OUT_X550;
pub const IXGBE_I2C_CLK_OUT_X550EM_A: usize = IXGBE_I2C_CLK_OUT_X550;
pub const IXGBE_I2C_DATA_IN: usize = 0x00000004;
pub const IXGBE_I2C_DATA_IN_X540: usize = IXGBE_I2C_DATA_IN;
pub const IXGBE_I2C_DATA_IN_X550: usize = 0x00001000;
pub const IXGBE_I2C_DATA_IN_X550EM_X: usize = IXGBE_I2C_DATA_IN_X550;
pub const IXGBE_I2C_DATA_IN_X550EM_A: usize = IXGBE_I2C_DATA_IN_X550;
pub const IXGBE_I2C_DATA_OUT: usize = 0x00000008;
pub const IXGBE_I2C_DATA_OUT_X540: usize = IXGBE_I2C_DATA_OUT;
pub const IXGBE_I2C_DATA_OUT_X550: usize = 0x00000400;
pub const IXGBE_I2C_DATA_OUT_X550EM_X: usize = IXGBE_I2C_DATA_OUT_X550;
pub const IXGBE_I2C_DATA_OUT_X550EM_A: usize = IXGBE_I2C_DATA_OUT_X550;
pub const IXGBE_I2C_DATA_OE_N_EN: usize = 0;
pub const IXGBE_I2C_DATA_OE_N_EN_X540: usize = IXGBE_I2C_DATA_OE_N_EN;
pub const IXGBE_I2C_DATA_OE_N_EN_X550: usize = 0x00000800;
pub const IXGBE_I2C_DATA_OE_N_EN_X550EM_X: usize = IXGBE_I2C_DATA_OE_N_EN_X550;
pub const IXGBE_I2C_DATA_OE_N_EN_X550EM_A: usize = IXGBE_I2C_DATA_OE_N_EN_X550;

pub const IXGBE_I2C_BB_EN: usize = 0;
pub const IXGBE_I2C_BB_EN_X540: usize = IXGBE_I2C_BB_EN;
pub const IXGBE_I2C_BB_EN_X550: usize = 0x00000100;
pub const IXGBE_I2C_BB_EN_X550EM_X: usize = IXGBE_I2C_BB_EN_X550;
pub const IXGBE_I2C_BB_EN_X550EM_A: usize = IXGBE_I2C_BB_EN_X550;

pub const IXGBE_I2C_CLK_OE_N_EN: usize = 0;
pub const IXGBE_I2C_CLK_OE_N_EN_X540: usize = IXGBE_I2C_CLK_OE_N_EN;
pub const IXGBE_I2C_CLK_OE_N_EN_X550: usize = 0x00002000;
pub const IXGBE_I2C_CLK_OE_N_EN_X550EM_X: usize = IXGBE_I2C_CLK_OE_N_EN_X550;
pub const IXGBE_I2C_CLK_OE_N_EN_X550EM_A: usize = IXGBE_I2C_CLK_OE_N_EN_X550;
pub const IXGBE_I2C_CLOCK_STRETCHING_TIMEOUT: usize = 500;

pub const NVM_OROM_OFFSET: usize = 0x17;
pub const NVM_OROM_BLK_LOW: usize = 0x83;
pub const NVM_OROM_BLK_HI: usize = 0x84;
pub const NVM_OROM_PATCH_MASK: usize = 0xFF;
pub const NVM_OROM_SHIFT: usize = 8;

pub const NVM_VER_MASK: usize = 0x00FF;
pub const NVM_VER_SHIFT: usize = 8;
pub const NVM_OEM_PROD_VER_PTR: usize = 0x1B;
pub const NVM_OEM_PROD_VER_CAP_OFF: usize = 0x1;
pub const NVM_OEM_PROD_VER_OFF_L: usize = 0x2;
pub const NVM_OEM_PROD_VER_OFF_H: usize = 0x3;
pub const NVM_OEM_PROD_VER_CAP_MASK: usize = 0xF;
pub const NVM_OEM_PROD_VER_MOD_LEN: usize = 0x3;
pub const NVM_ETK_OFF_LOW: usize = 0x2D;
pub const NVM_ETK_OFF_HI: usize = 0x2E;
pub const NVM_ETK_SHIFT: usize = 16;
pub const NVM_VER_INVALID: usize = 0xFFFF;
pub const NVM_ETK_VALID: usize = 0x8000;
pub const NVM_INVALID_PTR: usize = 0xFFFF;
pub const NVM_VER_SIZE: usize = 32;

// Struct definition in Rust for NVM Version details
#[derive(Debug, Clone, Copy)]
pub struct IXGBENvmVersion {
    pub etk_id: u32,
    pub nvm_major: u8,
    pub nvm_minor: u16,
    pub nvm_id: u8,

    pub oem_valid: bool,
    pub oem_major: u8,
    pub oem_minor: u8,
    pub oem_release: u16,

    pub or_valid: bool,
    pub or_major: u8,
    pub or_build: u16,
    pub or_patch: u8,
}

// Interrupt Registers
pub const IXGBE_EICR: usize = 0x00800;
pub const IXGBE_EICS: usize = 0x00808;
pub const IXGBE_EIMS: usize = 0x00880;
pub const IXGBE_EIMC: usize = 0x00888;
pub const IXGBE_EIAC: usize = 0x00810;
pub const IXGBE_EIAM: usize = 0x00890;
pub const IXGBE_EICS_EX: fn(usize) -> usize = |i| 0x00A90 + (i * 4);
pub const IXGBE_EIMS_EX: fn(usize) -> usize = |i| 0x00AA0 + (i * 4);
pub const IXGBE_EIMC_EX: fn(usize) -> usize = |i| 0x00AB0 + (i * 4);
pub const IXGBE_EIAM_EX: fn(usize) -> usize = |i| 0x00AD0 + (i * 4);
pub const IXGBE_MAX_INT_RATE: usize = 488281;
pub const IXGBE_MIN_INT_RATE: usize = 956;
pub const IXGBE_MAX_EITR: usize = 0x00000FF8;
pub const IXGBE_MIN_EITR: usize = 8;
pub const IXGBE_EITR: fn(usize) -> usize = |i| {
    if i <= 23 {
        0x00820 + (i * 4)
    } else {
        0x012300 + ((i - 24) * 4)
    }
};
pub const IXGBE_EITR_ITR_INT_MASK: u32 = 0x00000FF8;
pub const IXGBE_EITR_LLI_MOD: u32 = 0x00008000;
pub const IXGBE_EITR_CNT_WDIS: u32 = 0x80000000;
pub const IXGBE_IVAR: fn(usize) -> usize = |i| 0x00900 + (i * 4); // 24 at 0x900-0x960
pub const IXGBE_IVAR_MISC: usize = 0x00A00; // misc MSI-X interrupt causes
pub const IXGBE_EITRSEL: usize = 0x00894;
pub const IXGBE_MSIXT: usize = 0x00000; // MSI-X Table. 0x0000 - 0x01C
pub const IXGBE_MSIXPBA: usize = 0x02000; // MSI-X Pending bit array
pub const IXGBE_PBACL: fn(usize) -> usize = |i| if i == 0 { 0x11068 } else { 0x110C0 + (i * 4) };
pub const IXGBE_GPIE: usize = 0x00898;

// Flow Control Registers
pub const IXGBE_FCADBUL: usize = 0x03210;
pub const IXGBE_FCADBUH: usize = 0x03214;
pub const IXGBE_FCAMACL: usize = 0x04328;
pub const IXGBE_FCAMACH: usize = 0x0432C;
pub const IXGBE_FCRTH_82599: fn(usize) -> usize = |i| 0x03260 + (i * 4); // 8 of these (0-7)
pub const IXGBE_FCRTL_82599: fn(usize) -> usize = |i| 0x03220 + (i * 4); // 8 of these (0-7)
pub const IXGBE_PFCTOP: usize = 0x03008;
pub const IXGBE_FCTTV: fn(usize) -> usize = |i| 0x03200 + (i * 4); // 4 of these (0-3)
pub const IXGBE_FCRTL: fn(usize) -> usize = |i| 0x03220 + (i * 8); // 8 of these (0-7)
pub const IXGBE_FCRTH: fn(usize) -> usize = |i| 0x03260 + (i * 8); // 8 of these (0-7)
pub const IXGBE_FCRTV: usize = 0x032A0;
pub const IXGBE_FCCFG: usize = 0x03D00;
pub const IXGBE_TFCS: usize = 0x0CE00;

// Receive DMA Registers
pub const IXGBE_RDBAL: fn(usize) -> usize = |i| {
    if i < 64 {
        0x01000 + (i * 0x40)
    } else {
        0x0D000 + ((i - 64) * 0x40)
    }
};
pub const IXGBE_RDBAH: fn(usize) -> usize = |i| {
    if i < 64 {
        0x01004 + (i * 0x40)
    } else {
        0x0D004 + ((i - 64) * 0x40)
    }
};
pub const IXGBE_RDLEN: fn(usize) -> usize = |i| {
    if i < 64 {
        0x01008 + (i * 0x40)
    } else {
        0x0D008 + ((i - 64) * 0x40)
    }
};
pub const IXGBE_RDH: fn(usize) -> usize = |i| {
    if i < 64 {
        0x01010 + (i * 0x40)
    } else {
        0x0D010 + ((i - 64) * 0x40)
    }
};
pub const IXGBE_RDT: fn(usize) -> usize = |i| {
    if i < 64 {
        0x01018 + (i * 0x40)
    } else {
        0x0D018 + ((i - 64) * 0x40)
    }
};
pub const IXGBE_RXDCTL: fn(usize) -> usize = |i| {
    if i < 64 {
        0x01028 + (i * 0x40)
    } else {
        0x0D028 + ((i - 64) * 0x40)
    }
};
pub const IXGBE_RSCCTL: fn(usize) -> usize = |i| {
    if i < 64 {
        0x0102C + (i * 0x40)
    } else {
        0x0D02C + ((i - 64) * 0x40)
    }
};
pub const IXGBE_RSCDBU: usize = 0x03028;
pub const IXGBE_RDDCC: usize = 0x02F20;
pub const IXGBE_RXMEMWRAP: usize = 0x03190;
pub const IXGBE_STARCTRL: usize = 0x03024;

// Split and Replication Receive Control Registers
pub const IXGBE_SRRCTL: fn(usize) -> usize = |i| {
    if i <= 15 {
        0x02100 + (i * 4)
    } else if i < 64 {
        0x01014 + (i * 0x40)
    } else {
        0x0D014 + ((i - 64) * 0x40)
    }
};

// Rx DCA Control Register
pub const IXGBE_DCA_RXCTRL: fn(usize) -> usize = |i| {
    if i <= 15 {
        0x02200 + (i * 4)
    } else if i < 64 {
        0x0100C + (i * 0x40)
    } else {
        0x0D00C + ((i - 64) * 0x40)
    }
};
pub const IXGBE_RDRXCTL: usize = 0x02F00;

// 8 of these 0x03C00 - 0x03C1C
pub const IXGBE_RXPBSIZE: fn(usize) -> usize = |i| 0x03C00 + (i * 4);
pub const IXGBE_RXCTRL: usize = 0x03000;
pub const IXGBE_DROPEN: usize = 0x03D04;
pub const IXGBE_RXPBSIZE_SHIFT: usize = 10;
pub const IXGBE_RXPBSIZE_MASK: usize = 0x000FFC00;

// Receive Registers
pub const IXGBE_RXCSUM: usize = 0x05000;
pub const IXGBE_RFCTL: usize = 0x05008;
pub const IXGBE_DRECCCTL: usize = 0x02F08;
pub const IXGBE_DRECCCTL_DISABLE: usize = 0;
pub const IXGBE_DRECCCTL2: usize = 0x02F8C;

// Multicast Table Array - 128 entries
pub const IXGBE_MTA: fn(u32) -> u32 = |i| 0x05200 + (i * 4);
pub const IXGBE_RAL: fn(u32) -> u32 = |i| {
    if i <= 15 {
        0x05400 + (i * 8)
    } else {
        0x0A200 + (i * 8)
    }
};
pub const IXGBE_RAH: fn(u32) -> u32 = |i| {
    if i <= 15 {
        0x05404 + (i * 8)
    } else {
        0x0A204 + (i * 8)
    }
};
pub const IXGBE_MPSAR_LO: fn(u32) -> u32 = |i| 0x0A600 + (i * 8);
pub const IXGBE_MPSAR_HI: fn(u32) -> u32 = |i| 0x0A604 + (i * 8);
// Packet split receive type
pub const IXGBE_PSRTYPE: fn(u32) -> u32 = |i| {
    if i <= 15 {
        0x05480 + (i * 4)
    } else {
        0x0EA00 + (i * 4)
    }
};
// Array of 4096 1-bit vlan filters
pub const IXGBE_VFTA: fn(usize) -> usize = |i| 0x0A000 + (i * 4);
// Array of 4096 4-bit vlan vmdq indices
pub const IXGBE_VFTAVIND: fn(usize, usize) -> usize = |j, i| 0x0A200 + (j * 0x200) + (i * 4);
pub const IXGBE_FCTRL: usize = 0x05080;
pub const IXGBE_VLNCTRL: usize = 0x05088;
pub const IXGBE_MCSTCTRL: usize = 0x05090;
pub const IXGBE_MRQC: usize = 0x05818;
pub const IXGBE_SAQF: fn(usize) -> usize = |i| 0x0E000 + (i * 4); // Source Address Queue Filter
pub const IXGBE_DAQF: fn(usize) -> usize = |i| 0x0E200 + (i * 4); // Destination Address Queue Filter
pub const IXGBE_SDPQF: fn(usize) -> usize = |i| 0x0E400 + (i * 4); // Src Dest. Addr Queue Filter
pub const IXGBE_FTQF: fn(usize) -> usize = |i| 0x0E600 + (i * 4); // Five Tuple Queue Filter
pub const IXGBE_ETQF: fn(usize) -> usize = |i| 0x05128 + (i * 4); // EType Queue Filter
pub const IXGBE_ETQS: fn(usize) -> usize = |i| 0x0EC00 + (i * 4); // EType Queue Select
pub const IXGBE_SYNQF: usize = 0x0EC30; // SYN Packet Queue Filter
pub const IXGBE_RQTC: usize = 0x0EC70;
pub const IXGBE_MTQC: usize = 0x08120;
pub const IXGBE_VLVF: fn(u32) -> u32 = |i| 0x0F100 + (i * 4); // 64 of these (0-63)
pub const IXGBE_VLVFB: fn(u32) -> u32 = |i| 0x0F200 + (i * 4); // 128 of these (0-127)
pub const IXGBE_VMVIR: fn(usize) -> usize = |i| 0x08000 + (i * 4); // 64 of these (0-63)
pub const IXGBE_PFFLPL: usize = 0x050B0;
pub const IXGBE_PFFLPH: usize = 0x050B4;
pub const IXGBE_VT_CTL: usize = 0x051B0;
pub const IXGBE_PFMAILBOX: fn(usize) -> usize = |i| 0x04B00 + (4 * i); // 64 total
                                                                       // 64 Mailboxes, 16 DW each
pub const IXGBE_PFMBMEM: fn(usize) -> usize = |i| 0x13000 + (64 * i);
pub const IXGBE_PFMBICR: fn(usize) -> usize = |i| 0x00710 + (4 * i); // 4 total
pub const IXGBE_PFMBIMR: fn(usize) -> usize = |i| 0x00720 + (4 * i); // 4 total
pub const IXGBE_VFRE: fn(usize) -> usize = |i| 0x051E0 + (i * 4);
pub const IXGBE_VFTE: fn(usize) -> usize = |i| 0x08110 + (i * 4);
pub const IXGBE_VMECM: fn(usize) -> usize = |i| 0x08790 + (i * 4);
pub const IXGBE_QDE: usize = 0x2F04;
pub const IXGBE_VMTXSW: fn(usize) -> usize = |i| 0x05180 + (i * 4); // 2 total
pub const IXGBE_VMOLR: fn(usize) -> usize = |i| 0x0F000 + (i * 4); // 64 total
pub const IXGBE_UTA: fn(usize) -> usize = |i| 0x0F400 + (i * 4);
pub const IXGBE_MRCTL: fn(usize) -> usize = |i| 0x0F600 + (i * 4);
pub const IXGBE_VMRVLAN: fn(usize) -> usize = |i| 0x0F610 + (i * 4);
pub const IXGBE_VMRVM: fn(usize) -> usize = |i| 0x0F630 + (i * 4);
pub const IXGBE_LVMMC_RX: usize = 0x2FA8;
pub const IXGBE_LVMMC_TX: usize = 0x8108;
pub const IXGBE_LMVM_RX: usize = 0x2FA4;
pub const IXGBE_LMVM_TX: usize = 0x8124;
pub const IXGBE_WQBR_RX: fn(usize) -> usize = |i| 0x2FB0 + (i * 4); // 4 total
pub const IXGBE_WQBR_TX: fn(usize) -> usize = |i| 0x8130 + (i * 4); // 4 total
pub const IXGBE_L34T_IMIR: fn(usize) -> usize = |i| 0x0E800 + (i * 4); //128 of these (0-127)
pub const IXGBE_RXFECCERR0: usize = 0x051B8;
pub const IXGBE_LLITHRESH: usize = 0x0EC90;
pub const IXGBE_IMIR: fn(usize) -> usize = |i| 0x05A80 + (i * 4); // 8 of these (0-7)
pub const IXGBE_IMIREXT: fn(usize) -> usize = |i| 0x05AA0 + (i * 4); // 8 of these (0-7)
pub const IXGBE_IMIRVP: usize = 0x05AC0;
pub const IXGBE_VMD_CTL: usize = 0x0581C;
pub const IXGBE_RETA: fn(usize) -> usize = |i| 0x05C00 + (i * 4); // 32 of these (0-31)
pub const IXGBE_ERETA: fn(usize) -> usize = |i| 0x0EE80 + (i * 4); // 96 of these (0-95)
pub const IXGBE_RSSRK: fn(usize) -> usize = |i| 0x05C80 + (i * 4); // 10 of these (0-9)

// Registers for setting up RSS on X550 with SRIOV
// _p - pool number (0..63)
// _i - index (0..10 for PFVFRSSRK, 0..15 for PFVFRETA)
pub const IXGBE_PFVFMRQC: fn(usize) -> usize = |p| 0x03400 + (p * 4);
pub const IXGBE_PFVFRSSRK: fn(usize, usize) -> usize = |i, p| 0x018000 + (i * 4) + (p * 0x40);
pub const IXGBE_PFVFRETA: fn(usize, usize) -> usize = |i, p| 0x019000 + (i * 4) + (p * 0x40);

// Flow Director registers
pub const IXGBE_FDIRCTRL: usize = 0x0EE00;
pub const IXGBE_FDIRHKEY: usize = 0x0EE68;
pub const IXGBE_FDIRSKEY: usize = 0x0EE6C;
pub const IXGBE_FDIRDIP4M: usize = 0x0EE3C;
pub const IXGBE_FDIRSIP4M: usize = 0x0EE40;
pub const IXGBE_FDIRTCPM: usize = 0x0EE44;
pub const IXGBE_FDIRUDPM: usize = 0x0EE48;
pub const IXGBE_FDIRSCTPM: usize = 0x0EE78;
pub const IXGBE_FDIRIP6M: usize = 0x0EE74;
pub const IXGBE_FDIRM: usize = 0x0EE70;

// Flow Director Stats registers
pub const IXGBE_FDIRFREE: usize = 0x0EE38;
pub const IXGBE_FDIRLEN: usize = 0x0EE4C;
pub const IXGBE_FDIRUSTAT: usize = 0x0EE50;
pub const IXGBE_FDIRFSTAT: usize = 0x0EE54;
pub const IXGBE_FDIRMATCH: usize = 0x0EE58;
pub const IXGBE_FDIRMISS: usize = 0x0EE5C;

// Flow Director Programming registers
pub const IXGBE_FDIRSIP_V6: fn(usize) -> usize = |i| 0x0EE0C + (i * 4); // 3 of these (0-2)
pub const IXGBE_FDIRIPSA: usize = 0x0EE18;
pub const IXGBE_FDIRIPDA: usize = 0x0EE1C;
pub const IXGBE_FDIRPORT: usize = 0x0EE20;
pub const IXGBE_FDIRVLAN: usize = 0x0EE24;
pub const IXGBE_FDIRHASH: usize = 0x0EE28;
pub const IXGBE_FDIRCMD: usize = 0x0EE2C;

// Transmit DMA registers
pub const IXGBE_TDBAL: fn(usize) -> usize = |i| 0x06000 + (i * 0x40); // 32 of them (0-31)
pub const IXGBE_TDBAH: fn(usize) -> usize = |i| 0x06004 + (i * 0x40);
pub const IXGBE_TDLEN: fn(usize) -> usize = |i| 0x06008 + (i * 0x40);
pub const IXGBE_TDH: fn(usize) -> usize = |i| 0x06010 + (i * 0x40);
pub const IXGBE_TDT: fn(usize) -> usize = |i| 0x06018 + (i * 0x40);
pub const IXGBE_TXDCTL: fn(usize) -> usize = |i| 0x06028 + (i * 0x40);
pub const IXGBE_TDWBAL: fn(usize) -> usize = |i| 0x06038 + (i * 0x40);
pub const IXGBE_TDWBAH: fn(usize) -> usize = |i| 0x0603C + (i * 0x40);
pub const IXGBE_DTXCTL: usize = 0x07E00;

pub const IXGBE_DMATXCTL: usize = 0x04A80;
pub const IXGBE_PFVFSPOOF: fn(usize) -> usize = |i| 0x08200 + (i * 4); // 8 of these 0 - 7
pub const IXGBE_PFDTXGSWC: usize = 0x08220;
pub const IXGBE_DTXMXSZRQ: usize = 0x08100;
pub const IXGBE_DTXTCPFLGL: usize = 0x04A88;
pub const IXGBE_DTXTCPFLGH: usize = 0x04A8C;
pub const IXGBE_LBDRPEN: usize = 0x0CA00;
pub const IXGBE_TXPBTHRESH: fn(usize) -> usize = |i| 0x04950 + (i * 4); // 8 of these 0 - 7

pub const IXGBE_DMATXCTL_TE: usize = 0x1; // Transmit Enable
pub const IXGBE_DMATXCTL_NS: usize = 0x2; // No Snoop LSO hdr buffer
pub const IXGBE_DMATXCTL_GDV: usize = 0x8; // Global Double VLAN
pub const IXGBE_DMATXCTL_MDP_EN: usize = 0x20; // Bit 5
pub const IXGBE_DMATXCTL_MBINTEN: usize = 0x40; // Bit 6
pub const IXGBE_DMATXCTL_VT_SHIFT: usize = 16; // VLAN EtherType

pub const IXGBE_PFDTXGSWC_VT_LBEN: u32 = 0x1; // Local L2 VT switch enable

// Anti-spoofing defines
pub const IXGBE_SPOOF_MACAS_MASK: usize = 0xFF;
pub const IXGBE_SPOOF_VLANAS_MASK: usize = 0xFF00;
pub const IXGBE_SPOOF_VLANAS_SHIFT: usize = 8;
pub const IXGBE_SPOOF_ETHERTYPEAS: usize = 0xFF000000;
pub const IXGBE_SPOOF_ETHERTYPEAS_SHIFT: usize = 16;
pub const IXGBE_PFVFSPOOF_REG_COUNT: usize = 8;
// 16 of these (0-15)
pub const IXGBE_DCA_TXCTRL: fn(usize) -> usize = |i| 0x07200 + (i * 4);
// Tx DCA Control register : 128 of these (0-127)
pub const IXGBE_DCA_TXCTRL_82599: fn(usize) -> usize = |i| 0x0600C + (i * 0x40);
pub const IXGBE_TIPG: usize = 0x0CB00;
pub const IXGBE_TXPBSIZE: fn(usize) -> usize = |i| 0x0CC00 + (i * 4); // 8 of these
pub const IXGBE_MNGTXMAP: usize = 0x0CD10;
pub const IXGBE_TIPG_FIBER_DEFAULT: usize = 3;
pub const IXGBE_TXPBSIZE_SHIFT: usize = 10;

// Wake up registers
pub const IXGBE_WUC: usize = 0x05800;
pub const IXGBE_WUFC: usize = 0x05808;
pub const IXGBE_WUS: usize = 0x05810;
pub const IXGBE_IPAV: usize = 0x05838;
pub const IXGBE_IP4AT: usize = 0x05840; // IPv4 table 0x5840-0x5858
pub const IXGBE_IP6AT: usize = 0x05880; // IPv6 table 0x5880-0x588F

pub const IXGBE_WUPL: usize = 0x05900;
pub const IXGBE_WUPM: usize = 0x05A00; // wake up pkt memory 0x5A00-0x5A7C
pub const IXGBE_PROXYS: usize = 0x05F60; // Proxying Status Register
pub const IXGBE_PROXYFC: usize = 0x05F64; // Proxying Filter Control Register
pub const IXGBE_VXLANCTRL: usize = 0x0000507C; // Rx filter VXLAN UDPPORT Register

// Masks for accessing VXLAN and GENEVE UDP ports
pub const IXGBE_VXLANCTRL_VXLAN_UDPPORT_MASK: usize = 0x0000ffff; // VXLAN port
pub const IXGBE_VXLANCTRL_GENEVE_UDPPORT_MASK: usize = 0xffff0000; // GENEVE port
pub const IXGBE_VXLANCTRL_ALL_UDPPORT_MASK: usize = 0xffffffff; // GENEVE/VXLAN
pub const IXGBE_VXLANCTRL_GENEVE_UDPPORT_SHIFT: usize = 16;

pub const IXGBE_FHFT: fn(usize) -> usize = |_n| 0x09000 + (_n * 0x100); // Flex host filter table
                                                                        // Ext Flexible Host Filter Table
pub const IXGBE_FHFT_EXT: fn(usize) -> usize = |_n| 0x09800 + (_n * 0x100);
pub const IXGBE_FHFT_EXT_X550: fn(usize) -> usize = |_n| 0x09600 + (_n * 0x100);

// Four Flexible Filters are supported
pub const IXGBE_FLEXIBLE_FILTER_COUNT_MAX: usize = 4;
// Six Flexible Filters are supported
pub const IXGBE_FLEXIBLE_FILTER_COUNT_MAX_6: usize = 6;
// Eight Flexible Filters are supported
pub const IXGBE_FLEXIBLE_FILTER_COUNT_MAX_8: usize = 8;
pub const IXGBE_EXT_FLEXIBLE_FILTER_COUNT_MAX: usize = 2;

// Each Flexible Filter is at most 128 (0x80) bytes in length
pub const IXGBE_FLEXIBLE_FILTER_SIZE_MAX: usize = 128;
pub const IXGBE_FHFT_LENGTH_OFFSET: usize = 0xFC; // Length byte in FHFT
pub const IXGBE_FHFT_LENGTH_MASK: usize = 0x0FF; // Length in lower byte

// Definitions for power management and wakeup registers
// Wake Up Control
pub const IXGBE_WUC_PME_EN: usize = 0x00000002; // PME Enable
pub const IXGBE_WUC_PME_STATUS: usize = 0x00000004; // PME Status
pub const IXGBE_WUC_WKEN: usize = 0x00000010; // Enable PE_WAKE_N pin assertion

// Wake Up Filter Control
pub const IXGBE_WUFC_LNKC: usize = 0x00000001; // Link Status Change Wakeup Enable
pub const IXGBE_WUFC_MAG: usize = 0x00000002; // Magic Packet Wakeup Enable
pub const IXGBE_WUFC_EX: usize = 0x00000004; // Directed Exact Wakeup Enable
pub const IXGBE_WUFC_MC: usize = 0x00000008; // Directed Multicast Wakeup Enable
pub const IXGBE_WUFC_BC: usize = 0x00000010; // Broadcast Wakeup Enable
pub const IXGBE_WUFC_ARP: usize = 0x00000020; // ARP Request Packet Wakeup Enable
pub const IXGBE_WUFC_IPV4: usize = 0x00000040; // Directed IPv4 Packet Wakeup Enable
pub const IXGBE_WUFC_IPV6: usize = 0x00000080; // Directed IPv6 Packet Wakeup Enable
pub const IXGBE_WUFC_MNG: usize = 0x00000100; // Directed Mgmt Packet Wakeup Enable

pub const IXGBE_WUFC_IGNORE_TCO: usize = 0x00008000; // Ignore WakeOn TCO packets
pub const IXGBE_WUFC_FLX0: usize = 0x00010000; // Flexible Filter 0 Enable
pub const IXGBE_WUFC_FLX1: usize = 0x00020000; // Flexible Filter 1 Enable
pub const IXGBE_WUFC_FLX2: usize = 0x00040000; // Flexible Filter 2 Enable
pub const IXGBE_WUFC_FLX3: usize = 0x00080000; // Flexible Filter 3 Enable
pub const IXGBE_WUFC_FLX4: usize = 0x00100000; // Flexible Filter 4 Enable
pub const IXGBE_WUFC_FLX5: usize = 0x00200000; // Flexible Filter 5 Enable
pub const IXGBE_WUFC_FLX_FILTERS: usize = 0x000F0000; // Mask for 4 flex filters
pub const IXGBE_WUFC_FLX_FILTERS_6: usize = 0x003F0000; // Mask for 6 flex filters
pub const IXGBE_WUFC_FLX_FILTERS_8: usize = 0x00FF0000; // Mask for 8 flex filters
pub const IXGBE_WUFC_FW_RST_WK: usize = 0x80000000; // Ena wake on FW reset assertion
                                                    // Mask for Ext. flex filters
pub const IXGBE_WUFC_EXT_FLX_FILTERS: usize = 0x00300000;
pub const IXGBE_WUFC_ALL_FILTERS: usize = 0x000F00FF; // Mask all 4 flex filters
pub const IXGBE_WUFC_ALL_FILTERS_6: usize = 0x003F00FF; // Mask all 6 flex filters
pub const IXGBE_WUFC_ALL_FILTERS_8: usize = 0x00FF00FF; // Mask all 8 flex filters
pub const IXGBE_WUFC_FLX_OFFSET: usize = 16; // Offset to the Flexible Filters bits

// Wake Up Status
pub const IXGBE_WUS_LNKC: usize = IXGBE_WUFC_LNKC;
pub const IXGBE_WUS_MAG: usize = IXGBE_WUFC_MAG;
pub const IXGBE_WUS_EX: usize = IXGBE_WUFC_EX;
pub const IXGBE_WUS_MC: usize = IXGBE_WUFC_MC;
pub const IXGBE_WUS_BC: usize = IXGBE_WUFC_BC;
pub const IXGBE_WUS_ARP: usize = IXGBE_WUFC_ARP;
pub const IXGBE_WUS_IPV4: usize = IXGBE_WUFC_IPV4;
pub const IXGBE_WUS_IPV6: usize = IXGBE_WUFC_IPV6;
pub const IXGBE_WUS_MNG: usize = IXGBE_WUFC_MNG;
pub const IXGBE_WUS_FLX0: usize = IXGBE_WUFC_FLX0;
pub const IXGBE_WUS_FLX1: usize = IXGBE_WUFC_FLX1;
pub const IXGBE_WUS_FLX2: usize = IXGBE_WUFC_FLX2;
pub const IXGBE_WUS_FLX3: usize = IXGBE_WUFC_FLX3;
pub const IXGBE_WUS_FLX4: usize = IXGBE_WUFC_FLX4;
pub const IXGBE_WUS_FLX5: usize = IXGBE_WUFC_FLX5;
pub const IXGBE_WUS_FLX_FILTERS: usize = IXGBE_WUFC_FLX_FILTERS;
pub const IXGBE_WUS_FW_RST_WK: usize = IXGBE_WUFC_FW_RST_WK;
// Proxy Status
pub const IXGBE_PROXYS_EX: usize = 0x00000004; // Exact packet received
pub const IXGBE_PROXYS_ARP_DIR: usize = 0x00000020; // ARP w/filter match received
pub const IXGBE_PROXYS_NS: usize = 0x00000200; // IPV6 NS received
pub const IXGBE_PROXYS_NS_DIR: usize = 0x00000400; // IPV6 NS w/DA match received
pub const IXGBE_PROXYS_ARP: usize = 0x00000800; // ARP request packet received
pub const IXGBE_PROXYS_MLD: usize = 0x00001000; // IPv6 MLD packet received

// Proxying Filter Control
pub const IXGBE_PROXYFC_ENABLE: usize = 0x00000001; // Port Proxying Enable
pub const IXGBE_PROXYFC_EX: usize = 0x00000004; // Directed Exact Proxy Enable
pub const IXGBE_PROXYFC_ARP_DIR: usize = 0x00000020; // Directed ARP Proxy Enable
pub const IXGBE_PROXYFC_NS: usize = 0x00000200; // IPv6 Neighbor Solicitation
pub const IXGBE_PROXYFC_ARP: usize = 0x00000800; // ARP Request Proxy Enable
pub const IXGBE_PROXYFC_MLD: usize = 0x00000800; // IPv6 MLD Proxy Enable
pub const IXGBE_PROXYFC_NO_TCO: usize = 0x00008000; // Ignore TCO packets

pub const IXGBE_WUPL_LENGTH_MASK: usize = 0xFFFF;

// DCB registers
pub const IXGBE_DCB_MAX_TRAFFIC_CLASS: usize = 8;
pub const IXGBE_RMCS: usize = 0x03D00;
pub const IXGBE_DPMCS: usize = 0x07F40;
pub const IXGBE_PDPMCS: usize = 0x0CD00;
pub const IXGBE_RUPPBMR: usize = 0x050A0;
pub const IXGBE_RT2CR: fn(usize) -> usize = |i| 0x03C20 + (i * 4); // 8 of these (0-7)
pub const IXGBE_RT2SR: fn(usize) -> usize = |i| 0x03C40 + (i * 4); // 8 of these (0-7)
pub const IXGBE_TDTQ2TCCR: fn(usize) -> usize = |i| 0x0602C + (i * 0x40); // 8 of these (0-7)
pub const IXGBE_TDTQ2TCSR: fn(usize) -> usize = |i| 0x0622C + (i * 0x40); // 8 of these (0-7)
pub const IXGBE_TDPT2TCCR: fn(usize) -> usize = |i| 0x0CD20 + (i * 4); // 8 of these (0-7)
pub const IXGBE_TDPT2TCSR: fn(usize) -> usize = |i| 0x0CD40 + (i * 4); // 8 of these (0-7)

// Power Management
// DMA Coalescing configuration
struct IxgbeDmacConfig {
    watchdog_timer: u16, // usec units
    link_speed: u32,
    fcoe_tc: u8,
    num_tcs: u8,
}

/*
 * DMA Coalescing threshold Rx PB TC[n] value in Kilobyte by link speed.
 * DMACRXT = 10Gbps = 10,000 bits / usec = 1250 bytes / usec 70 * 1250 ==
 * 87500 bytes [85KB]
 */
pub const IXGBE_DMACRXT_10G: usize = 0x55;
pub const IXGBE_DMACRXT_1G: usize = 0x09;
pub const IXGBE_DMACRXT_100M: usize = 0x01;

// DMA Coalescing registers
pub const IXGBE_DMCMNGTH: usize = 0x15F20; /* Management Threshold */
pub const IXGBE_DMACR: usize = 0x02400; /* Control register */
pub const IXGBE_DMCTH: fn(usize) -> usize = |i| 0x03300 + (i * 4); /* 8 of these */
pub const IXGBE_DMCTLX: usize = 0x02404; /* Time to Lx request */
/* DMA Coalescing register fields */
pub const IXGBE_DMCMNGTH_DMCMNGTH_MASK: usize = 0x000FFFF0; /* Mng Threshold mask */
pub const IXGBE_DMCMNGTH_DMCMNGTH_SHIFT: usize = 4; /* Management Threshold shift */
pub const IXGBE_DMACR_DMACWT_MASK: usize = 0x0000FFFF; /* Watchdog Timer mask */
pub const IXGBE_DMACR_HIGH_PRI_TC_MASK: usize = 0x00FF0000;
pub const IXGBE_DMACR_HIGH_PRI_TC_SHIFT: usize = 16;
pub const IXGBE_DMACR_EN_MNG_IND: usize = 0x10000000; /* Enable Mng Indications */
pub const IXGBE_DMACR_LX_COAL_IND: usize = 0x40000000; /* Lx Coalescing indicate */
pub const IXGBE_DMACR_DMAC_EN: usize = 0x80000000; /* DMA Coalescing Enable */
pub const IXGBE_DMCTH_DMACRXT_MASK: usize = 0x000001FF; /* Receive Threshold mask */
pub const IXGBE_DMCTLX_TTLX_MASK: usize = 0x00000FFF; /* Time to Lx request mask */

// EEE registers
pub const IXGBE_EEER: usize = 0x043A0; /* EEE register */
pub const IXGBE_EEE_STAT: usize = 0x04398; /* EEE Status */
pub const IXGBE_EEE_SU: usize = 0x04380; /* EEE Set up */
pub const IXGBE_EEE_SU_TEEE_DLY_SHIFT: usize = 26;
pub const IXGBE_TLPIC: usize = 0x041F4; /* EEE Tx LPI count */
pub const IXGBE_RLPIC: usize = 0x041F8; /* EEE Rx LPI count */

// EEE register fields
pub const IXGBE_EEER_TX_LPI_EN: usize = 0x00010000; /* Enable EEE LPI TX path */
pub const IXGBE_EEER_RX_LPI_EN: usize = 0x00020000; /* Enable EEE LPI RX path */
pub const IXGBE_EEE_STAT_NEG: usize = 0x20000000; /* EEE support neg on link */
pub const IXGBE_EEE_RX_LPI_STATUS: usize = 0x40000000; /* RX Link in LPI status */
pub const IXGBE_EEE_TX_LPI_STATUS: usize = 0x80000000; /* TX Link in LPI status */

// Security Control Registers
pub const IXGBE_SECTXCTRL: usize = 0x08800;
pub const IXGBE_SECTXSTAT: usize = 0x08804;
pub const IXGBE_SECTXBUFFAF: usize = 0x08808;
pub const IXGBE_SECTXMINIFG: usize = 0x08810;
pub const IXGBE_SECRXCTRL: usize = 0x08D00;
pub const IXGBE_SECRXSTAT: usize = 0x08D04;

// Security Bit Fields and Masks
pub const IXGBE_SECTXCTRL_SECTX_DIS: usize = 0x00000001;
pub const IXGBE_SECTXCTRL_TX_DIS: usize = 0x00000002;
pub const IXGBE_SECTXCTRL_STORE_FORWARD: usize = 0x00000004;

pub const IXGBE_SECTXSTAT_SECTX_RDY: usize = 0x00000001;
pub const IXGBE_SECTXSTAT_ECC_TXERR: usize = 0x00000002;

pub const IXGBE_SECRXCTRL_SECRX_DIS: usize = 0x00000001;
pub const IXGBE_SECRXCTRL_RX_DIS: usize = 0x00000002;

pub const IXGBE_SECRXSTAT_SECRX_RDY: usize = 0x00000001;
pub const IXGBE_SECRXSTAT_ECC_RXERR: usize = 0x00000002;

// LinkSec (MacSec) Registers
pub const IXGBE_LSECTXCAP: usize = 0x08A00;
pub const IXGBE_LSECRXCAP: usize = 0x08F00;
pub const IXGBE_LSECTXCTRL: usize = 0x08A04;
pub const IXGBE_LSECTXSCL: usize = 0x08A08; /* SCI Low */
pub const IXGBE_LSECTXSCH: usize = 0x08A0C; /* SCI High */
pub const IXGBE_LSECTXSA: usize = 0x08A10;
pub const IXGBE_LSECTXPN0: usize = 0x08A14;
pub const IXGBE_LSECTXPN1: usize = 0x08A18;
pub const IXGBE_LSECTXKEY0: fn(usize) -> usize = |_n| 0x08A1C + (4 * _n); /* 4 of these (0-3) */
pub const IXGBE_LSECTXKEY1: fn(usize) -> usize = |_n| 0x08A2C + (4 * _n); /* 4 of these (0-3) */
pub const IXGBE_LSECRXCTRL: usize = 0x08F04;
pub const IXGBE_LSECRXSCL: usize = 0x08F08;
pub const IXGBE_LSECRXSCH: usize = 0x08F0C;
pub const IXGBE_LSECRXSA: fn(usize) -> usize = |_i| 0x08F10 + (4 * _i); /* 2 of these (0-1) */
pub const IXGBE_LSECRXPN: fn(usize) -> usize = |_i| 0x08F18 + (4 * _i); /* 2 of these (0-1) */
pub const IXGBE_LSECRXKEY: fn(usize, usize) -> usize = |_n, _m| 0x08F20 + ((0x10 * _n) + (4 * _m));
pub const IXGBE_LSECTXUT: usize = 0x08A3C; /* OutPktsUntagged */
pub const IXGBE_LSECTXPKTE: usize = 0x08A40; /* OutPktsEncrypted */
pub const IXGBE_LSECTXPKTP: usize = 0x08A44; /* OutPktsProtected */
pub const IXGBE_LSECTXOCTE: usize = 0x08A48; /* OutOctetsEncrypted */
pub const IXGBE_LSECTXOCTP: usize = 0x08A4C; /* OutOctetsProtected */
pub const IXGBE_LSECRXUT: usize = 0x08F40; /* InPktsUntagged/InPktsNoTag */
pub const IXGBE_LSECRXOCTD: usize = 0x08F44; /* InOctetsDecrypted */
pub const IXGBE_LSECRXOCTV: usize = 0x08F48; /* InOctetsValidated */
pub const IXGBE_LSECRXBAD: usize = 0x08F4C; /* InPktsBadTag */
pub const IXGBE_LSECRXNOSCI: usize = 0x08F50; /* InPktsNoSci */
pub const IXGBE_LSECRXUNSCI: usize = 0x08F54; /* InPktsUnknownSci */
pub const IXGBE_LSECRXUNCH: usize = 0x08F58; /* InPktsUnchecked */
pub const IXGBE_LSECRXDELAY: usize = 0x08F5C; /* InPktsDelayed */
pub const IXGBE_LSECRXLATE: usize = 0x08F60; /* InPktsLate */
pub const IXGBE_LSECRXOK: fn(usize) -> usize = |_n| 0x08F64 + (0x04 * _n); /* InPktsOk */
pub const IXGBE_LSECRXINV: fn(usize) -> usize = |_n| 0x08F6C + (0x04 * _n); /* InPktsInvalid */
pub const IXGBE_LSECRXNV: fn(usize) -> usize = |_n| 0x08F74 + (0x04 * _n); /* InPktsNotValid */
pub const IXGBE_LSECRXUNSA: usize = 0x08F7C; /* InPktsUnusedSa */
pub const IXGBE_LSECRXNUSA: usize = 0x08F80; /* InPktsNotUsingSa */

// LinkSec (MacSec) Bit Fields and Masks
pub const IXGBE_LSECTXCAP_SUM_MASK: usize = 0x00FF0000;
pub const IXGBE_LSECTXCAP_SUM_SHIFT: usize = 16;
pub const IXGBE_LSECRXCAP_SUM_MASK: usize = 0x00FF0000;
pub const IXGBE_LSECRXCAP_SUM_SHIFT: usize = 16;

pub const IXGBE_LSECTXCTRL_EN_MASK: usize = 0x00000003;
pub const IXGBE_LSECTXCTRL_DISABLE: usize = 0x0;
pub const IXGBE_LSECTXCTRL_AUTH: usize = 0x1;
pub const IXGBE_LSECTXCTRL_AUTH_ENCRYPT: usize = 0x2;
pub const IXGBE_LSECTXCTRL_AISCI: usize = 0x00000020;
pub const IXGBE_LSECTXCTRL_PNTHRSH_MASK: usize = 0xFFFFFF00;
pub const IXGBE_LSECTXCTRL_RSV_MASK: usize = 0x000000D8;

pub const IXGBE_LSECRXCTRL_EN_MASK: usize = 0x0000000C;
pub const IXGBE_LSECRXCTRL_EN_SHIFT: usize = 2;
pub const IXGBE_LSECRXCTRL_DISABLE: usize = 0x0;
pub const IXGBE_LSECRXCTRL_CHECK: usize = 0x1;
pub const IXGBE_LSECRXCTRL_STRICT: usize = 0x2;
pub const IXGBE_LSECRXCTRL_DROP: usize = 0x3;
pub const IXGBE_LSECRXCTRL_PLSH: usize = 0x00000040;
pub const IXGBE_LSECRXCTRL_RP: usize = 0x00000080;
pub const IXGBE_LSECRXCTRL_RSV_MASK: usize = 0xFFFFFF33;

// IpSec Registers
pub const IXGBE_IPSTXIDX: usize = 0x08900;
pub const IXGBE_IPSTXSALT: usize = 0x08904;
pub const IXGBE_IPSTXKEY: fn(usize) -> usize = |_i| 0x08908 + (4 * _i); /* 4 of these (0-3) */
pub const IXGBE_IPSRXIDX: usize = 0x08E00;
pub const IXGBE_IPSRXIPADDR: fn(usize) -> usize = |_i| 0x08E04 + (4 * _i); /* 4 of these (0-3) */
pub const IXGBE_IPSRXSPI: usize = 0x08E14;
pub const IXGBE_IPSRXIPIDX: usize = 0x08E18;
pub const IXGBE_IPSRXKEY: fn(usize) -> usize = |_i| 0x08E1C + (4 * _i); /* 4 of these (0-3) */
pub const IXGBE_IPSRXSALT: usize = 0x08E2C;
pub const IXGBE_IPSRXMOD: usize = 0x08E30;

// Security Bit Fields and Masks
pub const IXGBE_SECTXCTRL_STORE_FORWARD_ENABLE: usize = 0x4;

// DCB registers
pub const IXGBE_RTRPCS: usize = 0x02430;
pub const IXGBE_RTTDCS: usize = 0x04900;
pub const IXGBE_RTTDCS_ARBDIS: usize = 0x00000040; /* DCB arbiter disable */
pub const IXGBE_RTTPCS: usize = 0x0CD00;
pub const IXGBE_RTRUP2TC: usize = 0x03020;
pub const IXGBE_RTTUP2TC: usize = 0x0C800;
pub const IXGBE_RTRPT4C: fn(usize) -> usize = |_i| 0x02140 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_TXLLQ: fn(usize) -> usize = |_i| 0x082E0 + (_i * 4); /* 4 of these (0-3) */
pub const IXGBE_RTRPT4S: fn(usize) -> usize = |_i| 0x02160 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_RTTDT2C: fn(usize) -> usize = |_i| 0x04910 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_RTTDT2S: fn(usize) -> usize = |_i| 0x04930 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_RTTPT2C: fn(usize) -> usize = |_i| 0x0CD20 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_RTTPT2S: fn(usize) -> usize = |_i| 0x0CD40 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_RTTDQSEL: usize = 0x04904;
pub const IXGBE_RTTDT1C: fn(usize) -> usize = |_i| 0x04920 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_RTTDT1S: fn(usize) -> usize = |_i| 0x04940 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_RTTPT1C: fn(usize) -> usize = |_i| 0x0CD30 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_RTTPT1S: fn(usize) -> usize = |_i| 0x0CD50 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_RTTBCNRC: usize = 0x04984;

// BCN (for DCB) Registers
pub const IXGBE_RTTBCNRS: usize = 0x04988;
pub const IXGBE_RTTBCNCR: usize = 0x08B00;
pub const IXGBE_RTTBCNACH: usize = 0x08B04;
pub const IXGBE_RTTBCNACL: usize = 0x08B08;
pub const IXGBE_RTTBCNTG: usize = 0x04A90;
pub const IXGBE_RTTBCNIDX: usize = 0x08B0C;
pub const IXGBE_RTTBCNCP: usize = 0x08B10;
pub const IXGBE_RTFRTIMER: usize = 0x08B14;
pub const IXGBE_RTTBCNRTT: usize = 0x05150;
pub const IXGBE_RTTBCNRD: usize = 0x0498C;

// FCoE DMA Context Registers
// FCoE Direct DMA Context
pub const IXGBE_FCDDC: fn(usize, usize) -> usize = |_i, _j| 0x20000 + (_i * 0x4) + (_j * 0x10);
pub const IXGBE_FCPTRL: usize = 0x02410; // FC User Desc. PTR Low
pub const IXGBE_FCPTRH: usize = 0x02414; // FC User Desc. PTR High
pub const IXGBE_FCBUFF: usize = 0x02418; // FC Buffer Control
pub const IXGBE_FCDMARW: usize = 0x02420; // FC Receive DMA RW
pub const IXGBE_FCBUFF_VALID: usize = 1 << 0; // DMA Context Valid
pub const IXGBE_FCBUFF_BUFFSIZE: usize = 3 << 3; // User Buffer Size
pub const IXGBE_FCBUFF_WRCONTX: usize = 1 << 7; // 0: Initiator, 1: Target
pub const IXGBE_FCBUFF_BUFFCNT: usize = 0x0000ff00; // Number of User Buffers
pub const IXGBE_FCBUFF_OFFSET: usize = 0xffff0000; // User Buffer Offset
pub const IXGBE_FCBUFF_BUFFSIZE_SHIFT: usize = 3;
pub const IXGBE_FCBUFF_BUFFCNT_SHIFT: usize = 8;
pub const IXGBE_FCBUFF_OFFSET_SHIFT: usize = 16;
pub const IXGBE_FCDMARW_WE: usize = 1 << 14; // Write enable
pub const IXGBE_FCDMARW_RE: usize = 1 << 15; // Read enable
pub const IXGBE_FCDMARW_FCOESEL: usize = 0x000001ff; // FC X_ID: 11 bits
pub const IXGBE_FCDMARW_LASTSIZE: usize = 0xffff0000; // Last User Buffer Size
pub const IXGBE_FCDMARW_LASTSIZE_SHIFT: usize = 16;

// FCoE SOF/EOF
pub const IXGBE_TEOFF: usize = 0x04A94; // Tx FC EOF
pub const IXGBE_TSOFF: usize = 0x04A98; // Tx FC SOF
pub const IXGBE_REOFF: usize = 0x05158; // Rx FC EOF
pub const IXGBE_RSOFF: usize = 0x051F8; // Rx FC SOF

// FCoE Filter Context Registers
pub const IXGBE_FCD_ID: usize = 0x05114; // FCoE D_ID
pub const IXGBE_FCSMAC: usize = 0x0510C; // FCoE Source MAC
pub const IXGBE_FCFLTRW_SMAC_HIGH_SHIFT: usize = 16;

// FCoE Direct Filter Context
pub const IXGBE_FCDFC: fn(usize, usize) -> usize = |_i, _j| 0x28000 + (_i * 0x4) + (_j * 0x10);
pub const IXGBE_FCDFCD: fn(usize) -> usize = |_i| 0x30000 + (_i * 0x4);
pub const IXGBE_FCFLT: usize = 0x05108; // FC FLT Context
pub const IXGBE_FCFLTRW: usize = 0x05110; // FC Filter RW Control
pub const IXGBE_FCPARAM: usize = 0x051d8; // FC Offset Parameter
pub const IXGBE_FCFLT_VALID: usize = 1 << 0; // Filter Context Valid
pub const IXGBE_FCFLT_FIRST: usize = 1 << 1; // Filter First
pub const IXGBE_FCFLT_SEQID: usize = 0x00ff0000; // Sequence ID
pub const IXGBE_FCFLT_SEQCNT: usize = 0xff000000; // Sequence Count
pub const IXGBE_FCFLTRW_RVALDT: usize = 1 << 13; // Fast Re-Validation
pub const IXGBE_FCFLTRW_WE: usize = 1 << 14; // Write Enable
pub const IXGBE_FCFLTRW_RE: usize = 1 << 15; // Read Enable

// FCoE Receive Control
pub const IXGBE_FCRXCTRL: usize = 0x05100; // FC Receive Control
pub const IXGBE_FCRXCTRL_FCOELLI: usize = 1 << 0; // Low latency interrupt
pub const IXGBE_FCRXCTRL_SAVBAD: usize = 1 << 1; // Save Bad Frames
pub const IXGBE_FCRXCTRL_FRSTRDH: usize = 1 << 2; // EN 1st Read Header
pub const IXGBE_FCRXCTRL_LASTSEQH: usize = 1 << 3; // EN Last Header in Seq
pub const IXGBE_FCRXCTRL_ALLH: usize = 1 << 4; // EN All Headers
pub const IXGBE_FCRXCTRL_FRSTSEQH: usize = 1 << 5; // EN 1st Seq. Header
pub const IXGBE_FCRXCTRL_ICRC: usize = 1 << 6; // Ignore Bad FC CRC
pub const IXGBE_FCRXCTRL_FCCRCBO: usize = 1 << 7; // FC CRC Byte Ordering
pub const IXGBE_FCRXCTRL_FCOEVER: usize = 0x00000f00; // FCoE Version: 4 bits
pub const IXGBE_FCRXCTRL_FCOEVER_SHIFT: usize = 8;

// FCoE Redirection
pub const IXGBE_FCRECTL: usize = 0x0ED00; // FC Redirection Control
pub const IXGBE_FCRETA0: usize = 0x0ED10; // FC Redirection Table 0
pub const IXGBE_FCRETA: fn(usize) -> usize = |_i| IXGBE_FCRETA0 + (_i * 4); // FCoE Redir
pub const IXGBE_FCRECTL_ENA: usize = 0x1; // FCoE Redir Table Enable
pub const IXGBE_FCRETASEL_ENA: usize = 0x2; // FCoE FCRETASEL bit
pub const IXGBE_FCRETA_SIZE: usize = 8; // Max entries in FCRETA
pub const IXGBE_FCRETA_ENTRY_MASK: usize = 0x0000007f; // 7 bits for the queue index
pub const IXGBE_FCRETA_SIZE_X550: usize = 32; // Max entries in FCRETA
                                              // Higher 7 bits for the queue index
pub const IXGBE_FCRETA_ENTRY_HIGH_MASK: usize = 0x007F0000;
pub const IXGBE_FCRETA_ENTRY_HIGH_SHIFT: usize = 16;

// Stats registers
pub const IXGBE_CRCERRS: usize = 0x04000;
pub const IXGBE_ILLERRC: usize = 0x04004;
pub const IXGBE_ERRBC: usize = 0x04008;
pub const IXGBE_MSPDC: usize = 0x04010;
pub const IXGBE_MPC: fn(usize) -> usize = |_i| 0x03FA0 + (_i * 4); // 8 of these 3FA0-3FBC
pub const IXGBE_MLFC: usize = 0x04034;
pub const IXGBE_MRFC: usize = 0x04038;
pub const IXGBE_RLEC: usize = 0x04040;
pub const IXGBE_LXONTXC: usize = 0x03F60;
pub const IXGBE_LXONRXC: usize = 0x0CF60;
pub const IXGBE_LXOFFTXC: usize = 0x03F68;
pub const IXGBE_LXOFFRXC: usize = 0x0CF68;
pub const IXGBE_LXONRXCNT: usize = 0x041A4;
pub const IXGBE_LXOFFRXCNT: usize = 0x041A8;
pub const IXGBE_PXONRXCNT: fn(usize) -> usize = |_i| 0x04140 + (_i * 4); // 8 of these
pub const IXGBE_PXOFFRXCNT: fn(usize) -> usize = |_i| 0x04160 + (_i * 4); // 8 of these
pub const IXGBE_PXON2OFFCNT: fn(usize) -> usize = |_i| 0x03240 + (_i * 4); // 8 of these
pub const IXGBE_PXONTXC: fn(usize) -> usize = |_i| 0x03F00 + (_i * 4); // 8 of these 3F00-3F1C
pub const IXGBE_PXONRXC: fn(usize) -> usize = |_i| 0x0CF00 + (_i * 4); // 8 of these CF00-CF1C
pub const IXGBE_PXOFFTXC: fn(usize) -> usize = |_i| 0x03F20 + (_i * 4); // 8 of these 3F20-3F3C
pub const IXGBE_PXOFFRXC: fn(usize) -> usize = |_i| 0x0CF20 + (_i * 4); // 8 of these CF20-CF3C
pub const IXGBE_PRC64: usize = 0x0405C;
pub const IXGBE_PRC127: usize = 0x04060;
pub const IXGBE_PRC255: usize = 0x04064;
pub const IXGBE_PRC511: usize = 0x04068;
pub const IXGBE_PRC1023: usize = 0x0406C;
pub const IXGBE_PRC1522: usize = 0x04070;
pub const IXGBE_GPRC: usize = 0x04074;
pub const IXGBE_BPRC: usize = 0x04078;
pub const IXGBE_MPRC: usize = 0x0407C;
pub const IXGBE_GPTC: usize = 0x04080;
pub const IXGBE_GORCL: usize = 0x04088;
pub const IXGBE_GORCH: usize = 0x0408C;
pub const IXGBE_GOTCL: usize = 0x04090;
pub const IXGBE_GOTCH: usize = 0x04094;
pub const IXGBE_RNBC: fn(usize) -> usize = |_i| 0x03FC0 + (_i * 4); // 8 of these 3FC0-3FDC
pub const IXGBE_RUC: usize = 0x040A4;
pub const IXGBE_RFC: usize = 0x040A8;
pub const IXGBE_ROC: usize = 0x040AC;
pub const IXGBE_RJC: usize = 0x040B0;
pub const IXGBE_MNGPRC: usize = 0x040B4;
pub const IXGBE_MNGPDC: usize = 0x040B8;
pub const IXGBE_MNGPTC: usize = 0x0CF90;
pub const IXGBE_TORL: usize = 0x040C0;
pub const IXGBE_TORH: usize = 0x040C4;
pub const IXGBE_TPR: usize = 0x040D0;
pub const IXGBE_TPT: usize = 0x040D4;
pub const IXGBE_PTC64: usize = 0x040D8;
pub const IXGBE_PTC127: usize = 0x040DC;
pub const IXGBE_PTC255: usize = 0x040E0;
pub const IXGBE_PTC511: usize = 0x040E4;
pub const IXGBE_PTC1023: usize = 0x040E8;
pub const IXGBE_PTC1522: usize = 0x040EC;
pub const IXGBE_MPTC: usize = 0x040F0;
pub const IXGBE_BPTC: usize = 0x040F4;
pub const IXGBE_XEC: usize = 0x04120;
pub const IXGBE_SSVPC: usize = 0x08780;

pub const IXGBE_RQSMR: fn(usize) -> usize = |_i| 0x02300 + (_i * 4);
pub const IXGBE_TQSMR: fn(usize) -> usize = |_i| {
    if _i <= 7 {
        0x07300 + (_i * 4)
    } else {
        0x08600 + (_i * 4)
    }
};
pub const IXGBE_TQSM: fn(usize) -> usize = |_i| 0x08600 + (_i * 4);

pub const IXGBE_QPRC: fn(usize) -> usize = |_i| 0x01030 + (_i * 0x40); /* 16 of these */
pub const IXGBE_QPTC: fn(usize) -> usize = |_i| 0x06030 + (_i * 0x40); /* 16 of these */
pub const IXGBE_QBRC: fn(usize) -> usize = |_i| 0x01034 + (_i * 0x40); /* 16 of these */
pub const IXGBE_QBTC: fn(usize) -> usize = |_i| 0x06034 + (_i * 0x40); /* 16 of these */
pub const IXGBE_QBRC_L: fn(usize) -> usize = |_i| 0x01034 + (_i * 0x40); /* 16 of these */
pub const IXGBE_QBRC_H: fn(usize) -> usize = |_i| 0x01038 + (_i * 0x40); /* 16 of these */
pub const IXGBE_QPRDC: fn(usize) -> usize = |_i| 0x01430 + (_i * 0x40); /* 16 of these */
pub const IXGBE_QBTC_L: fn(usize) -> usize = |_i| 0x08700 + (_i * 0x8); /* 16 of these */
pub const IXGBE_QBTC_H: fn(usize) -> usize = |_i| 0x08704 + (_i * 0x8); /* 16 of these */
pub const IXGBE_FCCRC: usize = 0x05118; /* Num of Good Eth CRC w/ Bad FC CRC */
pub const IXGBE_FCOERPDC: usize = 0x0241C; /* FCoE Rx Packets Dropped Count */
pub const IXGBE_FCLAST: usize = 0x02424; /* FCoE Last Error Count */
pub const IXGBE_FCOEPRC: usize = 0x02428; /* Number of FCoE Packets Received */
pub const IXGBE_FCOEDWRC: usize = 0x0242C; /* Number of FCoE DWords Received */
pub const IXGBE_FCOEPTC: usize = 0x08784; /* Number of FCoE Packets Transmitted */
pub const IXGBE_FCOEDWTC: usize = 0x08788; /* Number of FCoE DWords Transmitted */
pub const IXGBE_FCCRC_CNT_MASK: usize = 0x0000FFFF; /* CRC_CNT: bit 0 - 15 */
pub const IXGBE_FCLAST_CNT_MASK: usize = 0x0000FFFF; /* Last_CNT: bit 0 - 15 */
pub const IXGBE_O2BGPTC: usize = 0x041C4;
pub const IXGBE_O2BSPC: usize = 0x087B0;
pub const IXGBE_B2OSPC: usize = 0x041C0;
pub const IXGBE_B2OGPRC: usize = 0x02F90;
pub const IXGBE_BUPRC: usize = 0x04180;
pub const IXGBE_BMPRC: usize = 0x04184;
pub const IXGBE_BBPRC: usize = 0x04188;
pub const IXGBE_BUPTC: usize = 0x0418C;
pub const IXGBE_BMPTC: usize = 0x04190;
pub const IXGBE_BBPTC: usize = 0x04194;
pub const IXGBE_BCRCERRS: usize = 0x04198;
pub const IXGBE_BXONRXC: usize = 0x0419C;
pub const IXGBE_BXOFFRXC: usize = 0x041E0;
pub const IXGBE_BXONTXC: usize = 0x041E4;
pub const IXGBE_BXOFFTXC: usize = 0x041E8;

// Management
pub const IXGBE_MAVTV: fn(usize) -> usize = |_i| 0x05010 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_MFUTP: fn(usize) -> usize = |_i| 0x05030 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_MANC: usize = 0x05820;
pub const IXGBE_MFVAL: usize = 0x05824;
pub const IXGBE_MANC2H: usize = 0x05860;
pub const IXGBE_MDEF: fn(usize) -> usize = |_i| 0x05890 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_MIPAF: usize = 0x058B0;
pub const IXGBE_MMAL: fn(usize) -> usize = |_i| 0x05910 + (_i * 8); /* 4 of these (0-3) */
pub const IXGBE_MMAH: fn(usize) -> usize = |_i| 0x05914 + (_i * 8); /* 4 of these (0-3) */
pub const IXGBE_FTFT: usize = 0x09400; /* 0x9400-0x97FC */
pub const IXGBE_METF: fn(usize) -> usize = |_i| 0x05190 + (_i * 4); /* 4 of these (0-3) */
pub const IXGBE_MDEF_EXT: fn(usize) -> usize = |_i| 0x05160 + (_i * 4); /* 8 of these (0-7) */
pub const IXGBE_LSWFW: usize = 0x15F14;
pub const IXGBE_BMCIP: fn(usize) -> usize = |_i| 0x05050 + (_i * 4); /* 0x5050-0x505C */
pub const IXGBE_BMCIPVAL: usize = 0x05060;
pub const IXGBE_BMCIP_IPADDR_TYPE: usize = 0x00000001;
pub const IXGBE_BMCIP_IPADDR_VALID: usize = 0x00000002;

// Firmware Semaphore Register
pub const IXGBE_FWSM_MODE_MASK: usize = 0xE;
pub const IXGBE_FWSM_TS_ENABLED: u32 = 0x1;
pub const IXGBE_FWSM_FW_MODE_PT: usize = 0x4;

// ARC Subsystem registers
pub const IXGBE_HICR: usize = 0x15F00;
pub const IXGBE_FWSTS: usize = 0x15F0C;
pub const IXGBE_HSMC0R: usize = 0x15F04;
pub const IXGBE_HSMC1R: usize = 0x15F08;
pub const IXGBE_SWSR: usize = 0x15F10;
pub const IXGBE_HFDR: usize = 0x15FE8;
pub const IXGBE_FLEX_MNG: usize = 0x15800; /* 0x15800 - 0x15EFC */

pub const IXGBE_HICR_EN: u32 = 0x01; /* Enable bit - RO */
// Driver sets this bit when done to put command in RAM
pub const IXGBE_HICR_C: u32 = 0x02;
pub const IXGBE_HICR_SV: u32 = 0x04; /* Status Validity */
pub const IXGBE_HICR_FW_RESET_ENABLE: u32 = 0x40;
pub const IXGBE_HICR_FW_RESET: u32 = 0x80;

// PCI-E registers
pub const IXGBE_GCR: usize = 0x11000;
pub const IXGBE_GTV: usize = 0x11004;
pub const IXGBE_FUNCTAG: usize = 0x11008;
pub const IXGBE_GLT: usize = 0x1100C;
pub const IXGBE_PCIEPIPEADR: usize = 0x11004;
pub const IXGBE_PCIEPIPEDAT: usize = 0x11008;
pub const IXGBE_GSCL_1: usize = 0x11010;
pub const IXGBE_GSCL_2: usize = 0x11014;
pub const IXGBE_GSCL_1_X540: usize = IXGBE_GSCL_1;
pub const IXGBE_GSCL_2_X540: usize = IXGBE_GSCL_2;
pub const IXGBE_GSCL_3: usize = 0x11018;
pub const IXGBE_GSCL_4: usize = 0x1101C;
pub const IXGBE_GSCN_0: usize = 0x11020;
pub const IXGBE_GSCN_1: usize = 0x11024;
pub const IXGBE_GSCN_2: usize = 0x11028;
pub const IXGBE_GSCN_3: usize = 0x1102C;
pub const IXGBE_GSCN_0_X540: usize = IXGBE_GSCN_0;
pub const IXGBE_GSCN_1_X540: usize = IXGBE_GSCN_1;
pub const IXGBE_GSCN_2_X540: usize = IXGBE_GSCN_2;
pub const IXGBE_GSCN_3_X540: usize = IXGBE_GSCN_3;
pub const IXGBE_FACTPS: usize = 0x10150;
pub const IXGBE_FACTPS_X540: usize = IXGBE_FACTPS;
pub const IXGBE_GSCL_1_X550: usize = 0x11800;
pub const IXGBE_GSCL_2_X550: usize = 0x11804;
pub const IXGBE_GSCL_1_X550EM_X: usize = IXGBE_GSCL_1_X550;
pub const IXGBE_GSCL_2_X550EM_X: usize = IXGBE_GSCL_2_X550;
pub const IXGBE_GSCN_0_X550: usize = 0x11820;
pub const IXGBE_GSCN_1_X550: usize = 0x11824;
pub const IXGBE_GSCN_2_X550: usize = 0x11828;
pub const IXGBE_GSCN_3_X550: usize = 0x1182C;
pub const IXGBE_GSCN_0_X550EM_X: usize = IXGBE_GSCN_0_X550;
pub const IXGBE_GSCN_1_X550EM_X: usize = IXGBE_GSCN_1_X550;
pub const IXGBE_GSCN_2_X550EM_X: usize = IXGBE_GSCN_2_X550;
pub const IXGBE_GSCN_3_X550EM_X: usize = IXGBE_GSCN_3_X550;
pub const IXGBE_FACTPS_X550: usize = IXGBE_FACTPS;
pub const IXGBE_FACTPS_X550EM_X: usize = IXGBE_FACTPS;
pub const IXGBE_GSCL_1_X550EM_A: usize = IXGBE_GSCL_1_X550;
pub const IXGBE_GSCL_2_X550EM_A: usize = IXGBE_GSCL_2_X550;
pub const IXGBE_GSCN_0_X550EM_A: usize = IXGBE_GSCN_0_X550;
pub const IXGBE_GSCN_1_X550EM_A: usize = IXGBE_GSCN_1_X550;
pub const IXGBE_GSCN_2_X550EM_A: usize = IXGBE_GSCN_2_X550;
pub const IXGBE_GSCN_3_X550EM_A: usize = IXGBE_GSCN_3_X550;
pub const IXGBE_FACTPS_X550EM_A: usize = 0x15FEC;

pub const IXGBE_PCIEANACTL: usize = 0x11040;
pub const IXGBE_SWSM: usize = 0x10140;
pub const IXGBE_SWSM_X540: usize = IXGBE_SWSM;
pub const IXGBE_SWSM_X550: usize = IXGBE_SWSM;
pub const IXGBE_SWSM_X550EM_X: usize = IXGBE_SWSM;
pub const IXGBE_SWSM_X550EM_A: usize = 0x15F70;

pub const IXGBE_FWSM: usize = 0x10148;
pub const IXGBE_FWSM_X540: usize = IXGBE_FWSM;
pub const IXGBE_FWSM_X550: usize = IXGBE_FWSM;
pub const IXGBE_FWSM_X550EM_X: usize = IXGBE_FWSM;
pub const IXGBE_FWSM_X550EM_A: usize = 0x15F74;

pub const IXGBE_SWFW_SYNC: usize = IXGBE_GSSR;
pub const IXGBE_SWFW_SYNC_X540: usize = IXGBE_SWFW_SYNC;
pub const IXGBE_SWFW_SYNC_X550: usize = IXGBE_SWFW_SYNC;
pub const IXGBE_SWFW_SYNC_X550EM_X: usize = IXGBE_SWFW_SYNC;
pub const IXGBE_SWFW_SYNC_X550EM_A: usize = 0x15F78;

pub const IXGBE_GSSR: usize = 0x10160;
pub const IXGBE_MREVID: usize = 0x11064;
pub const IXGBE_DCA_ID: usize = 0x11070;
pub const IXGBE_DCA_CTRL: usize = 0x11074;

// PCI-E registers 82599-Specific
pub const IXGBE_GCR_EXT: usize = 0x11050;
pub const IXGBE_GSCL_5_82599: usize = 0x11030;
pub const IXGBE_GSCL_6_82599: usize = 0x11034;
pub const IXGBE_GSCL_7_82599: usize = 0x11038;
pub const IXGBE_GSCL_8_82599: usize = 0x1103C;
pub const IXGBE_GSCL_5_X540: usize = IXGBE_GSCL_5_82599;
pub const IXGBE_GSCL_6_X540: usize = IXGBE_GSCL_6_82599;
pub const IXGBE_GSCL_7_X540: usize = IXGBE_GSCL_7_82599;
pub const IXGBE_GSCL_8_X540: usize = IXGBE_GSCL_8_82599;
pub const IXGBE_PHYADR_82599: usize = 0x11040;
pub const IXGBE_PHYDAT_82599: usize = 0x11044;
pub const IXGBE_PHYCTL_82599: usize = 0x11048;
pub const IXGBE_PBACLR_82599: usize = 0x11068;
pub const IXGBE_CIAA: usize = 0x11088;
pub const IXGBE_CIAD: usize = 0x1108C;
pub const IXGBE_CIAA_82599: usize = IXGBE_CIAA;
pub const IXGBE_CIAD_82599: usize = IXGBE_CIAD;
pub const IXGBE_CIAA_X540: usize = IXGBE_CIAA;
pub const IXGBE_CIAD_X540: usize = IXGBE_CIAD;
pub const IXGBE_GSCL_5_X550: usize = 0x11810;
pub const IXGBE_GSCL_6_X550: usize = 0x11814;
pub const IXGBE_GSCL_7_X550: usize = 0x11818;
pub const IXGBE_GSCL_8_X550: usize = 0x1181C;
pub const IXGBE_GSCL_5_X550EM_X: usize = IXGBE_GSCL_5_X550;
pub const IXGBE_GSCL_6_X550EM_X: usize = IXGBE_GSCL_6_X550;
pub const IXGBE_GSCL_7_X550EM_X: usize = IXGBE_GSCL_7_X550;
pub const IXGBE_GSCL_8_X550EM_X: usize = IXGBE_GSCL_8_X550;
pub const IXGBE_CIAA_X550: usize = 0x11508;
pub const IXGBE_CIAD_X550: usize = 0x11510;
pub const IXGBE_CIAA_X550EM_X: usize = IXGBE_CIAA_X550;
pub const IXGBE_CIAD_X550EM_X: usize = IXGBE_CIAD_X550;
pub const IXGBE_GSCL_5_X550EM_A: usize = IXGBE_GSCL_5_X550;
pub const IXGBE_GSCL_6_X550EM_A: usize = IXGBE_GSCL_6_X550;
pub const IXGBE_GSCL_7_X550EM_A: usize = IXGBE_GSCL_7_X550;
pub const IXGBE_GSCL_8_X550EM_A: usize = IXGBE_GSCL_8_X550;
pub const IXGBE_CIAA_X550EM_A: usize = IXGBE_CIAA_X550;
pub const IXGBE_CIAD_X550EM_A: usize = IXGBE_CIAD_X550;
pub const IXGBE_PICAUSE: usize = 0x110B0;
pub const IXGBE_PIENA: usize = 0x110B8;
pub const IXGBE_CDQ_MBR_82599: usize = 0x110B4;
pub const IXGBE_PCIESPARE: usize = 0x110BC;
pub const IXGBE_MISC_REG_82599: usize = 0x110F0;
pub const IXGBE_ECC_CTRL_0_82599: usize = 0x11100;
pub const IXGBE_ECC_CTRL_1_82599: usize = 0x11104;
pub const IXGBE_ECC_STATUS_82599: usize = 0x110E0;
pub const IXGBE_BAR_CTRL_82599: usize = 0x110F4;

// PCI Express Control
pub const IXGBE_GCR_CMPL_TMOUT_MASK: usize = 0x0000F000;
pub const IXGBE_GCR_CMPL_TMOUT_10MS: usize = 0x00001000;
pub const IXGBE_GCR_CMPL_TMOUT_RESEND: usize = 0x00010000;
pub const IXGBE_GCR_CAP_VER2: usize = 0x00040000;

pub const IXGBE_GCR_EXT_MSIX_EN: usize = 0x80000000;
pub const IXGBE_GCR_EXT_BUFFERS_CLEAR: usize = 0x40000000;
pub const IXGBE_GCR_EXT_VT_MODE_16: usize = 0x00000001;
pub const IXGBE_GCR_EXT_VT_MODE_32: usize = 0x00000002;
pub const IXGBE_GCR_EXT_VT_MODE_64: usize = 0x00000003;
pub const IXGBE_GCR_EXT_SRIOV: usize = IXGBE_GCR_EXT_MSIX_EN | IXGBE_GCR_EXT_VT_MODE_64;
pub const IXGBE_GCR_EXT_VT_MODE_MASK: usize = 0x00000003;

// Time Sync Registers
pub const IXGBE_TSYNCRXCTL: usize = 0x05188; // Rx Time Sync Control register - RW
pub const IXGBE_TSYNCTXCTL: usize = 0x08C00; // Tx Time Sync Control register - RW
pub const IXGBE_RXSTMPL: usize = 0x051E8; // Rx timestamp Low - RO
pub const IXGBE_RXSTMPH: usize = 0x051A4; // Rx timestamp High - RO
pub const IXGBE_RXSATRL: usize = 0x051A0; // Rx timestamp attribute low - RO
pub const IXGBE_RXSATRH: usize = 0x051A8; // Rx timestamp attribute high - RO
pub const IXGBE_RXMTRL: usize = 0x05120; // RX message type register low - RW
pub const IXGBE_TXSTMPL: usize = 0x08C04; // Tx timestamp value Low - RO
pub const IXGBE_TXSTMPH: usize = 0x08C08; // Tx timestamp value High - RO
pub const IXGBE_SYSTIML: usize = 0x08C0C; // System time register Low - RO
pub const IXGBE_SYSTIMH: usize = 0x08C10; // System time register High - RO
pub const IXGBE_SYSTIMR: usize = 0x08C58; // System time register Residue - RO
pub const IXGBE_TIMINCA: usize = 0x08C14; // Increment attributes register - RW
pub const IXGBE_TIMADJL: usize = 0x08C18; // Time Adjustment Offset register Low - RW
pub const IXGBE_TIMADJH: usize = 0x08C1C; // Time Adjustment Offset register High - RW
pub const IXGBE_TSAUXC: usize = 0x08C20; // TimeSync Auxiliary Control register - RW
pub const IXGBE_TRGTTIML0: usize = 0x08C24; // Target Time Register 0 Low - RW
pub const IXGBE_TRGTTIMH0: usize = 0x08C28; // Target Time Register 0 High - RW
pub const IXGBE_TRGTTIML1: usize = 0x08C2C; // Target Time Register 1 Low - RW
pub const IXGBE_TRGTTIMH1: usize = 0x08C30; // Target Time Register 1 High - RW
pub const IXGBE_CLKTIML: usize = 0x08C34; // Clock Out Time Register Low - RW
pub const IXGBE_CLKTIMH: usize = 0x08C38; // Clock Out Time Register High - RW
pub const IXGBE_FREQOUT0: usize = 0x08C34; // Frequency Out 0 Control register - RW
pub const IXGBE_FREQOUT1: usize = 0x08C38; // Frequency Out 1 Control register - RW
pub const IXGBE_AUXSTMPL0: usize = 0x08C3C; // Auxiliary Time Stamp 0 register Low - RO
pub const IXGBE_AUXSTMPH0: usize = 0x08C40; // Auxiliary Time Stamp 0 register High - RO
pub const IXGBE_AUXSTMPL1: usize = 0x08C44; // Auxiliary Time Stamp 1 register Low - RO
pub const IXGBE_AUXSTMPH1: usize = 0x08C48; // Auxiliary Time Stamp 1 register High - RO
pub const IXGBE_TSIM: usize = 0x08C68; // TimeSync Interrupt Mask Register - RW
pub const IXGBE_TSICR: usize = 0x08C60; // TimeSync Interrupt Cause Register - WO
pub const IXGBE_TSSDP: usize = 0x0003C; // TimeSync SDP Configuration Register - RW

// Diagnostic Registers
pub const IXGBE_RDSTATCTL: usize = 0x02C20;
pub const IXGBE_RDSTAT: fn(usize) -> usize = |_i| 0x02C00 + (_i * 4); // 0x02C00-0x02C1C
pub const IXGBE_RDHMPN: usize = 0x02F08;
pub const IXGBE_RIC_DW: fn(usize) -> usize = |_i| 0x02F10 + (_i * 4);
pub const IXGBE_RDPROBE: usize = 0x02F20;
pub const IXGBE_RDMAM: usize = 0x02F30;
pub const IXGBE_RDMAD: usize = 0x02F34;
pub const IXGBE_TDHMPN: usize = 0x07F08;
pub const IXGBE_TDHMPN2: usize = 0x082FC;
pub const IXGBE_TXDESCIC: usize = 0x082CC;
pub const IXGBE_TIC_DW: fn(usize) -> usize = |_i| 0x07F10 + (_i * 4);
pub const IXGBE_TIC_DW2: fn(usize) -> usize = |_i| 0x082B0 + (_i * 4);
pub const IXGBE_TDPROBE: usize = 0x07F20;
pub const IXGBE_TXBUFCTRL: usize = 0x0C600;
pub const IXGBE_TXBUFDATA0: usize = 0x0C610;
pub const IXGBE_TXBUFDATA1: usize = 0x0C614;
pub const IXGBE_TXBUFDATA2: usize = 0x0C618;
pub const IXGBE_TXBUFDATA3: usize = 0x0C61C;
pub const IXGBE_RXBUFCTRL: usize = 0x03600;
pub const IXGBE_RXBUFDATA0: usize = 0x03610;
pub const IXGBE_RXBUFDATA1: usize = 0x03614;
pub const IXGBE_RXBUFDATA2: usize = 0x03618;
pub const IXGBE_RXBUFDATA3: usize = 0x0361C;
pub const IXGBE_PCIE_DIAG: fn(usize) -> usize = |_i| 0x11090 + (_i * 4); // 8 of these
pub const IXGBE_RFVAL: usize = 0x050A4;
pub const IXGBE_MDFTC1: usize = 0x042B8;
pub const IXGBE_MDFTC2: usize = 0x042C0;
pub const IXGBE_MDFTFIFO1: usize = 0x042C4;
pub const IXGBE_MDFTFIFO2: usize = 0x042C8;
pub const IXGBE_MDFTS: usize = 0x042CC;
pub const IXGBE_RXDATAWRPTR: fn(usize) -> usize = |_i| 0x03700 + (_i * 4); // 8 of these 3700-370C
pub const IXGBE_RXDESCWRPTR: fn(usize) -> usize = |_i| 0x03710 + (_i * 4); // 8 of these 3710-371C
pub const IXGBE_RXDATARDPTR: fn(usize) -> usize = |_i| 0x03720 + (_i * 4); // 8 of these 3720-372C
pub const IXGBE_RXDESCRDPTR: fn(usize) -> usize = |_i| 0x03730 + (_i * 4); // 8 of these 3730-373C
pub const IXGBE_TXDATAWRPTR: fn(usize) -> usize = |_i| 0x0C700 + (_i * 4); // 8 of these C700-C70C
pub const IXGBE_TXDESCWRPTR: fn(usize) -> usize = |_i| 0x0C710 + (_i * 4); // 8 of these C710-C71C
pub const IXGBE_TXDATARDPTR: fn(usize) -> usize = |_i| 0x0C720 + (_i * 4); // 8 of these C720-C72C
pub const IXGBE_TXDESCRDPTR: fn(usize) -> usize = |_i| 0x0C730 + (_i * 4); // 8 of these C730-C73C
pub const IXGBE_PCIEECCCTL: usize = 0x1106C;
pub const IXGBE_RXWRPTR: fn(usize) -> usize = |i| 0x03100 + (i * 4);
pub const IXGBE_RXUSED: fn(usize) -> usize = |i| 0x03120 + (i * 4);
pub const IXGBE_RXRDPTR: fn(usize) -> usize = |i| 0x03140 + (i * 4);
pub const IXGBE_RXRDWRPTR: fn(usize) -> usize = |i| 0x03160 + (i * 4);
pub const IXGBE_TXWRPTR: fn(usize) -> usize = |i| 0x0C100 + (i * 4);
pub const IXGBE_TXUSED: fn(usize) -> usize = |i| 0x0C120 + (i * 4);
pub const IXGBE_TXRDPTR: fn(usize) -> usize = |i| 0x0C140 + (i * 4);
pub const IXGBE_TXRDWRPTR: fn(usize) -> usize = |i| 0x0C160 + (i * 4);
pub const IXGBE_PCIEECCCTL0: usize = 0x11100;
pub const IXGBE_PCIEECCCTL1: usize = 0x11104;
pub const IXGBE_RXDBUECC: usize = 0x03F70;
pub const IXGBE_TXDBUECC: usize = 0x0CF70;
pub const IXGBE_RXDBUEST: usize = 0x03F74;
pub const IXGBE_TXDBUEST: usize = 0x0CF74;
pub const IXGBE_PBTXECC: usize = 0x0C300;
pub const IXGBE_PBRXECC: usize = 0x03300;
pub const IXGBE_GHECCR: usize = 0x110B0;

// MAC Registers
pub const IXGBE_PCS1GCFIG: usize = 0x04200;
pub const IXGBE_PCS1GLCTL: usize = 0x04208;
pub const IXGBE_PCS1GLSTA: usize = 0x0420C;
pub const IXGBE_PCS1GDBG0: usize = 0x04210;
pub const IXGBE_PCS1GDBG1: usize = 0x04214;
pub const IXGBE_PCS1GANA: usize = 0x04218;
pub const IXGBE_PCS1GANLP: usize = 0x0421C;
pub const IXGBE_PCS1GANNP: usize = 0x04220;
pub const IXGBE_PCS1GANLPNP: usize = 0x04224;
pub const IXGBE_HLREG0: usize = 0x04240;
pub const IXGBE_HLREG1: usize = 0x04244;
pub const IXGBE_PAP: usize = 0x04248;
pub const IXGBE_MACA: usize = 0x0424C;
pub const IXGBE_APAE: usize = 0x04250;
pub const IXGBE_ARD: usize = 0x04254;
pub const IXGBE_AIS: usize = 0x04258;
pub const IXGBE_MSCA: usize = 0x0425C;
pub const IXGBE_MSRWD: usize = 0x04260;
pub const IXGBE_MLADD: usize = 0x04264;
pub const IXGBE_MHADD: usize = 0x04268;
pub const IXGBE_MAXFRS: usize = 0x04268;
pub const IXGBE_TREG: usize = 0x0426C;
pub const IXGBE_PCSS1: usize = 0x04288;
pub const IXGBE_PCSS2: usize = 0x0428C;
pub const IXGBE_XPCSS: usize = 0x04290;
pub const IXGBE_MFLCN: usize = 0x04294;
pub const IXGBE_SERDESC: usize = 0x04298;
pub const IXGBE_MAC_SGMII_BUSY: usize = 0x04298;
pub const IXGBE_MACS: usize = 0x0429C;
pub const IXGBE_AUTOC: usize = 0x042A0;
pub const IXGBE_LINKS: usize = 0x042A4;
pub const IXGBE_LINKS2: usize = 0x04324;
pub const IXGBE_AUTOC2: usize = 0x042A8;
pub const IXGBE_AUTOC3: usize = 0x042AC;
pub const IXGBE_ANLP1: usize = 0x042B0;
pub const IXGBE_ANLP2: usize = 0x042B4;
pub const IXGBE_MACC: usize = 0x04330;
pub const IXGBE_ATLASCTL: usize = 0x04800;
pub const IXGBE_MMNGC: usize = 0x042D0;
pub const IXGBE_ANLPNP1: usize = 0x042D4;
pub const IXGBE_ANLPNP2: usize = 0x042D8;
pub const IXGBE_KRPCSFC: usize = 0x042E0;
pub const IXGBE_KRPCSS: usize = 0x042E4;
pub const IXGBE_FECS1: usize = 0x042E8;
pub const IXGBE_FECS2: usize = 0x042EC;
pub const IXGBE_SMADARCTL: usize = 0x14F10;
pub const IXGBE_MPVC: usize = 0x04318;
pub const IXGBE_SGMIIC: usize = 0x04314;

// Statistics Registers
pub const IXGBE_RXNFGPC: usize = 0x041B0;
pub const IXGBE_RXNFGBCL: usize = 0x041B4;
pub const IXGBE_RXNFGBCH: usize = 0x041B8;
pub const IXGBE_RXDGPC: usize = 0x02F50;
pub const IXGBE_RXDGBCL: usize = 0x02F54;
pub const IXGBE_RXDGBCH: usize = 0x02F58;
pub const IXGBE_RXDDGPC: usize = 0x02F5C;
pub const IXGBE_RXDDGBCL: usize = 0x02F60;
pub const IXGBE_RXDDGBCH: usize = 0x02F64;
pub const IXGBE_RXLPBKGPC: usize = 0x02F68;
pub const IXGBE_RXLPBKGBCL: usize = 0x02F6C;
pub const IXGBE_RXLPBKGBCH: usize = 0x02F70;
pub const IXGBE_RXDLPBKGPC: usize = 0x02F74;
pub const IXGBE_RXDLPBKGBCL: usize = 0x02F78;
pub const IXGBE_RXDLPBKGBCH: usize = 0x02F7C;
pub const IXGBE_TXDGPC: usize = 0x087A0;
pub const IXGBE_TXDGBCL: usize = 0x087A4;
pub const IXGBE_TXDGBCH: usize = 0x087A8;

pub const IXGBE_RXDSTATCTRL: usize = 0x02F40;

// Copper Pond 2 link timeout
pub const IXGBE_VALIDATE_LINK_READY_TIMEOUT: usize = 50;

// Omer CORECTL
pub const IXGBE_CORECTL: usize = 0x014F00;

// BARCTRL
pub const IXGBE_BARCTRL: usize = 0x110F4;
pub const IXGBE_BARCTRL_FLSIZE: usize = 0x0700;
pub const IXGBE_BARCTRL_FLSIZE_SHIFT: usize = 8;
pub const IXGBE_BARCTRL_CSRSIZE: usize = 0x2000;

// RSCCTL Bit Masks
pub const IXGBE_RSCCTL_RSCEN: usize = 0x01;
pub const IXGBE_RSCCTL_MAXDESC_1: usize = 0x00;
pub const IXGBE_RSCCTL_MAXDESC_4: usize = 0x04;
pub const IXGBE_RSCCTL_MAXDESC_8: usize = 0x08;
pub const IXGBE_RSCCTL_MAXDESC_16: usize = 0x0C;
pub const IXGBE_RSCCTL_TS_DIS: usize = 0x02;

// RSCDBU Bit Masks
pub const IXGBE_RSCDBU_RSCSMALDIS_MASK: usize = 0x0000007F;
pub const IXGBE_RSCDBU_RSCACKDIS: usize = 0x00000080;

// RDRXCTL Bit Masks
pub const IXGBE_RDRXCTL_RDMTS_1_2: usize = 0x00000000; // Rx Desc Min THLD Size
pub const IXGBE_RDRXCTL_CRCSTRIP: usize = 0x00000002; // CRC Strip
pub const IXGBE_RDRXCTL_PSP: usize = 0x00000004; // Pad Small Packet
pub const IXGBE_RDRXCTL_MVMEN: usize = 0x00000020;
pub const IXGBE_RDRXCTL_RSC_PUSH_DIS: usize = 0x00000020;
pub const IXGBE_RDRXCTL_DMAIDONE: usize = 0x00000008; // DMA init cycle done
pub const IXGBE_RDRXCTL_RSC_PUSH: usize = 0x00000080;
pub const IXGBE_RDRXCTL_AGGDIS: usize = 0x00010000; // Aggregation disable
pub const IXGBE_RDRXCTL_RSCFRSTSIZE: usize = 0x003E0000; // RSC First packet size
pub const IXGBE_RDRXCTL_RSCLLIDIS: usize = 0x00800000; // Disable RSC compl on LLI
pub const IXGBE_RDRXCTL_RSCACKC: usize = 0x02000000; // must set 1 when RSC enabled
pub const IXGBE_RDRXCTL_FCOE_WRFIX: usize = 0x04000000; // must set 1 when RSC enabled
pub const IXGBE_RDRXCTL_MBINTEN: usize = 0x10000000;
pub const IXGBE_RDRXCTL_MDP_EN: usize = 0x20000000;

// RQTC Bit Masks and Shifts
pub fn ixgbe_rqtc_shift_tc(i: usize) -> usize {
    i * 4
}
pub const IXGBE_RQTC_TC0_MASK: usize = 0x7 << 0;
pub const IXGBE_RQTC_TC1_MASK: usize = 0x7 << 4;
pub const IXGBE_RQTC_TC2_MASK: usize = 0x7 << 8;
pub const IXGBE_RQTC_TC3_MASK: usize = 0x7 << 12;
pub const IXGBE_RQTC_TC4_MASK: usize = 0x7 << 16;
pub const IXGBE_RQTC_TC5_MASK: usize = 0x7 << 20;
pub const IXGBE_RQTC_TC6_MASK: usize = 0x7 << 24;
pub const IXGBE_RQTC_TC7_MASK: usize = 0x7 << 28;

// PSRTYPE.RQPL Bit masks and shift
pub const IXGBE_PSRTYPE_RQPL_MASK: usize = 0x7;
pub const IXGBE_PSRTYPE_RQPL_SHIFT: usize = 29;

// CTRL Bit Masks
pub const IXGBE_CTRL_GIO_DIS: u32 = 0x00000004; // Global IO Master Disable bit
pub const IXGBE_CTRL_LNK_RST: u32 = 0x00000008; // Link Reset. Resets everything.
pub const IXGBE_CTRL_RST: u32 = 0x04000000; // Reset (SW)
pub const IXGBE_CTRL_RST_MASK: u32 = IXGBE_CTRL_LNK_RST | IXGBE_CTRL_RST;

// FACTPS
pub const IXGBE_FACTPS_MNGCG: u32 = 0x20000000; // Manageability Clock Gated
pub const IXGBE_FACTPS_LFS: u32 = 0x40000000; // LAN Function Select

// MHADD Bit Masks
pub const IXGBE_MHADD_MFS_MASK: u32 = 0xFFFF0000;
pub const IXGBE_MHADD_MFS_SHIFT: u32 = 16;

// Extended Device Control
pub const IXGBE_CTRL_EXT_PFRSTD: u32 = 0x00004000; // Physical Function Reset Done
pub const IXGBE_CTRL_EXT_NS_DIS: u32 = 0x00010000; // No Snoop disable
pub const IXGBE_CTRL_EXT_RO_DIS: u32 = 0x00020000; // Relaxed Ordering disable
pub const IXGBE_CTRL_EXT_DRV_LOAD: u32 = 0x10000000; // Driver loaded bit for FW

// Direct Cache Access (DCA) definitions
pub const IXGBE_DCA_CTRL_DCA_ENABLE: usize = 0x00000000; // DCA Enable
pub const IXGBE_DCA_CTRL_DCA_DISABLE: usize = 0x00000001; // DCA Disable

pub const IXGBE_DCA_CTRL_DCA_MODE_CB1: usize = 0x00; // DCA Mode CB1
pub const IXGBE_DCA_CTRL_DCA_MODE_CB2: usize = 0x02; // DCA Mode CB2

pub const IXGBE_DCA_RXCTRL_CPUID_MASK: u32 = 0x0000001F; // Rx CPUID Mask
pub const IXGBE_DCA_RXCTRL_CPUID_MASK_82599: u32 = 0xFF000000; // Rx CPUID Mask
pub const IXGBE_DCA_RXCTRL_CPUID_SHIFT_82599: u32 = 24; // Rx CPUID Shift
pub const IXGBE_DCA_RXCTRL_DESC_DCA_EN: u32 = 1 << 5; // Rx Desc enable
pub const IXGBE_DCA_RXCTRL_HEAD_DCA_EN: u32 = 1 << 6; // Rx Desc header enable
pub const IXGBE_DCA_RXCTRL_DATA_DCA_EN: u32 = 1 << 7; // Rx Desc payload enable
pub const IXGBE_DCA_RXCTRL_DESC_RRO_EN: u32 = 1 << 9; // Rx read Desc Relax Order
pub const IXGBE_DCA_RXCTRL_DATA_WRO_EN: u32 = 1 << 13; // Rx write data Relax Order
pub const IXGBE_DCA_RXCTRL_HEAD_WRO_EN: u32 = 1 << 15; // Rx write header RO

pub const IXGBE_DCA_TXCTRL_CPUID_MASK: u32 = 0x0000001F; // Tx CPUID Mask
pub const IXGBE_DCA_TXCTRL_CPUID_MASK_82599: u32 = 0xFF000000; // Tx CPUID Mask
pub const IXGBE_DCA_TXCTRL_CPUID_SHIFT_82599: u32 = 24; // Tx CPUID Shift
pub const IXGBE_DCA_TXCTRL_DESC_DCA_EN: u32 = 1 << 5; // DCA Tx Desc enable
pub const IXGBE_DCA_TXCTRL_DESC_RRO_EN: u32 = 1 << 9; // Tx read Desc Relax Order
pub const IXGBE_DCA_TXCTRL_DESC_WRO_EN: u32 = 1 << 11; // Tx Desc writeback RO bit
pub const IXGBE_DCA_TXCTRL_DATA_RRO_EN: u32 = 1 << 13; // Tx read data Relax Order

// MSCA Bit Masks
pub const IXGBE_MSCA_NP_ADDR_MASK: usize = 0x0000FFFF; // MDI Addr (new protocol)
pub const IXGBE_MSCA_NP_ADDR_SHIFT: usize = 0;
pub const IXGBE_MSCA_DEV_TYPE_MASK: usize = 0x001F0000; // Dev Type (new protocol)
pub const IXGBE_MSCA_DEV_TYPE_SHIFT: usize = 16; // Register Address (old protocol)
pub const IXGBE_MSCA_PHY_ADDR_MASK: usize = 0x03E00000; // PHY Address mask
pub const IXGBE_MSCA_PHY_ADDR_SHIFT: usize = 21; // PHY Address shift
pub const IXGBE_MSCA_OP_CODE_MASK: usize = 0x0C000000; // OP CODE mask
pub const IXGBE_MSCA_OP_CODE_SHIFT: usize = 26; // OP CODE shift
pub const IXGBE_MSCA_ADDR_CYCLE: usize = 0x00000000; // OP CODE 00 (address cycle)
pub const IXGBE_MSCA_WRITE: usize = 0x04000000; // OP CODE 01 (write)
pub const IXGBE_MSCA_READ: usize = 0x0C000000; // OP CODE 11 (read)
pub const IXGBE_MSCA_READ_AUTOINC: usize = 0x08000000; // OP CODE 10 (read auto increment)
pub const IXGBE_MSCA_ST_CODE_MASK: usize = 0x30000000; // ST Code mask
pub const IXGBE_MSCA_ST_CODE_SHIFT: usize = 28; // ST Code shift
pub const IXGBE_MSCA_NEW_PROTOCOL: usize = 0x00000000; // ST CODE 00 (new protocol)
pub const IXGBE_MSCA_OLD_PROTOCOL: usize = 0x10000000; // ST CODE 01 (old protocol)
pub const IXGBE_MSCA_MDI_COMMAND: usize = 0x40000000; // Initiate MDI command
pub const IXGBE_MSCA_MDI_IN_PROG_EN: usize = 0x80000000; // MDI in progress enable

// MSRWD bit masks
pub const IXGBE_MSRWD_WRITE_DATA_MASK: usize = 0x0000FFFF;
pub const IXGBE_MSRWD_WRITE_DATA_SHIFT: usize = 0;
pub const IXGBE_MSRWD_READ_DATA_MASK: usize = 0xFFFF0000;
pub const IXGBE_MSRWD_READ_DATA_SHIFT: usize = 16;

// Atlas registers
pub const IXGBE_ATLAS_PDN_LPBK: usize = 0x24;
pub const IXGBE_ATLAS_PDN_10G: usize = 0xB;
pub const IXGBE_ATLAS_PDN_1G: usize = 0xC;
pub const IXGBE_ATLAS_PDN_AN: usize = 0xD;

// Atlas bit masks
pub const IXGBE_ATLASCTL_WRITE_CMD: usize = 0x00010000;
pub const IXGBE_ATLAS_PDN_TX_REG_EN: usize = 0x10;
pub const IXGBE_ATLAS_PDN_TX_10G_QL_ALL: usize = 0xF0;
pub const IXGBE_ATLAS_PDN_TX_1G_QL_ALL: usize = 0xF0;
pub const IXGBE_ATLAS_PDN_TX_AN_QL_ALL: usize = 0xF0;

// Omer bit masks
pub const IXGBE_CORECTL_WRITE_CMD: usize = 0x00010000;

pub const IXGBE_MDIO_ZERO_DEV_TYPE: u32 = 0x0;
pub const IXGBE_MDIO_PMA_PMD_DEV_TYPE: u32 = 0x1;
pub const IXGBE_MDIO_PCS_DEV_TYPE: u32 = 0x3;
pub const IXGBE_MDIO_PHY_XS_DEV_TYPE: u32 = 0x4;
pub const IXGBE_MDIO_AUTO_NEG_DEV_TYPE: u32 = 0x7;
pub const IXGBE_MDIO_VENDOR_SPECIFIC_1_DEV_TYPE: u32 = 0x1E; // Device 30
pub const IXGBE_TWINAX_DEV: u32 = 1;

pub const IXGBE_MDIO_COMMAND_TIMEOUT: u32 = 100; // PHY Timeout for 1 GB mode

pub const IXGBE_MDIO_VENDOR_SPECIFIC_1_CONTROL: u32 = 0x0; // VS1 Ctrl Reg
pub const IXGBE_MDIO_VENDOR_SPECIFIC_1_STATUS: u32 = 0x1; // VS1 Status Reg
pub const IXGBE_MDIO_VENDOR_SPECIFIC_1_LINK_STATUS: u32 = 0x0008; // 1 = Link Up
pub const IXGBE_MDIO_VENDOR_SPECIFIC_1_SPEED_STATUS: u32 = 0x0010; // 0-10G, 1-1G
pub const IXGBE_MDIO_VENDOR_SPECIFIC_1_10G_SPEED: u32 = 0x0018;
pub const IXGBE_MDIO_VENDOR_SPECIFIC_1_1G_SPEED: u32 = 0x0010;

pub const IXGBE_MDIO_AUTO_NEG_CONTROL: u32 = 0x0; // AUTO_NEG Control Reg
pub const IXGBE_MDIO_AUTO_NEG_STATUS: u32 = 0x1; // AUTO_NEG Status Reg
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_STAT: u32 = 0xC800; // AUTO_NEG Vendor Status Reg
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_TX_ALARM: u32 = 0xCC00; // AUTO_NEG Vendor TX Reg
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_TX_ALARM2: u32 = 0xCC01; // AUTO_NEG Vendor Tx Reg
pub const IXGBE_MDIO_AUTO_NEG_VEN_LSC: u32 = 0x1; // AUTO_NEG Vendor Tx LSC
pub const IXGBE_MDIO_AUTO_NEG_ADVT: u32 = 0x10; // AUTO_NEG Advt Reg
pub const IXGBE_MDIO_AUTO_NEG_LP: u32 = 0x13; // AUTO_NEG LP Status Reg
pub const IXGBE_MDIO_AUTO_NEG_EEE_ADVT: u32 = 0x3C; // AUTO_NEG EEE Advt Reg
pub const IXGBE_AUTO_NEG_10GBASE_EEE_ADVT: u32 = 0x8; // AUTO NEG EEE 10GBaseT Advt
pub const IXGBE_AUTO_NEG_1000BASE_EEE_ADVT: u32 = 0x4; // AUTO NEG EEE 1000BaseT Advt
pub const IXGBE_AUTO_NEG_100BASE_EEE_ADVT: u32 = 0x2; // AUTO NEG EEE 100BaseT Advt
pub const IXGBE_MDIO_PHY_XS_CONTROL: u32 = 0x0; // PHY_XS Control Reg
pub const IXGBE_MDIO_PHY_XS_RESET: u32 = 0x8000; // PHY_XS Reset
pub const IXGBE_MDIO_PHY_ID_HIGH: u32 = 0x2; // PHY ID High Reg
pub const IXGBE_MDIO_PHY_ID_LOW: u32 = 0x3; // PHY ID Low Reg
pub const IXGBE_MDIO_PHY_SPEED_ABILITY: u32 = 0x4; // Speed Ability Reg
pub const IXGBE_MDIO_PHY_SPEED_10G: u32 = 0x0001; // 10G capable
pub const IXGBE_MDIO_PHY_SPEED_1G: u32 = 0x0010; // 1G capable
pub const IXGBE_MDIO_PHY_SPEED_100M: u32 = 0x0020; // 100M capable
pub const IXGBE_MDIO_PHY_EXT_ABILITY: u32 = 0xB; // Ext Ability Reg
pub const IXGBE_MDIO_PHY_10GBASET_ABILITY: u32 = 0x0004; // 10GBaseT capable
pub const IXGBE_MDIO_PHY_1000BASET_ABILITY: u32 = 0x0020; // 1000BaseT capable
pub const IXGBE_MDIO_PHY_100BASETX_ABILITY: u32 = 0x0080; // 100BaseTX capable
pub const IXGBE_MDIO_PHY_SET_LOW_POWER_MODE: u32 = 0x0800; // Set low power mode
pub const IXGBE_AUTO_NEG_LP_STATUS: u32 = 0xE820; // AUTO NEG Rx LP Status Reg
pub const IXGBE_AUTO_NEG_LP_1000BASE_CAP: u32 = 0x8000; // AUTO NEG Rx LP 1000BaseT Cap
pub const IXGBE_AUTO_NEG_LP_10GBASE_CAP: u32 = 0x0800; // AUTO NEG Rx LP 10GBaseT Cap
pub const IXGBE_AUTO_NEG_10GBASET_STAT: u32 = 0x0021; // AUTO NEG 10G BaseT Stat

pub const IXGBE_MDIO_TX_VENDOR_ALARMS_3: u32 = 0xCC02; // Vendor Alarms 3 Reg
pub const IXGBE_MDIO_TX_VENDOR_ALARMS_3_RST_MASK: u32 = 0x3; // PHY Reset Complete Mask
pub const IXGBE_MDIO_GLOBAL_RES_PR_10: u32 = 0xC479; // Global Resv Provisioning 10 Reg
pub const IXGBE_MDIO_POWER_UP_STALL: u32 = 0x8000; // Power Up Stall
pub const IXGBE_MDIO_GLOBAL_INT_CHIP_STD_MASK: u32 = 0xFF00; // int std mask
pub const IXGBE_MDIO_GLOBAL_CHIP_STD_INT_FLAG: u32 = 0xFC00; // chip std int flag
pub const IXGBE_MDIO_GLOBAL_INT_CHIP_VEN_MASK: u32 = 0xFF01; // int chip-wide mask
pub const IXGBE_MDIO_GLOBAL_INT_CHIP_VEN_FLAG: u32 = 0xFC01; // int chip-wide mask
pub const IXGBE_MDIO_GLOBAL_ALARM_1: u32 = 0xCC00; // Global alarm 1
pub const IXGBE_MDIO_GLOBAL_ALM_1_DEV_FAULT: u32 = 0x0010; // device fault
pub const IXGBE_MDIO_GLOBAL_ALM_1_HI_TMP_FAIL: u32 = 0x4000; // high temp failure
pub const IXGBE_MDIO_GLOBAL_FAULT_MSG: u32 = 0xC850; // Global Fault Message
pub const IXGBE_MDIO_GLOBAL_FAULT_MSG_HI_TMP: u32 = 0x8007; // high temp failure
pub const IXGBE_MDIO_GLOBAL_INT_MASK: u32 = 0xD400; // Global int mask
pub const IXGBE_MDIO_GLOBAL_AN_VEN_ALM_INT_EN: u32 = 0x1000; // autoneg vendor alarm int enable
pub const IXGBE_MDIO_GLOBAL_ALARM_1_INT: u32 = 0x4; // int in Global alarm 1
pub const IXGBE_MDIO_GLOBAL_VEN_ALM_INT_EN: u32 = 0x1; // vendor alarm int enable
pub const IXGBE_MDIO_GLOBAL_STD_ALM2_INT: u32 = 0x200; // vendor alarm2 int mask
pub const IXGBE_MDIO_GLOBAL_INT_HI_TEMP_EN: u32 = 0x4000; // int high temp enable
pub const IXGBE_MDIO_GLOBAL_INT_DEV_FAULT_EN: u32 = 0x0010; // int dev fault enable
pub const IXGBE_MDIO_PMA_PMD_CONTROL_ADDR: u32 = 0x0000; // PMA/PMD Control Reg
pub const IXGBE_MDIO_PMA_PMD_SDA_SCL_ADDR: u32 = 0xC30A; // PHY_XS SDA/SCL Addr Reg
pub const IXGBE_MDIO_PMA_PMD_SDA_SCL_DATA: u32 = 0xC30B; // PHY_XS SDA/SCL Data Reg
pub const IXGBE_MDIO_PMA_PMD_SDA_SCL_STAT: u32 = 0xC30C; // PHY_XS SDA/SCL Status Reg
pub const IXGBE_MDIO_PMA_TX_VEN_LASI_INT_MASK: u32 = 0xD401; // PHY TX Vendor LASI
pub const IXGBE_MDIO_PMA_TX_VEN_LASI_INT_EN: u32 = 0x1; // PHY TX Vendor LASI enable
pub const IXGBE_MDIO_PMD_STD_TX_DISABLE_CNTR: u32 = 0x9; // Standard Transmit Dis Reg
pub const IXGBE_MDIO_PMD_GLOBAL_TX_DISABLE: u32 = 0x0001; // PMD Global Transmit Dis

pub const IXGBE_PCRC8ECL: u32 = 0x0E810; // PCR CRC-8 Error Count Lo
pub const IXGBE_PCRC8ECH: u32 = 0x0E811; // PCR CRC-8 Error Count Hi
pub const IXGBE_PCRC8ECH_MASK: u32 = 0x1F;
pub const IXGBE_LDPCECL: u32 = 0x0E820; // PCR Uncorrected Error Count Lo
pub const IXGBE_LDPCECH: u32 = 0x0E821; // PCR Uncorrected Error Count Hi

// MII clause 22/28 definitions
pub const IXGBE_MDIO_PHY_LOW_POWER_MODE: u32 = 0x0800;

pub const IXGBE_MDIO_XENPAK_LASI_STATUS: u32 = 0x9005; // XENPAK LASI Status register
pub const IXGBE_XENPAK_LASI_LINK_STATUS_ALARM: u32 = 0x1; // Link Status Alarm change

pub const IXGBE_MDIO_AUTO_NEG_LINK_STATUS: u32 = 0x4; // Indicates if link is up

pub const IXGBE_MDIO_AUTO_NEG_VENDOR_STATUS_MASK: u32 = 0x7; // Speed/Duplex Mask
pub const IXGBE_MDIO_AUTO_NEG_VEN_STAT_SPEED_MASK: u32 = 0x6; // Speed Mask
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_STATUS_10M_HALF: u32 = 0x0; // 10Mb/s Half Duplex
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_STATUS_10M_FULL: u32 = 0x1; // 10Mb/s Full Duplex
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_STATUS_100M_HALF: u32 = 0x2; // 100Mb/s Half Duplex
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_STATUS_100M_FULL: u32 = 0x3; // 100Mb/s Full Duplex
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_STATUS_1GB_HALF: u32 = 0x4; // 1Gb/s Half Duplex
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_STATUS_1GB_FULL: u32 = 0x5; // 1Gb/s Full Duplex
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_STATUS_10GB_HALF: u32 = 0x6; // 10Gb/s Half Duplex
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_STATUS_10GB_FULL: u32 = 0x7; // 10Gb/s Full Duplex
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_STATUS_1GB: u32 = 0x4; // 1Gb/s
pub const IXGBE_MDIO_AUTO_NEG_VENDOR_STATUS_10GB: u32 = 0x6; // 10Gb/s

pub const IXGBE_MII_10GBASE_T_AUTONEG_CTRL_REG: u32 = 0x20; // 10G Control Reg
pub const IXGBE_MII_AUTONEG_VENDOR_PROVISION_1_REG: u32 = 0xC400; // 1G Provisioning 1
pub const IXGBE_MII_AUTONEG_XNP_TX_REG: u32 = 0x17; // 1G XNP Transmit
pub const IXGBE_MII_AUTONEG_ADVERTISE_REG: u32 = 0x10; // 100M Advertisement
pub const IXGBE_MII_10GBASE_T_ADVERTISE: u16 = 0x1000; // full duplex, bit:12
pub const IXGBE_MII_1GBASE_T_ADVERTISE_XNP_TX: u16 = 0x4000; // full duplex, bit:14
pub const IXGBE_MII_1GBASE_T_ADVERTISE: u16 = 0x8000; // full duplex, bit:15
pub const IXGBE_MII_2_5GBASE_T_ADVERTISE: u16 = 0x0400;
pub const IXGBE_MII_5GBASE_T_ADVERTISE: u16 = 0x0800;
pub const IXGBE_MII_100BASE_T_ADVERTISE: u16 = 0x0100; // full duplex, bit:8
pub const IXGBE_MII_100BASE_T_ADVERTISE_HALF: u16 = 0x0080; // half duplex, bit:7
pub const IXGBE_MII_RESTART: u16 = 0x200;
pub const IXGBE_MII_AUTONEG_COMPLETE: u16 = 0x20;
pub const IXGBE_MII_AUTONEG_LINK_UP: u16 = 0x04;
pub const IXGBE_MII_AUTONEG_REG: u32 = 0x0;

pub const IXGBE_PHY_REVISION_MASK: u32 = 0xFFFFFFF0;
pub const IXGBE_MAX_PHY_ADDR: u16 = 32;

// PHY IDs
pub const TN1010_PHY_ID: u32 = 0x00A19410;
pub const TNX_FW_REV: u32 = 0xB;
pub const X540_PHY_ID: u32 = 0x01540200;
pub const X550_PHY_ID2: u32 = 0x01540223;
pub const X550_PHY_ID3: u32 = 0x01540221;
pub const X557_PHY_ID: u32 = 0x01540240;
pub const X557_PHY_ID2: u32 = 0x01540250;
pub const AQ_FW_REV: u32 = 0x20;
pub const QT2022_PHY_ID: u32 = 0x0043A400;
pub const ATH_PHY_ID: u32 = 0x03429050;

// PHY Types
pub const IXGBE_M88E1500_E_PHY_ID: u32 = 0x01410DD0;
pub const IXGBE_M88E1543_E_PHY_ID: u32 = 0x01410EA0;

// Special PHY Init Routine
pub const IXGBE_PHY_INIT_OFFSET_NL: u32 = 0x002B;
pub const IXGBE_PHY_INIT_END_NL: u32 = 0xFFFF;
pub const IXGBE_CONTROL_MASK_NL: u32 = 0xF000;
pub const IXGBE_DATA_MASK_NL: u32 = 0x0FFF;
pub const IXGBE_CONTROL_SHIFT_NL: u32 = 12;
pub const IXGBE_DELAY_NL: u32 = 0;
pub const IXGBE_DATA_NL: u32 = 1;
pub const IXGBE_CONTROL_NL: u32 = 0x000F;
pub const IXGBE_CONTROL_EOL_NL: u32 = 0x0FFF;
pub const IXGBE_CONTROL_SOL_NL: u32 = 0x0000;

// General purpose Interrupt Enable
pub const IXGBE_SDP0_GPIEN: u32 = 0x00000001; // SDP0
pub const IXGBE_SDP1_GPIEN: u32 = 0x00000002; // SDP1
pub const IXGBE_SDP2_GPIEN: u32 = 0x00000004; // SDP2
pub const IXGBE_SDP0_GPIEN_X540: u32 = 0x00000002; // SDP0 on X540 and X550
pub const IXGBE_SDP1_GPIEN_X540: u32 = 0x00000004; // SDP1 on X540 and X550
pub const IXGBE_SDP2_GPIEN_X540: u32 = 0x00000008; // SDP2 on X540 and X550
pub const IXGBE_SDP0_GPIEN_X550: u32 = IXGBE_SDP0_GPIEN_X540;
pub const IXGBE_SDP1_GPIEN_X550: u32 = IXGBE_SDP1_GPIEN_X540;
pub const IXGBE_SDP2_GPIEN_X550: u32 = IXGBE_SDP2_GPIEN_X540;
pub const IXGBE_SDP0_GPIEN_X550EM_X: u32 = IXGBE_SDP0_GPIEN_X540;
pub const IXGBE_SDP1_GPIEN_X550EM_X: u32 = IXGBE_SDP1_GPIEN_X540;
pub const IXGBE_SDP2_GPIEN_X550EM_X: u32 = IXGBE_SDP2_GPIEN_X540;
pub const IXGBE_SDP0_GPIEN_X550EM_A: u32 = IXGBE_SDP0_GPIEN_X540;
pub const IXGBE_SDP1_GPIEN_X550EM_A: u32 = IXGBE_SDP1_GPIEN_X540;
pub const IXGBE_SDP2_GPIEN_X550EM_A: u32 = IXGBE_SDP2_GPIEN_X540;

// Other general purpose Interrupt Enable definitions
pub const IXGBE_GPIE_MSIX_MODE: u32 = 0x00000010; // MSI-X mode
pub const IXGBE_GPIE_OCD: u32 = 0x00000020; // Other Clear Disable
pub const IXGBE_GPIE_EIMEN: u32 = 0x00000040; // Immediate Interrupt Enable
pub const IXGBE_GPIE_EIAME: u32 = 0x40000000;
pub const IXGBE_GPIE_PBA_SUPPORT: u32 = 0x80000000;
pub const IXGBE_GPIE_LLI_DELAY_SHIFT: usize = 7;
pub const IXGBE_GPIE_RSC_DELAY_SHIFT: usize = 11;
pub const IXGBE_GPIE_VTMODE_MASK: u32 = 0x0000C000; // VT Mode Mask
pub const IXGBE_GPIE_VTMODE_16: u32 = 0x00004000; // 16 VFs 8 queues per VF
pub const IXGBE_GPIE_VTMODE_32: u32 = 0x00008000; // 32 VFs 4 queues per VF
pub const IXGBE_GPIE_VTMODE_64: u32 = 0x0000C000; // 64 VFs 2 queues per VF

// Packet Buffer Initialization
pub const IXGBE_MAX_PACKET_BUFFERS: u32 = 8;

pub const IXGBE_TXPBSIZE_20KB: u32 = 0x00005000; // 20KB Packet Buffer
pub const IXGBE_TXPBSIZE_40KB: u32 = 0x0000A000; // 40KB Packet Buffer
pub const IXGBE_RXPBSIZE_48KB: u32 = 0x0000C000; // 48KB Packet Buffer
pub const IXGBE_RXPBSIZE_64KB: u32 = 0x00010000; // 64KB Packet Buffer
pub const IXGBE_RXPBSIZE_80KB: u32 = 0x00014000; // 80KB Packet Buffer
pub const IXGBE_RXPBSIZE_128KB: u32 = 0x00020000; // 128KB Packet Buffer
pub const IXGBE_RXPBSIZE_MAX: u32 = 0x00080000; // 512KB Packet Buffer
pub const IXGBE_TXPBSIZE_MAX: u32 = 0x00028000; // 160KB Packet Buffer

pub const IXGBE_TXPKT_SIZE_MAX: u32 = 0xA; // Max Tx Packet size
pub const IXGBE_MAX_PB: u32 = 8;

// Packet buffer allocation strategies
pub enum PbaStrategy {
    Equal = 0,    // Distribute PB space equally
    Weighted = 1, // Weight front half of TCs
}

// Transmit Flow Control status
pub const IXGBE_TFCS_TXON: u32 = 0x00000001;
pub const IXGBE_TFCS_TXOFF: u32 = 0x00000001;
pub const IXGBE_TFCS_TXOFF0: u32 = 0x00000100;
pub const IXGBE_TFCS_TXOFF1: u32 = 0x00000200;
pub const IXGBE_TFCS_TXOFF2: u32 = 0x00000400;
pub const IXGBE_TFCS_TXOFF3: u32 = 0x00000800;
pub const IXGBE_TFCS_TXOFF4: u32 = 0x00001000;
pub const IXGBE_TFCS_TXOFF5: u32 = 0x00002000;
pub const IXGBE_TFCS_TXOFF6: u32 = 0x00004000;
pub const IXGBE_TFCS_TXOFF7: u32 = 0x00008000;

// TCP Timer
pub const IXGBE_TCPTIMER_KS: u32 = 0x00000100;
pub const IXGBE_TCPTIMER_COUNT_ENABLE: u32 = 0x00000200;
pub const IXGBE_TCPTIMER_COUNT_FINISH: u32 = 0x00000400;
pub const IXGBE_TCPTIMER_LOOP: u32 = 0x00000800;
pub const IXGBE_TCPTIMER_DURATION_MASK: u32 = 0x000000FF;

// HLREG0 Bit Masks
pub const IXGBE_HLREG0_TXCRCEN: u32 = 0x00000001; // bit 0
pub const IXGBE_HLREG0_RXCRCSTRP: u32 = 0x00000002; // bit 1
pub const IXGBE_HLREG0_JUMBOEN: u32 = 0x00000004; // bit 2
pub const IXGBE_HLREG0_TXPADEN: u32 = 0x00000400; // bit 10
pub const IXGBE_HLREG0_TXPAUSEEN: u32 = 0x00001000; // bit 12
pub const IXGBE_HLREG0_RXPAUSEEN: u32 = 0x00004000; // bit 14
pub const IXGBE_HLREG0_LPBK: u32 = 0x00008000; // bit 15
pub const IXGBE_HLREG0_MDCSPD: u32 = 0x00010000; // bit 16
pub const IXGBE_HLREG0_CONTMDC: u32 = 0x00020000; // bit 17
pub const IXGBE_HLREG0_CTRLFLTR: u32 = 0x00040000; // bit 18
pub const IXGBE_HLREG0_PREPEND: u32 = 0x00F00000; // bits 20-23
pub const IXGBE_HLREG0_PRIPAUSEEN: u32 = 0x01000000; // bit 24
pub const IXGBE_HLREG0_RXPAUSERECDA: u32 = 0x06000000; // bits 25-26
pub const IXGBE_HLREG0_RXLNGTHERREN: u32 = 0x08000000; // bit 27
pub const IXGBE_HLREG0_RXPADSTRIPEN: u32 = 0x10000000; // bit 28

// VMD_CTL bitmasks
pub const IXGBE_VMD_CTL_VMDQ_EN: u32 = 0x00000001;
pub const IXGBE_VMD_CTL_VMDQ_FILTER: u32 = 0x00000002;

// VT_CTL bitmasks
pub const IXGBE_VT_CTL_DIS_DEFPL: u32 = 0x20000000; // disable default pool
pub const IXGBE_VT_CTL_REPLEN: u32 = 0x40000000; // replication enabled
pub const IXGBE_VT_CTL_VT_ENABLE: u32 = 0x00000001; // Enable VT Mode
pub const IXGBE_VT_CTL_POOL_SHIFT: usize = 7;
pub const IXGBE_VT_CTL_POOL_MASK: u32 = 0x3F << IXGBE_VT_CTL_POOL_SHIFT; // Pool mask

// VMOLR bitmasks
pub const IXGBE_VMOLR_UPE: u32 = 0x00400000; // unicast promiscuous
pub const IXGBE_VMOLR_VPE: u32 = 0x00800000; // VLAN promiscuous
pub const IXGBE_VMOLR_AUPE: u32 = 0x01000000; // accept untagged packets
pub const IXGBE_VMOLR_ROMPE: u32 = 0x02000000; // accept packets in MTA tbl
pub const IXGBE_VMOLR_ROPE: u32 = 0x04000000; // accept packets in UC tbl
pub const IXGBE_VMOLR_BAM: u32 = 0x08000000; // accept broadcast packets
pub const IXGBE_VMOLR_MPE: u32 = 0x10000000; // multicast promiscuous

// VFRE bitmask
pub const IXGBE_VFRE_ENABLE_ALL: u32 = 0xFFFFFFFF;

// VF Initialization timeout
pub const IXGBE_VF_INIT_TIMEOUT: u32 = 200; // Number of retries to clear RSTI

// RDHMPN and TDHMPN bitmasks
pub const IXGBE_RDHMPN_RDICADDR: u32 = 0x007FF800;
pub const IXGBE_RDHMPN_RDICRDREQ: u32 = 0x00800000;
pub const IXGBE_RDHMPN_RDICADDR_SHIFT: u32 = 11;
pub const IXGBE_TDHMPN_TDICADDR: u32 = 0x003FF800;
pub const IXGBE_TDHMPN_TDICRDREQ: u32 = 0x00800000;
pub const IXGBE_TDHMPN_TDICADDR_SHIFT: u32 = 11;

// RDMAM related constants
pub const IXGBE_RDMAM_MEM_SEL_SHIFT: u32 = 13;
pub const IXGBE_RDMAM_DWORD_SHIFT: u32 = 9;
pub const IXGBE_RDMAM_DESC_COMP_FIFO: u32 = 1;
pub const IXGBE_RDMAM_DFC_CMD_FIFO: u32 = 2;
pub const IXGBE_RDMAM_RSC_HEADER_ADDR: u32 = 3;
pub const IXGBE_RDMAM_TCN_STATUS_RAM: u32 = 4;
pub const IXGBE_RDMAM_WB_COLL_FIFO: u32 = 5;
pub const IXGBE_RDMAM_QSC_CNT_RAM: u32 = 6;
pub const IXGBE_RDMAM_QSC_FCOE_RAM: u32 = 7;
pub const IXGBE_RDMAM_QSC_QUEUE_CNT: u32 = 8;
pub const IXGBE_RDMAM_QSC_QUEUE_RAM: u32 = 0xA;
pub const IXGBE_RDMAM_QSC_RSC_RAM: u32 = 0xB;
pub const IXGBE_RDMAM_DESC_COM_FIFO_RANGE: u32 = 135;
pub const IXGBE_RDMAM_DESC_COM_FIFO_COUNT: u32 = 4;
pub const IXGBE_RDMAM_DFC_CMD_FIFO_RANGE: u32 = 48;
pub const IXGBE_RDMAM_DFC_CMD_FIFO_COUNT: u32 = 7;
pub const IXGBE_RDMAM_RSC_HEADER_ADDR_RANGE: u32 = 32;
pub const IXGBE_RDMAM_RSC_HEADER_ADDR_COUNT: u32 = 4;
pub const IXGBE_RDMAM_TCN_STATUS_RAM_RANGE: u32 = 256;
pub const IXGBE_RDMAM_TCN_STATUS_RAM_COUNT: u32 = 9;
pub const IXGBE_RDMAM_WB_COLL_FIFO_RANGE: u32 = 8;
pub const IXGBE_RDMAM_WB_COLL_FIFO_COUNT: u32 = 4;
pub const IXGBE_RDMAM_QSC_CNT_RAM_RANGE: u32 = 64;
pub const IXGBE_RDMAM_QSC_CNT_RAM_COUNT: u32 = 4;
pub const IXGBE_RDMAM_QSC_FCOE_RAM_RANGE: u32 = 512;
pub const IXGBE_RDMAM_QSC_FCOE_RAM_COUNT: u32 = 5;
pub const IXGBE_RDMAM_QSC_QUEUE_CNT_RANGE: u32 = 32;
pub const IXGBE_RDMAM_QSC_QUEUE_CNT_COUNT: u32 = 4;
pub const IXGBE_RDMAM_QSC_QUEUE_RAM_RANGE: u32 = 128;
pub const IXGBE_RDMAM_QSC_QUEUE_RAM_COUNT: u32 = 8;
pub const IXGBE_RDMAM_QSC_RSC_RAM_RANGE: u32 = 32;
pub const IXGBE_RDMAM_QSC_RSC_RAM_COUNT: u32 = 8;

pub const IXGBE_TXDESCIC_READY: u32 = 0x80000000;

// Receive Checksum Control
pub const IXGBE_RXCSUM_IPPCSE: u32 = 0x00001000; // IP payload checksum enable
pub const IXGBE_RXCSUM_PCSD: u32 = 0x00002000; // packet checksum disabled

// FCRTL Bit Masks
pub const IXGBE_FCRTL_XONE: u32 = 0x80000000; // XON enable
pub const IXGBE_FCRTH_FCEN: u32 = 0x80000000; // Packet buffer fc enable

// PAP bit masks
pub const IXGBE_PAP_TXPAUSECNT_MASK: u32 = 0x0000FFFF; // Pause counter mask

// RMCS Bit Masks
pub const IXGBE_RMCS_RRM: u32 = 0x00000002; // Rx Recycle Mode enable
pub const IXGBE_RMCS_RAC: u32 = 0x00000004; // Receive Arbitration Control: 0 Round Robin, 1 DFP
pub const IXGBE_RMCS_DFP: u32 = IXGBE_RMCS_RAC; // Deficit Fixed Priority enable
pub const IXGBE_RMCS_TFCE_802_3X: u32 = 0x00000008; // Tx Priority FC enable
pub const IXGBE_RMCS_TFCE_PRIORITY: u32 = 0x00000010; // Tx Priority FC enable
pub const IXGBE_RMCS_ARBDIS: u32 = 0x00000040; // Arbitration disable bit

// FCCFG Bit Masks
pub const IXGBE_FCCFG_TFCE_802_3X: u32 = 0x00000008; // Tx link FC enable
pub const IXGBE_FCCFG_TFCE_PRIORITY: u32 = 0x00000010; // Tx priority FC enable

// Extended Interrupt Cause Read
pub const IXGBE_EICR_RTX_QUEUE: u32 = 0x0000FFFF; // RTx Queue Interrupt
pub const IXGBE_EICR_FLOW_DIR: u32 = 0x00010000; // FDir Exception
pub const IXGBE_EICR_RX_MISS: u32 = 0x00020000; // Packet Buffer Overrun
pub const IXGBE_EICR_PCI: u32 = 0x00040000; // PCI Exception
pub const IXGBE_EICR_MAILBOX: u32 = 0x00080000; // VF to PF Mailbox Interrupt
pub const IXGBE_EICR_LSC: u32 = 0x00100000; // Link Status Change
pub const IXGBE_EICR_LINKSEC: u32 = 0x00200000; // PN Threshold
pub const IXGBE_EICR_MNG: u32 = 0x00400000; // Manageability Event Interrupt
pub const IXGBE_EICR_TS: u32 = 0x00800000; // Thermal Sensor Event
pub const IXGBE_EICR_TIMESYNC: u32 = 0x01000000; // Timesync Event
pub const IXGBE_EICR_GPI_SDP0: u32 = 0x01000000; // General Purpose Interrupt on SDP0
pub const IXGBE_EICR_GPI_SDP1: u32 = 0x02000000; // General Purpose Interrupt on SDP1
pub const IXGBE_EICR_GPI_SDP2: u32 = 0x04000000; // General Purpose Interrupt on SDP2
pub const IXGBE_EICR_ECC: u32 = 0x10000000; // ECC Error
pub const IXGBE_EICR_GPI_SDP0_X540: u32 = 0x02000000; // General Purpose Interrupt on SDP0 for X540
pub const IXGBE_EICR_GPI_SDP1_X540: u32 = 0x04000000; // General Purpose Interrupt on SDP1 for X540
pub const IXGBE_EICR_GPI_SDP2_X540: u32 = 0x08000000; // General Purpose Interrupt on SDP2 for X540
pub const IXGBE_EIMS_GPI_SDP0_X540: u32 = IXGBE_EICR_GPI_SDP0_X540; // Deprecated
pub const IXGBE_EIMS_GPI_SDP1_X540: u32 = IXGBE_EICR_GPI_SDP1_X540; // Deprecated
pub const IXGBE_EIMS_GPI_SDP2_X540: u32 = IXGBE_EICR_GPI_SDP2_X540; // Deprecated
pub const IXGBE_EICR_GPI_SDP0_X550: u32 = IXGBE_EICR_GPI_SDP0_X540; // General Purpose Interrupt on SDP0 for X550
pub const IXGBE_EICR_GPI_SDP1_X550: u32 = IXGBE_EICR_GPI_SDP1_X540; // General Purpose Interrupt on SDP1 for X550
pub const IXGBE_EICR_GPI_SDP2_X550: u32 = IXGBE_EICR_GPI_SDP2_X540; // General Purpose Interrupt on SDP2 for X550
pub const IXGBE_EICR_GPI_SDP0_X550EM_X: u32 = IXGBE_EICR_GPI_SDP0_X540; // General Purpose Interrupt on SDP0 for X550EM x
pub const IXGBE_EICR_GPI_SDP1_X550EM_X: u32 = IXGBE_EICR_GPI_SDP1_X540; // General Purpose Interrupt on SDP1 for X550EM x
pub const IXGBE_EICR_GPI_SDP2_X550EM_X: u32 = IXGBE_EICR_GPI_SDP2_X540; // General Purpose Interrupt on SDP2 for X550EM x
pub const IXGBE_EICR_GPI_SDP0_X550EM_A: u32 = IXGBE_EICR_GPI_SDP0_X540; // General Purpose Interrupt on SDP0 for X550EM a
pub const IXGBE_EICR_GPI_SDP1_X550EM_A: u32 = IXGBE_EICR_GPI_SDP1_X540; // General Purpose Interrupt on SDP1 for X550EM a
pub const IXGBE_EICR_GPI_SDP2_X550EM_A: u32 = IXGBE_EICR_GPI_SDP2_X540; // General Purpose Interrupt on SDP2 for X550EM a

pub const IXGBE_EICR_PBUR: u32 = 0x10000000; // Packet Buffer Handler Error
pub const IXGBE_EICR_DHER: u32 = 0x20000000; // Descriptor Handler Error
pub const IXGBE_EICR_TCP_TIMER: u32 = 0x40000000; // TCP Timer
pub const IXGBE_EICR_OTHER: u32 = 0x80000000; // Interrupt Cause Active

// Extended Interrupt Cause Set
pub const IXGBE_EICS_RTX_QUEUE: u32 = IXGBE_EICR_RTX_QUEUE;
pub const IXGBE_EICS_FLOW_DIR: u32 = IXGBE_EICR_FLOW_DIR;
pub const IXGBE_EICS_RX_MISS: u32 = IXGBE_EICR_RX_MISS;
pub const IXGBE_EICS_PCI: u32 = IXGBE_EICR_PCI;
pub const IXGBE_EICS_MAILBOX: u32 = IXGBE_EICR_MAILBOX;
pub const IXGBE_EICS_LSC: u32 = IXGBE_EICR_LSC;
pub const IXGBE_EICS_MNG: u32 = IXGBE_EICR_MNG;
pub const IXGBE_EICS_TIMESYNC: u32 = IXGBE_EICR_TIMESYNC;
pub const IXGBE_EICS_GPI_SDP0: u32 = IXGBE_EICR_GPI_SDP0;
pub const IXGBE_EICS_GPI_SDP1: u32 = IXGBE_EICR_GPI_SDP1;
pub const IXGBE_EICS_GPI_SDP2: u32 = IXGBE_EICR_GPI_SDP2;
pub const IXGBE_EICS_ECC: u32 = IXGBE_EICR_ECC;
pub const IXGBE_EICS_PBUR: u32 = IXGBE_EICR_PBUR;
pub const IXGBE_EICS_DHER: u32 = IXGBE_EICR_DHER;
pub const IXGBE_EICS_TCP_TIMER: u32 = IXGBE_EICR_TCP_TIMER;
pub const IXGBE_EICS_OTHER: u32 = IXGBE_EICR_OTHER;

// Extended Interrupt Mask Set
pub const IXGBE_EIMS_RTX_QUEUE: u32 = IXGBE_EICR_RTX_QUEUE;
pub const IXGBE_EIMS_FLOW_DIR: u32 = IXGBE_EICR_FLOW_DIR;
pub const IXGBE_EIMS_RX_MISS: u32 = IXGBE_EICR_RX_MISS;
pub const IXGBE_EIMS_PCI: u32 = IXGBE_EICR_PCI;
pub const IXGBE_EIMS_MAILBOX: u32 = IXGBE_EICR_MAILBOX;
pub const IXGBE_EIMS_LSC: u32 = IXGBE_EICR_LSC;
pub const IXGBE_EIMS_MNG: u32 = IXGBE_EICR_MNG;
pub const IXGBE_EIMS_TS: u32 = IXGBE_EICR_TS;
pub const IXGBE_EIMS_TIMESYNC: u32 = IXGBE_EICR_TIMESYNC;
pub const IXGBE_EIMS_GPI_SDP0: u32 = IXGBE_EICR_GPI_SDP0;
pub const IXGBE_EIMS_GPI_SDP1: u32 = IXGBE_EICR_GPI_SDP1;
pub const IXGBE_EIMS_GPI_SDP2: u32 = IXGBE_EICR_GPI_SDP2;
pub const IXGBE_EIMS_ECC: u32 = IXGBE_EICR_ECC;
pub const IXGBE_EIMS_PBUR: u32 = IXGBE_EICR_PBUR;
pub const IXGBE_EIMS_DHER: u32 = IXGBE_EICR_DHER;
pub const IXGBE_EIMS_TCP_TIMER: u32 = IXGBE_EICR_TCP_TIMER;
pub const IXGBE_EIMS_OTHER: u32 = IXGBE_EICR_OTHER;

// Extended Interrupt Mask Clear
pub const IXGBE_EIMC_RTX_QUEUE: u32 = IXGBE_EICR_RTX_QUEUE;
pub const IXGBE_EIMC_FLOW_DIR: u32 = IXGBE_EICR_FLOW_DIR;
pub const IXGBE_EIMC_RX_MISS: u32 = IXGBE_EICR_RX_MISS;
pub const IXGBE_EIMC_PCI: u32 = IXGBE_EICR_PCI;
pub const IXGBE_EIMC_MAILBOX: u32 = IXGBE_EICR_MAILBOX;
pub const IXGBE_EIMC_LSC: u32 = IXGBE_EICR_LSC;
pub const IXGBE_EIMC_MNG: u32 = IXGBE_EICR_MNG;
pub const IXGBE_EIMC_TIMESYNC: u32 = IXGBE_EICR_TIMESYNC;
pub const IXGBE_EIMC_GPI_SDP0: u32 = IXGBE_EICR_GPI_SDP0;
pub const IXGBE_EIMC_GPI_SDP1: u32 = IXGBE_EICR_GPI_SDP1;
pub const IXGBE_EIMC_GPI_SDP2: u32 = IXGBE_EICR_GPI_SDP2;
pub const IXGBE_EIMC_ECC: u32 = IXGBE_EICR_ECC;
pub const IXGBE_EIMC_PBUR: u32 = IXGBE_EICR_PBUR;
pub const IXGBE_EIMC_DHER: u32 = IXGBE_EICR_DHER;
pub const IXGBE_EIMC_TCP_TIMER: u32 = IXGBE_EICR_TCP_TIMER;
pub const IXGBE_EIMC_OTHER: u32 = IXGBE_EICR_OTHER;

pub const IXGBE_EIMS_ENABLE_MASK: u32 =
    IXGBE_EIMS_RTX_QUEUE | IXGBE_EIMS_LSC | IXGBE_EIMS_TCP_TIMER | IXGBE_EIMS_OTHER;

// Immediate Interrupt Rx (A.K.A. Low Latency Interrupt)
pub const IXGBE_IMIR_PORT_IM_EN: u32 = 0x00010000; // TCP port enable
pub const IXGBE_IMIR_PORT_BP: u32 = 0x00020000; // TCP port check bypass
pub const IXGBE_IMIREXT_SIZE_BP: u32 = 0x00001000; // Packet size bypass
pub const IXGBE_IMIREXT_CTRL_URG: u32 = 0x00002000; // Check URG bit in header
pub const IXGBE_IMIREXT_CTRL_ACK: u32 = 0x00004000; // Check ACK bit in header
pub const IXGBE_IMIREXT_CTRL_PSH: u32 = 0x00008000; // Check PSH bit in header
pub const IXGBE_IMIREXT_CTRL_RST: u32 = 0x00010000; // Check RST bit in header
pub const IXGBE_IMIREXT_CTRL_SYN: u32 = 0x00020000; // Check SYN bit in header
pub const IXGBE_IMIREXT_CTRL_FIN: u32 = 0x00040000; // Check FIN bit in header
pub const IXGBE_IMIREXT_CTRL_BP: u32 = 0x00080000; // Bypass check of control bits
pub const IXGBE_IMIR_SIZE_BP_82599: u32 = 0x00001000; // Packet size bypass
pub const IXGBE_IMIR_CTRL_URG_82599: u32 = 0x00002000; // Check URG bit in header
pub const IXGBE_IMIR_CTRL_ACK_82599: u32 = 0x00004000; // Check ACK bit in header
pub const IXGBE_IMIR_CTRL_PSH_82599: u32 = 0x00008000; // Check PSH bit in header
pub const IXGBE_IMIR_CTRL_RST_82599: u32 = 0x00010000; // Check RST bit in header
pub const IXGBE_IMIR_CTRL_SYN_82599: u32 = 0x00020000; // Check SYN bit in header
pub const IXGBE_IMIR_CTRL_FIN_82599: u32 = 0x00040000; // Check FIN bit in header
pub const IXGBE_IMIR_CTRL_BP_82599: u32 = 0x00080000; // Bypass chk of ctrl bits
pub const IXGBE_IMIR_LLI_EN_82599: u32 = 0x00100000; // Enables low latency Int
pub const IXGBE_IMIR_RX_QUEUE_MASK_82599: u32 = 0x0000007F; // Rx Queue Mask
pub const IXGBE_IMIR_RX_QUEUE_SHIFT_82599: u32 = 21; // Rx Queue Shift
pub const IXGBE_IMIRVP_PRIORITY_MASK: u32 = 0x00000007; // VLAN priority mask
pub const IXGBE_IMIRVP_PRIORITY_EN: u32 = 0x00000008; // VLAN priority enable

// Maximum Flow Tuple Query Filters
pub const IXGBE_MAX_FTQF_FILTERS: u32 = 128;
pub const IXGBE_FTQF_PROTOCOL_MASK: u32 = 0x00000003;
pub const IXGBE_FTQF_PROTOCOL_TCP: u32 = 0x00000000;
pub const IXGBE_FTQF_PROTOCOL_UDP: u32 = 0x00000001;
pub const IXGBE_FTQF_PROTOCOL_SCTP: u32 = 2;
pub const IXGBE_FTQF_PRIORITY_MASK: u32 = 0x00000007;
pub const IXGBE_FTQF_PRIORITY_SHIFT: u32 = 2;
pub const IXGBE_FTQF_POOL_MASK: u32 = 0x0000003F;
pub const IXGBE_FTQF_POOL_SHIFT: u32 = 8;
pub const IXGBE_FTQF_5TUPLE_MASK_MASK: u32 = 0x0000001F;
pub const IXGBE_FTQF_5TUPLE_MASK_SHIFT: u32 = 25;
pub const IXGBE_FTQF_SOURCE_ADDR_MASK: u32 = 0x1E;
pub const IXGBE_FTQF_DEST_ADDR_MASK: u32 = 0x1D;
pub const IXGBE_FTQF_SOURCE_PORT_MASK: u32 = 0x1B;
pub const IXGBE_FTQF_DEST_PORT_MASK: u32 = 0x17;
pub const IXGBE_FTQF_PROTOCOL_COMP_MASK: u32 = 0x0F;
pub const IXGBE_FTQF_POOL_MASK_EN: u32 = 0x40000000;
pub const IXGBE_FTQF_QUEUE_ENABLE: u32 = 0x80000000;

// Interrupt clear mask
pub const IXGBE_IRQ_CLEAR_MASK: u32 = 0xFFFFFFFF;

// Interrupt Vector Allocation Registers
pub const IXGBE_IVAR_REG_NUM: u32 = 25;
pub const IXGBE_IVAR_REG_NUM_82599: u32 = 64;
pub const IXGBE_IVAR_TXRX_ENTRY: u32 = 96;
pub const IXGBE_IVAR_RX_ENTRY: u32 = 64;
pub const IXGBE_IVAR_TX_ENTRY: u32 = 32;
pub fn ixgbe_ivar_rx_queue(i: u32) -> u32 {
    0 + i
}
pub fn ixgbe_ivar_tx_queue(i: u32) -> u32 {
    64 + i
}
pub const IXGBE_IVAR_TCP_TIMER_INDEX: u8 = 96; // 0 based index
pub const IXGBE_IVAR_OTHER_CAUSES_INDEX: u8 = 97; // 0 based index
pub fn ixgbe_msix_vector(i: u32) -> u32 {
    0 + i
}
pub const IXGBE_IVAR_ALLOC_VAL: u8 = 0x80; // Interrupt Allocation valid

// ETYPE Queue Filter/Select Bit Masks
pub const IXGBE_MAX_ETQF_FILTERS: u32 = 8;
pub const IXGBE_ETQF_FCOE: u32 = 0x08000000; // bit 27
pub const IXGBE_ETQF_BCN: u32 = 0x10000000; // bit 28
pub const IXGBE_ETQF_TX_ANTISPOOF: u32 = 0x20000000; // bit 29
pub const IXGBE_ETQF_1588: u32 = 0x40000000; // bit 30
pub const IXGBE_ETQF_FILTER_EN: u32 = 0x80000000; // bit 31
pub const IXGBE_ETQF_POOL_ENABLE: u32 = 1 << 26; // bit 26
pub const IXGBE_ETQF_POOL_SHIFT: u32 = 20;
pub const IXGBE_ETQS_RX_QUEUE: u32 = 0x007F0000; // bits 22:16
pub const IXGBE_ETQS_RX_QUEUE_SHIFT: u32 = 16;
pub const IXGBE_ETQS_LLI: u32 = 0x20000000; // bit 29
pub const IXGBE_ETQS_QUEUE_EN: u32 = 0x80000000; // bit 31

// ETQF filter list indices
pub const IXGBE_ETQF_FILTER_EAPOL: u32 = 0;
pub const IXGBE_ETQF_FILTER_FCOE: u32 = 2;
pub const IXGBE_ETQF_FILTER_1588: u32 = 3;
pub const IXGBE_ETQF_FILTER_FIP: u32 = 4;
pub const IXGBE_ETQF_FILTER_LLDP: u32 = 5;
pub const IXGBE_ETQF_FILTER_LACP: u32 = 6;
pub const IXGBE_ETQF_FILTER_FC: u32 = 7;

// VLAN Control Bit Masks
pub const IXGBE_VLNCTRL_VET: u32 = 0x0000FFFF; // bits 0-15
pub const IXGBE_VLNCTRL_CFI: u32 = 0x10000000; // bit 28
pub const IXGBE_VLNCTRL_CFIEN: u32 = 0x20000000; // bit 29
pub const IXGBE_VLNCTRL_VFE: u32 = 0x40000000; // bit 30
pub const IXGBE_VLNCTRL_VME: u32 = 0x80000000; // bit 31

// VLAN pool filtering masks
pub const IXGBE_VLVF_VIEN: u32 = 0x80000000; // filter is valid
pub const IXGBE_VLVF_ENTRIES: u32 = 64;
pub const IXGBE_VLVF_VLANID_MASK: u32 = 0x00000FFF;

// Per VF Port VLAN insertion rules
pub const IXGBE_VMVIR_VLANA_DEFAULT: u32 = 0x40000000; // Always use default VLAN
pub const IXGBE_VMVIR_VLANA_NEVER: u32 = 0x80000000; // Never insert VLAN tag

// Ethernet IEEE VLAN Type
pub const IXGBE_ETHERNET_IEEE_VLAN_TYPE: u16 = 0x8100; // 802.1q protocol

// STATUS Bit Masks
pub const IXGBE_STATUS_LAN_ID: u32 = 0x0000000C; // LAN ID
pub const IXGBE_STATUS_LAN_ID_SHIFT: u32 = 2; // LAN ID Shift
pub const IXGBE_STATUS_GIO: u32 = 0x00080000; // GIO Master Ena Status
pub const IXGBE_STATUS_LAN_ID_0: u32 = 0x00000000; // LAN ID 0
pub const IXGBE_STATUS_LAN_ID_1: u32 = 0x00000004; // LAN ID 1

// ESDP Bit Masks
pub const IXGBE_ESDP_SDP0: u32 = 0x00000001; // SDP0 Data Value
pub const IXGBE_ESDP_SDP1: u32 = 0x00000002; // SDP1 Data Value
pub const IXGBE_ESDP_SDP2: u32 = 0x00000004; // SDP2 Data Value
pub const IXGBE_ESDP_SDP3: u32 = 0x00000008; // SDP3 Data Value
pub const IXGBE_ESDP_SDP4: u32 = 0x00000010; // SDP4 Data Value
pub const IXGBE_ESDP_SDP5: u32 = 0x00000020; // SDP5 Data Value
pub const IXGBE_ESDP_SDP6: u32 = 0x00000040; // SDP6 Data Value
pub const IXGBE_ESDP_SDP7: u32 = 0x00000080; // SDP7 Data Value
pub const IXGBE_ESDP_SDP0_DIR: u32 = 0x00000100; // SDP0 IO direction
pub const IXGBE_ESDP_SDP1_DIR: u32 = 0x00000200; // SDP1 IO direction
pub const IXGBE_ESDP_SDP2_DIR: u32 = 0x00000400; // SDP2 IO direction
pub const IXGBE_ESDP_SDP3_DIR: u32 = 0x00000800; // SDP3 IO direction
pub const IXGBE_ESDP_SDP4_DIR: u32 = 0x00001000; // SDP4 IO direction
pub const IXGBE_ESDP_SDP5_DIR: u32 = 0x00002000; // SDP5 IO direction
pub const IXGBE_ESDP_SDP6_DIR: u32 = 0x00004000; // SDP6 IO direction
pub const IXGBE_ESDP_SDP7_DIR: u32 = 0x00008000; // SDP7 IO direction
pub const IXGBE_ESDP_SDP0_NATIVE: u32 = 0x00010000; // SDP0 IO mode
pub const IXGBE_ESDP_SDP1_NATIVE: u32 = 0x00020000; // SDP1 IO mode

// LEDCTL Bit Masks
pub const IXGBE_LED_IVRT_BASE: u32 = 0x00000040;
pub const IXGBE_LED_BLINK_BASE: u32 = 0x00000080;
pub const IXGBE_LED_MODE_MASK_BASE: u32 = 0x0000000F;

// Compute LED offset based on the index
pub fn ixgbe_led_offset(base: u32, i: u32) -> u32 {
    base << (8 * i)
}

// Compute LED mode shift based on the index
pub fn ixgbe_led_mode_shift(i: u32) -> u32 {
    8 * i
}

pub fn ixgbe_led_ivrt(i: u32) -> u32 {
    ixgbe_led_offset(IXGBE_LED_IVRT_BASE, i)
}

pub fn ixgbe_led_blink(i: u32) -> u32 {
    ixgbe_led_offset(IXGBE_LED_BLINK_BASE, i)
}

pub fn ixgbe_led_mode_mask(i: u32) -> u32 {
    ixgbe_led_offset(IXGBE_LED_MODE_MASK_BASE, i)
}

pub const IXGBE_X557_LED_MANUAL_SET_MASK: u32 = 1 << 8;
pub const IXGBE_X557_MAX_LED_INDEX: u32 = 3;
pub const IXGBE_X557_LED_PROVISIONING: u32 = 0xC430;

// LED modes
pub const IXGBE_LED_LINK_UP: u32 = 0x0;
pub const IXGBE_LED_LINK_10G: u32 = 0x1;
pub const IXGBE_LED_MAC: u32 = 0x2;
pub const IXGBE_LED_FILTER: u32 = 0x3;
pub const IXGBE_LED_LINK_ACTIVE: u32 = 0x4;
pub const IXGBE_LED_LINK_1G: u32 = 0x5;
pub const IXGBE_LED_ON: u32 = 0xE;
pub const IXGBE_LED_OFF: u32 = 0xF;

// AUTOC Bit Masks
pub const IXGBE_AUTOC_KX4_KX_SUPP_MASK: u32 = 0xC0000000;
pub const IXGBE_AUTOC_KX4_SUPP: u32 = 0x80000000;
pub const IXGBE_AUTOC_KX_SUPP: u32 = 0x40000000;
pub const IXGBE_AUTOC_PAUSE: u32 = 0x30000000;
pub const IXGBE_AUTOC_ASM_PAUSE: u32 = 0x20000000;
pub const IXGBE_AUTOC_SYM_PAUSE: u32 = 0x10000000;
pub const IXGBE_AUTOC_RF: u32 = 0x08000000;
pub const IXGBE_AUTOC_PD_TMR: u32 = 0x06000000;
pub const IXGBE_AUTOC_AN_RX_LOOSE: u32 = 0x01000000;
pub const IXGBE_AUTOC_AN_RX_DRIFT: u32 = 0x00800000;
pub const IXGBE_AUTOC_AN_RX_ALIGN: u32 = 0x007C0000;
pub const IXGBE_AUTOC_FECA: u32 = 0x00040000;
pub const IXGBE_AUTOC_FECR: u32 = 0x00020000;
pub const IXGBE_AUTOC_KR_SUPP: u32 = 0x00010000;
pub const IXGBE_AUTOC_AN_RESTART: u32 = 0x00001000;
pub const IXGBE_AUTOC_FLU: u32 = 0x00000001;
pub const IXGBE_AUTOC_LMS_SHIFT: u32 = 13;
pub const IXGBE_AUTOC_LMS_10G_SERIAL: u32 = 0x3 << IXGBE_AUTOC_LMS_SHIFT;
pub const IXGBE_AUTOC_LMS_KX4_KX_KR: u32 = 0x4 << IXGBE_AUTOC_LMS_SHIFT;
pub const IXGBE_AUTOC_LMS_SGMII_1G_100M: u32 = 0x5 << IXGBE_AUTOC_LMS_SHIFT;
pub const IXGBE_AUTOC_LMS_KX4_KX_KR_1G_AN: u32 = 0x6 << IXGBE_AUTOC_LMS_SHIFT;
pub const IXGBE_AUTOC_LMS_KX4_KX_KR_SGMII: u32 = 0x7 << IXGBE_AUTOC_LMS_SHIFT;
pub const IXGBE_AUTOC_LMS_MASK: u32 = 0x7 << IXGBE_AUTOC_LMS_SHIFT;
pub const IXGBE_AUTOC_LMS_1G_LINK_NO_AN: u32 = 0x0 << IXGBE_AUTOC_LMS_SHIFT;
pub const IXGBE_AUTOC_LMS_10G_LINK_NO_AN: u32 = 0x1 << IXGBE_AUTOC_LMS_SHIFT;
pub const IXGBE_AUTOC_LMS_1G_AN: u32 = 0x2 << IXGBE_AUTOC_LMS_SHIFT;
pub const IXGBE_AUTOC_LMS_KX4_AN: u32 = 0x4 << IXGBE_AUTOC_LMS_SHIFT;
pub const IXGBE_AUTOC_LMS_KX4_AN_1G_AN: u32 = 0x6 << IXGBE_AUTOC_LMS_SHIFT;
pub const IXGBE_AUTOC_LMS_ATTACH_TYPE: u32 = 0x7 << IXGBE_AUTOC_10G_PMA_PMD_SHIFT;

pub const IXGBE_AUTOC_1G_PMA_PMD_MASK: u32 = 0x00000200;
pub const IXGBE_AUTOC_1G_PMA_PMD_SHIFT: u32 = 9;
pub const IXGBE_AUTOC_10G_PMA_PMD_MASK: u32 = 0x00000180;
pub const IXGBE_AUTOC_10G_PMA_PMD_SHIFT: u32 = 7;
pub const IXGBE_AUTOC_10G_XAUI: u32 = 0x0 << IXGBE_AUTOC_10G_PMA_PMD_SHIFT;
pub const IXGBE_AUTOC_10G_KX4: u32 = 0x1 << IXGBE_AUTOC_10G_PMA_PMD_SHIFT;
pub const IXGBE_AUTOC_10G_CX4: u32 = 0x2 << IXGBE_AUTOC_10G_PMA_PMD_SHIFT;
pub const IXGBE_AUTOC_1G_BX: u32 = 0x0 << IXGBE_AUTOC_1G_PMA_PMD_SHIFT;
pub const IXGBE_AUTOC_1G_KX: u32 = 0x1 << IXGBE_AUTOC_1G_PMA_PMD_SHIFT;
pub const IXGBE_AUTOC_1G_SFI: u32 = 0x0 << IXGBE_AUTOC_1G_PMA_PMD_SHIFT;
pub const IXGBE_AUTOC_1G_KX_BX: u32 = 0x1 << IXGBE_AUTOC_1G_PMA_PMD_SHIFT;

// AUTOC2 Bit Masks
pub const IXGBE_AUTOC2_UPPER_MASK: u32 = 0xFFFF0000;
pub const IXGBE_AUTOC2_10G_SERIAL_PMA_PMD_MASK: u32 = 0x00030000;
pub const IXGBE_AUTOC2_10G_SERIAL_PMA_PMD_SHIFT: u32 = 16;
pub const IXGBE_AUTOC2_10G_KR: u32 = 0x0 << IXGBE_AUTOC2_10G_SERIAL_PMA_PMD_SHIFT;
pub const IXGBE_AUTOC2_10G_XFI: u32 = 0x1 << IXGBE_AUTOC2_10G_SERIAL_PMA_PMD_SHIFT;
pub const IXGBE_AUTOC2_10G_SFI: u32 = 0x2 << IXGBE_AUTOC2_10G_SERIAL_PMA_PMD_SHIFT;
pub const IXGBE_AUTOC2_LINK_DISABLE_ON_D3_MASK: u32 = 0x50000000;
pub const IXGBE_AUTOC2_LINK_DISABLE_MASK: u32 = 0x70000000;

// MACC Bit Masks
pub const IXGBE_MACC_FLU: u32 = 0x00000001;
pub const IXGBE_MACC_FSV_10G: u32 = 0x00030000;
pub const IXGBE_MACC_FS: u32 = 0x00040000;
pub const IXGBE_MAC_RX2TX_LPBK: u32 = 0x00000002;

// Veto Bit definition
pub const IXGBE_MMNGC_MNG_VETO: u32 = 0x00000001;

// LINKS Bit Masks
pub const IXGBE_LINKS_KX_AN_COMP: u32 = 0x80000000;
pub const IXGBE_LINKS_UP: u32 = 0x40000000;
pub const IXGBE_LINKS_SPEED: u32 = 0x20000000;
pub const IXGBE_LINKS_MODE: u32 = 0x18000000;
pub const IXGBE_LINKS_RX_MODE: u32 = 0x06000000;
pub const IXGBE_LINKS_TX_MODE: u32 = 0x01800000;
pub const IXGBE_LINKS_XGXS_EN: u32 = 0x00400000;
pub const IXGBE_LINKS_SGMII_EN: u32 = 0x02000000;
pub const IXGBE_LINKS_PCS_1G_EN: u32 = 0x00200000;
pub const IXGBE_LINKS_1G_AN_EN: u32 = 0x00100000;
pub const IXGBE_LINKS_KX_AN_IDLE: u32 = 0x00080000;
pub const IXGBE_LINKS_1G_SYNC: u32 = 0x00040000;
pub const IXGBE_LINKS_10G_ALIGN: u32 = 0x00020000;
pub const IXGBE_LINKS_10G_LANE_SYNC: u32 = 0x00017000;
pub const IXGBE_LINKS_TL_FAULT: u32 = 0x00001000;
pub const IXGBE_LINKS_SIGNAL: u32 = 0x00000F00;

pub const IXGBE_LINKS_SPEED_NON_STD: u32 = 0x08000000;
pub const IXGBE_LINKS_SPEED_82599: u32 = 0x30000000;
pub const IXGBE_LINKS_SPEED_10G_82599: u32 = 0x30000000;
pub const IXGBE_LINKS_SPEED_1G_82599: u32 = 0x20000000;
pub const IXGBE_LINKS_SPEED_100_82599: u32 = 0x10000000;
pub const IXGBE_LINKS_SPEED_10_X550EM_A: u32 = 0x00000000;
pub const IXGBE_LINK_UP_TIME: u32 = 90; // 9.0 Seconds
pub const IXGBE_AUTO_NEG_TIME: u32 = 45; // 4.5 Seconds

pub const IXGBE_LINKS2_AN_SUPPORTED: u32 = 0x00000040;

// PCS1GLSTA Bit Masks
pub const IXGBE_PCS1GLSTA_LINK_OK: u32 = 1;
pub const IXGBE_PCS1GLSTA_SYNK_OK: u32 = 0x10;
pub const IXGBE_PCS1GLSTA_AN_COMPLETE: u32 = 0x10000;
pub const IXGBE_PCS1GLSTA_AN_PAGE_RX: u32 = 0x20000;
pub const IXGBE_PCS1GLSTA_AN_TIMED_OUT: u32 = 0x40000;
pub const IXGBE_PCS1GLSTA_AN_REMOTE_FAULT: u32 = 0x80000;
pub const IXGBE_PCS1GLSTA_AN_ERROR_RWS: u32 = 0x100000;

// PCS1GANA Bit Masks
pub const IXGBE_PCS1GANA_SYM_PAUSE: u32 = 0x80;
pub const IXGBE_PCS1GANA_ASM_PAUSE: u32 = 0x100;

// PCS1GLCTL Bit Masks
pub const IXGBE_PCS1GLCTL_AN_1G_TIMEOUT_EN: u32 = 0x00040000; // PCS 1G autoneg to en
pub const IXGBE_PCS1GLCTL_FLV_LINK_UP: u32 = 1;
pub const IXGBE_PCS1GLCTL_FORCE_LINK: u32 = 0x20;
pub const IXGBE_PCS1GLCTL_LOW_LINK_LATCH: u32 = 0x40;
pub const IXGBE_PCS1GLCTL_AN_ENABLE: u32 = 0x10000;
pub const IXGBE_PCS1GLCTL_AN_RESTART: u32 = 0x20000;

// ANLP1 Bit Masks
pub const IXGBE_ANLP1_PAUSE: u32 = 0x0C00;
pub const IXGBE_ANLP1_SYM_PAUSE: u32 = 0x0400;
pub const IXGBE_ANLP1_ASM_PAUSE: u32 = 0x0800;
pub const IXGBE_ANLP1_AN_STATE_MASK: u32 = 0x000f0000;

// SW Semaphore Register bitmasks
pub const IXGBE_SWSM_SMBI: u32 = 0x00000001; // Driver Semaphore bit
pub const IXGBE_SWSM_SWESMBI: u32 = 0x00000002; // FW Semaphore bit
pub const IXGBE_SWSM_WMNG: u32 = 0x00000004; // Wake MNG Clock
pub const IXGBE_SWFW_REGSMP: u32 = 0x80000000; // Register Semaphore bit 31

// SW_FW_SYNC/GSSR definitions
pub const IXGBE_GSSR_EEP_SM: u32 = 0x0001;
pub const IXGBE_GSSR_PHY0_SM: u32 = 0x0002;
pub const IXGBE_GSSR_PHY1_SM: u32 = 0x0004;
pub const IXGBE_GSSR_MAC_CSR_SM: u32 = 0x0008;
pub const IXGBE_GSSR_FLASH_SM: u32 = 0x0010;
pub const IXGBE_GSSR_NVM_UPDATE_SM: u32 = 0x0200;
pub const IXGBE_GSSR_SW_MNG_SM: u32 = 0x0400;
pub const IXGBE_GSSR_TOKEN_SM: u32 = 0x40000000; // SW bit for shared access
pub const IXGBE_GSSR_SHARED_I2C_SM: u32 = 0x1806; // Wait for both phys and both I2Cs
pub const IXGBE_GSSR_I2C_MASK: u32 = 0x1800;
pub const IXGBE_GSSR_NVM_PHY_MASK: u32 = 0xF;

// FW Status register bitmask
pub const IXGBE_FWSTS_FWRI: u32 = 0x00000200; // Firmware Reset Indication

// EEC Register
pub const IXGBE_EEC_SK: u32 = 0x00000001; // EEPROM Clock
pub const IXGBE_EEC_CS: u32 = 0x00000002; // EEPROM Chip Select
pub const IXGBE_EEC_DI: u32 = 0x00000004; // EEPROM Data In
pub const IXGBE_EEC_DO: u32 = 0x00000008; // EEPROM Data Out
pub const IXGBE_EEC_FWE_MASK: u32 = 0x00000030; // FLASH Write Enable
pub const IXGBE_EEC_FWE_DIS: u32 = 0x00000010; // Disable FLASH writes
pub const IXGBE_EEC_FWE_EN: u32 = 0x00000020; // Enable FLASH writes
pub const IXGBE_EEC_FWE_SHIFT: u32 = 4;
pub const IXGBE_EEC_REQ: u32 = 0x00000040; // EEPROM Access Request
pub const IXGBE_EEC_GNT: u32 = 0x00000080; // EEPROM Access Grant
pub const IXGBE_EEC_PRES: u32 = 0x00000100; // EEPROM Present
pub const IXGBE_EEC_ARD: u32 = 0x00000200; // EEPROM Auto Read Done
pub const IXGBE_EEC_FLUP: u32 = 0x00800000; // Flash update command
pub const IXGBE_EEC_SEC1VAL: u32 = 0x02000000; // Sector 1 Valid
pub const IXGBE_EEC_FLUDONE: u32 = 0x04000000; // Flash update done

// EEPROM Addressing bits based on type (0-small, 1-large)
pub const IXGBE_EEC_ADDR_SIZE: u32 = 0x00000400;
pub const IXGBE_EEC_SIZE: u32 = 0x00007800; // EEPROM Size
pub const IXGBE_EERD_MAX_ADDR: u32 = 0x00003FFF; // EERD allows 14 bits for addr.

pub const IXGBE_EEC_SIZE_SHIFT: u32 = 11;
pub const IXGBE_EEPROM_WORD_SIZE_SHIFT: u16 = 6;
pub const IXGBE_EEPROM_OPCODE_BITS: u32 = 8;

// FLA Register
pub const IXGBE_FLA_LOCKED: u32 = 0x00000040;

// Part Number String Length
pub const IXGBE_PBANUM_LENGTH: u32 = 11;

// Checksum and EEPROM pointers
pub const IXGBE_PBANUM_PTR_GUARD: u16 = 0xFAFA;
pub const IXGBE_EEPROM_CHECKSUM: u16 = 0x3F;
pub const IXGBE_EEPROM_SUM: u16 = 0xBABA;
pub const IXGBE_EEPROM_CTRL_4: u16 = 0x45;
pub const IXGBE_EE_CTRL_4_INST_ID: u16 = 0x10;
pub const IXGBE_EE_CTRL_4_INST_ID_SHIFT: u16 = 4;
pub const IXGBE_PCIE_ANALOG_PTR: u16 = 0x03;
pub const IXGBE_ATLAS0_CONFIG_PTR: u16 = 0x04;
pub const IXGBE_PHY_PTR: u16 = 0x04;
pub const IXGBE_ATLAS1_CONFIG_PTR: u16 = 0x05;
pub const IXGBE_OPTION_ROM_PTR: u16 = 0x05;
pub const IXGBE_PCIE_GENERAL_PTR: u16 = 0x06;
pub const IXGBE_PCIE_CONFIG0_PTR: u16 = 0x07;
pub const IXGBE_PCIE_CONFIG1_PTR: u16 = 0x08;
pub const IXGBE_CORE0_PTR: u16 = 0x09;
pub const IXGBE_CORE1_PTR: u16 = 0x0A;
pub const IXGBE_MAC0_PTR: u16 = 0x0B;
pub const IXGBE_MAC1_PTR: u16 = 0x0C;
pub const IXGBE_CSR0_CONFIG_PTR: u16 = 0x0D;
pub const IXGBE_CSR1_CONFIG_PTR: u16 = 0x0E;
pub const IXGBE_PCIE_ANALOG_PTR_X550: u16 = 0x02;
pub const IXGBE_SHADOW_RAM_SIZE_X550: u16 = 0x4000;
pub const IXGBE_IXGBE_PCIE_GENERAL_SIZE: u16 = 0x24;
pub const IXGBE_PCIE_CONFIG_SIZE: u16 = 0x08;
pub const IXGBE_EEPROM_LAST_WORD: u16 = 0x41;
pub const IXGBE_FW_PTR: u16 = 0x0F;
pub const IXGBE_PBANUM0_PTR: u16 = 0x15;
pub const IXGBE_PBANUM1_PTR: u16 = 0x16;
pub const IXGBE_ALT_MAC_ADDR_PTR: u16 = 0x37;
pub const IXGBE_FREE_SPACE_PTR: u16 = 0x3E;

pub const IXGBE_SAN_MAC_ADDR_PTR: usize = 0x28;
pub const IXGBE_DEVICE_CAPS: usize = 0x2C;
pub const IXGBE_82599_SERIAL_NUMBER_MAC_ADDR: usize = 0x11;
pub const IXGBE_X550_SERIAL_NUMBER_MAC_ADDR: usize = 0x04;

pub const IXGBE_PCIE_MSIX_82599_CAPS: u32 = 0x72;
pub const IXGBE_MAX_MSIX_VECTORS_82599: u32 = 0x40;
pub const IXGBE_PCIE_MSIX_82598_CAPS: u32 = 0x62;
pub const IXGBE_MAX_MSIX_VECTORS_82598: u32 = 0x13;

// MSI-X capability fields masks
pub const IXGBE_PCIE_MSIX_TBL_SZ_MASK: u32 = 0x7FF;
// Legacy EEPROM word offsets
pub const IXGBE_ISCSI_BOOT_CAPS: u16 = 0x0033;
pub const IXGBE_ISCSI_SETUP_PORT_0: u16 = 0x0030;
pub const IXGBE_ISCSI_SETUP_PORT_1: u16 = 0x0034;

// EEPROM Commands - SPI
pub const IXGBE_EEPROM_MAX_RETRY_SPI: u32 = 5000; // Max wait 5ms for RDY signal
pub const IXGBE_EEPROM_STATUS_RDY_SPI: u8 = 0x01;
pub const IXGBE_EEPROM_READ_OPCODE_SPI: u8 = 0x03; // EEPROM read opcode
pub const IXGBE_EEPROM_WRITE_OPCODE_SPI: u8 = 0x02; // EEPROM write opcode
pub const IXGBE_EEPROM_A8_OPCODE_SPI: u8 = 0x08; // opcode bit-3 = addr bit-8
pub const IXGBE_EEPROM_WREN_OPCODE_SPI: u8 = 0x06; // EEPROM set Write Ena latch
pub const IXGBE_EEPROM_WRDI_OPCODE_SPI: u8 = 0x04; // EEPROM reset Write Enable latch
pub const IXGBE_EEPROM_RDSR_OPCODE_SPI: u8 = 0x05; // EEPROM read Status reg
pub const IXGBE_EEPROM_WRSR_OPCODE_SPI: u8 = 0x01; // EEPROM write Status reg
pub const IXGBE_EEPROM_ERASE4K_OPCODE_SPI: u8 = 0x20; // EEPROM ERASE 4KB
pub const IXGBE_EEPROM_ERASE64K_OPCODE_SPI: u8 = 0xD8; // EEPROM ERASE 64KB
pub const IXGBE_EEPROM_ERASE256_OPCODE_SPI: u8 = 0xDB; // EEPROM ERASE 256B

// EEPROM Read Register
pub const IXGBE_EEPROM_RW_REG_DATA: u16 = 16; // data offset in EEPROM read reg
pub const IXGBE_EEPROM_RW_REG_DONE: u16 = 2; // Offset to READ done bit
pub const IXGBE_EEPROM_RW_REG_START: u16 = 1; // First bit to start operation
pub const IXGBE_EEPROM_RW_ADDR_SHIFT: u16 = 2; // Shift to the address bits
pub const IXGBE_NVM_POLL_WRITE: u16 = 1; // Flag for polling for wr complete
pub const IXGBE_NVM_POLL_READ: u16 = 0; // Flag for polling for rd complete

// EEPROM-related
pub const NVM_INIT_CTRL_3: u16 = 0x38;
pub const NVM_INIT_CTRL_3_LPLU: u16 = 0x8;
pub const NVM_INIT_CTRL_3_D10GMP_PORT0: u16 = 0x40;
pub const NVM_INIT_CTRL_3_D10GMP_PORT1: u16 = 0x100;

// Ethernet
pub const IXGBE_ETH_LENGTH_OF_ADDRESS: usize = 6;

// EEPROM Page and Buffer Sizes
pub const IXGBE_EEPROM_PAGE_SIZE_MAX: u16 = 128;
pub const IXGBE_EEPROM_RD_BUFFER_MAX_COUNT: u16 = 256; // words read in burst
pub const IXGBE_EEPROM_WR_BUFFER_MAX_COUNT: u16 = 256; // words write in burst
pub const IXGBE_EEPROM_CTRL_2: u8 = 1;
pub const IXGBE_EEPROM_CCD_BIT: u8 = 2;

pub const IXGBE_EEPROM_GRANT_ATTEMPTS: u32 = 1000; // EEPROM attempts to gain grant

// Delays and Timeouts
pub const IXGBE_EERD_EEWR_ATTEMPTS: u32 = 100000; // Number of 5 microseconds we wait for EERD read and EERW write to complete
pub const IXGBE_FLUDONE_ATTEMPTS: u32 = 20000; // # attempts we wait for flush update to complete

// PCIe Control
pub const IXGBE_PCIE_CTRL2: u8 = 0x5; // PCIe Control 2 Offset
pub const IXGBE_PCIE_CTRL2_DUMMY_ENABLE: u8 = 0x8; // Dummy Function Enable
pub const IXGBE_PCIE_CTRL2_LAN_DISABLE: u8 = 0x2; // LAN PCI Disable
pub const IXGBE_PCIE_CTRL2_DISABLE_SELECT: u8 = 0x1; // LAN Disable Select
                                                     // SAN MAC Address Offsets
pub const IXGBE_SAN_MAC_ADDR_PORT0_OFFSET: u32 = 0x0;
pub const IXGBE_SAN_MAC_ADDR_PORT1_OFFSET: u32 = 0x3;

// Device Capabilities Flags
pub const IXGBE_DEVICE_CAPS_ALLOW_ANY_SFP: u32 = 0x1;
pub const IXGBE_DEVICE_CAPS_FCOE_OFFLOADS: u32 = 0x2;
pub const IXGBE_DEVICE_CAPS_NO_CROSSTALK_WR: u32 = 1 << 7;

// Firmware pointers and flags
pub const IXGBE_FW_LESM_PARAMETERS_PTR: u32 = 0x2;
pub const IXGBE_FW_LESM_STATE_1: u32 = 0x1;
pub const IXGBE_FW_LESM_STATE_ENABLED: u32 = 0x8000;
pub const IXGBE_FW_PASSTHROUGH_PATCH_CONFIG_PTR: u32 = 0x4;
pub const IXGBE_FW_PATCH_VERSION_4: u32 = 0x7;

// iSCSI/FCOE block pointers
pub const IXGBE_FCOE_IBA_CAPS_BLK_PTR: u32 = 0x33;
pub const IXGBE_FCOE_IBA_CAPS_FCOE: u32 = 0x20;
pub const IXGBE_ISCSI_FCOE_BLK_PTR: u32 = 0x17;
pub const IXGBE_ISCSI_FCOE_FLAGS_OFFSET: u32 = 0x0;
pub const IXGBE_ISCSI_FCOE_FLAGS_ENABLE: u32 = 0x1;

// Alternate SAN MAC address block pointers
pub const IXGBE_ALT_SAN_MAC_ADDR_BLK_PTR: u32 = 0x27;
pub const IXGBE_ALT_SAN_MAC_ADDR_CAPS_OFFSET: u32 = 0x0;
pub const IXGBE_ALT_SAN_MAC_ADDR_PORT0_OFFSET: u32 = 0x1;
pub const IXGBE_ALT_SAN_MAC_ADDR_PORT1_OFFSET: u32 = 0x4;
pub const IXGBE_ALT_SAN_MAC_ADDR_WWNN_OFFSET: u32 = 0x7;
pub const IXGBE_ALT_SAN_MAC_ADDR_WWPN_OFFSET: u32 = 0x8;
pub const IXGBE_ALT_SAN_MAC_ADDR_CAPS_SANMAC: u32 = 0x0;
pub const IXGBE_ALT_SAN_MAC_ADDR_CAPS_ALTWWN: u32 = 0x1;

// PCI Bus Information
pub const IXGBE_PCI_DEVICE_STATUS: u32 = 0xAA;
pub const IXGBE_PCI_DEVICE_STATUS_TRANSACTION_PENDING: u32 = 0x0020;
pub const IXGBE_PCI_LINK_STATUS: u32 = 0xB2;
pub const IXGBE_PCI_DEVICE_CONTROL2: u32 = 0xC8;
pub const IXGBE_PCI_LINK_WIDTH: u32 = 0x3F0;
pub const IXGBE_PCI_LINK_WIDTH_1: u32 = 0x10;
pub const IXGBE_PCI_LINK_WIDTH_2: u32 = 0x20;
pub const IXGBE_PCI_LINK_WIDTH_4: u32 = 0x40;
pub const IXGBE_PCI_LINK_WIDTH_8: u32 = 0x80;
pub const IXGBE_PCI_LINK_SPEED: u32 = 0xF;
pub const IXGBE_PCI_LINK_SPEED_2500: u32 = 0x1;
pub const IXGBE_PCI_LINK_SPEED_5000: u32 = 0x2;
pub const IXGBE_PCI_LINK_SPEED_8000: u32 = 0x3;
pub const IXGBE_PCI_HEADER_TYPE_REGISTER: u32 = 0x0E;
pub const IXGBE_PCI_HEADER_TYPE_MULTIFUNC: u32 = 0x80;
pub const IXGBE_PCI_DEVICE_CONTROL2_16MS: u32 = 0x0005;

// PCI Device Control 2 Timeout Settings
pub const IXGBE_PCIDEVCTRL2_TIMEO_MASK: u32 = 0xf;
pub const IXGBE_PCIDEVCTRL2_16_32MS_DEF: u32 = 0x0;
pub const IXGBE_PCIDEVCTRL2_50_100US: u32 = 0x1;
pub const IXGBE_PCIDEVCTRL2_1_2MS: u32 = 0x2;
pub const IXGBE_PCIDEVCTRL2_16_32MS: u32 = 0x5;
pub const IXGBE_PCIDEVCTRL2_65_130MS: u32 = 0x6;
pub const IXGBE_PCIDEVCTRL2_260_520MS: u32 = 0x9;
pub const IXGBE_PCIDEVCTRL2_1_2S: u32 = 0xa;
pub const IXGBE_PCIDEVCTRL2_4_8S: u32 = 0xd;
pub const IXGBE_PCIDEVCTRL2_17_34S: u32 = 0xe;

// PCI Express master disable timeout
pub const IXGBE_PCI_MASTER_DISABLE_TIMEOUT: u32 = 800;

// Check if an address is multicast
pub fn ixgbe_is_multicast(address: &[u8]) -> bool {
    address[0] & 0x01 != 0
}

// Check if an address is broadcast
pub fn ixgbe_is_broadcast(address: &[u8]) -> bool {
    address.iter().all(|&x| x == 0xff)
}

// Receive Address High Register fields
pub const IXGBE_RAH_VIND_MASK: u32 = 0x003C0000;
pub const IXGBE_RAH_VIND_SHIFT: u32 = 18;
pub const IXGBE_RAH_AV: u32 = 0x80000000;

// Clear all VMDq
pub const IXGBE_CLEAR_VMDQ_ALL: u32 = 0xFFFFFFFF;

// Header split receive configuration
pub const IXGBE_RFCTL_ISCSI_DIS: u32 = 0x00000001;
pub const IXGBE_RFCTL_ISCSI_DWC_MASK: u32 = 0x0000003E;
pub const IXGBE_RFCTL_ISCSI_DWC_SHIFT: u32 = 1;
pub const IXGBE_RFCTL_RSC_DIS: u32 = 0x00000020;
pub const IXGBE_RFCTL_NFSW_DIS: u32 = 0x00000040;
pub const IXGBE_RFCTL_NFSR_DIS: u32 = 0x00000080;
pub const IXGBE_RFCTL_NFS_VER_MASK: u32 = 0x00000300;
pub const IXGBE_RFCTL_NFS_VER_SHIFT: u32 = 8;
pub const IXGBE_RFCTL_IPV6_DIS: u32 = 0x00000400;
pub const IXGBE_RFCTL_IPV6_XSUM_DIS: u32 = 0x00000800;
pub const IXGBE_RFCTL_IPFRSP_DIS: u32 = 0x00004000;
pub const IXGBE_RFCTL_IPV6_EX_DIS: u32 = 0x00010000;
pub const IXGBE_RFCTL_NEW_IPV6_EXT_DIS: u32 = 0x00020000;

// Transmit configuration masks
pub const IXGBE_TXDCTL_ENABLE: u32 = 0x02000000;
pub const IXGBE_TXDCTL_SWFLSH: u32 = 0x04000000;
pub const IXGBE_TXDCTL_WTHRESH_SHIFT: u32 = 16;
pub const IXGBE_TX_PAD_ENABLE: u32 = 0x00000400;
pub const IXGBE_JUMBO_FRAME_ENABLE: u32 = 0x00000004;
pub const IXGBE_MAX_FRAME_SZ: u32 = 0x40040000;

// Write-back behavior on Tx
pub const IXGBE_TDWBAL_HEAD_WB_ENABLE: u32 = 0x1;
pub const IXGBE_TDWBAL_SEQNUM_WB_ENABLE: u32 = 0x2;

// Receive configuration masks
pub const IXGBE_RXCTRL_RXEN: u32 = 0x00000001;
pub const IXGBE_RXCTRL_DMBYPS: u32 = 0x00000002;
pub const IXGBE_RXDCTL_ENABLE: u32 = 0x02000000;
pub const IXGBE_RXDCTL_SWFLSH: u32 = 0x04000000;
pub const IXGBE_RXDCTL_RLPMLMASK: u32 = 0x00003FFF;
pub const IXGBE_RXDCTL_RLPML_EN: u32 = 0x00008000;
pub const IXGBE_RXDCTL_VME: u32 = 0x40000000;

// Timestamping auxiliary control
pub const IXGBE_TSAUXC_EN_CLK: u32 = 0x00000004;
pub const IXGBE_TSAUXC_SYNCLK: u32 = 0x00000008;
pub const IXGBE_TSAUXC_SDP0_INT: u32 = 0x00000040;
pub const IXGBE_TSAUXC_EN_TT0: u32 = 0x00000001;
pub const IXGBE_TSAUXC_EN_TT1: u32 = 0x00000002;
pub const IXGBE_TSAUXC_ST0: u32 = 0x00000010;
pub const IXGBE_TSAUXC_DISABLE_SYSTIME: u32 = 0x80000000;

// Timestamping System Data Pointer
pub const IXGBE_TSSDP_TS_SDP0_SEL_MASK: u32 = 0x000000C0;
pub const IXGBE_TSSDP_TS_SDP0_CLK0: u32 = 0x00000080;
pub const IXGBE_TSSDP_TS_SDP0_EN: u32 = 0x00000100;

// TSYNCTXCTL constants
pub const IXGBE_TSYNCTXCTL_VALID: u32 = 0x00000001; // Tx timestamp valid
pub const IXGBE_TSYNCTXCTL_ENABLED: u32 = 0x00000010; // Tx timestamping enabled

// TSYNCRXCTL constants
pub const IXGBE_TSYNCRXCTL_VALID: u32 = 0x00000001; // Rx timestamp valid
pub const IXGBE_TSYNCRXCTL_TYPE_MASK: u32 = 0x0000000E; // Rx type mask
pub const IXGBE_TSYNCRXCTL_TYPE_L2_V2: u32 = 0x00;
pub const IXGBE_TSYNCRXCTL_TYPE_L4_V1: u32 = 0x02;
pub const IXGBE_TSYNCRXCTL_TYPE_L2_L4_V2: u32 = 0x04;
pub const IXGBE_TSYNCRXCTL_TYPE_ALL: u32 = 0x08;
pub const IXGBE_TSYNCRXCTL_TYPE_EVENT_V2: u32 = 0x0A;
pub const IXGBE_TSYNCRXCTL_ENABLED: u32 = 0x00000010; // Rx Timestamping enabled
pub const IXGBE_TSYNCRXCTL_TSIP_UT_EN: u32 = 0x00800000; // Rx Timestamp in Packet
pub const IXGBE_TSYNCRXCTL_TSIP_UP_MASK: u32 = 0xFF000000; // Rx Timestamp UP Mask

// TSIM constants
pub const IXGBE_TSIM_SYS_WRAP: u32 = 0x00000001;
pub const IXGBE_TSIM_TXTS: u32 = 0x00000002;
pub const IXGBE_TSIM_TADJ: u32 = 0x00000080;

// TSICR constants (reused from TSIM)
pub const IXGBE_TSICR_SYS_WRAP: u32 = IXGBE_TSIM_SYS_WRAP;
pub const IXGBE_TSICR_TXTS: u32 = IXGBE_TSIM_TXTS;
pub const IXGBE_TSICR_TADJ: u32 = IXGBE_TSIM_TADJ;

// RXMTRL constants
pub const IXGBE_RXMTRL_V1_CTRLT_MASK: u32 = 0x000000FF;
pub const IXGBE_RXMTRL_V1_SYNC_MSG: u32 = 0x00;
pub const IXGBE_RXMTRL_V1_DELAY_REQ_MSG: u32 = 0x01;
pub const IXGBE_RXMTRL_V1_FOLLOWUP_MSG: u32 = 0x02;
pub const IXGBE_RXMTRL_V1_DELAY_RESP_MSG: u32 = 0x03;
pub const IXGBE_RXMTRL_V1_MGMT_MSG: u32 = 0x04;

pub const IXGBE_RXMTRL_V2_MSGID_MASK: u32 = 0x0000FF00;
pub const IXGBE_RXMTRL_V2_SYNC_MSG: u32 = 0x0000;
pub const IXGBE_RXMTRL_V2_DELAY_REQ_MSG: u32 = 0x0100;
pub const IXGBE_RXMTRL_V2_PDELAY_REQ_MSG: u32 = 0x0200;
pub const IXGBE_RXMTRL_V2_PDELAY_RESP_MSG: u32 = 0x0300;
pub const IXGBE_RXMTRL_V2_FOLLOWUP_MSG: u32 = 0x0800;
pub const IXGBE_RXMTRL_V2_DELAY_RESP_MSG: u32 = 0x0900;
pub const IXGBE_RXMTRL_V2_PDELAY_FOLLOWUP_MSG: u32 = 0x0A00;
pub const IXGBE_RXMTRL_V2_ANNOUNCE_MSG: u32 = 0x0B00;
pub const IXGBE_RXMTRL_V2_SIGNALLING_MSG: u32 = 0x0C00;
pub const IXGBE_RXMTRL_V2_MGMT_MSG: u32 = 0x0D00;

// FCTRL constants
pub const IXGBE_FCTRL_SBP: u32 = 0x00000002; // Store Bad Packet
pub const IXGBE_FCTRL_MPE: u32 = 0x00000100; // Multicast Promiscuous Ena
pub const IXGBE_FCTRL_UPE: u32 = 0x00000200; // Unicast Promiscuous Ena
pub const IXGBE_FCTRL_BAM: u32 = 0x00000400; // Broadcast Accept Mode
pub const IXGBE_FCTRL_PMCF: u32 = 0x00001000; // Pass MAC Control Frames
pub const IXGBE_FCTRL_DPF: u32 = 0x00002000; // Discard Pause Frame
pub const IXGBE_FCTRL_RPFCE: u32 = 0x00004000; // Receive Priority Flow Control Enable
pub const IXGBE_FCTRL_RFCE: u32 = 0x00008000; // Receive Flow Control Ena

// MFLCN constants
pub const IXGBE_MFLCN_PMCF: u32 = 0x00000001; // Pass MAC Control Frames
pub const IXGBE_MFLCN_DPF: u32 = 0x00000002; // Discard Pause Frame
pub const IXGBE_MFLCN_RPFCE: u32 = 0x00000004; // Receive Priority FC Enable
pub const IXGBE_MFLCN_RFCE: u32 = 0x00000008; // Receive FC Enable
pub const IXGBE_MFLCN_RPFCE_MASK: u32 = 0x00000FF4; // Rx Priority FC bitmap mask
pub const IXGBE_MFLCN_RPFCE_SHIFT: u32 = 4; // Rx Priority FC bitmap shift

// Multiple Receive Queue Control
pub const IXGBE_MRQC_RSSEN: u32 = 0x00000001; // RSS Enable
pub const IXGBE_MRQC_MRQE_MASK: u32 = 0xF; // Bits 3:0
pub const IXGBE_MRQC_RT8TCEN: u32 = 0x00000002; // 8 TC no RSS
pub const IXGBE_MRQC_RT4TCEN: u32 = 0x00000003; // 4 TC no RSS
pub const IXGBE_MRQC_RTRSS8TCEN: u32 = 0x00000004; // 8 TC with RSS
pub const IXGBE_MRQC_RTRSS4TCEN: u32 = 0x00000005; // 4 TC with RSS
pub const IXGBE_MRQC_VMDQEN: u32 = 0x00000008; // VMDq2 64 pools no RSS
pub const IXGBE_MRQC_VMDQRSS32EN: u32 = 0x0000000A; // VMDq2 32 pools with RSS
pub const IXGBE_MRQC_VMDQRSS64EN: u32 = 0x0000000B; // VMDq2 64 pools with RSS
pub const IXGBE_MRQC_VMDQRT8TCEN: u32 = 0x0000000C; // VMDq2/RT 16 pool 8 TC
pub const IXGBE_MRQC_VMDQRT4TCEN: u32 = 0x0000000D; // VMDq2/RT 32 pool 4 TC
pub const IXGBE_MRQC_L3L4TXSWEN: u32 = 0x00008000; // Enable L3/L4 Tx switch
pub const IXGBE_MRQC_RSS_FIELD_MASK: u32 = 0xFFFF0000;
pub const IXGBE_MRQC_RSS_FIELD_IPV4_TCP: u32 = 0x00010000;
pub const IXGBE_MRQC_RSS_FIELD_IPV4: u32 = 0x00020000;
pub const IXGBE_MRQC_RSS_FIELD_IPV6_EX_TCP: u32 = 0x00040000;
pub const IXGBE_MRQC_RSS_FIELD_IPV6_EX: u32 = 0x00080000;
pub const IXGBE_MRQC_RSS_FIELD_IPV6: u32 = 0x00100000;
pub const IXGBE_MRQC_RSS_FIELD_IPV6_TCP: u32 = 0x00200000;
pub const IXGBE_MRQC_RSS_FIELD_IPV4_UDP: u32 = 0x00400000;
pub const IXGBE_MRQC_RSS_FIELD_IPV6_UDP: u32 = 0x00800000;
pub const IXGBE_MRQC_RSS_FIELD_IPV6_EX_UDP: u32 = 0x01000000;
pub const IXGBE_MRQC_MULTIPLE_RSS: u32 = 0x00002000;

// Queue Drop Enable
pub const IXGBE_QDE_ENABLE: u32 = 0x00000001;
pub const IXGBE_QDE_HIDE_VLAN: u32 = 0x00000002;
pub const IXGBE_QDE_IDX_MASK: u32 = 0x00007F00;
pub const IXGBE_QDE_IDX_SHIFT: u8 = 8;
pub const IXGBE_QDE_WRITE: u32 = 0x00010000;
pub const IXGBE_QDE_READ: u32 = 0x00020000;

// TX Descriptor packet option bits
pub const IXGBE_TXD_POPTS_IXSM: u32 = 0x01; // Insert IP checksum
pub const IXGBE_TXD_POPTS_TXSM: u32 = 0x02; // Insert TCP/UDP checksum

// TX Descriptor command bits
pub const IXGBE_TXD_CMD_EOP: u32 = 0x01000000; // End of Packet
pub const IXGBE_TXD_CMD_IFCS: u32 = 0x02000000; // Insert FCS (Ethernet CRC)
pub const IXGBE_TXD_CMD_IC: u32 = 0x04000000; // Insert Checksum
pub const IXGBE_TXD_CMD_RS: u32 = 0x08000000; // Report Status
pub const IXGBE_TXD_CMD_DEXT: u32 = 0x20000000; // Descriptor extension (0 = legacy)
pub const IXGBE_TXD_CMD_VLE: u32 = 0x40000000; // Add VLAN tag

// TX Descriptor status bits
pub const IXGBE_TXD_STAT_DD: u32 = 0x00000001; // Descriptor Done

// RX Descriptor advanced IPSEC status bits
pub const IXGBE_RXDADV_IPSEC_STATUS_SECP: u32 = 0x00020000;
pub const IXGBE_RXDADV_IPSEC_ERROR_INVALID_PROTOCOL: u32 = 0x08000000;
pub const IXGBE_RXDADV_IPSEC_ERROR_INVALID_LENGTH: u32 = 0x10000000;
pub const IXGBE_RXDADV_IPSEC_ERROR_AUTH_FAILED: u32 = 0x18000000;
pub const IXGBE_RXDADV_IPSEC_ERROR_BIT_MASK: u32 = 0x18000000;

// Multiple Transmit Queue Command Register
pub const IXGBE_MTQC_RT_ENA: u32 = 0x1; // DCB Enable
pub const IXGBE_MTQC_VT_ENA: u32 = 0x2; // VMDQ2 Enable
pub const IXGBE_MTQC_64Q_1PB: u32 = 0x0; // 64 queues, 1 packet buffer
pub const IXGBE_MTQC_32VF: u32 = 0x8; // 4 TX Queues per pool with 32 VFs
pub const IXGBE_MTQC_64VF: u32 = 0x4; // 2 TX Queues per pool with 64 VFs
pub const IXGBE_MTQC_4TC_4TQ: u32 = 0x8; // 4 TC if RT_ENA and VT_ENA
pub const IXGBE_MTQC_8TC_8TQ: u32 = 0xC; // 8 TC if RT_ENA or 8 TQ if VT_ENA

// Receive Descriptor bit definitions
pub const IXGBE_RXD_STAT_DD: u32 = 0x01; // Descriptor Done
pub const IXGBE_RXD_STAT_EOP: u32 = 0x02; // End of Packet
pub const IXGBE_RXD_STAT_FLM: u32 = 0x04; // FDir Match
pub const IXGBE_RXD_STAT_VP: u32 = 0x08; // IEEE VLAN Packet
pub const IXGBE_RXDADV_NEXTP_MASK: u32 = 0x000FFFF0; // Next Descriptor Index
pub const IXGBE_RXDADV_NEXTP_SHIFT: u32 = 0x00000004;
pub const IXGBE_RXD_STAT_UDPCS: u32 = 0x10; // UDP checksum calculated
pub const IXGBE_RXD_STAT_L4CS: u32 = 0x20; // L4 checksum calculated
pub const IXGBE_RXD_STAT_IPCS: u32 = 0x40; // IP checksum calculated
pub const IXGBE_RXD_STAT_PIF: u32 = 0x80; // Passed in-exact filter
pub const IXGBE_RXD_STAT_CRCV: u32 = 0x100; // Speculative CRC Valid
pub const IXGBE_RXD_STAT_OUTERIPCS: u32 = 0x100; // Cloud IP checksum calculated
pub const IXGBE_RXD_STAT_VEXT: u32 = 0x200; // 1st VLAN found
pub const IXGBE_RXD_STAT_UDPV: u32 = 0x400; // Valid UDP checksum
pub const IXGBE_RXD_STAT_DYNINT: u32 = 0x800; // Packet caused INT via DYNINT
pub const IXGBE_RXD_STAT_LLINT: u32 = 0x800; // Packet caused Low Latency Interrupt
pub const IXGBE_RXD_STAT_TSIP: u32 = 0x08000; // Time Stamp in packet buffer
pub const IXGBE_RXD_STAT_TS: u32 = 0x10000; // Time Stamp
pub const IXGBE_RXD_STAT_SECP: u32 = 0x20000; // Security Processing
pub const IXGBE_RXD_STAT_LB: u32 = 0x40000; // Loopback Status
pub const IXGBE_RXD_STAT_ACK: u32 = 0x8000; // ACK Packet indication
pub const IXGBE_RXD_ERR_CE: u32 = 0x01; // CRC Error
pub const IXGBE_RXD_ERR_LE: u32 = 0x02; // Length Error
pub const IXGBE_RXD_ERR_PE: u32 = 0x08; // Packet Error
pub const IXGBE_RXD_ERR_OSE: u32 = 0x10; // Oversize Error
pub const IXGBE_RXD_ERR_USE: u32 = 0x20; // Undersize Error
pub const IXGBE_RXD_ERR_TCPE: u32 = 0x40; // TCP/UDP Checksum Error
pub const IXGBE_RXD_ERR_IPE: u32 = 0x80; // IP Checksum Error
pub const IXGBE_RXDADV_ERR_MASK: u32 = 0xfff00000; // RDESC.ERRORS mask
pub const IXGBE_RXDADV_ERR_SHIFT: u32 = 20; // RDESC.ERRORS shift
pub const IXGBE_RXDADV_ERR_OUTERIPER: u32 = 0x04000000; // CRC IP Header error
pub const IXGBE_RXDADV_ERR_RXE: u32 = 0x20000000; // Any MAC Error
pub const IXGBE_RXDADV_ERR_FCEOFE: u32 = 0x80000000; // FCEOFe/IPE
pub const IXGBE_RXDADV_ERR_FCERR: u32 = 0x00700000; // FCERR/FDIRERR
pub const IXGBE_RXDADV_ERR_FDIR_LEN: u32 = 0x00100000; // FDIR Length error
pub const IXGBE_RXDADV_ERR_FDIR_DROP: u32 = 0x00200000; // FDIR Drop error
pub const IXGBE_RXDADV_ERR_FDIR_COLL: u32 = 0x00400000; // FDIR Collision error
pub const IXGBE_RXDADV_ERR_HBO: u32 = 0x00800000; // Header Buffer Overflow
pub const IXGBE_RXDADV_ERR_CE: u32 = 0x01000000; // CRC Error
pub const IXGBE_RXDADV_ERR_LE: u32 = 0x02000000; // Length Error
pub const IXGBE_RXDADV_ERR_PE: u32 = 0x08000000; // Packet Error
pub const IXGBE_RXDADV_ERR_OSE: u32 = 0x10000000; // Oversize Error
pub const IXGBE_RXDADV_ERR_USE: u32 = 0x20000000; // Undersize Error
pub const IXGBE_RXDADV_ERR_TCPE: u32 = 0x40000000; // TCP/UDP Checksum Error
pub const IXGBE_RXDADV_ERR_IPE: u32 = 0x80000000; // IP Checksum Error

// VLAN ID, Priority, and CFI Masks and Shifts
pub const IXGBE_RXD_VLAN_ID_MASK: u32 = 0x0FFF; // VLAN ID is in lower 12 bits
pub const IXGBE_RXD_PRI_MASK: u32 = 0xE000; // Priority is in upper 3 bits
pub const IXGBE_RXD_PRI_SHIFT: u32 = 13;
pub const IXGBE_RXD_CFI_MASK: u32 = 0x1000; // CFI is bit 12
pub const IXGBE_RXD_CFI_SHIFT: u32 = 12;

// RXDADV Stat Definitions
pub const IXGBE_RXDADV_STAT_DD: u32 = IXGBE_RXD_STAT_DD; // Done
pub const IXGBE_RXDADV_STAT_EOP: u32 = IXGBE_RXD_STAT_EOP; // End of Packet
pub const IXGBE_RXDADV_STAT_FLM: u32 = IXGBE_RXD_STAT_FLM; // FDir Match
pub const IXGBE_RXDADV_STAT_VP: u32 = IXGBE_RXD_STAT_VP; // IEEE VLAN Packet
pub const IXGBE_RXDADV_STAT_MASK: u32 = 0x000fffff; // Stat/NEXTP: bit 0-19
pub const IXGBE_RXDADV_STAT_FCEOFS: u32 = 0x00000040; // FCoE EOF/SOF Stat
pub const IXGBE_RXDADV_STAT_FCSTAT: u32 = 0x00000030; // FCoE Pkt Stat
pub const IXGBE_RXDADV_STAT_FCSTAT_NOMTCH: u32 = 0x00000000; // No Ctxt Match
pub const IXGBE_RXDADV_STAT_FCSTAT_NODDP: u32 = 0x00000010; // Ctxt w/o DDP
pub const IXGBE_RXDADV_STAT_FCSTAT_FCPRSP: u32 = 0x00000020; // Recv. FCP_RSP
pub const IXGBE_RXDADV_STAT_FCSTAT_DDP: u32 = 0x00000030; // Ctxt w/ DDP
pub const IXGBE_RXDADV_STAT_TS: u32 = 0x00010000; // IEEE1588 Time Stamp
pub const IXGBE_RXDADV_STAT_TSIP: u32 = 0x00008000; // Time Stamp in packet buffer

// PSRTYPE Bit Definitions
pub const IXGBE_PSRTYPE_TCPHDR: u32 = 0x00000010;
pub const IXGBE_PSRTYPE_UDPHDR: u32 = 0x00000020;
pub const IXGBE_PSRTYPE_IPV4HDR: u32 = 0x00000100;
pub const IXGBE_PSRTYPE_IPV6HDR: u32 = 0x00000200;
pub const IXGBE_PSRTYPE_L2HDR: u32 = 0x00001000;

// SRRCTL Bit Definitions
pub const IXGBE_SRRCTL_BSIZEPKT_SHIFT: u32 = 10;
pub const IXGBE_SRRCTL_BSIZEHDRSIZE_SHIFT: u32 = 2;
pub const IXGBE_SRRCTL_RDMTS_SHIFT: u32 = 22;
pub const IXGBE_SRRCTL_RDMTS_MASK: u32 = 0x01C00000;
pub const IXGBE_SRRCTL_DROP_EN: u32 = 0x10000000;
pub const IXGBE_SRRCTL_BSIZEPKT_MASK: u32 = 0x0000007F;
pub const IXGBE_SRRCTL_BSIZEHDR_MASK: u32 = 0x00003F00;
pub const IXGBE_SRRCTL_DESCTYPE_LEGACY: u32 = 0x00000000;
pub const IXGBE_SRRCTL_DESCTYPE_ADV_ONEBUF: u32 = 0x02000000;
pub const IXGBE_SRRCTL_DESCTYPE_HDR_SPLIT: u32 = 0x04000000;
pub const IXGBE_SRRCTL_DESCTYPE_HDR_REPLICATION_LARGE_PKT: u32 = 0x08000000;
pub const IXGBE_SRRCTL_DESCTYPE_HDR_SPLIT_ALWAYS: u32 = 0x0A000000;
pub const IXGBE_SRRCTL_DESCTYPE_MASK: u32 = 0x0E000000;

// Receive Descriptor Packet Split Header Status
pub const IXGBE_RXDPS_HDRSTAT_HDRSP: u32 = 0x00008000;
pub const IXGBE_RXDPS_HDRSTAT_HDRLEN_MASK: u32 = 0x000003FF;

// Receive Descriptor Advanced Definitions
pub const IXGBE_RXDADV_RSSTYPE_MASK: u32 = 0x0000000F;
pub const IXGBE_RXDADV_PKTTYPE_MASK: u32 = 0x0000FFF0;
pub const IXGBE_RXDADV_PKTTYPE_MASK_EX: u32 = 0x0001FFF0;
pub const IXGBE_RXDADV_HDRBUFLEN_MASK: u32 = 0x00007FE0;
pub const IXGBE_RXDADV_RSCCNT_MASK: u32 = 0x001E0000;
pub const IXGBE_RXDADV_RSCCNT_SHIFT: u32 = 17;
pub const IXGBE_RXDADV_HDRBUFLEN_SHIFT: u32 = 5;
pub const IXGBE_RXDADV_SPLITHEADER_EN: u32 = 0x00001000;
pub const IXGBE_RXDADV_SPH: u16 = 0x8000;

// RSS Hash Results Types
pub const IXGBE_RXDADV_RSSTYPE_NONE: u32 = 0x00000000;
pub const IXGBE_RXDADV_RSSTYPE_IPV4_TCP: u32 = 0x00000001;
pub const IXGBE_RXDADV_RSSTYPE_IPV4: u32 = 0x00000002;
pub const IXGBE_RXDADV_RSSTYPE_IPV6_TCP: u32 = 0x00000003;
pub const IXGBE_RXDADV_RSSTYPE_IPV6_EX: u32 = 0x00000004;
pub const IXGBE_RXDADV_RSSTYPE_IPV6: u32 = 0x00000005;
pub const IXGBE_RXDADV_RSSTYPE_IPV6_TCP_EX: u32 = 0x00000006;
pub const IXGBE_RXDADV_RSSTYPE_IPV4_UDP: u32 = 0x00000007;
pub const IXGBE_RXDADV_RSSTYPE_IPV6_UDP: u32 = 0x00000008;
pub const IXGBE_RXDADV_RSSTYPE_IPV6_UDP_EX: u32 = 0x00000009;

// RSS Packet Types
pub const IXGBE_RXDADV_PKTTYPE_NONE: u32 = 0x00000000;
pub const IXGBE_RXDADV_PKTTYPE_IPV4: u32 = 0x00000010; // IPv4 hdr present
pub const IXGBE_RXDADV_PKTTYPE_IPV4_EX: u32 = 0x00000020; // IPv4 hdr + extensions
pub const IXGBE_RXDADV_PKTTYPE_IPV6: u32 = 0x00000040; // IPv6 hdr present
pub const IXGBE_RXDADV_PKTTYPE_IPV6_EX: u32 = 0x00000080; // IPv6 hdr + extensions
pub const IXGBE_RXDADV_PKTTYPE_TCP: u32 = 0x00000100; // TCP hdr present
pub const IXGBE_RXDADV_PKTTYPE_UDP: u32 = 0x00000200; // UDP hdr present
pub const IXGBE_RXDADV_PKTTYPE_SCTP: u32 = 0x00000400; // SCTP hdr present
pub const IXGBE_RXDADV_PKTTYPE_NFS: u32 = 0x00000800; // NFS hdr present
pub const IXGBE_RXDADV_PKTTYPE_GENEVE: u32 = 0x00000800; // GENEVE hdr present
pub const IXGBE_RXDADV_PKTTYPE_VXLAN: u32 = 0x00000800; // VXLAN hdr present
pub const IXGBE_RXDADV_PKTTYPE_TUNNEL: u32 = 0x00010000; // Tunnel type
pub const IXGBE_RXDADV_PKTTYPE_IPSEC_ESP: u32 = 0x00001000; // IPSec ESP
pub const IXGBE_RXDADV_PKTTYPE_IPSEC_AH: u32 = 0x00002000; // IPSec AH
pub const IXGBE_RXDADV_PKTTYPE_LINKSEC: u32 = 0x00004000; // LinkSec Encap
pub const IXGBE_RXDADV_PKTTYPE_ETQF: u32 = 0x00008000; // PKTTYPE is ETQF index
pub const IXGBE_RXDADV_PKTTYPE_ETQF_MASK: u32 = 0x00000070; // ETQF has 8 indices
pub const IXGBE_RXDADV_PKTTYPE_ETQF_SHIFT: u32 = 4; // Right-shift 4 bits

pub const IXGBE_RXDADV_LNKSEC_STATUS_SECP: u32 = 0x00020000;
pub const IXGBE_RXDADV_LNKSEC_ERROR_NO_SA_MATCH: u32 = 0x08000000;
pub const IXGBE_RXDADV_LNKSEC_ERROR_REPLAY_ERROR: u32 = 0x10000000;
pub const IXGBE_RXDADV_LNKSEC_ERROR_BIT_MASK: u32 = 0x18000000;
pub const IXGBE_RXDADV_LNKSEC_ERROR_BAD_SIG: u32 = 0x18000000;

pub const IXGBE_RXD_ERR_FRAME_ERR_MASK: u32 =
    IXGBE_RXD_ERR_CE | IXGBE_RXD_ERR_LE | IXGBE_RXD_ERR_PE | IXGBE_RXD_ERR_OSE | IXGBE_RXD_ERR_USE;

pub const IXGBE_RXDADV_ERR_FRAME_ERR_MASK: u32 = IXGBE_RXDADV_ERR_CE
    | IXGBE_RXDADV_ERR_LE
    | IXGBE_RXDADV_ERR_PE
    | IXGBE_RXDADV_ERR_OSE
    | IXGBE_RXDADV_ERR_USE;

pub const IXGBE_RXDADV_ERR_FRAME_ERR_MASK_82599: u32 = IXGBE_RXDADV_ERR_RXE;

pub const IXGBE_MCSTCTRL_MFE: u32 = 0x4;

// Number of Transmit and Receive Descriptors must be a multiple of 8
pub const IXGBE_REQ_TX_DESCRIPTOR_MULTIPLE: u32 = 8;
pub const IXGBE_REQ_RX_DESCRIPTOR_MULTIPLE: u32 = 8;
pub const IXGBE_REQ_TX_BUFFER_GRANULARITY: u32 = 1024;

// Vlan-specific macros
pub const IXGBE_RX_DESC_SPECIAL_VLAN_MASK: u32 = 0x0FFF; // VLAN ID in lower 12 bits
pub const IXGBE_RX_DESC_SPECIAL_PRI_MASK: u32 = 0xE000; // Priority in upper 3 bits
pub const IXGBE_RX_DESC_SPECIAL_PRI_SHIFT: u32 = 0x000D; // Priority in upper 3 of 16
pub const IXGBE_TX_DESC_SPECIAL_PRI_SHIFT: u32 = IXGBE_RX_DESC_SPECIAL_PRI_SHIFT;

// SR-IOV specific macros
pub const IXGBE_MBVFICR_INDEX: fn(vf_number: u32) -> u32 = |vf_number| vf_number >> 4;
pub const IXGBE_MBVFICR: fn(i: u32) -> u32 = |i| 0x00710 + (i * 4);
pub const IXGBE_VFLRE: fn(i: u32) -> u32 = |i| (i & 1 != 0).then(|| 0x001C0).unwrap_or(0x00600);
pub const IXGBE_VFLREC: fn(i: u32) -> u32 = |i| 0x00700 + (i * 4);

// Translated register #defines
pub const IXGBE_PVFCTRL: fn(p: u32) -> u32 = |p| 0x00300 + (4 * p);
pub const IXGBE_PVFSTATUS: fn(p: u32) -> u32 = |p| 0x00008 + (0 * p);
pub const IXGBE_PVFLINKS: fn(p: u32) -> u32 = |p| 0x042A4 + (0 * p);
pub const IXGBE_PVFRTIMER: fn(p: u32) -> u32 = |p| 0x00048 + (0 * p);
pub const IXGBE_PVFMAILBOX: fn(p: u32) -> u32 = |p| 0x04C00 + (4 * p);
pub const IXGBE_PVFRXMEMWRAP: fn(p: u32) -> u32 = |p| 0x03190 + (0 * p);
pub const IXGBE_PVTEICR: fn(p: u32) -> u32 = |p| 0x00B00 + (4 * p);
pub const IXGBE_PVTEICS: fn(p: u32) -> u32 = |p| 0x00C00 + (4 * p);
pub const IXGBE_PVTEIMS: fn(p: u32) -> u32 = |p| 0x00D00 + (4 * p);
pub const IXGBE_PVTEIMC: fn(p: u32) -> u32 = |p| 0x00E00 + (4 * p);
pub const IXGBE_PVTEIAC: fn(p: u32) -> u32 = |p| 0x00F00 + (4 * p);
pub const IXGBE_PVTEIAM: fn(p: u32) -> u32 = |p| 0x04D00 + (4 * p);
pub const IXGBE_PVTEITR: fn(p: u32) -> u32 = |p| {
    (p < 24)
        .then(|| 0x00820 + (p * 4))
        .unwrap_or(0x012300 + ((p - 24) * 4))
};
pub const IXGBE_PVTIVAR: fn(p: u32) -> u32 = |p| 0x12500 + (4 * p);
pub const IXGBE_PVTIVAR_MISC: fn(p: u32) -> u32 = |p| 0x04E00 + (4 * p);
pub const IXGBE_PVTRSCINT: fn(p: u32) -> u32 = |p| 0x12000 + (4 * p);
pub const IXGBE_VFPBACL: fn(p: u32) -> u32 = |p| 0x110C8 + (4 * p);

pub const IXGBE_PVFRDBAL: fn(p: u32) -> u32 = |p| {
    if p < 64 {
        0x01000 + (0x40 * p)
    } else {
        0x0D000 + (0x40 * (p - 64))
    }
};

pub const IXGBE_PVFRDBAH: fn(p: u32) -> u32 = |p| {
    if p < 64 {
        0x01004 + (0x40 * p)
    } else {
        0x0D004 + (0x40 * (p - 64))
    }
};

pub const IXGBE_PVFRDLEN: fn(p: u32) -> u32 = |p| {
    if p < 64 {
        0x01008 + (0x40 * p)
    } else {
        0x0D008 + (0x40 * (p - 64))
    }
};

pub const IXGBE_PVFRDH: fn(p: u32) -> u32 = |p| {
    if p < 64 {
        0x01010 + (0x40 * p)
    } else {
        0x0D010 + (0x40 * (p - 64))
    }
};

pub const IXGBE_PVFRDT: fn(p: u32) -> u32 = |p| {
    if p < 64 {
        0x01018 + (0x40 * p)
    } else {
        0x0D018 + (0x40 * (p - 64))
    }
};

pub const IXGBE_PVFRXDCTL: fn(p: u32) -> u32 = |p| {
    if p < 64 {
        0x01028 + (0x40 * p)
    } else {
        0x0D028 + (0x40 * (p - 64))
    }
};

pub const IXGBE_PVFSRRCTL: fn(p: u32) -> u32 = |p| {
    if p < 64 {
        0x01014 + (0x40 * p)
    } else {
        0x0D014 + (0x40 * (p - 64))
    }
};

pub const IXGBE_PVFPSRTYPE: fn(p: u32) -> u32 = |p| 0x0EA00 + (4 * p);

pub const IXGBE_PVFTDBAL: fn(p: u32) -> u32 = |p| 0x06000 + (0x40 * p);
pub const IXGBE_PVFTDBAH: fn(p: u32) -> u32 = |p| 0x06004 + (0x40 * p);
pub const IXGBE_PVFTDLEN: fn(p: u32) -> u32 = |p| 0x06008 + (0x40 * p);
pub const IXGBE_PVFTDH: fn(p: u32) -> u32 = |p| 0x06010 + (0x40 * p);
pub const IXGBE_PVFTDT: fn(p: u32) -> u32 = |p| 0x06018 + (0x40 * p);
pub const IXGBE_PVFTXDCTL: fn(p: u32) -> u32 = |p| 0x06028 + (0x40 * p);
pub const IXGBE_PVFTDWBAL: fn(p: u32) -> u32 = |p| 0x06038 + (0x40 * p);
pub const IXGBE_PVFTDWBAH: fn(p: u32) -> u32 = |p| 0x0603C + (0x40 * p);

pub const IXGBE_PVFDCA_RXCTRL: fn(p: u32) -> u32 = |p| {
    if p < 64 {
        0x0100C + (0x40 * p)
    } else {
        0x0D00C + (0x40 * (p - 64))
    }
};

pub const IXGBE_PVFDCA_TXCTRL: fn(p: u32) -> u32 = |p| 0x0600C + (0x40 * p);
pub const IXGBE_PVFGPRC: fn(x: u32) -> u32 = |x| 0x0101C + (0x40 * x);
pub const IXGBE_PVFGPTC: fn(x: u32) -> u32 = |x| 0x08300 + (0x04 * x);
pub const IXGBE_PVFGORC_LSB: fn(x: u32) -> u32 = |x| 0x01020 + (0x40 * x);
pub const IXGBE_PVFGORC_MSB: fn(x: u32) -> u32 = |x| 0x0D020 + (0x40 * x);
pub const IXGBE_PVFGOTC_LSB: fn(x: u32) -> u32 = |x| 0x08400 + (0x08 * x);
pub const IXGBE_PVFGOTC_MSB: fn(x: u32) -> u32 = |x| 0x08404 + (0x08 * x);
pub const IXGBE_PVFMPRC: fn(x: u32) -> u32 = |x| 0x0D01C + (0x40 * x);

// Macro functions for accessing specific fields
pub const IXGBE_PVFTDWBALN: fn(q_per_pool: u32, vf_number: u32, vf_q_index: u32) -> u32 =
    |q_per_pool, vf_number, vf_q_index| IXGBE_PVFTDWBAL((q_per_pool * vf_number) + vf_q_index);

pub const IXGBE_PVFTDWBAHN: fn(q_per_pool: u32, vf_number: u32, vf_q_index: u32) -> u32 =
    |q_per_pool, vf_number, vf_q_index| IXGBE_PVFTDWBAH((q_per_pool * vf_number) + vf_q_index);

pub const IXGBE_PVFTDHN: fn(q_per_pool: u32, vf_number: u32, vf_q_index: u32) -> u32 =
    |q_per_pool, vf_number, vf_q_index| IXGBE_PVFTDH((q_per_pool * vf_number) + vf_q_index);

pub const IXGBE_PVFTDTN: fn(q_per_pool: u32, vf_number: u32, vf_q_index: u32) -> u32 =
    |q_per_pool, vf_number, vf_q_index| IXGBE_PVFTDT((q_per_pool * vf_number) + vf_q_index);

// Enum for flow director buffer allocation sizes
#[repr(u32)]
enum IxgbeFdirPballocType {
    None = 0,
    K64 = 1,
    K128 = 2,
    K256 = 3,
}

// Flow Director register values
pub const IXGBE_FDIRCTRL_PBALLOC_64K: u32 = 0x00000001;
pub const IXGBE_FDIRCTRL_PBALLOC_128K: u32 = 0x00000002;
pub const IXGBE_FDIRCTRL_PBALLOC_256K: u32 = 0x00000003;
pub const IXGBE_FDIRCTRL_INIT_DONE: u32 = 0x00000008;
pub const IXGBE_FDIRCTRL_PERFECT_MATCH: u32 = 0x00000010;
pub const IXGBE_FDIRCTRL_REPORT_STATUS: u32 = 0x00000020;
pub const IXGBE_FDIRCTRL_REPORT_STATUS_ALWAYS: u32 = 0x00000080;
pub const IXGBE_FDIRCTRL_DROP_Q_SHIFT: u32 = 8;
pub const IXGBE_FDIRCTRL_DROP_Q_MASK: u32 = 0x00007F00;
pub const IXGBE_FDIRCTRL_FLEX_SHIFT: u32 = 16;
pub const IXGBE_FDIRCTRL_DROP_NO_MATCH: u32 = 0x00008000;
pub const IXGBE_FDIRCTRL_FILTERMODE_SHIFT: u32 = 21;
pub const IXGBE_FDIRCTRL_FILTERMODE_MACVLAN: u32 = 0x0001; // 001b
pub const IXGBE_FDIRCTRL_FILTERMODE_CLOUD: u32 = 0x0002; // 010b
pub const IXGBE_FDIRCTRL_SEARCHLIM: u32 = 0x00800000;
pub const IXGBE_FDIRCTRL_FILTERMODE_MASK: u32 = 0x00E00000;
pub const IXGBE_FDIRCTRL_MAX_LENGTH_SHIFT: u32 = 24;
pub const IXGBE_FDIRCTRL_FULL_THRESH_MASK: u32 = 0xF0000000;
pub const IXGBE_FDIRCTRL_FULL_THRESH_SHIFT: u32 = 28;

pub const IXGBE_FDIRTCPM_DPORTM_SHIFT: u32 = 16;
pub const IXGBE_FDIRUDPM_DPORTM_SHIFT: u32 = 16;
pub const IXGBE_FDIRIP6M_DIPM_SHIFT: u32 = 16;
pub const IXGBE_FDIRM_VLANID: u32 = 0x00000001;
pub const IXGBE_FDIRM_VLANP: u32 = 0x00000002;
pub const IXGBE_FDIRM_POOL: u32 = 0x00000004;
pub const IXGBE_FDIRM_L4P: u32 = 0x00000008;
pub const IXGBE_FDIRM_FLEX: u32 = 0x00000010;
pub const IXGBE_FDIRM_DIPV6: u32 = 0x00000020;
pub const IXGBE_FDIRM_L3P: u32 = 0x00000040;

pub const IXGBE_FDIRIP6M_INNER_MAC: u32 = 0x03F0; // bit 9:4
pub const IXGBE_FDIRIP6M_TUNNEL_TYPE: u32 = 0x0800; // bit 11
pub const IXGBE_FDIRIP6M_TNI_VNI: u32 = 0xF000; // bit 15:12
pub const IXGBE_FDIRIP6M_TNI_VNI_24: u32 = 0x1000; // bit 12
pub const IXGBE_FDIRIP6M_ALWAYS_MASK: u32 = 0x040F; // bit 10, 3:0

pub const IXGBE_FDIRFREE_FREE_MASK: u32 = 0xFFFF;
pub const IXGBE_FDIRFREE_FREE_SHIFT: u32 = 0;
pub const IXGBE_FDIRFREE_COLL_MASK: u32 = 0x7FFF0000;
pub const IXGBE_FDIRFREE_COLL_SHIFT: u32 = 16;
pub const IXGBE_FDIRLEN_MAXLEN_MASK: u32 = 0x3F;
pub const IXGBE_FDIRLEN_MAXLEN_SHIFT: u32 = 0;
pub const IXGBE_FDIRLEN_MAXHASH_MASK: u32 = 0x7FFF0000;
pub const IXGBE_FDIRLEN_MAXHASH_SHIFT: u32 = 16;
pub const IXGBE_FDIRUSTAT_ADD_MASK: u32 = 0xFFFF;
pub const IXGBE_FDIRUSTAT_ADD_SHIFT: u32 = 0;
pub const IXGBE_FDIRUSTAT_REMOVE_MASK: u32 = 0xFFFF0000;
pub const IXGBE_FDIRUSTAT_REMOVE_SHIFT: u32 = 16;
pub const IXGBE_FDIRFSTAT_FADD_MASK: u32 = 0x00FF;
pub const IXGBE_FDIRFSTAT_FADD_SHIFT: u32 = 0;
pub const IXGBE_FDIRFSTAT_FREMOVE_MASK: u32 = 0xFF00;
pub const IXGBE_FDIRFSTAT_FREMOVE_SHIFT: u32 = 8;
pub const IXGBE_FDIRPORT_DESTINATION_SHIFT: u32 = 16;
pub const IXGBE_FDIRVLAN_FLEX_SHIFT: u32 = 16;
pub const IXGBE_FDIRHASH_BUCKET_VALID_SHIFT: u32 = 15;
pub const IXGBE_FDIRHASH_SIG_SW_INDEX_SHIFT: u32 = 16;

pub const IXGBE_FDIRCMD_CMD_MASK: u32 = 0x00000003;
pub const IXGBE_FDIRCMD_CMD_ADD_FLOW: u32 = 0x00000001;
pub const IXGBE_FDIRCMD_CMD_REMOVE_FLOW: u32 = 0x00000002;
pub const IXGBE_FDIRCMD_CMD_QUERY_REM_FILT: u32 = 0x00000003;
pub const IXGBE_FDIRCMD_FILTER_VALID: u32 = 0x00000004;
pub const IXGBE_FDIRCMD_FILTER_UPDATE: u32 = 0x00000008;
pub const IXGBE_FDIRCMD_IPV6DMATCH: u32 = 0x00000010;
pub const IXGBE_FDIRCMD_L4TYPE_UDP: u32 = 0x00000020;
pub const IXGBE_FDIRCMD_L4TYPE_TCP: u32 = 0x00000040;
pub const IXGBE_FDIRCMD_L4TYPE_SCTP: u32 = 0x00000060;
pub const IXGBE_FDIRCMD_IPV6: u32 = 0x00000080;
pub const IXGBE_FDIRCMD_CLEARHT: u32 = 0x00000100;
pub const IXGBE_FDIRCMD_DROP: u32 = 0x00000200;
pub const IXGBE_FDIRCMD_INT: u32 = 0x00000400;
pub const IXGBE_FDIRCMD_LAST: u32 = 0x00000800;
pub const IXGBE_FDIRCMD_COLLISION: u32 = 0x00001000;
pub const IXGBE_FDIRCMD_QUEUE_EN: u32 = 0x00008000;
pub const IXGBE_FDIRCMD_FLOW_TYPE_SHIFT: u32 = 5;
pub const IXGBE_FDIRCMD_RX_QUEUE_SHIFT: u32 = 16;
pub const IXGBE_FDIRCMD_TUNNEL_FILTER_SHIFT: u32 = 23;
pub const IXGBE_FDIRCMD_VT_POOL_SHIFT: u32 = 24;
pub const IXGBE_FDIR_INIT_DONE_POLL: u32 = 10;
pub const IXGBE_FDIRCMD_CMD_POLL: u32 = 10;
pub const IXGBE_FDIRCMD_TUNNEL_FILTER: u32 = 0x00800000;
pub const IXGBE_FDIR_DROP_QUEUE: u32 = 127;

/* Manageability Host Interface defines */
pub const IXGBE_HI_MAX_BLOCK_BYTE_LENGTH: u32 = 1792; /* Num of bytes in range */
pub const IXGBE_HI_MAX_BLOCK_DWORD_LENGTH: u32 = 448; /* Num of dwords in range */
pub const IXGBE_HI_COMMAND_TIMEOUT: u32 = 500; /* Process HI command limit */
pub const IXGBE_HI_FLASH_ERASE_TIMEOUT: u32 = 1000; /* Process Erase command limit */
pub const IXGBE_HI_FLASH_UPDATE_TIMEOUT: u32 = 5000; /* Process Update command limit */
pub const IXGBE_HI_FLASH_APPLY_TIMEOUT: u32 = 0; /* Process Apply command limit */
pub const IXGBE_HI_PHY_MGMT_REQ_TIMEOUT: u32 = 2000; /* Wait up to 2 seconds */

/* CEM Support */
pub const FW_CEM_HDR_LEN: u32 = 0x4;
pub const FW_CEM_CMD_DRIVER_INFO: u32 = 0xDD;
pub const FW_CEM_CMD_DRIVER_INFO_LEN: u32 = 0x5;
pub const FW_CEM_CMD_RESERVED: u32 = 0x0;
pub const FW_CEM_UNUSED_VER: u32 = 0x0;
pub const FW_CEM_MAX_RETRIES: u32 = 3;
pub const FW_CEM_RESP_STATUS_SUCCESS: u32 = 0x1;
pub const FW_CEM_DRIVER_VERSION_SIZE: usize = 39; /* +9 would send 48 bytes to fw */
pub const FW_READ_SHADOW_RAM_CMD: u8 = 0x31;
pub const FW_READ_SHADOW_RAM_LEN: u8 = 0x6;
pub const FW_WRITE_SHADOW_RAM_CMD: u32 = 0x33;
pub const FW_WRITE_SHADOW_RAM_LEN: u32 = 0xA; /* 8 plus 1 WORD to write */
pub const FW_SHADOW_RAM_DUMP_CMD: u32 = 0x36;
pub const FW_SHADOW_RAM_DUMP_LEN: u32 = 0;
pub const FW_DEFAULT_CHECKSUM: u8 = 0xFF; /* checksum always 0xFF */
pub const FW_NVM_DATA_OFFSET: usize = 3;
pub const FW_MAX_READ_BUFFER_SIZE: u16 = 1024;
pub const FW_DISABLE_RXEN_CMD: u8 = 0xDE;
pub const FW_DISABLE_RXEN_LEN: u8 = 0x1;
pub const FW_PHY_MGMT_REQ_CMD: u32 = 0x20;
pub const FW_PHY_TOKEN_REQ_CMD: u32 = 0xA;
pub const FW_PHY_TOKEN_REQ_LEN: u32 = 2;
pub const FW_PHY_TOKEN_REQ: u32 = 0;
pub const FW_PHY_TOKEN_REL: u32 = 1;
pub const FW_PHY_TOKEN_OK: u32 = 1;
pub const FW_PHY_TOKEN_RETRY: u32 = 0x80;
pub const FW_PHY_TOKEN_DELAY: u32 = 5; /* milliseconds */
pub const FW_PHY_TOKEN_WAIT: u32 = 5; /* seconds */
pub const FW_PHY_TOKEN_RETRIES: u32 = (FW_PHY_TOKEN_WAIT * 1000) / FW_PHY_TOKEN_DELAY;
pub const FW_INT_PHY_REQ_CMD: u32 = 0xB;
pub const FW_INT_PHY_REQ_LEN: u32 = 10;
pub const FW_INT_PHY_REQ_READ: u32 = 0;
pub const FW_INT_PHY_REQ_WRITE: u32 = 1;
pub const FW_PHY_ACT_REQ_CMD: u32 = 5;
pub const FW_PHY_ACT_DATA_COUNT: usize = 4;
pub const FW_PHY_ACT_REQ_LEN: usize = 4 + 4 * FW_PHY_ACT_DATA_COUNT;
pub const FW_PHY_ACT_INIT_PHY: u32 = 1;
pub const FW_PHY_ACT_SETUP_LINK: u32 = 2;
pub const FW_PHY_ACT_LINK_SPEED_10: u32 = 1 << 0;
pub const FW_PHY_ACT_LINK_SPEED_100: u32 = 1 << 1;
pub const FW_PHY_ACT_LINK_SPEED_1G: u32 = 1 << 2;
pub const FW_PHY_ACT_LINK_SPEED_2_5G: u32 = 1 << 3;
pub const FW_PHY_ACT_LINK_SPEED_5G: u32 = 1 << 4;
pub const FW_PHY_ACT_LINK_SPEED_10G: u32 = 1 << 5;
pub const FW_PHY_ACT_LINK_SPEED_20G: u32 = 1 << 6;
pub const FW_PHY_ACT_LINK_SPEED_25G: u32 = 1 << 7;
pub const FW_PHY_ACT_LINK_SPEED_40G: u32 = 1 << 8;
pub const FW_PHY_ACT_LINK_SPEED_50G: u32 = 1 << 9;
pub const FW_PHY_ACT_LINK_SPEED_100G: u32 = 1 << 10;
pub const FW_PHY_ACT_SETUP_LINK_PAUSE_SHIFT: u32 = 16;
pub const FW_PHY_ACT_SETUP_LINK_PAUSE_MASK: u32 = 3 << FW_PHY_ACT_SETUP_LINK_PAUSE_SHIFT;
pub const FW_PHY_ACT_SETUP_LINK_PAUSE_NONE: u32 = 0;
pub const FW_PHY_ACT_SETUP_LINK_PAUSE_TX: u32 = 1;
pub const FW_PHY_ACT_SETUP_LINK_PAUSE_RX: u32 = 2;
pub const FW_PHY_ACT_SETUP_LINK_PAUSE_RXTX: u32 = 3;
pub const FW_PHY_ACT_SETUP_LINK_LP: u32 = 1 << 18;
pub const FW_PHY_ACT_SETUP_LINK_HP: u32 = 1 << 19;
pub const FW_PHY_ACT_SETUP_LINK_EEE: u32 = 1 << 20;
pub const FW_PHY_ACT_SETUP_LINK_AN: u32 = 1 << 22;
pub const FW_PHY_ACT_SETUP_LINK_RSP_DOWN: u32 = 1 << 0;
pub const FW_PHY_ACT_GET_LINK_INFO: u32 = 3;
pub const FW_PHY_ACT_GET_LINK_INFO_EEE: u32 = 1 << 19;
pub const FW_PHY_ACT_GET_LINK_INFO_FC_TX: u32 = 1 << 20;
pub const FW_PHY_ACT_GET_LINK_INFO_FC_RX: u32 = 1 << 21;
pub const FW_PHY_ACT_GET_LINK_INFO_POWER: u32 = 1 << 22;
pub const FW_PHY_ACT_GET_LINK_INFO_AN_COMPLETE: u32 = 1 << 24;
pub const FW_PHY_ACT_GET_LINK_INFO_TEMP: u32 = 1 << 25;
pub const FW_PHY_ACT_GET_LINK_INFO_LP_FC_TX: u32 = 1 << 28;
pub const FW_PHY_ACT_GET_LINK_INFO_LP_FC_RX: u32 = 1 << 29;
pub const FW_PHY_ACT_FORCE_LINK_DOWN: u32 = 4;
pub const FW_PHY_ACT_FORCE_LINK_DOWN_OFF: u32 = 1 << 0;
pub const FW_PHY_ACT_PHY_SW_RESET: u32 = 5;
pub const FW_PHY_ACT_PHY_HW_RESET: u32 = 6;
pub const FW_PHY_ACT_GET_PHY_INFO: u32 = 7;
pub const FW_PHY_ACT_UD_2: u32 = 0x1002;
pub const FW_PHY_ACT_UD_2_10G_KR_EEE: u32 = 1 << 6;
pub const FW_PHY_ACT_UD_2_10G_KX4_EEE: u32 = 1 << 5;
pub const FW_PHY_ACT_UD_2_1G_KX_EEE: u32 = 1 << 4;
pub const FW_PHY_ACT_UD_2_10G_T_EEE: u32 = 1 << 3;
pub const FW_PHY_ACT_UD_2_1G_T_EEE: u32 = 1 << 2;
pub const FW_PHY_ACT_UD_2_100M_TX_EEE: u32 = 1 << 1;
pub const FW_PHY_ACT_RETRIES: u32 = 50;
pub const FW_PHY_INFO_SPEED_MASK: u32 = 0xFFF;
pub const FW_PHY_INFO_ID_HI_MASK: u32 = 0xFFFF0000;
pub const FW_PHY_INFO_ID_LO_MASK: u32 = 0x0000FFFF;

/* Adv Transmit Descriptor Config Masks */
pub const IXGBE_ADVTXD_DTALEN_MASK: u32 = 0x0000FFFF; /* Data buf length(bytes) */
pub const IXGBE_ADVTXD_MAC_LINKSEC: u32 = 0x00040000; /* Insert LinkSec */
pub const IXGBE_ADVTXD_MAC_TSTAMP: u32 = 0x00080000; /* IEEE1588 time stamp */
pub const IXGBE_ADVTXD_IPSEC_SA_INDEX_MASK: u32 = 0x000003FF; /* IPSec SA index */
pub const IXGBE_ADVTXD_IPSEC_ESP_LEN_MASK: u32 = 0x000001FF; /* IPSec ESP length */
pub const IXGBE_ADVTXD_DTYP_MASK: u32 = 0x00F00000; /* DTYP mask */
pub const IXGBE_ADVTXD_DTYP_CTXT: u32 = 0x00200000; /* Adv Context Desc */
pub const IXGBE_ADVTXD_DTYP_DATA: u32 = 0x00300000; /* Adv Data Descriptor */
pub const IXGBE_ADVTXD_DCMD_EOP: u32 = IXGBE_TXD_CMD_EOP; /* End of Packet */
pub const IXGBE_ADVTXD_DCMD_IFCS: u32 = IXGBE_TXD_CMD_IFCS; /* Insert FCS */
pub const IXGBE_ADVTXD_DCMD_RS: u32 = IXGBE_TXD_CMD_RS; /* Report Status */
pub const IXGBE_ADVTXD_DCMD_DDTYP_ISCSI: u32 = 0x10000000; /* DDP hdr type or iSCSI */
pub const IXGBE_ADVTXD_DCMD_DEXT: u32 = IXGBE_TXD_CMD_DEXT; /* Desc ext 1=Adv */
pub const IXGBE_ADVTXD_DCMD_VLE: u32 = IXGBE_TXD_CMD_VLE; /* VLAN pkt enable */
pub const IXGBE_ADVTXD_DCMD_TSE: u32 = 0x80000000; /* TCP Seg enable */
pub const IXGBE_ADVTXD_STAT_DD: u32 = IXGBE_TXD_STAT_DD; /* Descriptor Done */
pub const IXGBE_ADVTXD_STAT_SN_CRC: u32 = 0x00000002; /* NXTSEQ/SEED pres in WB */
pub const IXGBE_ADVTXD_STAT_RSV: u32 = 0x0000000C; /* STA Reserved */
pub const IXGBE_ADVTXD_IDX_SHIFT: u32 = 4; /* Adv desc Index shift */
pub const IXGBE_ADVTXD_CC: u32 = 0x00000080; /* Check Context */
pub const IXGBE_ADVTXD_POPTS_SHIFT: u32 = 8; /* Adv desc POPTS shift */
pub const IXGBE_ADVTXD_POPTS_IXSM: u32 = IXGBE_TXD_POPTS_IXSM << IXGBE_ADVTXD_POPTS_SHIFT;
pub const IXGBE_ADVTXD_POPTS_TXSM: u32 = IXGBE_TXD_POPTS_TXSM << IXGBE_ADVTXD_POPTS_SHIFT;
pub const IXGBE_ADVTXD_POPTS_ISCO_1ST: u32 = 0x00000000; /* 1st TSO of iSCSI PDU */
pub const IXGBE_ADVTXD_POPTS_ISCO_MDL: u32 = 0x00000800; /* Middle TSO of iSCSI PDU */
pub const IXGBE_ADVTXD_POPTS_ISCO_LAST: u32 = 0x00001000; /* Last TSO of iSCSI PDU */

/* 1st&Last TSO-full iSCSI PDU */
pub const IXGBE_ADVTXD_POPTS_ISCO_FULL: u32 = 0x00001800;
pub const IXGBE_ADVTXD_POPTS_RSV: u32 = 0x00002000; /* POPTS Reserved */
pub const IXGBE_ADVTXD_PAYLEN_MASK: u32 = 0x0003FFFF; /* Adv desc PAYLEN */
pub const IXGBE_ADVTXD_PAYLEN_SHIFT: u32 = 14; /* Adv desc PAYLEN shift */
pub const IXGBE_ADVTXD_MACLEN_SHIFT: u32 = 9; /* Adv ctxt desc mac len shift */
pub const IXGBE_ADVTXD_VLAN_SHIFT: u32 = 16; /* Adv ctxt vlan tag shift */
pub const IXGBE_ADVTXD_TUCMD_IPV4: u32 = 0x00000400; /* IP Packet Type: 1=IPv4 */
pub const IXGBE_ADVTXD_TUCMD_IPV6: u32 = 0x00000000; /* IP Packet Type: 0=IPv6 */
pub const IXGBE_ADVTXD_TUCMD_L4T_UDP: u32 = 0x00000000; /* L4 Packet TYPE of UDP */
pub const IXGBE_ADVTXD_TUCMD_L4T_TCP: u32 = 0x00000800; /* L4 Packet TYPE of TCP */
pub const IXGBE_ADVTXD_TUCMD_L4T_SCTP: u32 = 0x00001000; /* L4 Packet TYPE of SCTP */
pub const IXGBE_ADVTXD_TUCMD_L4T_RSV: u32 = 0x00001800; /* RSV L4 Packet TYPE */
pub const IXGBE_ADVTXD_TUCMD_MKRREQ: u32 = 0x00002000; /* req Markers and CRC */
pub const IXGBE_ADVTXD_POPTS_IPSEC: u32 = 0x00000400; /* IPSec offload request */
pub const IXGBE_ADVTXD_TUCMD_IPSEC_TYPE_ESP: u32 = 0x00002000; /* IPSec Type ESP */
pub const IXGBE_ADVTXD_TUCMD_IPSEC_ENCRYPT_EN: u32 = 0x00004000; /* ESP Encrypt Enable */
pub const IXGBE_ADVTXT_TUCMD_FCOE: u32 = 0x00008000; /* FCoE Frame Type */
pub const IXGBE_ADVTXD_FCOEF_EOF_MASK: u32 = 0x3 << 10; /* FC EOF index */
pub const IXGBE_ADVTXD_FCOEF_SOF: u32 = (1 << 2) << 10; /* FC SOF index */
pub const IXGBE_ADVTXD_FCOEF_PARINC: u32 = (1 << 3) << 10; /* Rel_Off in F_CTL */
pub const IXGBE_ADVTXD_FCOEF_ORIE: u32 = (1 << 4) << 10; /* Orientation End */
pub const IXGBE_ADVTXD_FCOEF_ORIS: u32 = (1 << 5) << 10; /* Orientation Start */
pub const IXGBE_ADVTXD_FCOEF_EOF_N: u32 = 0x0 << 10; /* 00: EOFn */
pub const IXGBE_ADVTXD_FCOEF_EOF_T: u32 = 0x1 << 10; /* 01: EOFt */
pub const IXGBE_ADVTXD_FCOEF_EOF_NI: u32 = 0x2 << 10; /* 10: EOFni */
pub const IXGBE_ADVTXD_FCOEF_EOF_A: u32 = 0x3 << 10; /* 11: EOFa */
pub const IXGBE_ADVTXD_L4LEN_SHIFT: u32 = 8; /* Adv ctxt L4LEN shift */
pub const IXGBE_ADVTXD_MSS_SHIFT: u32 = 16; /* Adv ctxt MSS shift */

pub const IXGBE_ADVTXD_OUTER_IPLEN: u32 = 16; /* Adv ctxt OUTERIPLEN shift */
pub const IXGBE_ADVTXD_TUNNEL_LEN: u32 = 24; /* Adv ctxt TUNNELLEN shift */
pub const IXGBE_ADVTXD_TUNNEL_TYPE_SHIFT: u32 = 16; /* Adv Tx Desc Tunnel Type shift */
pub const IXGBE_ADVTXD_OUTERIPCS_SHIFT: u32 = 17; /* Adv Tx Desc OUTERIPCS Shift */
pub const IXGBE_ADVTXD_TUNNEL_TYPE_NVGRE: u32 = 1; /* Adv Tx Desc Tunnel Type NVGRE */
/* Adv Tx Desc OUTERIPCS Shift for X550EM_a */
pub const IXGBE_ADVTXD_OUTERIPCS_SHIFT_X550EM_A: u32 = 26;

/* Autonegotiation advertised speeds */
pub type IxgbeAutonegAdvertised = u32;
/* Link speed */
pub const IXGBE_LINK_SPEED_UNKNOWN: u32 = 0;
pub const IXGBE_LINK_SPEED_10_FULL: u32 = 0x0002;
pub const IXGBE_LINK_SPEED_100_FULL: u32 = 0x0008;
pub const IXGBE_LINK_SPEED_1GB_FULL: u32 = 0x0020;
pub const IXGBE_LINK_SPEED_2_5GB_FULL: u32 = 0x0400;
pub const IXGBE_LINK_SPEED_5GB_FULL: u32 = 0x0800;
pub const IXGBE_LINK_SPEED_10GB_FULL: u32 = 0x0080;
//pub const IXGBE_LINK_SPEED_82598_AUTONEG: u32 =
//IXGBE_LINK_SPEED_1GB_FULL | IXGBE_LINK_SPEED_10GB_FULL;
//pub const IXGBE_LINK_SPEED_82599_AUTONEG: u32 =
//IXGBE_LINK_SPEED_100_FULL | IXGBE_LINK_SPEED_1GB_FULL | IXGBE_LINK_SPEED_10GB_FULL;

/* Physical layer type */
pub type IxgbePhysicalLayer = u64;
pub const IXGBE_PHYSICAL_LAYER_UNKNOWN: u64 = 0;
pub const IXGBE_PHYSICAL_LAYER_10GBASE_T: u64 = 0x00001;
pub const IXGBE_PHYSICAL_LAYER_1000BASE_T: u64 = 0x00002;
pub const IXGBE_PHYSICAL_LAYER_100BASE_TX: u64 = 0x00004;
pub const IXGBE_PHYSICAL_LAYER_SFP_PLUS_CU: u64 = 0x00008;
pub const IXGBE_PHYSICAL_LAYER_10GBASE_LR: u64 = 0x00010;
pub const IXGBE_PHYSICAL_LAYER_10GBASE_LRM: u64 = 0x00020;
pub const IXGBE_PHYSICAL_LAYER_10GBASE_SR: u64 = 0x00040;
pub const IXGBE_PHYSICAL_LAYER_10GBASE_KX4: u64 = 0x00080;
pub const IXGBE_PHYSICAL_LAYER_10GBASE_CX4: u64 = 0x00100;
pub const IXGBE_PHYSICAL_LAYER_1000BASE_KX: u64 = 0x00200;
pub const IXGBE_PHYSICAL_LAYER_1000BASE_BX: u64 = 0x00400;
pub const IXGBE_PHYSICAL_LAYER_10GBASE_KR: u64 = 0x00800;
pub const IXGBE_PHYSICAL_LAYER_10GBASE_XAUI: u64 = 0x01000;
pub const IXGBE_PHYSICAL_LAYER_SFP_ACTIVE_DA: u64 = 0x02000;
pub const IXGBE_PHYSICAL_LAYER_1000BASE_SX: u64 = 0x04000;
pub const IXGBE_PHYSICAL_LAYER_10BASE_T: u64 = 0x08000;
pub const IXGBE_PHYSICAL_LAYER_2500BASE_KX: u64 = 0x10000;
pub const IXGBE_PHYSICAL_LAYER_1000BASE_LX: u64 = 0x20000;

/* Flow Control Data Sheet defined values
 * Calculation and defines taken from 802.1bb Annex O
 */

/* BitTimes (BT) conversion */
#[allow(non_snake_case)]
pub const fn IXGBE_BT2KB(bt: u32) -> u32 {
    (bt + (8 * 1024 - 1)) / (8 * 1024)
}

#[allow(non_snake_case)]
pub const fn IXGBE_B2BT(bt: u32) -> u32 {
    bt * 8
}

/* Calculate Delay to respond to PFC */
pub const IXGBE_PFC_D: u32 = 672;

/* Calculate Cable Delay */
pub const IXGBE_CABLE_DC: u32 = 5556; /* Delay Copper */
pub const IXGBE_CABLE_DO: u32 = 5000; /* Delay Optical */

/* Calculate Interface Delay X540 */
pub const IXGBE_PHY_DC: u32 = 25600; /* Delay 10G BASET */
pub const IXGBE_MAC_DC: u32 = 8192; /* Delay Copper XAUI interface */
pub const IXGBE_XAUI_DC: u32 = 2 * 2048; /* Delay Copper Phy */

pub const IXGBE_ID_X540: u32 = IXGBE_MAC_DC + IXGBE_XAUI_DC + IXGBE_PHY_DC;

/* Calculate Interface Delay 82598, 82599 */
pub const IXGBE_PHY_D: u32 = 12800;
pub const IXGBE_MAC_D: u32 = 4096;
pub const IXGBE_XAUI_D: u32 = 2 * 1024;

pub const IXGBE_ID: u32 = IXGBE_MAC_D + IXGBE_XAUI_D + IXGBE_PHY_D;

/* Calculate Delay incurred from higher layer */
pub const IXGBE_HD: u32 = 6144;

/* Calculate PCI Bus delay for low thresholds */
pub const IXGBE_PCI_DELAY: u32 = 10000;

#[allow(non_snake_case)]
pub const fn IXGBE_DV_X540(max_frame_link: u32, max_frame_tc: u32) -> u32 {
    (36 * (IXGBE_B2BT(max_frame_link)
        + IXGBE_PFC_D
        + (2 * IXGBE_CABLE_DC)
        + (2 * IXGBE_ID_X540)
        + IXGBE_HD)
        / 25
        + 1)
        + 2 * IXGBE_B2BT(max_frame_tc)
}

#[allow(non_snake_case)]
pub const fn IXGBE_DV(max_frame_link: u32, max_frame_tc: u32) -> u32 {
    (36 * (IXGBE_B2BT(max_frame_link)
        + IXGBE_PFC_D
        + (2 * IXGBE_CABLE_DC)
        + (2 * IXGBE_ID)
        + IXGBE_HD)
        / 25
        + 1)
        + 2 * IXGBE_B2BT(max_frame_tc)
}

#[allow(non_snake_case)]
pub const fn IXGBE_LOW_DV_X540(max_frame_tc: u32) -> u32 {
    2 * IXGBE_B2BT(max_frame_tc) + (36 * IXGBE_PCI_DELAY / 25) + 1
}

#[allow(non_snake_case)]
pub const fn IXGBE_LOW_DV(max_frame_tc: u32) -> u32 {
    2 * IXGBE_LOW_DV_X540(max_frame_tc)
}

/* Software ATR hash keys */
pub const IXGBE_ATR_BUCKET_HASH_KEY: u32 = 0x3DAD14E2;
pub const IXGBE_ATR_SIGNATURE_HASH_KEY: u32 = 0x174D3614;

/* Software ATR input stream values and masks */
pub const IXGBE_ATR_HASH_MASK: u32 = 0x7fff;
pub const IXGBE_ATR_L4TYPE_MASK: u32 = 0x3;
pub const IXGBE_ATR_L4TYPE_UDP: u32 = 0x1;
pub const IXGBE_ATR_L4TYPE_TCP: u32 = 0x2;
pub const IXGBE_ATR_L4TYPE_SCTP: u32 = 0x3;
pub const IXGBE_ATR_L4TYPE_IPV6_MASK: u32 = 0x4;
pub const IXGBE_ATR_L4TYPE_TUNNEL_MASK: u32 = 0x10;

pub const IXGBE_VFMAILBOX_SIZE: u32 = 16; // 16 32 bit words - 64 bytes
pub const IXGBE_ERR_MBX: i32 = -100;

pub const IXGBE_VFMAILBOX: u32 = 0x002FC;
pub const IXGBE_VFMBMEM: u32 = 0x00200;

/* Define mailbox register bits */
pub const IXGBE_VFMAILBOX_REQ: u32 = 0x00000001; // Request for PF Ready bit
pub const IXGBE_VFMAILBOX_ACK: u32 = 0x00000002; // Ack PF message received
pub const IXGBE_VFMAILBOX_VFU: u32 = 0x00000004; // VF owns the mailbox buffer
pub const IXGBE_VFMAILBOX_PFU: u32 = 0x00000008; // PF owns the mailbox buffer
pub const IXGBE_VFMAILBOX_PFSTS: u32 = 0x00000010; // PF wrote a message in the MB
pub const IXGBE_VFMAILBOX_PFACK: u32 = 0x00000020; // PF ack the previous VF msg
pub const IXGBE_VFMAILBOX_RSTI: u32 = 0x00000040; // PF has reset indication
pub const IXGBE_VFMAILBOX_RSTD: u32 = 0x00000080; // PF has indicated reset done
pub const IXGBE_VFMAILBOX_R2C_BITS: u32 = 0x000000B0; // All read to clear bits

pub const IXGBE_PFMAILBOX_STS: u32 = 0x00000001; // Initiate message send to VF
pub const IXGBE_PFMAILBOX_ACK: u32 = 0x00000002; // Ack message recv'd from VF
pub const IXGBE_PFMAILBOX_VFU: u32 = 0x00000004; // VF owns the mailbox buffer
pub const IXGBE_PFMAILBOX_PFU: u32 = 0x00000008; // PF owns the mailbox buffer
pub const IXGBE_PFMAILBOX_RVFU: u32 = 0x00000010; // Reset VFU - used when VF stuck

pub const IXGBE_MBVFICR_VFREQ_MASK: u32 = 0x0000FFFF; // bits for VF messages
pub const IXGBE_MBVFICR_VFREQ_VF1: u32 = 0x00000001; // bit for VF 1 message
pub const IXGBE_MBVFICR_VFACK_MASK: u32 = 0xFFFF0000; // bits for VF acks
pub const IXGBE_MBVFICR_VFACK_VF1: u32 = 0x00010000; // bit for VF 1 ack

/* If it's a IXGBE_VF_* msg then it originates in the VF and is sent to the
 * PF. The reverse is TRUE if it is IXGBE_PF_*.
 * Message ACK's are the value or'd with 0xF0000000
 */
pub const IXGBE_VT_MSGTYPE_ACK: u32 = 0x80000000; // Messages below or'd with this are the ACK
pub const IXGBE_VT_MSGTYPE_NACK: u32 = 0x40000000; // Messages below or'd with this are the NACK
pub const IXGBE_VT_MSGTYPE_CTS: u32 = 0x20000000; // Indicates that VF is still clear to send requests
pub const IXGBE_VT_MSGINFO_SHIFT: u32 = 16;
/* bits 23:16 are used for extra info for certain messages */
pub const IXGBE_VT_MSGINFO_MASK: u32 = 0xFF << IXGBE_VT_MSGINFO_SHIFT;

/* mailbox API, legacy requests */
pub const IXGBE_VF_RESET: u32 = 0x01; // VF requests reset
pub const IXGBE_VF_SET_MAC_ADDR: u32 = 0x02; // VF requests PF to set MAC addr
pub const IXGBE_VF_SET_MULTICAST: u32 = 0x03; // VF requests PF to set MC addr
pub const IXGBE_VF_SET_VLAN: u32 = 0x04; // VF requests PF to set VLAN

/* mailbox API, version 1.0 VF requests */
pub const IXGBE_VF_SET_LPE: u32 = 0x05; // VF requests PF to set VMOLR.LPE
pub const IXGBE_VF_SET_MACVLAN: u32 = 0x06; // VF requests PF for unicast filter
pub const IXGBE_VF_API_NEGOTIATE: u32 = 0x08; // negotiate API version

/* mailbox API, version 1.1 VF requests */
pub const IXGBE_VF_GET_QUEUES: u32 = 0x09; // get queue configuration

/* mailbox API, version 1.2 VF requests */
pub const IXGBE_VF_GET_RETA: u32 = 0x0A; // VF request for RETA
pub const IXGBE_VF_GET_RSS_KEY: u32 = 0x0B; // get RSS key
pub const IXGBE_VF_UPDATE_XCAST_MODE: u32 = 0x0C;

/* GET_QUEUES return data indices within the mailbox */
pub const IXGBE_VF_TX_QUEUES: u32 = 1; // number of Tx queues supported
pub const IXGBE_VF_RX_QUEUES: u32 = 2; // number of Rx queues supported
pub const IXGBE_VF_TRANS_VLAN: u32 = 3; // Indication of port vlan
pub const IXGBE_VF_DEF_QUEUE: u32 = 4; // Default queue offset

/* length of permanent address message returned from PF */
pub const IXGBE_VF_PERMADDR_MSG_LEN: u32 = 4;
/* word in permanent address message with the current multicast type */
pub const IXGBE_VF_MC_TYPE_WORD: u32 = 3;

pub const IXGBE_PF_CONTROL_MSG: u32 = 0x0100; // PF control message

/* mailbox API, version 2.0 VF requests */
pub const IXGBE_VF_ENABLE_MACADDR: u32 = 0x0A; // enable MAC address
pub const IXGBE_VF_DISABLE_MACADDR: u32 = 0x0B; // disable MAC address
pub const IXGBE_VF_GET_MACADDRS: u32 = 0x0C; // get all configured MAC addrs
pub const IXGBE_VF_SET_MCAST_PROMISC: u32 = 0x0D; // enable multicast promiscuous
pub const IXGBE_VF_GET_MTU: u32 = 0x0E; // get bounds on MTU
pub const IXGBE_VF_SET_MTU: u32 = 0x0F; // set a specific MTU

/* mailbox API, version 2.0 PF requests */
pub const IXGBE_PF_TRANSPARENT_VLAN: u32 = 0x0101; // enable transparent vlan

pub const IXGBE_VF_MBX_INIT_TIMEOUT: u32 = 2000; // number of retries on mailbox
pub const IXGBE_VF_MBX_INIT_DELAY: u32 = 500; // microseconds between retries

pub const BYPASS_PAGE_CTL0: u32 = 0x00000000;
pub const BYPASS_PAGE_CTL1: u32 = 0x40000000;
pub const BYPASS_PAGE_CTL2: u32 = 0x80000000;
pub const BYPASS_PAGE_M: u32 = 0xc0000000;
pub const BYPASS_WE: u32 = 0x20000000;

pub const BYPASS_AUTO: u32 = 0x0;
pub const BYPASS_NOP: u32 = 0x0;
pub const BYPASS_NORM: u32 = 0x1;
pub const BYPASS_BYPASS: u32 = 0x2;
pub const BYPASS_ISOLATE: u32 = 0x3;

pub const BYPASS_EVENT_MAIN_ON: u32 = 0x1;
pub const BYPASS_EVENT_AUX_ON: u32 = 0x2;
pub const BYPASS_EVENT_MAIN_OFF: u32 = 0x3;
pub const BYPASS_EVENT_AUX_OFF: u32 = 0x4;
pub const BYPASS_EVENT_WDT_TO: u32 = 0x5;
pub const BYPASS_EVENT_USR: u32 = 0x6;

pub const BYPASS_MODE_OFF_M: u32 = 0x00000003;
pub const BYPASS_STATUS_OFF_M: u32 = 0x0000000c;
pub const BYPASS_AUX_ON_M: u32 = 0x00000030;
pub const BYPASS_MAIN_ON_M: u32 = 0x000000c0;
pub const BYPASS_MAIN_OFF_M: u32 = 0x00000300;
pub const BYPASS_AUX_OFF_M: u32 = 0x00000c00;
pub const BYPASS_WDTIMEOUT_M: u32 = 0x00003000;
pub const BYPASS_WDT_ENABLE_M: u32 = 0x00004000;
pub const BYPASS_WDT_VALUE_M: u32 = 0x00070000;

pub const BYPASS_MODE_OFF_SHIFT: u32 = 0;
pub const BYPASS_STATUS_OFF_SHIFT: u32 = 2;
pub const BYPASS_AUX_ON_SHIFT: u32 = 4;
pub const BYPASS_MAIN_ON_SHIFT: u32 = 6;
pub const BYPASS_MAIN_OFF_SHIFT: u32 = 8;
pub const BYPASS_AUX_OFF_SHIFT: u32 = 10;
pub const BYPASS_WDTIMEOUT_SHIFT: u32 = 12;
pub const BYPASS_WDT_ENABLE_SHIFT: u32 = 14;
pub const BYPASS_WDT_TIME_SHIFT: u32 = 16;

pub const BYPASS_WDT_1: u32 = 0x0;
pub const BYPASS_WDT_1_5: u32 = 0x1;
pub const BYPASS_WDT_2: u32 = 0x2;
pub const BYPASS_WDT_3: u32 = 0x3;
pub const BYPASS_WDT_4: u32 = 0x4;
pub const BYPASS_WDT_8: u32 = 0x5;
pub const BYPASS_WDT_16: u32 = 0x6;
pub const BYPASS_WDT_32: u32 = 0x7;
pub const BYPASS_WDT_OFF: u32 = 0xffff;

pub const BYPASS_CTL1_TIME_M: u32 = 0x01ffffff;
pub const BYPASS_CTL1_VALID_M: u32 = 0x02000000;
pub const BYPASS_CTL1_OFFTRST_M: u32 = 0x04000000;
pub const BYPASS_CTL1_WDT_PET_M: u32 = 0x08000000;

pub const BYPASS_CTL1_VALID: u32 = 0x02000000;
pub const BYPASS_CTL1_OFFTRST: u32 = 0x04000000;
pub const BYPASS_CTL1_WDT_PET: u32 = 0x08000000;

pub const BYPASS_CTL2_DATA_M: u32 = 0x000000ff;
pub const BYPASS_CTL2_OFFSET_M: u32 = 0x0000ff00;
pub const BYPASS_CTL2_RW_M: u32 = 0x00010000;
pub const BYPASS_CTL2_HEAD_M: u32 = 0x0ff00000;

pub const BYPASS_CTL2_OFFSET_SHIFT: u32 = 8;
pub const BYPASS_CTL2_HEAD_SHIFT: u32 = 20;

pub const BYPASS_CTL2_RW: u32 = 0x00010000;

pub const BYPASS_MAX_LOGS: u32 = 43;
pub const BYPASS_LOG_SIZE: u32 = 5;
pub const BYPASS_LOG_LINE_SIZE: u32 = 37;

pub const BYPASS_EEPROM_VER_ADD: u32 = 0x02;

pub const BYPASS_LOG_TIME_M: u32 = 0x01ffffff;
pub const BYPASS_LOG_TIME_VALID_M: u32 = 0x02000000;
pub const BYPASS_LOG_HEAD_M: u32 = 0x04000000;
pub const BYPASS_LOG_CLEAR_M: u32 = 0x08000000;
pub const BYPASS_LOG_EVENT_M: u32 = 0xf0000000;
pub const BYPASS_LOG_ACTION_M: u32 = 0x03;

pub const BYPASS_LOG_EVENT_SHIFT: u32 = 28;
pub const BYPASS_LOG_CLEAR_SHIFT: u32 = 24;

#[allow(non_snake_case)]
pub const fn IXGBE_FUSES0_GROUP(i: u32) -> u32 {
    0x11158 + (i * 4)
}
pub const IXGBE_FUSES0_300MHZ: u32 = 1 << 5;
pub const IXGBE_FUSES0_REV_MASK: u32 = 3 << 6;

#[allow(non_snake_case)]
pub const fn IXGBE_KRM_PORT_CAR_GEN_CTRL(p: bool) -> u32 {
    if p {
        0x8010
    } else {
        0x4010
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_LINK_S1(p: bool) -> u32 {
    if p {
        0x8200
    } else {
        0x4200
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_LINK_CTRL_1(p: bool) -> u32 {
    if p {
        0x820C
    } else {
        0x420C
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_AN_CNTL_1(p: bool) -> u32 {
    if p {
        0x822C
    } else {
        0x422C
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_AN_CNTL_4(p: bool) -> u32 {
    if p {
        0x8238
    } else {
        0x4238
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_AN_CNTL_8(p: bool) -> u32 {
    if p {
        0x8248
    } else {
        0x4248
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_PCS_KX_AN(p: bool) -> u32 {
    if p {
        0x9918
    } else {
        0x5918
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_PCS_KX_AN_LP(p: bool) -> u32 {
    if p {
        0x991C
    } else {
        0x591C
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_SGMII_CTRL(p: bool) -> u32 {
    if p {
        0x82A0
    } else {
        0x42A0
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_LP_BASE_PAGE_HIGH(p: bool) -> u32 {
    if p {
        0x836C
    } else {
        0x436C
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_DSP_TXFFE_STATE_4(p: bool) -> u32 {
    if p {
        0x8634
    } else {
        0x4634
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_DSP_TXFFE_STATE_5(p: bool) -> u32 {
    if p {
        0x8638
    } else {
        0x4638
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_RX_TRN_LINKUP_CTRL(p: bool) -> u32 {
    if p {
        0x8B00
    } else {
        0x4B00
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_PMD_DFX_BURNIN(p: bool) -> u32 {
    if p {
        0x8E00
    } else {
        0x4E00
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_PMD_FLX_MASK_ST20(p: bool) -> u32 {
    if p {
        0x9054
    } else {
        0x5054
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_TX_COEFF_CTRL_1(p: bool) -> u32 {
    if p {
        0x9520
    } else {
        0x5520
    }
}
#[allow(non_snake_case)]
pub const fn IXGBE_KRM_RX_ANA_CTL(p: bool) -> u32 {
    if p {
        0x9A00
    } else {
        0x5A00
    }
}

pub const IXGBE_KRM_PMD_FLX_MASK_ST20_SFI_10G_DA: u32 = !(0x3 << 20);
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_SFI_10G_SR: u32 = 1u32 << 20;
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_SFI_10G_LR: u32 = 0x2 << 20;
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_SGMII_EN: u32 = 1u32 << 25;
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_AN37_EN: u32 = 1u32 << 26;
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_AN_EN: u32 = 1u32 << 27;
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_SPEED_10M: u32 = !(0x7 << 28);
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_SPEED_100M: u32 = 1u32 << 28;
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_SPEED_1G: u32 = 0x2 << 28;
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_SPEED_10G: u32 = 0x3 << 28;
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_SPEED_AN: u32 = 0x4 << 28;
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_SPEED_2_5G: u32 = 0x7 << 28;
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_SPEED_MASK: u32 = 0x7 << 28;
pub const IXGBE_KRM_PMD_FLX_MASK_ST20_FW_AN_RESTART: u32 = 1u32 << 31;

pub const IXGBE_KRM_PORT_CAR_GEN_CTRL_NELB_32B: u32 = 1 << 9;
pub const IXGBE_KRM_PORT_CAR_GEN_CTRL_NELB_KRPCS: u32 = 1 << 11;

pub const IXGBE_KRM_LINK_CTRL_1_TETH_FORCE_SPEED_MASK: u32 = 0x7 << 8;
pub const IXGBE_KRM_LINK_CTRL_1_TETH_FORCE_SPEED_1G: u32 = 2 << 8;
pub const IXGBE_KRM_LINK_CTRL_1_TETH_FORCE_SPEED_10G: u32 = 4 << 8;
pub const IXGBE_KRM_LINK_CTRL_1_TETH_AN_SGMII_EN: u32 = 1 << 12;
pub const IXGBE_KRM_LINK_CTRL_1_TETH_AN_CLAUSE_37_EN: u32 = 1 << 13;
pub const IXGBE_KRM_LINK_CTRL_1_TETH_AN_FEC_REQ: u32 = 1 << 14;
pub const IXGBE_KRM_LINK_CTRL_1_TETH_AN_CAP_FEC: u32 = 1 << 15;
pub const IXGBE_KRM_LINK_CTRL_1_TETH_AN_CAP_KX: u32 = 1 << 16;
pub const IXGBE_KRM_LINK_CTRL_1_TETH_AN_CAP_KR: u32 = 1 << 18;
pub const IXGBE_KRM_LINK_CTRL_1_TETH_EEE_CAP_KX: u32 = 1 << 24;
pub const IXGBE_KRM_LINK_CTRL_1_TETH_EEE_CAP_KR: u32 = 1 << 26;
pub const IXGBE_KRM_LINK_S1_MAC_AN_COMPLETE: u32 = 1 << 28;
pub const IXGBE_KRM_LINK_CTRL_1_TETH_AN_ENABLE: u32 = 1 << 29;
pub const IXGBE_KRM_LINK_CTRL_1_TETH_AN_RESTART: u32 = 1u32 << 31;

pub const IXGBE_KRM_AN_CNTL_1_SYM_PAUSE: u32 = 1 << 28;
pub const IXGBE_KRM_AN_CNTL_1_ASM_PAUSE: u32 = 1 << 29;
pub const IXGBE_KRM_PCS_KX_AN_SYM_PAUSE: u32 = 1 << 1;
pub const IXGBE_KRM_PCS_KX_AN_ASM_PAUSE: u32 = 1 << 2;
pub const IXGBE_KRM_PCS_KX_AN_LP_SYM_PAUSE: u32 = 1 << 2;
pub const IXGBE_KRM_PCS_KX_AN_LP_ASM_PAUSE: u32 = 1 << 3;
pub const IXGBE_KRM_AN_CNTL_4_ECSR_AN37_OVER_73: u32 = 1 << 29;
pub const IXGBE_KRM_AN_CNTL_8_LINEAR: u32 = 1 << 0;
pub const IXGBE_KRM_AN_CNTL_8_LIMITING: u32 = 1 << 1;

pub const IXGBE_KRM_LP_BASE_PAGE_HIGH_SYM_PAUSE: u32 = 1 << 10;
pub const IXGBE_KRM_LP_BASE_PAGE_HIGH_ASM_PAUSE: u32 = 1 << 11;

pub const IXGBE_KRM_SGMII_CTRL_MAC_TAR_FORCE_100_D: u32 = 1 << 12;
pub const IXGBE_KRM_SGMII_CTRL_MAC_TAR_FORCE_10_D: u32 = 1 << 19;

pub const IXGBE_KRM_DSP_TXFFE_STATE_C0_EN: u32 = 1 << 6;
pub const IXGBE_KRM_DSP_TXFFE_STATE_CP1_CN1_EN: u32 = 1 << 15;
pub const IXGBE_KRM_DSP_TXFFE_STATE_CO_ADAPT_EN: u32 = 1 << 16;

pub const IXGBE_KRM_RX_TRN_LINKUP_CTRL_CONV_WO_PROTOCOL: u32 = 1 << 4;
pub const IXGBE_KRM_RX_TRN_LINKUP_CTRL_PROTOCOL_BYPASS: u32 = 1 << 2;

pub const IXGBE_KRM_PMD_DFX_BURNIN_TX_RX_KR_LB_MASK: u32 = 0x3 << 16;

pub const IXGBE_KRM_TX_COEFF_CTRL_1_CMINUS1_OVRRD_EN: u32 = 1 << 1;
pub const IXGBE_KRM_TX_COEFF_CTRL_1_CPLUS1_OVRRD_EN: u32 = 1 << 2;
pub const IXGBE_KRM_TX_COEFF_CTRL_1_CZERO_EN: u32 = 1 << 3;
pub const IXGBE_KRM_TX_COEFF_CTRL_1_OVRRD_EN: u32 = 1u32 << 31;

pub const IXGBE_SB_IOSF_INDIRECT_CTRL: u32 = 0x00011144;
pub const IXGBE_SB_IOSF_INDIRECT_DATA: u32 = 0x00011148;

pub const IXGBE_SB_IOSF_CTRL_ADDR_SHIFT: u32 = 0;
pub const IXGBE_SB_IOSF_CTRL_ADDR_MASK: u32 = 0xFF;
pub const IXGBE_SB_IOSF_CTRL_RESP_STAT_SHIFT: u32 = 18;
pub const IXGBE_SB_IOSF_CTRL_RESP_STAT_MASK: u32 = 0x3 << IXGBE_SB_IOSF_CTRL_RESP_STAT_SHIFT;
pub const IXGBE_SB_IOSF_CTRL_CMPL_ERR_SHIFT: u32 = 20;
pub const IXGBE_SB_IOSF_CTRL_CMPL_ERR_MASK: u32 = 0xFF << IXGBE_SB_IOSF_CTRL_CMPL_ERR_SHIFT;
pub const IXGBE_SB_IOSF_CTRL_TARGET_SELECT_SHIFT: u32 = 28;
pub const IXGBE_SB_IOSF_CTRL_TARGET_SELECT_MASK: u32 = 0x7;
pub const IXGBE_SB_IOSF_CTRL_BUSY_SHIFT: u32 = 31;
pub const IXGBE_SB_IOSF_CTRL_BUSY: u32 = 1 << IXGBE_SB_IOSF_CTRL_BUSY_SHIFT;
pub const IXGBE_SB_IOSF_TARGET_KR_PHY: u32 = 0;

pub const IXGBE_NW_MNG_IF_SEL: u32 = 0x00011178;
pub const IXGBE_NW_MNG_IF_SEL_MDIO_ACT: u32 = 1u32 << 1;
pub const IXGBE_NW_MNG_IF_SEL_MDIO_IF_MODE: u32 = 1u32 << 2;
pub const IXGBE_NW_MNG_IF_SEL_EN_SHARED_MDIO: u32 = 1u32 << 13;
pub const IXGBE_NW_MNG_IF_SEL_PHY_SPEED_10M: u32 = 1u32 << 17;
pub const IXGBE_NW_MNG_IF_SEL_PHY_SPEED_100M: u32 = 1u32 << 18;
pub const IXGBE_NW_MNG_IF_SEL_PHY_SPEED_1G: u32 = 1u32 << 19;
pub const IXGBE_NW_MNG_IF_SEL_PHY_SPEED_2_5G: u32 = 1u32 << 20;
pub const IXGBE_NW_MNG_IF_SEL_PHY_SPEED_10G: u32 = 1u32 << 21;
pub const IXGBE_NW_MNG_IF_SEL_SGMII_ENABLE: u32 = 1u32 << 25;
pub const IXGBE_NW_MNG_IF_SEL_INT_PHY_MODE: u32 = 1 << 24;
pub const IXGBE_NW_MNG_IF_SEL_MDIO_PHY_ADD_SHIFT: u32 = 3;
pub const IXGBE_NW_MNG_IF_SEL_MDIO_PHY_ADD: u32 = 0x1F << IXGBE_NW_MNG_IF_SEL_MDIO_PHY_ADD_SHIFT;

/* PHY */
pub const IXGBE_I2C_EEPROM_DEV_ADDR: u32 = 0xA0;
pub const IXGBE_I2C_EEPROM_DEV_ADDR2: u32 = 0xA2;
pub const IXGBE_I2C_EEPROM_BANK_LEN: u32 = 0xFF;

/* EEPROM byte offsets */
pub const IXGBE_SFF_IDENTIFIER: u32 = 0x0;
pub const IXGBE_SFF_IDENTIFIER_SFP: u32 = 0x3;
pub const IXGBE_SFF_VENDOR_OUI_BYTE0: u32 = 0x25;
pub const IXGBE_SFF_VENDOR_OUI_BYTE1: u32 = 0x26;
pub const IXGBE_SFF_VENDOR_OUI_BYTE2: u32 = 0x27;
pub const IXGBE_SFF_1GBE_COMP_CODES: u32 = 0x6;
pub const IXGBE_SFF_10GBE_COMP_CODES: u32 = 0x3;
pub const IXGBE_SFF_CABLE_TECHNOLOGY: u32 = 0x8;
pub const IXGBE_SFF_CABLE_SPEC_COMP: u32 = 0x3C;
pub const IXGBE_SFF_SFF_8472_SWAP: u32 = 0x5C;
pub const IXGBE_SFF_SFF_8472_COMP: u32 = 0x5E;
pub const IXGBE_SFF_SFF_8472_OSCB: u32 = 0x6E;
pub const IXGBE_SFF_SFF_8472_ESCB: u32 = 0x76;
pub const IXGBE_SFF_IDENTIFIER_QSFP_PLUS: u32 = 0xD;
pub const IXGBE_SFF_QSFP_VENDOR_OUI_BYTE0: u32 = 0xA5;
pub const IXGBE_SFF_QSFP_VENDOR_OUI_BYTE1: u32 = 0xA6;
pub const IXGBE_SFF_QSFP_VENDOR_OUI_BYTE2: u32 = 0xA7;
pub const IXGBE_SFF_QSFP_CONNECTOR: u32 = 0x82;
pub const IXGBE_SFF_QSFP_10GBE_COMP: u32 = 0x83;
pub const IXGBE_SFF_QSFP_1GBE_COMP: u32 = 0x86;
pub const IXGBE_SFF_QSFP_CABLE_LENGTH: u32 = 0x92;
pub const IXGBE_SFF_QSFP_DEVICE_TECH: u32 = 0x93;

/* Bitmasks */
pub const IXGBE_SFF_DA_PASSIVE_CABLE: u32 = 0x4;
pub const IXGBE_SFF_DA_ACTIVE_CABLE: u32 = 0x8;
pub const IXGBE_SFF_DA_SPEC_ACTIVE_LIMITING: u32 = 0x4;
pub const IXGBE_SFF_1GBASESX_CAPABLE: u32 = 0x1;
pub const IXGBE_SFF_1GBASELX_CAPABLE: u32 = 0x2;
pub const IXGBE_SFF_1GBASET_CAPABLE: u32 = 0x8;
pub const IXGBE_SFF_10GBASESR_CAPABLE: u32 = 0x10;
pub const IXGBE_SFF_10GBASELR_CAPABLE: u32 = 0x20;
pub const IXGBE_SFF_DA_BAD_HP_CABLE: u32 = 0x80;
pub const IXGBE_SFF_SOFT_RS_SELECT_MASK: u32 = 0x8;
pub const IXGBE_SFF_SOFT_RS_SELECT_10G: u32 = 0x8;
pub const IXGBE_SFF_SOFT_RS_SELECT_1G: u32 = 0x0;
pub const IXGBE_SFF_ADDRESSING_MODE: u32 = 0x4;
pub const IXGBE_SFF_QSFP_DA_ACTIVE_CABLE: u32 = 0x1;
pub const IXGBE_SFF_QSFP_DA_PASSIVE_CABLE: u32 = 0x8;
pub const IXGBE_SFF_QSFP_CONNECTOR_NOT_SEPARABLE: u32 = 0x23;
pub const IXGBE_SFF_QSFP_TRANSMITER_850NM_VCSEL: u32 = 0x0;
pub const IXGBE_I2C_EEPROM_READ_MASK: u32 = 0x100;
pub const IXGBE_I2C_EEPROM_STATUS_MASK: u32 = 0x3;
pub const IXGBE_I2C_EEPROM_STATUS_NO_OPERATION: u32 = 0x0;
pub const IXGBE_I2C_EEPROM_STATUS_PASS: u32 = 0x1;
pub const IXGBE_I2C_EEPROM_STATUS_FAIL: u32 = 0x2;
pub const IXGBE_I2C_EEPROM_STATUS_IN_PROGRESS: u32 = 0x3;

pub const IXGBE_CS4227: u32 = 0xBE; /* CS4227 address */
pub const IXGBE_CS4227_GLOBAL_ID_LSB: u32 = 0;
pub const IXGBE_CS4227_GLOBAL_ID_MSB: u32 = 1;
pub const IXGBE_CS4227_SCRATCH: u32 = 2;
pub const IXGBE_CS4227_GLOBAL_ID_VALUE: u32 = 0x03E5;
pub const IXGBE_CS4227_EFUSE_PDF_SKU: u32 = 0x19F;
pub const IXGBE_CS4223_SKU_ID: u32 = 0x0010; /* Quad port */
pub const IXGBE_CS4227_SKU_ID: u32 = 0x0014; /* Dual port */
pub const IXGBE_CS4227_RESET_PENDING: u32 = 0x1357;
pub const IXGBE_CS4227_RESET_COMPLETE: u32 = 0x5AA5;
pub const IXGBE_CS4227_RETRIES: u32 = 15;
pub const IXGBE_CS4227_EFUSE_STATUS: u32 = 0x0181;
pub const IXGBE_CS4227_LINE_SPARE22_MSB: u32 = 0x12AD; /* Reg to program speed */
pub const IXGBE_CS4227_LINE_SPARE24_LSB: u32 = 0x12B0; /* Reg to program EDC */
pub const IXGBE_CS4227_HOST_SPARE22_MSB: u32 = 0x1AAD; /* Reg to program speed */
pub const IXGBE_CS4227_HOST_SPARE24_LSB: u32 = 0x1AB0; /* Reg to program EDC */
pub const IXGBE_CS4227_EEPROM_STATUS: u32 = 0x5001;
pub const IXGBE_CS4227_EEPROM_LOAD_OK: u32 = 0x0001;
pub const IXGBE_CS4227_SPEED_1G: u32 = 0x8000;
pub const IXGBE_CS4227_SPEED_10G: u32 = 0;
pub const IXGBE_CS4227_EDC_MODE_CX1: u32 = 0x0002;
pub const IXGBE_CS4227_EDC_MODE_SR: u32 = 0x0004;
pub const IXGBE_CS4227_EDC_MODE_DIAG: u32 = 0x0008;
pub const IXGBE_CS4227_RESET_HOLD: u32 = 500; /* microseconds */
pub const IXGBE_CS4227_RESET_DELAY: u32 = 450; /* milliseconds */
pub const IXGBE_CS4227_CHECK_DELAY: u32 = 30; /* milliseconds */
pub const IXGBE_PE: u32 = 0xE0; /* Port expander address */
pub const IXGBE_PE_OUTPUT: u32 = 1; /* Output register offset */
pub const IXGBE_PE_CONFIG: u32 = 3; /* Config register offset */
pub const IXGBE_PE_BIT1: u32 = 1 << 1;

/* Flow control defines */
pub const IXGBE_TAF_SYM_PAUSE: u32 = 0x400;
pub const IXGBE_TAF_ASM_PAUSE: u32 = 0x800;

/* Bit-shift macros */
pub const IXGBE_SFF_VENDOR_OUI_BYTE0_SHIFT: u32 = 24;
pub const IXGBE_SFF_VENDOR_OUI_BYTE1_SHIFT: u32 = 16;
pub const IXGBE_SFF_VENDOR_OUI_BYTE2_SHIFT: u32 = 8;

/* Vendor OUIs: format of OUI is 0x[byte0][byte1][byte2][00] */
pub const IXGBE_SFF_VENDOR_OUI_TYCO: u32 = 0x00407600;
pub const IXGBE_SFF_VENDOR_OUI_FTL: u32 = 0x00906500;
pub const IXGBE_SFF_VENDOR_OUI_AVAGO: u32 = 0x00176A00;
pub const IXGBE_SFF_VENDOR_OUI_INTEL: u32 = 0x001B2100;

/* I2C SDA and SCL timing parameters for standard mode */
pub const IXGBE_I2C_T_HD_STA: u32 = 4;
pub const IXGBE_I2C_T_LOW: u32 = 5;
pub const IXGBE_I2C_T_HIGH: u32 = 4;
pub const IXGBE_I2C_T_SU_STA: u32 = 5;
pub const IXGBE_I2C_T_HD_DATA: u32 = 5;
pub const IXGBE_I2C_T_SU_DATA: u32 = 1;
pub const IXGBE_I2C_T_RISE: u32 = 1;
pub const IXGBE_I2C_T_FALL: u32 = 1;
pub const IXGBE_I2C_T_SU_STO: u32 = 4;
pub const IXGBE_I2C_T_BUF: u32 = 5;

pub const IXGBE_SFP_DETECT_RETRIES: u32 = 10;

pub const IXGBE_TN_LASI_STATUS_REG: u32 = 0x9005;
pub const IXGBE_TN_LASI_STATUS_TEMP_ALARM: u32 = 0x0008;

/* SFP+ SFF-8472 Compliance */
pub const IXGBE_SFF_SFF_8472_UNSUP: u32 = 0x00;

pub const IXGBE_FLAGS_DOUBLE_RESET_REQUIRED: u8 = 0x01;

#[repr(C, packed)]
pub struct IxgbeHicHdr {
    pub cmd: u8,
    pub buf_len: u8,
    pub cmd_or_resp: u8,
    pub checksum: u8,
}

#[repr(C, packed)]
#[derive(Clone, Copy)]
pub struct IxgbeHicHdr2Req {
    pub cmd: u8,
    pub buf_lenh: u8,
    pub buf_lenl: u8,
    pub checksum: u8,
}

#[repr(C, packed)]
#[derive(Clone, Copy)]
pub struct IxgbeHicHdr2Rsp {
    pub cmd: u8,
    pub buf_lenl: u8,
    pub buf_lenh_status: u8, // 7-5: high bits of buf_len, 4-0: status
    pub checksum: u8,
}

#[repr(C, packed)]
pub union IxgbeHicHdr2 {
    pub req: IxgbeHicHdr2Req,
    pub rsp: IxgbeHicHdr2Rsp,
}

#[repr(C, packed)]
struct IxgbeHicDrvInfo {
    hdr: IxgbeHicHdr,
    port_num: u8,
    ver_sub: u8,
    ver_build: u8,
    ver_min: u8,
    ver_maj: u8,
    pad: u8,   // end spacing to ensure length is mult. of dword
    pad2: u16, // end spacing to ensure length is mult. of dword2
}

#[repr(C, packed)]
struct IxgbeHicDrvInfo2 {
    hdr: IxgbeHicHdr,
    port_num: u8,
    ver_sub: u8,
    ver_build: u8,
    ver_min: u8,
    ver_maj: u8,
    driver_string: [u8; FW_CEM_DRIVER_VERSION_SIZE],
}

#[repr(C, packed)]
pub struct IxgbeHicReadShadowRam {
    pub hdr: IxgbeHicHdr2,
    pub address: u32,
    pub length: u16,
    pub pad2: u16,
    pub data: u16,
    pub pad3: u16,
}

#[repr(C, packed)]
pub struct IxgbeHicWriteShadowRam {
    hdr: IxgbeHicHdr2,
    address: u32,
    length: u16,
    pad2: u16,
    data: u16,
    pad3: u16,
}

#[repr(C, packed)]
pub struct IxgbeHicDisableRxen {
    pub hdr: IxgbeHicHdr,
    pub port_number: u8,
    pub pad2: u8,
    pub pad3: u16,
}

#[repr(C, packed)]
pub struct IxgbeHicPhyTokenReq {
    hdr: IxgbeHicHdr,
    port_number: u8,
    command_type: u8,
    pad: u16,
}

#[repr(C, packed)]
pub struct IxgbeHicInternalPhyReq {
    hdr: IxgbeHicHdr,
    port_number: u8,
    command_type: u8,
    address: u16, // __be16 in C, needs appropriate conversion when used
    rsv1: u16,
    write_data: u32, // __be32 in C, needs appropriate conversion when used
    pad: u16,
}

#[repr(C, packed)]
pub struct IxgbeHicInternalPhyResp {
    hdr: IxgbeHicHdr,
    read_data: u32, // __be32 in C, needs appropriate conversion when used
}

#[repr(C, packed)]
pub struct IxgbeHicPhyActivityReq {
    hdr: IxgbeHicHdr,
    port_number: u8,
    pad: u8,
    activity_id: u16, // __le16 in C, needs appropriate conversion when used
    data: [u32; FW_PHY_ACT_DATA_COUNT], // __be32 in C, needs appropriate conversion when used
}

#[repr(C, packed)]
struct IxgbeHicPhyActivityResp {
    hdr: IxgbeHicHdr,
    data: [u32; FW_PHY_ACT_DATA_COUNT], // __be32 in C, needs appropriate conversion when used
}

pub fn get_i2c_clk_in_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let i2c_clk_in = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_I2C_CLK_IN,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_I2C_CLK_IN_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_I2C_CLK_IN_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_I2C_CLK_IN_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_I2C_CLK_IN_X550EM_A,
    };

    Ok(i2c_clk_in)
}

pub fn get_i2c_clk_out_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let i2c_clk_out = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_I2C_CLK_OUT,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_I2C_CLK_OUT_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_I2C_CLK_OUT_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_I2C_CLK_OUT_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_I2C_CLK_OUT_X550EM_A,
    };

    Ok(i2c_clk_out)
}

pub fn get_i2c_data_in_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let i2c_data_in = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_I2C_DATA_IN,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_I2C_DATA_IN_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_I2C_DATA_IN_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_I2C_DATA_IN_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_I2C_DATA_IN_X550EM_A,
    };

    Ok(i2c_data_in)
}

pub fn get_i2c_data_out_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let i2c_data_out = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_I2C_DATA_OUT,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_I2C_DATA_OUT_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_I2C_DATA_OUT_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_I2C_DATA_OUT_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_I2C_DATA_OUT_X550EM_A,
    };

    Ok(i2c_data_out)
}

pub fn get_i2c_data_oe_n_en_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let i2c_data_oe_n_en = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_I2C_DATA_OE_N_EN,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_I2C_DATA_OE_N_EN_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_I2C_DATA_OE_N_EN_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_I2C_DATA_OE_N_EN_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_I2C_DATA_OE_N_EN_X550EM_A,
    };

    Ok(i2c_data_oe_n_en)
}

pub fn get_i2c_bb_en_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let i2c_bb_en = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_I2C_BB_EN,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_I2C_BB_EN_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_I2C_BB_EN_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_I2C_BB_EN_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_I2C_BB_EN_X550EM_A,
    };

    Ok(i2c_bb_en)
}

pub fn get_i2c_clk_oe_n_en_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let i2c_clk_oe_n_en = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_I2C_CLK_OE_N_EN,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_I2C_CLK_OE_N_EN_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_I2C_CLK_OE_N_EN_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_I2C_CLK_OE_N_EN_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_I2C_CLK_OE_N_EN_X550EM_A,
    };

    Ok(i2c_clk_oe_n_en)
}

pub fn get_i2cctl_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let i2cctl = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_I2CCTL_82599,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_I2CCTL_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_I2CCTL_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_I2CCTL_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_I2CCTL_X550EM_A,
    };

    Ok(i2cctl)
}

pub fn get_eec_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let eec = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_EEC,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_EEC_X540,
        IxgbeMacX550 | IxgbeMacX550Vf | IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_EEC_X550,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_EEC_X550EM_A,
    };

    Ok(eec)
}

pub fn get_fla_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let fla = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_FLA,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_FLA_X540,
        IxgbeMacX550 | IxgbeMacX550Vf | IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_FLA_X540,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_FLA_X550EM_A,
    };

    Ok(fla)
}

pub fn get_grc_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let grc = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_GRC,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_GRC_X540,
        IxgbeMacX550 | IxgbeMacX550Vf | IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_GRC_X550,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_GRC_X550EM_A,
    };

    Ok(grc)
}

pub fn get_sramrel_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let sramrel = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_SRAMREL,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_SRAMREL_X540,
        IxgbeMacX550 | IxgbeMacX550Vf | IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_SRAMREL_X550,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_SRAMREL_X550EM_A,
    };

    Ok(sramrel)
}

pub fn get_factps_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let factps = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_FACTPS,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_FACTPS_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_FACTPS_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_FACTPS_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_FACTPS_X550EM_A,
    };

    Ok(factps)
}

pub fn get_swsm_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let swsm = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_SWSM,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_SWSM_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_SWSM_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_SWSM_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_SWSM_X550EM_A,
    };

    Ok(swsm)
}

pub fn get_fwsm_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let fwsm = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_FWSM,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_FWSM_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_FWSM_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_FWSM_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_FWSM_X550EM_A,
    };

    Ok(fwsm)
}

pub fn get_swfw_sync_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let swfw_sync = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_SWFW_SYNC,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_SWFW_SYNC_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_SWFW_SYNC_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_SWFW_SYNC_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_SWFW_SYNC_X550EM_A,
    };

    Ok(swfw_sync)
}

pub fn get_ciaa_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let ciaa = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_CIAA_82599,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_CIAA_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_CIAA_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_CIAA_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_CIAA_X550EM_A,
    };

    Ok(ciaa)
}

pub fn get_ciad_offset(device: u16) -> Result<usize, IxgbeDriverErr> {
    use MacType::*;

    let ciad = match get_mac_type(device)? {
        IxgbeMac82598EB | IxgbeMac82599EB | IxgbeMac82599Vf => IXGBE_CIAD_82599,
        IxgbeMacX540 | IxgbeMacX540Vf => IXGBE_CIAD_X540,
        IxgbeMacX550 | IxgbeMacX550Vf => IXGBE_CIAD_X550,
        IxgbeMacX550EMX | IxgbeMacX550EMXVf => IXGBE_CIAD_X550EM_X,
        IxgbeMacX550EMA | IxgbeMacX550EMAVf => IXGBE_CIAD_X550EM_A,
    };

    Ok(ciad)
}
