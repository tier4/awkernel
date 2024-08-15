use awkernel_lib::{
    addr::{virt_addr::VirtAddr, Addr},
    net::ether::{ETHER_CRC_LEN, ETHER_MAX_LEN, ETHER_MIN_LEN, MAX_JUMBO_FRAME_SIZE},
};
use bitflags::bitflags;

use crate::pcie::{pcie_id::INTEL_VENDOR_ID, BaseAddress, PCIeInfo};

use super::{igb_regs::*, IgbDriverErr};

const E1000_DEV_ID_82543GC_FIBER: u16 = 0x1001;
const E1000_DEV_ID_82542: u16 = 0x1000;
const E1000_DEV_ID_82543GC_COPPER: u16 = 0x1004;
const E1000_DEV_ID_82544EI_COPPER: u16 = 0x1008;
const E1000_DEV_ID_82544EI_FIBER: u16 = 0x1009;
const E1000_DEV_ID_82544GC_COPPER: u16 = 0x100C;
const E1000_DEV_ID_82544GC_LOM: u16 = 0x100D;
const E1000_DEV_ID_82540EM: u16 = 0x100E; // e1000
const E1000_DEV_ID_82540EM_LOM: u16 = 0x1015;
const E1000_DEV_ID_82540EP_LOM: u16 = 0x1016;
const E1000_DEV_ID_82540EP: u16 = 0x1017;
const E1000_DEV_ID_82540EP_LP: u16 = 0x101E;
const E1000_DEV_ID_82545EM_COPPER: u16 = 0x100F;
const E1000_DEV_ID_82545EM_FIBER: u16 = 0x1011;
const E1000_DEV_ID_82545GM_COPPER: u16 = 0x1026;
const E1000_DEV_ID_82545GM_FIBER: u16 = 0x1027;
const E1000_DEV_ID_82545GM_SERDES: u16 = 0x1028;
const E1000_DEV_ID_82546EB_COPPER: u16 = 0x1010;
const E1000_DEV_ID_82546EB_FIBER: u16 = 0x1012;
const E1000_DEV_ID_82546EB_QUAD_COPPER: u16 = 0x101D;
const E1000_DEV_ID_82541EI: u16 = 0x1013;
const E1000_DEV_ID_82541EI_MOBILE: u16 = 0x1018;
const E1000_DEV_ID_82541ER_LOM: u16 = 0x1014;
const E1000_DEV_ID_82541ER: u16 = 0x1078;
const E1000_DEV_ID_82547GI: u16 = 0x1075;
const E1000_DEV_ID_82541GI: u16 = 0x1076;
const E1000_DEV_ID_82541GI_MOBILE: u16 = 0x1077;
const E1000_DEV_ID_82541GI_LF: u16 = 0x107C;
const E1000_DEV_ID_82546GB_COPPER: u16 = 0x1079;
const E1000_DEV_ID_82546GB_FIBER: u16 = 0x107A;
const E1000_DEV_ID_82546GB_SERDES: u16 = 0x107B;
const E1000_DEV_ID_82546GB_PCIE: u16 = 0x108A;
const E1000_DEV_ID_82546GB_QUAD_COPPER: u16 = 0x1099;
const E1000_DEV_ID_82547EI: u16 = 0x1019;
const E1000_DEV_ID_82547EI_MOBILE: u16 = 0x101A;
const E1000_DEV_ID_82571EB_COPPER: u16 = 0x105E;
const E1000_DEV_ID_82571EB_FIBER: u16 = 0x105F;
const E1000_DEV_ID_82571EB_SERDES: u16 = 0x1060;
const E1000_DEV_ID_82571EB_SERDES_DUAL: u16 = 0x10D9;
const E1000_DEV_ID_82571EB_SERDES_QUAD: u16 = 0x10DA;
const E1000_DEV_ID_82571EB_QUAD_COPPER: u16 = 0x10A4;
const E1000_DEV_ID_82571EB_QUAD_FIBER: u16 = 0x10A5;
const E1000_DEV_ID_82571EB_QUAD_COPPER_LP: u16 = 0x10BC;
const E1000_DEV_ID_82571PT_QUAD_COPPER: u16 = 0x10D5;
const E1000_DEV_ID_82572EI_COPPER: u16 = 0x107D;
const E1000_DEV_ID_82572EI_FIBER: u16 = 0x107E;
const E1000_DEV_ID_82572EI_SERDES: u16 = 0x107F;
const E1000_DEV_ID_82572EI: u16 = 0x10B9;
const E1000_DEV_ID_82573E: u16 = 0x108B;
const E1000_DEV_ID_82573E_IAMT: u16 = 0x108C;
const E1000_DEV_ID_82573L: u16 = 0x109A;
const E1000_DEV_ID_82574L: u16 = 0x10D3; // e1000e
const E1000_DEV_ID_82574LA: u16 = 0x10F6;
const E1000_DEV_ID_82546GB_2: u16 = 0x109B;
const E1000_DEV_ID_82571EB_AT: u16 = 0x10A0;
const E1000_DEV_ID_82571EB_AF: u16 = 0x10A1;
const E1000_DEV_ID_82573L_PL_1: u16 = 0x10B0;
const E1000_DEV_ID_82573V_PM: u16 = 0x10B2;
const E1000_DEV_ID_82573E_PM: u16 = 0x10B3;
const E1000_DEV_ID_82573L_PL_2: u16 = 0x10B4;
const E1000_DEV_ID_82546GB_QUAD_COPPER_KSP3: u16 = 0x10B5;
const E1000_DEV_ID_80003ES2LAN_COPPER_DPT: u16 = 0x1096;
const E1000_DEV_ID_80003ES2LAN_SERDES_DPT: u16 = 0x1098;
const E1000_DEV_ID_80003ES2LAN_COPPER_SPT: u16 = 0x10BA;
const E1000_DEV_ID_80003ES2LAN_SERDES_SPT: u16 = 0x10BB;
const E1000_DEV_ID_ICH8_82567V_3: u16 = 0x1501;
const E1000_DEV_ID_ICH8_IGP_M_AMT: u16 = 0x1049;
const E1000_DEV_ID_ICH8_IGP_AMT: u16 = 0x104A;
const E1000_DEV_ID_ICH8_IGP_C: u16 = 0x104B;
const E1000_DEV_ID_ICH8_IFE: u16 = 0x104C;
const E1000_DEV_ID_ICH8_IFE_GT: u16 = 0x10C4;
const E1000_DEV_ID_ICH8_IFE_G: u16 = 0x10C5;
const E1000_DEV_ID_ICH8_IGP_M: u16 = 0x104D;
const E1000_DEV_ID_ICH9_IGP_M: u16 = 0x10BF;
const E1000_DEV_ID_ICH9_IGP_M_AMT: u16 = 0x10F5;
const E1000_DEV_ID_ICH9_IGP_M_V: u16 = 0x10CB;
const E1000_DEV_ID_ICH9_IGP_AMT: u16 = 0x10BD;
const E1000_DEV_ID_ICH9_BM: u16 = 0x10E5;
const E1000_DEV_ID_ICH9_IGP_C: u16 = 0x294C;
const E1000_DEV_ID_ICH9_IFE: u16 = 0x10C0;
const E1000_DEV_ID_ICH9_IFE_GT: u16 = 0x10C3;
const E1000_DEV_ID_ICH9_IFE_G: u16 = 0x10C2;
const E1000_DEV_ID_ICH10_R_BM_LM: u16 = 0x10CC;
const E1000_DEV_ID_ICH10_R_BM_LF: u16 = 0x10CD;
const E1000_DEV_ID_ICH10_R_BM_V: u16 = 0x10CE;
const E1000_DEV_ID_ICH10_D_BM_LM: u16 = 0x10DE;
const E1000_DEV_ID_ICH10_D_BM_LF: u16 = 0x10DF;
const E1000_DEV_ID_ICH10_D_BM_V: u16 = 0x1525;
const E1000_DEV_ID_PCH_M_HV_LM: u16 = 0x10EA;
const E1000_DEV_ID_PCH_M_HV_LC: u16 = 0x10EB;
const E1000_DEV_ID_PCH_D_HV_DM: u16 = 0x10EF;
const E1000_DEV_ID_PCH_D_HV_DC: u16 = 0x10F0;
const E1000_DEV_ID_PCH_LPT_I217_LM: u16 = 0x153A;
const E1000_DEV_ID_PCH_LPT_I217_V: u16 = 0x153B;
const E1000_DEV_ID_PCH_LPTLP_I218_LM: u16 = 0x155A;
const E1000_DEV_ID_PCH_LPTLP_I218_V: u16 = 0x1559;
const E1000_DEV_ID_PCH_I218_LM2: u16 = 0x15A0;
const E1000_DEV_ID_PCH_I218_V2: u16 = 0x15A1;
const E1000_DEV_ID_PCH_I218_LM3: u16 = 0x15A2;
const E1000_DEV_ID_PCH_I218_V3: u16 = 0x15A3;
const E1000_DEV_ID_PCH_SPT_I219_LM: u16 = 0x156F;
const E1000_DEV_ID_PCH_SPT_I219_V: u16 = 0x1570;
const E1000_DEV_ID_PCH_SPT_I219_LM2: u16 = 0x15B7;
const E1000_DEV_ID_PCH_SPT_I219_V2: u16 = 0x15B8;
const E1000_DEV_ID_PCH_LBG_I219_LM3: u16 = 0x15B9;
const E1000_DEV_ID_PCH_SPT_I219_LM4: u16 = 0x15D7;
const E1000_DEV_ID_PCH_SPT_I219_V4: u16 = 0x15D8;
const E1000_DEV_ID_PCH_SPT_I219_LM5: u16 = 0x15E3;
const E1000_DEV_ID_PCH_SPT_I219_V5: u16 = 0x15D6;
const E1000_DEV_ID_PCH_CNP_I219_LM6: u16 = 0x15BD;
const E1000_DEV_ID_PCH_CNP_I219_V6: u16 = 0x15BE;
const E1000_DEV_ID_PCH_CNP_I219_LM7: u16 = 0x15BB;
const E1000_DEV_ID_PCH_CNP_I219_V7: u16 = 0x15BC;
const E1000_DEV_ID_PCH_ICP_I219_LM8: u16 = 0x15DF;
const E1000_DEV_ID_PCH_ICP_I219_V8: u16 = 0x15E0;
const E1000_DEV_ID_PCH_ICP_I219_LM9: u16 = 0x15E1;
const E1000_DEV_ID_PCH_ICP_I219_V9: u16 = 0x15E2;
const E1000_DEV_ID_PCH_CMP_I219_LM10: u16 = 0x0D4E;
const E1000_DEV_ID_PCH_CMP_I219_V10: u16 = 0x0D4F;
const E1000_DEV_ID_PCH_CMP_I219_LM11: u16 = 0x0D4C;
const E1000_DEV_ID_PCH_CMP_I219_V11: u16 = 0x0D4D;
const E1000_DEV_ID_PCH_CMP_I219_LM12: u16 = 0x0D53;
const E1000_DEV_ID_PCH_CMP_I219_V12: u16 = 0x0D55;
const E1000_DEV_ID_PCH_TGP_I219_LM13: u16 = 0x15FB;
const E1000_DEV_ID_PCH_TGP_I219_V13: u16 = 0x15FC;
const E1000_DEV_ID_PCH_TGP_I219_LM14: u16 = 0x15F9;
const E1000_DEV_ID_PCH_TGP_I219_V14: u16 = 0x15FA;
const E1000_DEV_ID_PCH_TGP_I219_LM15: u16 = 0x15F4;
const E1000_DEV_ID_PCH_TGP_I219_V15: u16 = 0x15F5;
const E1000_DEV_ID_PCH_ADP_I219_LM16: u16 = 0x1A1E;
const E1000_DEV_ID_PCH_ADP_I219_V16: u16 = 0x1A1F;
const E1000_DEV_ID_PCH_ADP_I219_LM17: u16 = 0x1A1C;
const E1000_DEV_ID_PCH_ADP_I219_V17: u16 = 0x1A1D;
const E1000_DEV_ID_PCH_MTP_I219_LM18: u16 = 0x550A;
const E1000_DEV_ID_PCH_MTP_I219_V18: u16 = 0x550B;
const E1000_DEV_ID_PCH_MTP_I219_LM19: u16 = 0x550C;
const E1000_DEV_ID_PCH_MTP_I219_V19: u16 = 0x550D;
const E1000_DEV_ID_82575EB_PT: u16 = 0x10A7;
const E1000_DEV_ID_82575EB_PF: u16 = 0x10A9;
const E1000_DEV_ID_82575GB_QP: u16 = 0x10D6;
const E1000_DEV_ID_82575GB_QP_PM: u16 = 0x10E2;
const E1000_DEV_ID_82576: u16 = 0x10C9;
const E1000_DEV_ID_82576_FIBER: u16 = 0x10E6;
const E1000_DEV_ID_82576_SERDES: u16 = 0x10E7;
const E1000_DEV_ID_82576_QUAD_COPPER: u16 = 0x10E8;
const E1000_DEV_ID_82576_NS: u16 = 0x150A;
const E1000_DEV_ID_82583V: u16 = 0x150C;
const E1000_DEV_ID_82576_NS_SERDES: u16 = 0x1518;
const E1000_DEV_ID_82576_SERDES_QUAD: u16 = 0x150D;
const E1000_DEV_ID_PCH2_LV_LM: u16 = 0x1502;
const E1000_DEV_ID_PCH2_LV_V: u16 = 0x1503;
const E1000_DEV_ID_82580_COPPER: u16 = 0x150E;
const E1000_DEV_ID_82580_FIBER: u16 = 0x150F;
const E1000_DEV_ID_82580_SERDES: u16 = 0x1510;
const E1000_DEV_ID_82580_SGMII: u16 = 0x1511;
const E1000_DEV_ID_82580_COPPER_DUAL: u16 = 0x1516;
const E1000_DEV_ID_82580_QUAD_FIBER: u16 = 0x1527;
const E1000_DEV_ID_DH89XXCC_SGMII: u16 = 0x0438;
const E1000_DEV_ID_DH89XXCC_SERDES: u16 = 0x043A;
const E1000_DEV_ID_DH89XXCC_BACKPLANE: u16 = 0x043C;
const E1000_DEV_ID_DH89XXCC_SFP: u16 = 0x0440;
const E1000_DEV_ID_I350_COPPER: u16 = 0x1521;
const E1000_DEV_ID_I350_FIBER: u16 = 0x1522;
const E1000_DEV_ID_I350_SERDES: u16 = 0x1523;
const E1000_DEV_ID_I350_SGMII: u16 = 0x1524;
const E1000_DEV_ID_82576_QUAD_CU_ET2: u16 = 0x1526;
const E1000_DEV_ID_I210_COPPER: u16 = 0x1533;
const E1000_DEV_ID_I210_COPPER_OEM1: u16 = 0x1534;
const E1000_DEV_ID_I210_COPPER_IT: u16 = 0x1535;
const E1000_DEV_ID_I210_FIBER: u16 = 0x1536;
const E1000_DEV_ID_I210_SERDES: u16 = 0x1537;
const E1000_DEV_ID_I210_SGMII: u16 = 0x1538;
const E1000_DEV_ID_I210_COPPER_FLASHLESS: u16 = 0x157B;
const E1000_DEV_ID_I210_SERDES_FLASHLESS: u16 = 0x157C;
const E1000_DEV_ID_I211_COPPER: u16 = 0x1539;
const E1000_DEV_ID_I350_DA4: u16 = 0x1546;
const E1000_DEV_ID_I354_BACKPLANE_1GBPS: u16 = 0x1F40;
const E1000_DEV_ID_I354_SGMII: u16 = 0x1F41;
const E1000_DEV_ID_I354_BACKPLANE_2_5GBPS: u16 = 0x1F45;
const E1000_DEV_ID_EP80579_LAN_1: u16 = 0x5040;
const E1000_DEV_ID_EP80579_LAN_2: u16 = 0x5044;
const E1000_DEV_ID_EP80579_LAN_3: u16 = 0x5048;
const E1000_DEV_ID_EP80579_LAN_4: u16 = 0x5041;
const E1000_DEV_ID_EP80579_LAN_5: u16 = 0x5045;
const E1000_DEV_ID_EP80579_LAN_6: u16 = 0x5049;

const E1000_82542_2_0_REV_ID: u8 = 2;
const E1000_82542_2_1_REV_ID: u8 = 3;

pub const E1000_DEVICES: [(u16, u16); 185] = [
    (INTEL_VENDOR_ID, E1000_DEV_ID_82543GC_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82542),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82543GC_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82544EI_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82544EI_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82544GC_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82544GC_LOM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82540EM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82540EM_LOM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82540EP_LOM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82540EP),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82540EP_LP),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82545EM_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82545EM_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82545GM_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82545GM_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82545GM_SERDES),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82546EB_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82546EB_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82546EB_QUAD_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82541EI),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82541EI_MOBILE),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82541ER_LOM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82541ER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82547GI),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82541GI),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82541GI_MOBILE),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82541GI_LF),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82546GB_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82546GB_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82546GB_SERDES),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82546GB_PCIE),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82546GB_QUAD_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82547EI),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82547EI_MOBILE),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82571EB_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82571EB_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82571EB_SERDES),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82571EB_SERDES_DUAL),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82571EB_SERDES_QUAD),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82571EB_QUAD_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82571EB_QUAD_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82571EB_QUAD_COPPER_LP),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82571PT_QUAD_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82572EI_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82572EI_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82572EI_SERDES),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82572EI),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82573E),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82573E_IAMT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82573L),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82574L),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82574LA),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82546GB_2),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82571EB_AT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82571EB_AF),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82573L_PL_1),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82573V_PM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82573E_PM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82573L_PL_2),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82546GB_QUAD_COPPER_KSP3),
    (INTEL_VENDOR_ID, E1000_DEV_ID_80003ES2LAN_COPPER_DPT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_80003ES2LAN_SERDES_DPT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_80003ES2LAN_COPPER_SPT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_80003ES2LAN_SERDES_SPT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH8_82567V_3),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH8_IGP_M_AMT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH8_IGP_AMT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH8_IGP_C),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH8_IFE),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH8_IFE_GT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH8_IFE_G),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH8_IGP_M),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH9_IGP_M),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH9_IGP_M_AMT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH9_IGP_M_V),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH9_IGP_AMT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH9_BM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH9_IGP_C),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH9_IFE),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH9_IFE_GT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH9_IFE_G),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH10_R_BM_LM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH10_R_BM_LF),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH10_R_BM_V),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH10_D_BM_LM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH10_D_BM_LF),
    (INTEL_VENDOR_ID, E1000_DEV_ID_ICH10_D_BM_V),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_M_HV_LM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_M_HV_LC),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_D_HV_DM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_D_HV_DC),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_LPT_I217_LM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_LPT_I217_V),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_LPTLP_I218_LM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_LPTLP_I218_V),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_I218_LM2),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_I218_V2),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_I218_LM3),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_I218_V3),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_SPT_I219_LM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_SPT_I219_V),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_SPT_I219_LM2),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_SPT_I219_V2),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_LBG_I219_LM3),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_SPT_I219_LM4),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_SPT_I219_V4),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_SPT_I219_LM5),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_SPT_I219_V5),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_CNP_I219_LM6),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_CNP_I219_V6),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_CNP_I219_LM7),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_CNP_I219_V7),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_ICP_I219_LM8),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_ICP_I219_V8),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_ICP_I219_LM9),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_ICP_I219_V9),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_CMP_I219_LM10),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_CMP_I219_V10),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_CMP_I219_LM11),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_CMP_I219_V11),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_CMP_I219_LM12),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_CMP_I219_V12),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_TGP_I219_LM13),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_TGP_I219_V13),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_TGP_I219_LM14),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_TGP_I219_V14),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_TGP_I219_LM15),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_TGP_I219_V15),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_ADP_I219_LM16),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_ADP_I219_V16),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_ADP_I219_LM17),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_ADP_I219_V17),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_MTP_I219_LM18),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_MTP_I219_V18),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_MTP_I219_LM19),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH_MTP_I219_V19),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82575EB_PT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82575EB_PF),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82575GB_QP),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82575GB_QP_PM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82576),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82576_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82576_SERDES),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82576_QUAD_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82576_NS),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82583V),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82576_NS_SERDES),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82576_SERDES_QUAD),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH2_LV_LM),
    (INTEL_VENDOR_ID, E1000_DEV_ID_PCH2_LV_V),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82580_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82580_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82580_SERDES),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82580_SGMII),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82580_COPPER_DUAL),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82580_QUAD_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_DH89XXCC_SGMII),
    (INTEL_VENDOR_ID, E1000_DEV_ID_DH89XXCC_SERDES),
    (INTEL_VENDOR_ID, E1000_DEV_ID_DH89XXCC_BACKPLANE),
    (INTEL_VENDOR_ID, E1000_DEV_ID_DH89XXCC_SFP),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I350_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I350_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I350_SERDES),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I350_SGMII),
    (INTEL_VENDOR_ID, E1000_DEV_ID_82576_QUAD_CU_ET2),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I210_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I210_COPPER_OEM1),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I210_COPPER_IT),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I210_FIBER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I210_SERDES),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I210_SGMII),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I210_COPPER_FLASHLESS),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I210_SERDES_FLASHLESS),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I211_COPPER),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I350_DA4),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I354_BACKPLANE_1GBPS),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I354_SGMII),
    (INTEL_VENDOR_ID, E1000_DEV_ID_I354_BACKPLANE_2_5GBPS),
    (INTEL_VENDOR_ID, E1000_DEV_ID_EP80579_LAN_1),
    (INTEL_VENDOR_ID, E1000_DEV_ID_EP80579_LAN_2),
    (INTEL_VENDOR_ID, E1000_DEV_ID_EP80579_LAN_3),
    (INTEL_VENDOR_ID, E1000_DEV_ID_EP80579_LAN_4),
    (INTEL_VENDOR_ID, E1000_DEV_ID_EP80579_LAN_5),
    (INTEL_VENDOR_ID, E1000_DEV_ID_EP80579_LAN_6),
];

pub const CABLE_LENGTH_50: u16 = 0;
pub const CABLE_LENGTH_50_80: u16 = 1;
pub const CABLE_LENGTH_80_110: u16 = 2;
pub const CABLE_LENGTH_110_140: u16 = 3;
pub const CABLE_LENGTH_140: u16 = 4;

pub const GG_CABLE_LENGTH_60: u16 = 0;
pub const GG_CABLE_LENGTH_60_115: u16 = 1;
pub const GG_CABLE_LENGTH_115_150: u16 = 2;
pub const GG_CABLE_LENGTH_150: u16 = 4;

pub const _IGP_CABLE_LENGTH_10: u16 = 10;
pub const _IGP_CABLE_LENGTH_20: u16 = 20;
pub const _IGP_CABLE_LENGTH_30: u16 = 30;
pub const _IGP_CABLE_LENGTH_40: u16 = 40;
pub const IGP_CABLE_LENGTH_50: u16 = 50;
pub const IGP_CABLE_LENGTH_60: u16 = 60;
pub const _IGP_CABLE_LENGTH_70: u16 = 70;
pub const IGP_CABLE_LENGTH_80: u16 = 80;
pub const _IGP_CABLE_LENGTH_90: u16 = 90;
pub const _IGP_CABLE_LENGTH_100: u16 = 100;
pub const IGP_CABLE_LENGTH_110: u16 = 110;
pub const IGP_CABLE_LENGTH_115: u16 = 115;
pub const _IGP_CABLE_LENGTH_120: u16 = 120;
pub const _IGP_CABLE_LENGTH_130: u16 = 130;
pub const IGP_CABLE_LENGTH_140: u16 = 140;
pub const IGP_CABLE_LENGTH_150: u16 = 150;
pub const _IGP_CABLE_LENGTH_160: u16 = 160;
pub const IGP_CABLE_LENGTH_170: u16 = 170;
pub const IGP_CABLE_LENGTH_180: u16 = 180;

// Number of milliseconds we wait for Eeprom auto read bit done after MAC reset
const AUTO_READ_DONE_TIMEOUT: u32 = 10;

bitflags! {
    struct Ich8HwsFlashStatus: u16 {
        const FLCDONE = 1; // Flash Cycle Done
        const FLCERR = 1 << 1; // Flash Cycle Error
        const DAEL = 1 << 2; // Direct Access error Log
        const FLCINPROG = 1 << 5; // flash SPI cycle in progress
        const FLDESVALID = 1 << 14; // Flash Descriptor Valid
        const FLOCKDN = 1 << 15; // Flash Configuration Lock-Down
    }
}

// Number of milliseconds we wait for PHY configuration done after MAC reset
const PHY_CFG_TIMEOUT: u32 = 100;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PCIBusSpeed {
    Unknown,
    S33,
    S66,
    S100,
    S120,
    S133,
    S2500,
    Reserved,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PCIBusType {
    Unknown,
    Pci,
    PciX,
    PciExpress,
    Cpp,
    _Reserved,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpeedDuplex {
    S10Half,
    S10Full,
    S100Half,
    S100Full,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Speed {
    None,
    S10Mbps = 10,
    S100Mbps = 100,
    S1000Mbps = 1000,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Duplex {
    None,
    Half,
    Full,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MediaType {
    Copper,
    Fiber,
    InternalSerdes,
    Oem,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DataSize {
    Byte = 1,
    Word = 2,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PhyType {
    M88,
    Igp,
    Igp2,
    Gg82563,
    Igp3,
    Ife,
    Bm, // phy used in i82574L, ICH10 and some ICH9
    Oem,
    I82577,
    I82578,
    I82579,
    I217,
    I82580,
    Rtl8211,
    Undefined,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DspConfigState {
    Disabled,
    Enabled,
    Activated,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MSType {
    Default,
    ForceMaster,
    ForceSlave,
    Auto,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FfeConfig {
    Enabled,
    Active,
    _Blocked,
}

#[derive(Debug)]
struct FlashMemory {
    base_address: BaseAddress,
    offset: usize,
}

#[repr(C)]
#[derive(Debug)]
struct HostMngDhcpCookie {
    signature: u32,
    status: u8,
    reserved0: u8,
    vlan_id: u16,
    reserved1: u32,
    reserved2: u16,
    reserved3: u8,
    checksum: u8,
}

pub const ADVERTISE_10_HALF: u16 = 0x0001;
pub const ADVERTISE_10_FULL: u16 = 0x0002;
pub const ADVERTISE_100_HALF: u16 = 0x0004;
pub const ADVERTISE_100_FULL: u16 = 0x0008;
pub const ADVERTISE_1000_HALF: u16 = 0x0010;
pub const ADVERTISE_1000_FULL: u16 = 0x0020;

pub const AUTONEG_ADVERTISE_SPEED_DEFAULT: u16 = 0x002F; // Everything but 1000-Half
pub const AUTONEG_ADVERTISE_10_100_ALL: u16 = 0x000F; // All 10/100 speeds
pub const AUTONEG_ADVERTISE_10_ALL: u16 = 0x0003; // 10Mbps Full & Half speeds

const AUTONEG_ADV_DEFAULT: u16 = ADVERTISE_10_HALF
    | ADVERTISE_10_FULL
    | ADVERTISE_100_HALF
    | ADVERTISE_100_FULL
    | ADVERTISE_1000_FULL;

#[derive(Debug)]
pub struct IgbHw {
    mac_type: MacType,
    initialize_hw_bits_disable: bool,
    eee_enable: bool,
    icp_xxxx_port_num: u32,
    swfwhw_semaphore_present: bool,
    swfw_sync_present: bool,
    swfw: u16,
    eeprom_semaphore_present: bool,
    phy_reset_disable: bool,
    flash_memory: Option<FlashMemory>,
    flash_bank_size: Option<usize>,
    flash_base_address: Option<usize>,
    eeprom: Eeprom,
    tbi_compatibility_on: bool,
    tbi_compatibility_en: bool,
    media_type: MediaType,
    sgmii_active: bool,
    sw_flag: isize,
    phy_addr: u32,
    phy_revision: Option<u32>,
    phy_type: PhyType,
    phy_id: u32,
    bus_func: u8,
    fc_high_water: u16,
    fc_low_water: u16,
    fc_pause_time: u16,
    fc_send_xon: bool,
    fc: u8,
    original_fc: u8,
    max_frame_size: u32,
    min_frame_size: u32,
    perm_mac_addr: [u8; NODE_ADDRESS_SIZE],
    mac_addr: [u8; NODE_ADDRESS_SIZE],
    mng_cookie: HostMngDhcpCookie,
    autoneg: bool,
    icp_xxxx_is_link_up: bool,
    ledctl_default: u32,
    ledctl_mode1: u32,
    ledctl_mode2: u32,
    autoneg_advertised: u16,
    dsp_config_state: DspConfigState,
    master_slave: MSType,
    original_master_slave: MSType,
    ffe_config_state: FfeConfig,
    get_link_status: bool,
    autoneg_failed: bool,
    speed_downgraded: bool,
    serdes_link_down: bool,
    txcw: u32,
    forced_speed_duplex: SpeedDuplex,
    bus_type: PCIBusType,
    bus_speed: PCIBusSpeed,
    legacy_irq: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MacType {
    Em82542Rev2_0 = 0,
    Em82542Rev2_1,
    Em82543,
    Em82544,
    Em82540,
    Em82545,
    Em82545Rev3,
    EmICPxxxx,
    Em82546,
    Em82546Rev3,
    Em82541,
    Em82541Rev2,
    Em82547,
    Em82547Rev2,
    Em82571,
    Em82572,
    Em82573,
    Em82574,
    Em82575,
    Em82576,
    Em82580,
    EmI350,
    EmI210,
    Em80003es2lan,
    EmIch8lan,
    EmIch9lan,
    EmIch10lan,
    EmPchlan,
    EmPch2lan,
    EmPchLpt,
    EmPchSpt,
    EmPchCnp,
    EmPchTgp,
    EmPchAdp,
}

/// Return `(MacType, initialize_hw_bits_disable, eee_enable, icp_xxxx_port_num)`.
///
/// https://github.com/openbsd/src/blob/f058c8dbc8e3b2524b639ac291b898c7cc708996/sys/dev/pci/if_em_hw.c#L403
fn get_mac_type(device: u16, info: &PCIeInfo) -> Result<(MacType, bool, bool, u32), IgbDriverErr> {
    use MacType::*;

    let mut initialize_hw_bits_disable = false;
    let mut eee_enable = false;
    let mut icp_xxxx_port_num = 0;

    let result = match device {
        E1000_DEV_ID_82542 => match info.get_revision_id() {
            E1000_82542_2_0_REV_ID => Em82542Rev2_0,
            E1000_82542_2_1_REV_ID => Em82542Rev2_1,
            _ => return Err(IgbDriverErr::UnknownRevisionD),
        },
        E1000_DEV_ID_82543GC_FIBER | E1000_DEV_ID_82543GC_COPPER => Em82543,

        E1000_DEV_ID_82544EI_COPPER
        | E1000_DEV_ID_82544EI_FIBER
        | E1000_DEV_ID_82544GC_COPPER
        | E1000_DEV_ID_82544GC_LOM => Em82544,
        E1000_DEV_ID_82540EM
        | E1000_DEV_ID_82540EM_LOM
        | E1000_DEV_ID_82540EP
        | E1000_DEV_ID_82540EP_LOM
        | E1000_DEV_ID_82540EP_LP => Em82540, // e1000
        E1000_DEV_ID_82545EM_COPPER | E1000_DEV_ID_82545EM_FIBER => Em82545,
        E1000_DEV_ID_82545GM_COPPER | E1000_DEV_ID_82545GM_FIBER | E1000_DEV_ID_82545GM_SERDES => {
            Em82545Rev3
        }
        E1000_DEV_ID_82546EB_COPPER
        | E1000_DEV_ID_82546EB_FIBER
        | E1000_DEV_ID_82546EB_QUAD_COPPER => Em82546,
        E1000_DEV_ID_82546GB_COPPER
        | E1000_DEV_ID_82546GB_FIBER
        | E1000_DEV_ID_82546GB_SERDES
        | E1000_DEV_ID_82546GB_PCIE
        | E1000_DEV_ID_82546GB_QUAD_COPPER
        | E1000_DEV_ID_82546GB_QUAD_COPPER_KSP3
        | E1000_DEV_ID_82546GB_2 => Em82546Rev3,
        E1000_DEV_ID_82541EI | E1000_DEV_ID_82541EI_MOBILE | E1000_DEV_ID_82541ER_LOM => Em82541,
        E1000_DEV_ID_82541ER
        | E1000_DEV_ID_82541GI
        | E1000_DEV_ID_82541GI_LF
        | E1000_DEV_ID_82541GI_MOBILE => Em82541Rev2,
        E1000_DEV_ID_82547EI | E1000_DEV_ID_82547EI_MOBILE => Em82547,
        E1000_DEV_ID_82547GI => Em82547Rev2,
        E1000_DEV_ID_82571EB_AF
        | E1000_DEV_ID_82571EB_AT
        | E1000_DEV_ID_82571EB_COPPER
        | E1000_DEV_ID_82571EB_FIBER
        | E1000_DEV_ID_82571EB_SERDES
        | E1000_DEV_ID_82571EB_QUAD_COPPER
        | E1000_DEV_ID_82571EB_QUAD_FIBER
        | E1000_DEV_ID_82571EB_QUAD_COPPER_LP
        | E1000_DEV_ID_82571EB_SERDES_DUAL
        | E1000_DEV_ID_82571EB_SERDES_QUAD
        | E1000_DEV_ID_82571PT_QUAD_COPPER => Em82571,
        E1000_DEV_ID_82572EI_COPPER
        | E1000_DEV_ID_82572EI_FIBER
        | E1000_DEV_ID_82572EI_SERDES
        | E1000_DEV_ID_82572EI => Em82572,
        E1000_DEV_ID_82573E
        | E1000_DEV_ID_82573E_IAMT
        | E1000_DEV_ID_82573E_PM
        | E1000_DEV_ID_82573L
        | E1000_DEV_ID_82573L_PL_1
        | E1000_DEV_ID_82573L_PL_2
        | E1000_DEV_ID_82573V_PM => Em82573,
        E1000_DEV_ID_82574L | E1000_DEV_ID_82574LA | E1000_DEV_ID_82583V => Em82574,
        E1000_DEV_ID_82575EB_PT
        | E1000_DEV_ID_82575EB_PF
        | E1000_DEV_ID_82575GB_QP
        | E1000_DEV_ID_82575GB_QP_PM => {
            initialize_hw_bits_disable = true;
            Em82575
        }
        E1000_DEV_ID_82576
        | E1000_DEV_ID_82576_FIBER
        | E1000_DEV_ID_82576_SERDES
        | E1000_DEV_ID_82576_QUAD_COPPER
        | E1000_DEV_ID_82576_QUAD_CU_ET2
        | E1000_DEV_ID_82576_NS
        | E1000_DEV_ID_82576_NS_SERDES
        | E1000_DEV_ID_82576_SERDES_QUAD => {
            initialize_hw_bits_disable = true;
            Em82576
        }
        E1000_DEV_ID_82580_COPPER
        | E1000_DEV_ID_82580_FIBER
        | E1000_DEV_ID_82580_QUAD_FIBER
        | E1000_DEV_ID_82580_SERDES
        | E1000_DEV_ID_82580_SGMII
        | E1000_DEV_ID_82580_COPPER_DUAL
        | E1000_DEV_ID_DH89XXCC_SGMII
        | E1000_DEV_ID_DH89XXCC_SERDES
        | E1000_DEV_ID_DH89XXCC_BACKPLANE
        | E1000_DEV_ID_DH89XXCC_SFP => {
            initialize_hw_bits_disable = true;
            Em82580
        }
        E1000_DEV_ID_I210_COPPER
        | E1000_DEV_ID_I210_COPPER_OEM1
        | E1000_DEV_ID_I210_COPPER_IT
        | E1000_DEV_ID_I210_FIBER
        | E1000_DEV_ID_I210_SERDES
        | E1000_DEV_ID_I210_SGMII
        | E1000_DEV_ID_I210_COPPER_FLASHLESS
        | E1000_DEV_ID_I210_SERDES_FLASHLESS
        | E1000_DEV_ID_I211_COPPER => {
            initialize_hw_bits_disable = true;
            eee_enable = true;
            EmI210
        }
        E1000_DEV_ID_I350_COPPER
        | E1000_DEV_ID_I350_FIBER
        | E1000_DEV_ID_I350_SERDES
        | E1000_DEV_ID_I350_SGMII
        | E1000_DEV_ID_I350_DA4
        | E1000_DEV_ID_I354_BACKPLANE_1GBPS
        | E1000_DEV_ID_I354_SGMII
        | E1000_DEV_ID_I354_BACKPLANE_2_5GBPS => {
            initialize_hw_bits_disable = true;
            eee_enable = true;
            EmI350
        }
        E1000_DEV_ID_80003ES2LAN_COPPER_SPT
        | E1000_DEV_ID_80003ES2LAN_SERDES_SPT
        | E1000_DEV_ID_80003ES2LAN_COPPER_DPT
        | E1000_DEV_ID_80003ES2LAN_SERDES_DPT => Em80003es2lan,
        E1000_DEV_ID_ICH8_IFE
        | E1000_DEV_ID_ICH8_IFE_G
        | E1000_DEV_ID_ICH8_IFE_GT
        | E1000_DEV_ID_ICH8_IGP_AMT
        | E1000_DEV_ID_ICH8_IGP_C
        | E1000_DEV_ID_ICH8_IGP_M
        | E1000_DEV_ID_ICH8_IGP_M_AMT
        | E1000_DEV_ID_ICH8_82567V_3 => EmIch8lan,
        E1000_DEV_ID_ICH9_BM
        | E1000_DEV_ID_ICH9_IFE
        | E1000_DEV_ID_ICH9_IFE_G
        | E1000_DEV_ID_ICH9_IFE_GT
        | E1000_DEV_ID_ICH9_IGP_AMT
        | E1000_DEV_ID_ICH9_IGP_C
        | E1000_DEV_ID_ICH9_IGP_M
        | E1000_DEV_ID_ICH9_IGP_M_AMT
        | E1000_DEV_ID_ICH9_IGP_M_V
        | E1000_DEV_ID_ICH10_R_BM_LF
        | E1000_DEV_ID_ICH10_R_BM_LM
        | E1000_DEV_ID_ICH10_R_BM_V => EmIch9lan,
        E1000_DEV_ID_ICH10_D_BM_LF | E1000_DEV_ID_ICH10_D_BM_LM | E1000_DEV_ID_ICH10_D_BM_V => {
            EmIch10lan
        }
        E1000_DEV_ID_PCH_M_HV_LC
        | E1000_DEV_ID_PCH_M_HV_LM
        | E1000_DEV_ID_PCH_D_HV_DC
        | E1000_DEV_ID_PCH_D_HV_DM => {
            eee_enable = true;
            EmPchlan
        }
        E1000_DEV_ID_PCH2_LV_LM | E1000_DEV_ID_PCH2_LV_V => EmPch2lan,
        E1000_DEV_ID_PCH_LPT_I217_LM
        | E1000_DEV_ID_PCH_LPT_I217_V
        | E1000_DEV_ID_PCH_LPTLP_I218_LM
        | E1000_DEV_ID_PCH_LPTLP_I218_V
        | E1000_DEV_ID_PCH_I218_LM2
        | E1000_DEV_ID_PCH_I218_V2
        | E1000_DEV_ID_PCH_I218_LM3
        | E1000_DEV_ID_PCH_I218_V3 => EmPchLpt,
        E1000_DEV_ID_PCH_SPT_I219_LM
        | E1000_DEV_ID_PCH_SPT_I219_V
        | E1000_DEV_ID_PCH_SPT_I219_LM2
        | E1000_DEV_ID_PCH_SPT_I219_V2
        | E1000_DEV_ID_PCH_LBG_I219_LM3
        | E1000_DEV_ID_PCH_SPT_I219_LM4
        | E1000_DEV_ID_PCH_SPT_I219_V4
        | E1000_DEV_ID_PCH_SPT_I219_LM5
        | E1000_DEV_ID_PCH_SPT_I219_V5
        | E1000_DEV_ID_PCH_CMP_I219_LM12
        | E1000_DEV_ID_PCH_CMP_I219_V12 => EmPchSpt,
        E1000_DEV_ID_PCH_CNP_I219_LM6
        | E1000_DEV_ID_PCH_CNP_I219_V6
        | E1000_DEV_ID_PCH_CNP_I219_LM7
        | E1000_DEV_ID_PCH_CNP_I219_V7
        | E1000_DEV_ID_PCH_ICP_I219_LM8
        | E1000_DEV_ID_PCH_ICP_I219_V8
        | E1000_DEV_ID_PCH_ICP_I219_LM9
        | E1000_DEV_ID_PCH_ICP_I219_V9
        | E1000_DEV_ID_PCH_CMP_I219_LM10
        | E1000_DEV_ID_PCH_CMP_I219_V10
        | E1000_DEV_ID_PCH_CMP_I219_LM11
        | E1000_DEV_ID_PCH_CMP_I219_V11 => EmPchCnp,
        E1000_DEV_ID_PCH_TGP_I219_LM13
        | E1000_DEV_ID_PCH_TGP_I219_V13
        | E1000_DEV_ID_PCH_TGP_I219_LM14
        | E1000_DEV_ID_PCH_TGP_I219_V14
        | E1000_DEV_ID_PCH_TGP_I219_LM15
        | E1000_DEV_ID_PCH_TGP_I219_V15 => EmPchTgp,
        E1000_DEV_ID_PCH_ADP_I219_LM16
        | E1000_DEV_ID_PCH_ADP_I219_V16
        | E1000_DEV_ID_PCH_ADP_I219_LM17
        | E1000_DEV_ID_PCH_ADP_I219_V17
        | E1000_DEV_ID_PCH_MTP_I219_LM18
        | E1000_DEV_ID_PCH_MTP_I219_V18
        | E1000_DEV_ID_PCH_MTP_I219_LM19
        | E1000_DEV_ID_PCH_MTP_I219_V19 => EmPchAdp,
        E1000_DEV_ID_EP80579_LAN_1 => {
            icp_xxxx_port_num = 0;
            EmICPxxxx
        }
        E1000_DEV_ID_EP80579_LAN_2 | E1000_DEV_ID_EP80579_LAN_4 => {
            icp_xxxx_port_num = 1;
            EmICPxxxx
        }
        E1000_DEV_ID_EP80579_LAN_3 | E1000_DEV_ID_EP80579_LAN_5 => {
            icp_xxxx_port_num = 2;
            EmICPxxxx
        }
        E1000_DEV_ID_EP80579_LAN_6 => {
            icp_xxxx_port_num = 3;
            EmICPxxxx
        }
        _ => return Err(IgbDriverErr::UnknownDeviceID),
    };

    Ok((
        result,
        initialize_hw_bits_disable,
        eee_enable,
        icp_xxxx_port_num,
    ))
}

/// Return (swfwhw_semaphore_present, asf_firmware_present, swfw_sync_present, eeprom_semaphore_present).
fn get_hw_info(mac_type: &MacType) -> (bool, bool, bool) {
    use MacType::*;

    let mut swfwhw_semaphore_present = false;
    let mut swfw_sync_present = false;
    let mut eeprom_semaphore_present = false;

    match mac_type {
        EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt
        | EmPchCnp | EmPchTgp | EmPchAdp => {
            swfwhw_semaphore_present = true;
        }
        Em80003es2lan | Em82575 | Em82576 | Em82580 | EmI350 | EmI210 => {
            swfw_sync_present = true;
        }
        Em82571 | Em82572 | Em82573 | Em82574 => {
            eeprom_semaphore_present = true;
        }
        _ => (),
    }

    (
        swfwhw_semaphore_present,
        swfw_sync_present,
        eeprom_semaphore_present,
    )
}

/// Reject non-PCI Express devices.
///
/// https://github.com/openbsd/src/blob/d88178ae581240e08c6acece5c276298d1ac6c90/sys/dev/pci/if_em_hw.c#L8381
///
/// e1000 of PCI is supported because it is used in virtual machines.
fn check_pci_express(mac_type: &MacType) -> Result<(), IgbDriverErr> {
    use MacType::*;

    match mac_type {
        Em82540 | Em82571 | Em82572 | Em82573 | Em82574 | Em82575 | Em82576 | Em82580
        | Em80003es2lan | EmI210 | EmI350 | EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan
        | EmPch2lan | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp => Ok(()),
        _ => Err(IgbDriverErr::NotPciExpress),
    }
}

fn is_ich8(mac_type: &MacType) -> bool {
    use MacType::*;
    matches!(
        mac_type,
        EmIch8lan
            | EmIch9lan
            | EmIch10lan
            | EmPchlan
            | EmPch2lan
            | EmPchLpt
            | EmPchSpt
            | EmPchCnp
            | EmPchTgp
            | EmPchAdp
    )
}

fn round_up(value: u32, multiple: u32) -> u32 {
    (value + multiple - 1) & !(multiple - 1)
}

impl IgbHw {
    pub fn new(info: &mut PCIeInfo) -> Result<Self, IgbDriverErr> {
        use MacType::*;

        let (mac_type, initialize_hw_bits_disable, eee_enable, icp_xxxx_port_num) =
            get_mac_type(info.get_id(), info)?;

        check_pci_express(&mac_type)?;

        let (swfwhw_semaphore_present, swfw_sync_present, eeprom_semaphore_present) =
            get_hw_info(&mac_type);

        if matches!(mac_type, MacType::EmPchlan) {
            info.set_revision_id((info.get_id() & 0x0f) as u8);
        }

        // https://github.com/openbsd/src/blob/d88178ae581240e08c6acece5c276298d1ac6c90/sys/dev/pci/if_em.c#L1720-L1740
        let flash_memory = if matches!(mac_type, MacType::EmPchSpt) {
            Some(FlashMemory {
                base_address: info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?,
                offset: 0xe000,
            })
        } else if is_ich8(&mac_type) {
            let bar1 = info.get_bar(1).ok_or(IgbDriverErr::NoBar1)?;
            if matches!(bar1, BaseAddress::Mmio { .. }) {
                Some(FlashMemory {
                    base_address: bar1,
                    offset: 0,
                })
            } else {
                return Err(IgbDriverErr::Bar1IsNotMMIO);
            }
        } else {
            None
        };

        let (eeprom, flash_base_address, flash_bank_size) =
            Eeprom::new(&mac_type, &flash_memory, info)?;

        let (tbi_compatibility_en, media_type, sgmii_active) = set_media_type(&mac_type, info)?;

        let (bus_func, swfw) = if matches!(
            mac_type,
            Em80003es2lan | Em82575 | Em82576 | Em82580 | EmI210 | EmI350
        ) {
            let reg = read_reg(info, STATUS)?;
            let bus_func = (reg & STATUS_FUNC_MASK) >> STATUS_FUNC_SHIFT;

            let swfw = match bus_func {
                0 => SWFW_PHY0_SM,
                1 => SWFW_PHY1_SM,
                2 => SWFW_PHY2_SM,
                3 => SWFW_PHY3_SM,
                _ => return Err(IgbDriverErr::Phy),
            };

            (bus_func as u8, swfw)
        } else {
            (0, 0)
        };

        let max_frame_size = match mac_type {
            Em82573 => {
                return Err(IgbDriverErr::NotSupported);
            }
            Em82571 | Em82572 | Em82574 | Em82575 | Em82576 | Em82580 | EmI210 | EmI350
            | EmIch9lan | EmIch10lan | EmPch2lan | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp
            | EmPchAdp | Em80003es2lan => {
                // 9K Jumbo Frame size
                9234
            }
            EmPchlan => 4096,
            Em82542Rev2_0 | Em82542Rev2_1 | EmIch8lan => ETHER_MAX_LEN,
            _ => MAX_JUMBO_FRAME_SIZE,
        } as u32;

        let min_frame_size = (ETHER_MIN_LEN + ETHER_CRC_LEN) as u32;

        // These parameters control the automatic generation (Tx) and
        // response (Rx) to Ethernet PAUSE frames.
        // - High water mark should allow for at least two frames to be
        //   received after sending an XOFF.
        // - Low water mark works best when it is very near the high water mark.
        //   This allows the receiver to restart by sending XON when it has
        //   drained a bit.  Here we use an arbitrary value of 1500 which will
        //   restart after one full frame is pulled from the buffer.  There
        //   could be several smaller frames in the buffer and if so they will
        //   not trigger the XON until their total number reduces the buffer
        //   by 1500.
        // - The pause time is fairly large at 1000 x 512ns = 512 usec.

        let rx_buffer_size = (read_reg(info, PBA)? & 0xffff) << 10;
        let fc_high_water = rx_buffer_size as u16 - round_up(max_frame_size, 1024) as u16;
        let fc_low_water = fc_high_water - 1500;
        let fc_send_xon = true;
        let fc = FC_FULL;
        let fc_pause_time = if mac_type == Em80003es2lan {
            0xFFFF
        } else {
            1000
        };

        let mut hw = Self {
            mac_type,
            initialize_hw_bits_disable,
            eee_enable,
            icp_xxxx_port_num,
            swfwhw_semaphore_present,
            swfw,
            swfw_sync_present,
            eeprom_semaphore_present,
            phy_reset_disable: false,
            flash_memory,
            flash_base_address,
            flash_bank_size,
            eeprom,
            tbi_compatibility_on: false,
            tbi_compatibility_en,
            media_type,
            sgmii_active,
            sw_flag: 0,
            phy_addr: 0,
            phy_revision: None,
            phy_type: PhyType::Undefined,
            phy_id: 0,
            bus_func,
            fc_high_water,
            fc_low_water,
            fc_pause_time,
            fc_send_xon,
            fc,
            original_fc: fc,
            max_frame_size,
            min_frame_size,
            perm_mac_addr: [0; NODE_ADDRESS_SIZE],
            mac_addr: [0; NODE_ADDRESS_SIZE],
            mng_cookie: HostMngDhcpCookie {
                signature: 0,
                status: 0,
                reserved0: 0,
                vlan_id: 0,
                reserved1: 0,
                reserved2: 0,
                reserved3: 0,
                checksum: 0,
            },
            autoneg: true,
            icp_xxxx_is_link_up: false,
            ledctl_default: 0,
            ledctl_mode1: 0,
            ledctl_mode2: 0,
            autoneg_advertised: AUTONEG_ADV_DEFAULT,
            dsp_config_state: DspConfigState::Disabled,
            master_slave: MSType::Default,
            original_master_slave: MSType::Default,
            ffe_config_state: FfeConfig::Enabled,
            get_link_status: false,
            autoneg_failed: false,
            speed_downgraded: false,
            serdes_link_down: false,
            txcw: 0,
            forced_speed_duplex: SpeedDuplex::S10Half,
            bus_type: PCIBusType::Unknown,
            bus_speed: PCIBusSpeed::Unknown,
            legacy_irq: false,
        };

        // Initialize phy_addr, phy_revision, phy_type, and phy_id
        hw.detect_gig_phy(info)?;

        Ok(hw)
    }

    pub fn set_legacy_irq(&mut self, legacy_irq: bool) {
        self.legacy_irq = legacy_irq;
    }

    #[inline(always)]
    pub fn get_mac_type(&self) -> MacType {
        self.mac_type
    }

    pub fn get_max_frame_size(&self) -> u32 {
        self.max_frame_size
    }

    /// https://github.com/openbsd/src/blob/f058c8dbc8e3b2524b639ac291b898c7cc708996/sys/dev/pci/if_em_hw.c#L1559
    pub fn init_hw(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        // force full DMA clock frequency for ICH8
        if self.mac_type == EmIch8lan {
            let reg_data = read_reg(info, STATUS)?;
            let reg_data = reg_data & !0x80000000;
            write_reg(info, STATUS, reg_data)?;
        }

        if matches!(
            self.mac_type,
            EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp
        ) {
            // The MAC-PHY interconnect may still be in SMBus mode
            // after Sx->S0.  Toggle the LANPHYPC Value bit to force
            // the interconnect to PCIe mode, but only if there is no
            // firmware present otherwise firmware will have done it.
            let fwsm = read_reg(info, FWSM)?;
            if (fwsm & FWSM_FW_VALID) == 0 {
                let mut ctrl = read_reg(info, CTRL)?;
                ctrl |= CTRL_LANPHYPC_OVERRIDE;
                ctrl &= !CTRL_LANPHYPC_VALUE;
                write_reg(info, CTRL, ctrl)?;
                awkernel_lib::delay::wait_microsec(10);
                ctrl &= !CTRL_LANPHYPC_OVERRIDE;
                write_reg(info, CTRL, ctrl)?;
                awkernel_lib::delay::wait_microsec(50);
            }

            // Gate automatic PHY configuration on non-managed 82579
            if self.mac_type == EmPch2lan {
                self.gate_hw_phy_config_ich8lan(info, true)?;
            }

            self.disable_ulp_lpt_lp(info, true)?;

            // Reset the PHY before any access to it.  Doing so,
            // ensures that the PHY is in a known good state before
            // we read/write PHY registers.  The generic reset is
            // sufficient here, because we haven't determined
            // the PHY type yet.
            self.phy_reset(info)?;

            // Ungate automatic PHY configuration on non-managed 82579
            if self.mac_type == EmPch2lan && (fwsm & FWSM_FW_VALID) == 0 {
                self.gate_hw_phy_config_ich8lan(info, false)?;
            }

            // Set MDIO slow mode before any other MDIO access
            self.set_mdio_slow_mode_hv(info)?;
        }

        // Initialize Identification LED
        // Skip this because fileds regarding LED are never used.
        self.id_led_init(info)?;

        let (tbi_compatibility_en, media_type, sgmii_active) =
            set_media_type(&self.mac_type, info)?;
        self.tbi_compatibility_en = tbi_compatibility_en;
        self.media_type = media_type;
        self.sgmii_active = sgmii_active;

        // Magic delay that improves problems with i219LM on HP Elitebook
        awkernel_lib::delay::wait_millisec(1);

        // Must be called after em_set_media_type because media_type is used
        self.initialize_hardware_bits(info)?;

        // VET hardcoded to standard value and VFTA removed in ICH8/ICH9 LAN
        if !is_ich8(&self.mac_type) {
            if (self.mac_type as u32) < Em82546Rev3 as u32 {
                write_reg(info, VET, 0)?;
            }

            if self.mac_type == EmI350 {
                clear_vfta_i350(info)?;
            } else {
                self.clear_vfta(info)?;
            }
        }

        // For 82542 (rev 2.0), disable MWI and put the receiver into reset
        if self.mac_type == Em82542Rev2_0 {
            return Err(IgbDriverErr::NotSupported);
        }

        // Setup the receive address. This involves initializing all of the
        // Receive Address Registers (RARs 0 - 15).
        self.init_rx_addrs(info)?;

        // For 82542 (rev 2.0), take the receiver out of reset and enable MWI
        if self.mac_type == Em82542Rev2_0 {
            return Err(IgbDriverErr::NotSupported);
        }

        // Zero out the Multicast HASH table
        let mta_size = if is_ich8(&self.mac_type) {
            MC_TBL_SIZE_ICH8LAN
        } else {
            MC_TBL_SIZE
        };

        for i in 0..mta_size {
            write_reg_array(info, MTA, i, 0)?;
            // use write flush to prevent Memory Write Block (MWB) from
            // occurring when accessing our register space
            write_flush(info)?;
        }

        // More time needed for PHY to initialize
        if is_ich8(&self.mac_type) {
            awkernel_lib::delay::wait_millisec(15);
        }

        // The 82578 Rx buffer will stall if wakeup is enabled in host and
        // the ME.  Reading the BM_WUC register will clear the host wakeup bit.
        // Reset the phy after disabling host wakeup to reset the Rx buffer.
        if self.phy_type == PhyType::I82578 {
            self.read_phy_reg(info, phy_reg(BM_WUC_PAGE as u32, 1))?;
            self.phy_reset(info)?;
        }

        // Call a subroutine to configure the link and setup flow control.
        self.setup_link(info)?;

        if matches!(self.mac_type, Em82573 | Em82574) {
            self.enable_tx_pkt_filtering(info)?;
        }

        if self.mac_type == Em80003es2lan {
            // Enable retransmit on late collisions
            let mut tctl = read_reg(info, TCTL)?;
            tctl |= TCTL_RTLC;
            write_reg(info, TCTL, tctl)?;

            // Configure Gigabit Carry Extend Padding
            let mut tctl_ext = read_reg(info, TCTL_EXT)?;
            tctl_ext &= !TCTL_EXT_GCEX_MASK;
            tctl_ext |= DEFAULT_80003ES2LAN_TCTL_EXT_GCEX;
            write_reg(info, TCTL_EXT, tctl_ext)?;

            // Configure Transmit Inter-Packet Gap
            let mut tipg = read_reg(info, TIPG)?;
            tipg &= !TIPG_IPGT_MASK;
            tipg |= DEFAULT_80003ES2LAN_TIPG_IPGT_1000;
            write_reg(info, TIPG, tipg)?;

            let mut fflt = read_reg_array(info, FFLT, 0x0001)?;
            fflt &= !0x00100000;
            write_reg_array(info, FFLT, 0x0001, fflt)?;
        }

        if matches!(self.mac_type, Em82573 | Em82574) {
            let mut gcr = read_reg(info, GCR)?;
            gcr |= GCR_L1_ACT_WITHOUT_L0S_RX;
            write_reg(info, GCR, gcr)?;
        }

        // Clear all of the statistics registers (clear on read).  It is
        // important that we do this after we have tried to establish link
        // because the symbol error count will increment wildly if there is
        // no link.
        self.clear_hw_cntrs(info)?;

        // ICH8 No-snoop bits are opposite polarity. Set to snoop by default after reset.
        if is_ich8(&self.mac_type) {
            let snoop = if self.mac_type == EmIch8lan {
                PCI_EX_82566_SNOOP_ALL
            } else {
                !PCI_EX_NO_SNOOP_ALL
            };

            self.set_pci_ex_no_snoop(info, snoop)?;
        }

        // ungate DMA clock to avoid packet loss
        if (self.mac_type as u32) >= EmPchTgp as u32 {
            let mut fflt_dbg = read_reg(info, FFLT_DBG)?;
            fflt_dbg |= 1 << 12;
            write_reg(info, FFLT_DBG, fflt_dbg)?;
        }

        if info.id == E1000_DEV_ID_82546GB_QUAD_COPPER
            || info.id == E1000_DEV_ID_82546GB_QUAD_COPPER_KSP3
        {
            let mut ctrl_ext = read_reg(info, CTRL_EXT)?;
            // Relaxed ordering must be disabled to avoid a parity error
            // crash in a PCI slot.
            ctrl_ext |= CTRL_EXT_RO_DIS;
            write_reg(info, CTRL_EXT, ctrl_ext)?;
        }

        Ok(())
    }

    /// Clears all hardware statistics counters.
    pub fn clear_hw_cntrs(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        pub use MacType::*;

        read_reg(info, CRCERRS)?;
        read_reg(info, SYMERRS)?;
        read_reg(info, MPC)?;
        read_reg(info, SCC)?;
        read_reg(info, ECOL)?;
        read_reg(info, MCC)?;
        read_reg(info, LATECOL)?;
        read_reg(info, COLC)?;
        read_reg(info, DC)?;
        read_reg(info, SEC)?;
        read_reg(info, RLEC)?;
        read_reg(info, XONRXC)?;
        read_reg(info, XONTXC)?;
        read_reg(info, XOFFRXC)?;
        read_reg(info, XOFFTXC)?;
        read_reg(info, FCRUC)?;

        if is_ich8(&self.mac_type) {
            read_reg(info, PRC64)?;
            read_reg(info, PRC127)?;
            read_reg(info, PRC255)?;
            read_reg(info, PRC511)?;
            read_reg(info, PRC1023)?;
            read_reg(info, PRC1522)?;
        }

        read_reg(info, GPRC)?;
        read_reg(info, BPRC)?;
        read_reg(info, MPRC)?;
        read_reg(info, GPTC)?;
        read_reg(info, GORCL)?;
        read_reg(info, GORCH)?;
        read_reg(info, GOTCL)?;
        read_reg(info, GOTCH)?;
        read_reg(info, RNBC)?;
        read_reg(info, RUC)?;
        read_reg(info, RFC)?;
        read_reg(info, ROC)?;
        read_reg(info, RJC)?;
        read_reg(info, TORL)?;
        read_reg(info, TORH)?;
        read_reg(info, TOTL)?;
        read_reg(info, TOTH)?;
        read_reg(info, TPR)?;
        read_reg(info, TPT)?;

        if !is_ich8(&self.mac_type) {
            read_reg(info, PTC64)?;
            read_reg(info, PTC127)?;
            read_reg(info, PTC255)?;
            read_reg(info, PTC511)?;
            read_reg(info, PTC1023)?;
            read_reg(info, PTC1522)?;
        }

        read_reg(info, MPTC)?;
        read_reg(info, BPTC)?;

        if (self.mac_type as u32) < Em82543 as u32 {
            return Ok(());
        }

        read_reg(info, ALGNERRC)?;
        read_reg(info, RXERRC)?;
        read_reg(info, TNCRS)?;
        read_reg(info, CEXTERR)?;
        read_reg(info, TSCTC)?;
        read_reg(info, TSCTFC)?;

        if (self.mac_type as u32) <= Em82544 as u32 || self.mac_type == EmICPxxxx {
            return Ok(());
        }

        read_reg(info, MGTPRC)?;
        read_reg(info, MGTPDC)?;
        read_reg(info, MGTPTC)?;

        if (self.mac_type as u32) <= Em82547Rev2 as u32 {
            return Ok(());
        }

        read_reg(info, IAC)?;
        read_reg(info, ICRXOC)?;

        if matches!(
            self.phy_type,
            PhyType::I82577 | PhyType::I82578 | PhyType::I82579 | PhyType::I217
        ) {
            self.read_phy_reg(info, HV_SCC_UPPER)?;
            self.read_phy_reg(info, HV_SCC_LOWER)?;
            self.read_phy_reg(info, HV_ECOL_UPPER)?;
            self.read_phy_reg(info, HV_ECOL_LOWER)?;
            self.read_phy_reg(info, HV_MCC_UPPER)?;
            self.read_phy_reg(info, HV_MCC_LOWER)?;
            self.read_phy_reg(info, HV_LATECOL_UPPER)?;
            self.read_phy_reg(info, HV_LATECOL_LOWER)?;
            self.read_phy_reg(info, HV_COLC_UPPER)?;
            self.read_phy_reg(info, HV_COLC_LOWER)?;
            self.read_phy_reg(info, HV_DC_UPPER)?;
            self.read_phy_reg(info, HV_DC_LOWER)?;
            self.read_phy_reg(info, HV_TNCRS_UPPER)?;
            self.read_phy_reg(info, HV_TNCRS_LOWER)?;
        }

        if matches!(self.mac_type, EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan)
            || !matches!(
                self.mac_type,
                EmPch2lan | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp
            )
        {
            return Ok(());
        }

        read_reg(info, ICRXPTC)?;
        read_reg(info, ICRXATC)?;
        read_reg(info, ICTXPTC)?;
        read_reg(info, ICTXATC)?;
        read_reg(info, ICTXQEC)?;
        read_reg(info, ICTXQMTC)?;
        read_reg(info, ICRXDMTC)?;

        Ok(())
    }

    /// Configure PCI-Ex no-snoop
    fn set_pci_ex_no_snoop(&mut self, info: &PCIeInfo, no_snoop: u32) -> Result<(), IgbDriverErr> {
        if self.bus_type == PCIBusType::Unknown {
            self.get_bus_info(info)?;
        }

        if self.bus_type != PCIBusType::PciExpress {
            return Ok(());
        }

        if no_snoop != 0 {
            let mut gcr = read_reg(info, GCR)?;
            gcr &= !PCI_EX_NO_SNOOP_ALL;
            gcr |= no_snoop;
            write_reg(info, GCR, gcr)?;
        }

        if is_ich8(&self.mac_type) {
            let mut ctrl_ext = read_reg(info, CTRL_EXT)?;
            ctrl_ext |= CTRL_EXT_RO_DIS;
            write_reg(info, CTRL_EXT, ctrl_ext)?;
        }

        Ok(())
    }

    /// Gets the current PCI bus type, speed, and width of the hardware
    fn get_bus_info(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        match self.mac_type {
            Em82542Rev2_0 | Em82542Rev2_1 => {
                self.bus_type = PCIBusType::Unknown;
                self.bus_speed = PCIBusSpeed::Unknown;
            }
            EmICPxxxx => {
                self.bus_type = PCIBusType::Cpp;
                self.bus_speed = PCIBusSpeed::Unknown;
            }
            Em82571 | Em82572 | Em82573 | Em82574 | Em82575 | Em82576 | Em82580 | Em80003es2lan
            | EmI210 | EmI350 => {
                self.bus_type = PCIBusType::PciExpress;
                self.bus_speed = PCIBusSpeed::S2500;
            }
            EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt
            | EmPchCnp | EmPchTgp | EmPchAdp => {
                self.bus_type = PCIBusType::PciExpress;
                self.bus_speed = PCIBusSpeed::S2500;
            }
            _ => {
                let status = read_reg(info, STATUS)?;
                self.bus_type = if status & STATUS_PCIX_MODE != 0 {
                    PCIBusType::PciX
                } else {
                    PCIBusType::Pci
                };

                if info.id == E1000_DEV_ID_82546EB_QUAD_COPPER {
                    self.bus_speed = if self.bus_type == PCIBusType::Pci {
                        PCIBusSpeed::S66
                    } else {
                        PCIBusSpeed::S120
                    };
                } else if self.bus_type == PCIBusType::Pci {
                    self.bus_speed = if status & STATUS_PCI66 != 0 {
                        PCIBusSpeed::S66
                    } else {
                        PCIBusSpeed::S33
                    };
                } else {
                    match status & STATUS_PCIX_SPEED {
                        STATUS_PCIX_SPEED_66 => self.bus_speed = PCIBusSpeed::S66,
                        STATUS_PCIX_SPEED_100 => self.bus_speed = PCIBusSpeed::S100,
                        STATUS_PCIX_SPEED_133 => self.bus_speed = PCIBusSpeed::S133,
                        _ => self.bus_speed = PCIBusSpeed::Reserved,
                    }
                }
            }
        }

        Ok(())
    }

    /// This function checks whether tx pkt filtering needs to be enabled or not.
    fn enable_tx_pkt_filtering(&mut self, info: &PCIeInfo) -> Result<bool, IgbDriverErr> {
        let mut tx_filter = false;

        // called in init as well as watchdog timer functions
        if self.check_mng_mode(info)? && self.mng_enable_host_if(info).is_ok() {
            if self.host_if_read_cookie(info).is_ok() {
                let checksum = self.mng_cookie.checksum;
                self.mng_cookie.checksum = 0;

                if self.mng_cookie.signature == IAMT_SIGNATURE
                    && checksum == calculate_mng_checksum(&self.mng_cookie)
                {
                    if self.mng_cookie.status & MNG_DHCP_COOKIE_STATUS_PARSING_SUPPORT != 0 {
                        tx_filter = true;
                    }
                } else {
                    tx_filter = true;
                }
            } else {
                tx_filter = true;
            }
        }

        Ok(tx_filter)
    }

    /// This function checks whether the HOST IF is enabled for command operation
    /// and also checks whether the previous command is completed.
    /// It busy waits in case of previous command is not completed.
    fn mng_enable_host_if(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        // Check that the host interface is enabled.
        let hicr = read_reg(info, HICR)?;
        if hicr & HICR_EN == 0 {
            return Err(IgbDriverErr::HostInterfaceCommand);
        }

        // Check the previous command is completed.
        for _ in 0..MNG_DHCP_COMMAND_TIMEOUT {
            let hicr = read_reg(info, HICR)?;
            if hicr & HICR_C == 0 {
                return Ok(());
            }
            awkernel_lib::delay::wait_millisec(1);
        }

        Err(IgbDriverErr::HostInterfaceCommand)
    }

    /// This function reads the cookie from ARC ram.
    fn host_if_read_cookie(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        let buffer: &mut [u32; 4] = unsafe { core::mem::transmute(&mut self.mng_cookie) };
        let offset = (MNG_DHCP_COOKIE_OFFSET >> 2) as usize;

        for (i, buf) in buffer.iter_mut().enumerate() {
            *buf = read_reg_array(info, HOST_IF, offset + i)?;
        }

        Ok(())
    }

    fn id_led_init(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if (self.mac_type as u32) < Em82540 as u32 || self.mac_type == EmICPxxxx {
            // Nothing to do
            return Ok(());
        }

        let ledctl = read_reg(info, LEDCTL)?;
        self.ledctl_default = ledctl;
        self.ledctl_mode1 = self.ledctl_default;
        self.ledctl_mode2 = self.ledctl_default;

        let mut eeprom_data = [0; 1];
        self.read_eeprom(info, EEPROM_ID_LED_SETTINGS, &mut eeprom_data)?;

        if self.mac_type == Em82573 && eeprom_data[0] == ID_LED_RESERVED_82573 {
            eeprom_data[0] = ID_LED_DEFAULT_82573;
        } else if eeprom_data[0] == ID_LED_RESERVED_0000 || eeprom_data[0] == ID_LED_RESERVED_FFFF {
            if matches!(self.mac_type, EmIch8lan | EmIch9lan | EmIch10lan) {
                eeprom_data[0] = ID_LED_DEFAULT_ICH8LAN;
            } else {
                eeprom_data[0] = ID_LED_DEFAULT;
            }
        }

        let ledctl_mask = 0x000000FF;

        for i in 0..4 {
            let temp = (eeprom_data[0] >> (i << 2)) & 0x0f;
            match temp {
                ID_LED_ON1_DEF2 | ID_LED_ON1_ON2 | ID_LED_ON1_OFF2 => {
                    self.ledctl_mode1 &= !(ledctl_mask << (i << 3));
                    self.ledctl_mode1 |= LEDCTL_MODE_LED_ON << (i << 3);
                }
                ID_LED_OFF1_DEF2 | ID_LED_OFF1_ON2 | ID_LED_OFF1_OFF2 => {
                    self.ledctl_mode1 &= !(ledctl_mask << (i << 3));
                    self.ledctl_mode1 |= LEDCTL_MODE_LED_OFF << (i << 3);
                }
                _ => (),
            }

            match temp {
                ID_LED_DEF1_ON2 | ID_LED_ON1_ON2 | ID_LED_OFF1_ON2 => {
                    self.ledctl_mode2 &= !(ledctl_mask << (i << 3));
                    self.ledctl_mode2 |= LEDCTL_MODE_LED_ON << (i << 3);
                }
                ID_LED_DEF1_OFF2 | ID_LED_ON1_OFF2 | ID_LED_OFF1_OFF2 => {
                    self.ledctl_mode2 &= !(ledctl_mask << (i << 3));
                    self.ledctl_mode2 |= LEDCTL_MODE_LED_OFF << (i << 3);
                }
                _ => (),
            }
        }

        Ok(())
    }

    /// Configures flow control and link settings.
    ///
    /// Determines which flow control settings to use. Calls the appropriate media-
    /// specific link configuration function. Configures the flow control settings.
    /// Assuming the adapter has a valid link partner, a valid link should be
    /// established. Assumes the hardware has previously been reset and the
    /// transmitter and receiver are not enabled.
    fn setup_link(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        // In the case of the phy reset being blocked, we already have a
        // link. We do not have to set it up again.
        if self.check_phy_reset_block(info).is_err() {
            return Ok(());
        }

        let eeprom_control2_reg_offset = if self.mac_type != EmICPxxxx {
            EEPROM_INIT_CONTROL2_REG
        } else {
            eeprom_init_control3_icp_xxx(self.icp_xxxx_port_num)
        };

        if self.fc == FC_DEFAULT {
            if matches!(
                self.mac_type,
                EmIch8lan
                    | EmIch9lan
                    | EmIch10lan
                    | EmPch2lan
                    | EmPchlan
                    | EmPchLpt
                    | EmPchSpt
                    | EmPchCnp
                    | EmPchTgp
                    | EmPchAdp
                    | Em82573
                    | Em82574
            ) {
                self.fc = FC_FULL;
            } else {
                let mut eeprom_data = [0; 1];
                self.read_eeprom(info, eeprom_control2_reg_offset, &mut eeprom_data)?;

                if eeprom_data[0] & EEPROM_WORD0F_PAUSE_MASK == 0 {
                    self.fc = FC_NONE;
                } else if eeprom_data[0] & EEPROM_WORD0F_PAUSE_MASK == EEPROM_WORD0F_ASM_DIR {
                    self.fc = FC_TX_PAUSE;
                } else {
                    self.fc = FC_FULL;
                }
            }
        }

        // We want to save off the original Flow Control configuration just
        // in case we get disconnected and then reconnected into a different
        // hub or switch with different Flow Control capabilities.
        if self.mac_type == Em82542Rev2_0 || (self.mac_type as u32) < Em82543 as u32 {
            return Err(IgbDriverErr::NotSupported);
        }

        self.original_fc = self.fc;

        // Take the 4 bits from EEPROM word 0x0F that determine the initial
        // polarity value for the SW controlled pins, and setup the Extended
        // Device Control reg with that info. This is needed because one of
        // the SW controlled pins is used for signal detection.  So this
        // should be done before em_setup_pcs_link() or em_phy_setup() is
        // called.
        if self.mac_type == Em82543 {
            return Err(IgbDriverErr::NotSupported);
        }

        // Make sure we have a valid PHY
        self.detect_gig_phy(info)?;

        // Call the necessary subroutine to configure the link.
        match self.media_type {
            MediaType::Copper | MediaType::Oem => {
                self.setup_copper_link(info)?;
            }
            _ => {
                self.setup_fiber_serdes_link(info)?;
            }
        }

        // Initialize the flow control address, type, and PAUSE timer
        // registers to their default values.  This is done even if flow
        // control is disabled, because it does not hurt anything to
        // initialize these registers.

        // FCAL/H and FCT are hardcoded to standard values in
        // em_ich8lan / em_ich9lan / em_ich10lan.
        if !is_ich8(&self.mac_type) {
            write_reg(info, FCT, FLOW_CONTROL_TYPE)?;
            write_reg(info, FCAH, FLOW_CONTROL_ADDRESS_HIGH)?;
            write_reg(info, FCAL, FLOW_CONTROL_ADDRESS_LOW)?;
        }
        write_reg(info, FCTTV, self.fc_pause_time as u32)?;

        use PhyType::*;
        if matches!(self.phy_type, I82577 | I82578 | I82579 | I217) {
            write_reg(info, FCRTV_PCH, 0x1000)?;
            self.write_phy_reg(info, phy_reg(BM_PORT_CTRL_PAGE, 27), self.fc_pause_time)?;
        }

        // Set the flow control receive threshold registers.  Normally, these
        // registers will be set to a default threshold that may be adjusted
        // later by the driver's runtime code.  However, if the ability to
        // transmit pause frames in not enabled, then these registers will be
        // set to 0.
        if self.fc & FC_TX_PAUSE == 0 {
            write_reg(info, FCRTL, 0)?;
            write_reg(info, FCRTH, 0)?;
        } else {
            // We need to set up the Receive Threshold high and low water
            // marks as well as (optionally) enabling the transmission of
            // XON frames.
            if self.fc_send_xon {
                write_reg(info, FCRTL, self.fc_low_water as u32 | FCRTL_XONE)?;
                write_reg(info, FCRTH, self.fc_high_water as u32)?;
            } else {
                write_reg(info, FCRTL, self.fc_low_water as u32)?;
                write_reg(info, FCRTH, self.fc_high_water as u32)?;
            }
        }

        Ok(())
    }

    /// Detects which PHY is present and setup the speed and duplex
    fn setup_copper_link(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        match self.mac_type {
            Em80003es2lan | EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan
            | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp => {
                // Set the mac to wait the maximum time between each
                // iteration and increase the max iterations when polling the
                // phy; this fixes erroneous timeouts at 10Mbps.
                self.write_kmrn_reg(info, gg82563_reg(0x34, 4), 0xFFFF)?;
                let mut reg_data = self.read_kmrn_reg(info, gg82563_reg(0x34, 9))?;
                reg_data |= 0x3F;
                self.write_kmrn_reg(info, gg82563_reg(0x34, 9), reg_data)?;
            }
            _ => (),
        }

        // Check if it is a valid PHY and set PHY mode if necessary.
        self.copper_link_preconfig(info)?;

        if self.mac_type == Em80003es2lan {
            // Kumeran registers are written-only
            let mut reg_data = KUMCTRLSTA_INB_CTRL_LINK_STATUS_TX_TIMEOUT_DEFAULT;
            reg_data |= KUMCTRLSTA_INB_CTRL_DIS_PADDING;
            self.write_kmrn_reg(info, KUMCTRLSTA_OFFSET_INB_CTRL, reg_data)?;
        }

        match self.phy_type {
            PhyType::Igp | PhyType::Igp3 | PhyType::Igp2 => {
                self.copper_link_igp_setup(info)?;
            }
            PhyType::M88 | PhyType::Bm | PhyType::Oem | PhyType::I82578 => {
                self.copper_link_mgp_setup(info)?;
            }
            PhyType::Gg82563 => {
                self.copper_link_ggp_setup(info)?;
            }
            PhyType::I82577 | PhyType::I82579 | PhyType::I217 => {
                self.copper_link_82577_setup(info)?;
            }
            PhyType::I82580 => {
                self.copper_link_82580_setup(info)?;
            }
            PhyType::Rtl8211 => {
                self.copper_link_rtl8211_setup(info)?;
            }
            _ => (),
        }

        if self.autoneg {
            // Setup autoneg and flow control advertisement and perform
            // autonegotiation
            self.copper_link_autoneg(info)?;
        } else {
            // PHY will be set to 10H, 10F, 100H,or 100F depending on
            // value from forced_speed_duplex.
            self.phy_force_speed_duplex(info)?;
        }

        // Check link status. Wait up to 100 microseconds for link to become
        // valid.

        for _ in 0..10 {
            self.read_phy_reg(info, PHY_STATUS)?;
            let phy_data = self.read_phy_reg(info, PHY_STATUS)?;

            self.icp_xxxx_is_link_up = (phy_data & MII_SR_LINK_STATUS) != 0;

            if phy_data & MII_SR_LINK_STATUS != 0 {
                // Config the MAC and PHY after link is up
                self.copper_link_postconfig(info)?;

                return Ok(());
            }

            awkernel_lib::delay::wait_microsec(10);
        }

        Ok(())
    }

    /// Config the MAC and the PHY after link is up.
    ///   1) Set up the MAC to the current PHY speed/duplex
    ///      if we are on 82543.  If we
    ///      are on newer silicon, we only need to configure
    ///      collision distance in the Transmit Control Register.
    ///   2) Set up flow control on the MAC to that established with
    ///      the link partner.
    ///   3) Config DSP to improve Gigabit link quality for some PHY revisions.
    fn copper_link_postconfig(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if (self.mac_type as u32) >= Em82544 as u32 && self.mac_type != EmICPxxxx {
            self.config_collision_dist(info)?;
        } else {
            self.config_mac_to_phy(info)?;
        }

        self.config_fc_after_link_up(info)?;

        // Config DSP to improve Giga link quality
        if self.phy_type == PhyType::Igp {
            self.config_dsp_after_link_change(info, true)?;
        }

        Ok(())
    }

    /// Sets the collision distance in the Transmit Control register
    ///
    /// Link should have been established previously. Reads the speed and duplex
    /// information from the Device Status register.
    fn config_collision_dist(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        let col_dist = if (self.mac_type as u32) < MacType::Em82543 as u32 {
            COLLISION_DISTANCE_82542
        } else {
            COLLISION_DISTANCE
        };

        let mut tctl = read_reg(info, TCTL)?;

        tctl &= !TCTL_COLD;
        tctl |= col_dist << COLD_SHIFT;

        write_reg(info, TCTL, tctl)?;
        write_flush(info)?;

        Ok(())
    }

    /// Sets MAC speed and duplex settings to reflect the those in the PHY
    ///
    /// The contents of the PHY register containing the needed information need to
    /// be passed in.
    fn config_mac_to_phy(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        // 82544 or newer MAC, Auto Speed Detection takes care of MAC
        // speed/duplex configuration.
        if (self.mac_type as u32) >= MacType::Em82544 as u32 && self.mac_type != MacType::EmICPxxxx
        {
            return Ok(());
        }

        // Read the Device Control Register and set the bits to Force Speed
        // and Duplex.
        let mut ctrl = read_reg(info, CTRL)?;
        ctrl |= CTRL_FRCSPD | CTRL_FRCDPX;
        ctrl &= !(CTRL_SPD_SEL | CTRL_ILOS);

        // Set up duplex in the Device Control and Transmit Control registers
        // depending on negotiated values.
        let phy_data = self.read_phy_reg(info, M88E1000_PHY_SPEC_STATUS)?;

        if phy_data & M88E1000_PSSR_DPLX != 0 {
            ctrl |= CTRL_FD;
        } else {
            ctrl &= !CTRL_FD;
        }

        self.config_collision_dist(info)?;

        // Set up speed in the Device Control register depending on
        // negotiated values.
        if phy_data & M88E1000_PSSR_SPEED == M88E1000_PSSR_1000MBS {
            ctrl |= CTRL_SPD_1000;
        } else if phy_data & M88E1000_PSSR_SPEED == M88E1000_PSSR_100MBS {
            ctrl |= CTRL_SPD_100;
        }

        // Write the configured values back to the Device Control Reg.
        write_reg(info, CTRL, ctrl)?;

        Ok(())
    }

    /// Configures flow control settings after link is established
    ///
    /// Should be called immediately after a valid link has been established.
    /// Forces MAC flow control settings if link was forced. When in MII/GMII mode
    /// and autonegotiation is enabled, the MAC flow control settings will be set
    /// based on the flow control negotiated by the PHY. In TBI mode, the TFCE
    /// and RFCE bits will be automatically set to the negotiated flow control mode.
    fn config_fc_after_link_up(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        // Check for the case where we have fiber media and auto-neg failed
        // so we had to force link.  In this case, we need to force the
        // configuration of the MAC to match the "fc" parameter.
        if (matches!(
            self.media_type,
            MediaType::InternalSerdes | MediaType::Fiber
        ) && self.autoneg_failed)
            || (matches!(self.media_type, MediaType::Copper | MediaType::Oem) && !self.autoneg)
        {
            self.force_mac_fc(info)?;
        }

        // Check for the case where we have copper media and auto-neg is
        // enabled.  In this case, we need to check and see if Auto-Neg has
        // completed, and if so, how the PHY and link partner has flow
        // control configured.
        if matches!(self.media_type, MediaType::Copper | MediaType::Oem) && self.autoneg {
            // Read the MII Status Register and check to see if AutoNeg
            // has completed.  We read this twice because this reg has
            // some "sticky" (latched) bits.
            self.read_phy_reg(info, PHY_STATUS)?;
            let mii_status_reg = self.read_phy_reg(info, PHY_STATUS)?;

            if mii_status_reg & MII_SR_AUTONEG_COMPLETE != 0 {
                // The AutoNeg process has completed, so we now need
                // to read both the Auto Negotiation Advertisement
                // Register (Address 4) and the Auto_Negotiation Base
                // Page Ability Register (Address 5) to determine how
                // flow control was negotiated.
                let mii_nway_adv_reg = self.read_phy_reg(info, PHY_AUTONEG_ADV)?;
                let mii_nway_lp_ability_reg = self.read_phy_reg(info, PHY_LP_ABILITY)?;

                // Two bits in the Auto Negotiation Advertisement
                // Register (Address 4) and two bits in the Auto
                // Negotiation Base Page Ability Register (Address 5)
                // determine flow control for both the PHY and the
                // link partner.  The following table, taken out of
                // the IEEE 802.3ab/D6.0 dated March 25, 1999,
                // describes these PAUSE resolution bits and how flow
                // control is determined based upon these settings.
                // NOTE:  DC = Don't Care
                //
                //   LOCAL DEVICE   |   LINK PARTNER  |
                //  PAUSE | ASM_DIR | PAUSE | ASM_DIR | NIC Resolution
                // -------|---------|-------|---------|---------------
                //    0   |    0    |  DC   |   DC    | em_fc_none
                //    0   |    1    |   0   |   DC    | em_fc_none
                //    0   |    1    |   1   |    0    | em_fc_none
                //    0   |    1    |   1   |    1    | em_fc_tx_pause
                //    1   |    0    |   0   |   DC    | em_fc_none
                //    1   |   DC    |   1   |   DC    | em_fc_full
                //    1   |    1    |   0   |    0    | em_fc_none
                //    1   |    1    |   0   |    1    | em_fc_rx_pause

                // Are both PAUSE bits set to 1?  If so, this implies
                // Symmetric Flow Control is enabled at both ends.
                // The ASM_DIR bits are irrelevant per the spec.
                //
                // For Symmetric Flow Control:
                //
                //   LOCAL DEVICE  |   LINK PARTNER
                // PAUSE | ASM_DIR | PAUSE | ASM_DIR | Result
                // -------|---------|-------|---------|---------------
                //    1   |   DC    |   1   |   DC    | em_fc_full
                if (mii_nway_adv_reg & NWAY_AR_PAUSE) != 0
                    && (mii_nway_lp_ability_reg & NWAY_LPAR_PAUSE) != 0
                {
                    // Now we need to check if the user selected
                    // RX ONLY of pause frames.  In this case, we
                    // had to advertise FULL flow control because
                    // we could not advertise RX ONLY. Hence, we
                    // must now check to see if we need to turn
                    // OFF  the TRANSMISSION of PAUSE frames.
                    if self.original_fc == FC_FULL {
                        self.fc = FC_FULL;
                    } else {
                        self.fc = FC_RX_PAUSE;
                    }
                } else if (mii_nway_adv_reg & NWAY_AR_PAUSE == 0)
                    && (mii_nway_adv_reg & NWAY_AR_ASM_DIR != 0)
                    && (mii_nway_lp_ability_reg & NWAY_LPAR_PAUSE != 0)
                    && (mii_nway_lp_ability_reg & NWAY_LPAR_ASM_DIR != 0)
                {
                    self.fc = FC_TX_PAUSE;
                } else {
                    self.fc = FC_RX_PAUSE;
                }

                // Now we need to do one last check...  If we auto-
                // negotiated to HALF DUPLEX, flow control should not
                // be enabled per IEEE 802.3 spec.
                let (_speed, duplex) = self.get_speed_and_duplex(info)?;
                if duplex == Duplex::Half {
                    self.fc = FC_NONE;
                }

                // Now we call a subroutine to actually force the MAC
                // controller to use the correct flow control
                // settings.
                self.force_mac_fc(info)?;
            }
        }

        Ok(())
    }

    /// Forces the MAC's flow control settings.
    ///
    /// Sets the TFCE and RFCE bits in the device control register to reflect
    /// the adapter settings. TFCE and RFCE need to be explicitly set by
    /// software when a Copper PHY is used because autonegotiation is managed
    /// by the PHY rather than the MAC. Software must also configure these
    /// bits when link is forced on a fiber connection.
    fn force_mac_fc(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        // Get the current configuration of the Device Control Register
        let mut ctrl = read_reg(info, CTRL)?;

        // Because we didn't get link via the internal auto-negotiation
        // mechanism (we either forced link or we got link via PHY auto-neg),
        // we have to manually enable/disable transmit an receive flow
        // control.
        //
        // The "Case" statement below enables/disable flow control according to
        // the "hw->fc" parameter.
        //
        // The possible values of the "fc" parameter are: 0:  Flow control is
        // completely disabled 1:  Rx flow control is enabled (we can receive
        // pause frames but not send pause frames). 2:  Tx flow control is
        // enabled (we can send pause frames but we do not receive
        // pause frames). 3:  Both Rx and TX flow control (symmetric) is
        // enabled. other:  No other values should be possible at this point.

        match self.fc {
            FC_NONE => {
                ctrl &= !(CTRL_TFCE | CTRL_RFCE);
            }
            FC_RX_PAUSE => {
                ctrl &= !CTRL_TFCE;
                ctrl |= CTRL_RFCE;
            }
            FC_TX_PAUSE => {
                ctrl &= !CTRL_RFCE;
                ctrl |= CTRL_TFCE;
            }
            FC_FULL => {
                ctrl |= CTRL_TFCE | CTRL_RFCE;
            }
            _ => return Err(IgbDriverErr::Config),
        }

        // Disable TX Flow Control for 82542 (rev 2.0)
        if self.mac_type == MacType::Em82542Rev2_0 {
            ctrl &= !CTRL_TFCE;
        }

        write_reg(info, CTRL, ctrl)?;

        Ok(())
    }

    /// Detects the current speed and duplex settings of the hardware.
    pub fn get_speed_and_duplex(
        &mut self,
        info: &PCIeInfo,
    ) -> Result<(Speed, Duplex), IgbDriverErr> {
        use MacType::*;

        if (self.mac_type as u32) >= Em82575 as u32 && self.media_type != MediaType::Copper {
            return self.get_pcs_speed_and_duplex_82575(info);
        }

        let (speed, duplex) = if (self.mac_type as u32) >= Em82543 as u32 {
            let status = read_reg(info, STATUS)?;
            let speed = if status & STATUS_SPEED_1000 != 0 {
                Speed::S1000Mbps
            } else if status & STATUS_SPEED_100 != 0 {
                Speed::S100Mbps
            } else {
                Speed::S10Mbps
            };

            let duplex = if status & STATUS_FD != 0 {
                Duplex::Full
            } else {
                Duplex::Half
            };
            (speed, duplex)
        } else {
            (Speed::S1000Mbps, Duplex::Full)
        };

        // IGP01 PHY may advertise full duplex operation after speed
        // downgrade even if it is operating at half duplex.  Here we set the
        // duplex settings to match the duplex in the link partner's
        // capabilities.
        let duplex = if self.phy_type == PhyType::Igp && self.speed_downgraded {
            let phy_data = self.read_phy_reg(info, PHY_AUTONEG_EXP)?;

            if phy_data & NWAY_ER_LP_NWAY_CAPS == 0 {
                Duplex::Half
            } else {
                let phy_data = self.read_phy_reg(info, PHY_LP_ABILITY)?;
                if (speed == Speed::S100Mbps && phy_data & NWAY_LPAR_100TX_FD_CAPS == 0)
                    || (speed == Speed::S10Mbps && phy_data & NWAY_LPAR_10T_FD_CAPS == 0)
                {
                    Duplex::Half
                } else {
                    duplex
                }
            }
        } else {
            duplex
        };

        if self.mac_type == Em80003es2lan && self.media_type == MediaType::Copper {
            if speed == Speed::S1000Mbps {
                self.configure_kmrn_for_1000(info)?;
            } else {
                self.configure_kmrn_for_10_100(info, duplex)?;
            }
        }

        if self.mac_type == EmIch8lan && self.phy_type == PhyType::Igp3 && speed == Speed::S1000Mbps
        {
            self.kumeran_lock_loss_workaround(info)?;
        }

        Ok((speed, duplex))
    }

    fn get_pcs_speed_and_duplex_82575(
        &mut self,
        info: &PCIeInfo,
    ) -> Result<(Speed, Duplex), IgbDriverErr> {
        self.serdes_link_down = true;

        // Read the PCS Status register for link state. For non-copper mode,
        // the status register is not accurate. The PCS status register is
        // used instead.
        let pcs = read_reg(info, PCS_LSTAT)?;

        // The link up bit determines when link is up on autoneg. The sync ok
        // gets set once both sides sync up and agree upon link. Stable link
        // can be determined by checking for both link up and link sync ok
        if (pcs & PCS_LSTS_LINK_OK != 0) && (pcs & PCS_LSTS_SYNK_OK != 0) {
            self.serdes_link_down = false;

            // Detect and store PCS speed
            let speed = if pcs & PCS_LSTS_SPEED_1000 != 0 {
                Speed::S1000Mbps
            } else if pcs & PCS_LSTS_SPEED_100 != 0 {
                Speed::S100Mbps
            } else {
                Speed::S10Mbps
            };

            // Detect and store PCS duplex
            let duplex = if pcs & PCS_LSTS_DUPLEX_FULL != 0 {
                Duplex::Full
            } else {
                Duplex::Half
            };

            Ok((speed, duplex))
        } else {
            Err(IgbDriverErr::Phy)
        }
    }

    fn configure_kmrn_for_1000(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        self.write_kmrn_reg(
            info,
            KUMCTRLSTA_OFFSET_HD_CTRL,
            KUMCTRLSTA_HD_CTRL_1000_DEFAULT,
        )?;

        // Configure Transmit Inter-Packet Gap
        let mut tipg = read_reg(info, TIPG)?;
        tipg &= !TIPG_IPGT_MASK;
        tipg |= DEFAULT_80003ES2LAN_TIPG_IPGT_1000;
        write_reg(info, TIPG, tipg)?;

        let mut reg_data = self.read_phy_reg(info, GG82563_PHY_KMRN_MODE_CTRL)?;
        reg_data &= !GG82563_KMCR_PASS_FALSE_CARRIER;
        self.write_phy_reg(info, GG82563_PHY_KMRN_MODE_CTRL, reg_data)?;

        Ok(())
    }

    /// Configure the MAC-to-PHY interface for 10/100Mbps
    fn configure_kmrn_for_10_100(
        &mut self,
        info: &PCIeInfo,
        duplex: Duplex,
    ) -> Result<(), IgbDriverErr> {
        self.write_kmrn_reg(
            info,
            KUMCTRLSTA_OFFSET_HD_CTRL,
            KUMCTRLSTA_HD_CTRL_10_100_DEFAULT,
        )?;

        // Configure Transmit Inter-Packet Gap
        let mut tipg = read_reg(info, TIPG)?;
        tipg &= !TIPG_IPGT_MASK;
        tipg |= DEFAULT_80003ES2LAN_TIPG_IPGT_10_100;
        write_reg(info, TIPG, tipg)?;

        let mut reg_data = self.read_phy_reg(info, GG82563_PHY_KMRN_MODE_CTRL)?;

        if duplex == Duplex::Half {
            reg_data |= GG82563_KMCR_PASS_FALSE_CARRIER;
        } else {
            reg_data &= !GG82563_KMCR_PASS_FALSE_CARRIER;
        }

        self.write_phy_reg(info, GG82563_PHY_KMRN_MODE_CTRL, reg_data)?;

        Ok(())
    }

    /// Work-around for 82566 Kumeran PCS lock loss:
    /// On link status change (i.e. PCI reset, speed change) and link is up and
    /// speed is gigabit-
    /// 0) if workaround is optionally disabled do nothing
    /// 1) wait 1ms for Kumeran link to come up
    /// 2) check Kumeran Diagnostic register PCS lock loss bit
    /// 3) if not set the link is locked (all is good), otherwise...
    /// 4) reset the PHY
    /// 5) repeat up to 10 times
    /// Note: this is only called for IGP3 copper when speed is 1gb.
    fn kumeran_lock_loss_workaround(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        // Make sure link is up before proceeding.  If not just return.
        // Attempting this while link is negotiating fouled up link stability
        self.read_phy_reg(info, PHY_STATUS)?;
        let phy_data = self.read_phy_reg(info, PHY_STATUS)?;

        if phy_data & MII_SR_LINK_STATUS != 0 {
            for _ in 0..10 {
                // read once to clear
                self.read_phy_reg(info, IGP3_KMRN_DIAG)?;

                // and again to get new status
                let phy_data = self.read_phy_reg(info, IGP3_KMRN_DIAG)?;

                // check for PCS lock
                if phy_data & IGP3_KMRN_DIAG_PCS_LOCK_LOSS == 0 {
                    return Ok(());
                }

                // Issue PHY reset
                self.phy_hw_reset(info)?;
                awkernel_lib::delay::wait_millisec(5);
            }

            // Disable GigE link negotiation
            let mut reg = read_reg(info, PHY_CTRL as usize)?;
            reg |= PHY_CTRL_GBE_DISABLE | PHY_CTRL_NOND0A_GBE_DISABLE;
            write_reg(info, PHY_CTRL as usize, reg)?;

            // unable to acquire PCS lock
            return Err(IgbDriverErr::Phy);
        }

        Ok(())
    }

    /// 82541_rev_2 & 82547_rev_2 have the capability to configure the DSP when a
    /// gigabit link is achieved to improve link quality.
    fn config_dsp_after_link_change(
        &mut self,
        info: &PCIeInfo,
        link_up: bool,
    ) -> Result<(), IgbDriverErr> {
        if self.phy_type != PhyType::Igp {
            return Ok(());
        }

        let dsp_reg_array = [
            IGP01E1000_PHY_AGC_PARAM_A,
            IGP01E1000_PHY_AGC_PARAM_B,
            IGP01E1000_PHY_AGC_PARAM_C,
            IGP01E1000_PHY_AGC_PARAM_D,
        ];

        if link_up {
            let (speed, _duplex) = self.get_speed_and_duplex(info)?;

            if speed == Speed::S1000Mbps {
                let (min_length, _max_length) = self.get_cable_length(info)?;

                if self.dsp_config_state == DspConfigState::Enabled
                    && min_length >= IGP_CABLE_LENGTH_50
                {
                    for reg in dsp_reg_array.iter() {
                        let mut phy_data = self.read_phy_reg(info, *reg)?;
                        phy_data &= !IGP01E1000_PHY_EDAC_MU_INDEX;
                        self.write_phy_reg(info, *reg, phy_data)?;
                    }
                    self.dsp_config_state = DspConfigState::Activated;
                }

                if self.ffe_config_state == FfeConfig::Enabled && min_length < IGP_CABLE_LENGTH_50 {
                    let mut ffe_idle_err_timeout = FFE_IDLE_ERR_COUNT_TIMEOUT_20;
                    let mut idle_errs = 0;

                    // clear previous idle error counts
                    self.read_phy_reg(info, PHY_1000T_STATUS)?;

                    let mut i = 0;
                    while i < ffe_idle_err_timeout {
                        awkernel_lib::delay::wait_millisec(1);
                        let phy_data = self.read_phy_reg(info, PHY_1000T_STATUS)?;

                        idle_errs += phy_data & SR_1000T_IDLE_ERROR_CNT;
                        if idle_errs > SR_1000T_PHY_EXCESSIVE_IDLE_ERR_COUNT {
                            self.ffe_config_state = FfeConfig::Active;

                            self.write_phy_reg(
                                info,
                                IGP01E1000_PHY_DSP_FFE,
                                IGP01E1000_PHY_DSP_FFE_CM_CP,
                            )?;

                            break;
                        }

                        if idle_errs != 0 {
                            ffe_idle_err_timeout = FFE_IDLE_ERR_COUNT_TIMEOUT_100;
                        }

                        i += 1;
                    }
                }
            }
        } else {
            if self.dsp_config_state == DspConfigState::Activated {
                // Save off the current value of register 0x2F5B to
                // be restored at the end of the routines.
                let phy_saved_data = self.read_phy_reg(info, 0x2F5B)?;

                // Disable the PHY transmitter
                self.write_phy_reg(info, 0x2F5B, 0x0003)?;

                awkernel_lib::delay::wait_microsec(20);

                self.write_phy_reg(info, 0x000, IGP01E1000_IEEE_FORCE_GIGA)?;

                for reg in dsp_reg_array.iter() {
                    let mut phy_data = self.read_phy_reg(info, *reg)?;

                    phy_data &= !IGP01E1000_PHY_EDAC_MU_INDEX;
                    phy_data |= IGP01E1000_PHY_EDAC_SIGN_EXT_9_BITS;

                    self.write_phy_reg(info, *reg, phy_data)?;
                }

                self.write_phy_reg(info, 0x0000, IGP01E1000_IEEE_RESTART_AUTONEG)?;

                awkernel_lib::delay::wait_microsec(20);

                // Now enable the transmitter
                self.write_phy_reg(info, 0x2F5B, phy_saved_data)?;

                self.dsp_config_state = DspConfigState::Enabled;
            }

            if self.ffe_config_state == FfeConfig::Active {
                // Save off the current value of register 0x2F5B to
                // be restored at the end of the routines.
                let phy_saved_data = self.read_phy_reg(info, 0x2F5B)?;

                // Disable the PHY transmitter
                self.write_phy_reg(info, 0x2F5B, 0x0003)?;

                awkernel_lib::delay::wait_microsec(20);

                self.write_phy_reg(info, 0x000, IGP01E1000_IEEE_FORCE_GIGA)?;
                self.write_phy_reg(info, IGP01E1000_PHY_DSP_FFE, IGP01E1000_PHY_DSP_FFE_DEFAULT)?;
                self.write_phy_reg(info, 0x0000, IGP01E1000_IEEE_RESTART_AUTONEG)?;

                awkernel_lib::delay::wait_microsec(20);

                // Now enable the transmitter
                self.write_phy_reg(info, 0x2F5B, phy_saved_data)?;

                self.ffe_config_state = FfeConfig::Enabled;
            }
        }

        Ok(())
    }

    /// Estimates the cable length.
    ///
    /// This function always returns a ranged length (minimum & maximum).
    /// So for M88 phy's, this function interprets the one value returned from the
    /// register to the minimum and maximum range.
    /// For IGP phy's, the function calculates the range by the AGC registers.
    fn get_cable_length(&mut self, info: &PCIeInfo) -> Result<(u16, u16), IgbDriverErr> {
        use PhyType::*;

        // Use old method for Phy older than IGP
        if matches!(self.phy_type, M88 | Oem | I82578) {
            let phy_data = self.read_phy_reg(info, M88E1000_PHY_SPEC_STATUS)?;

            let cable_length =
                (phy_data & M88E1000_PSSR_CABLE_LENGTH) >> M88E1000_PSSR_CABLE_LENGTH_SHIFT;

            // Convert the enum value to ranged values
            let (min_length, max_length) = match cable_length {
                CABLE_LENGTH_50 => (0, IGP_CABLE_LENGTH_50),
                CABLE_LENGTH_50_80 => (IGP_CABLE_LENGTH_50, IGP_CABLE_LENGTH_80),
                CABLE_LENGTH_80_110 => (IGP_CABLE_LENGTH_80, IGP_CABLE_LENGTH_110),
                CABLE_LENGTH_110_140 => (IGP_CABLE_LENGTH_110, IGP_CABLE_LENGTH_140),
                CABLE_LENGTH_140 => (IGP_CABLE_LENGTH_140, IGP_CABLE_LENGTH_170),
                _ => return Err(IgbDriverErr::Phy),
            };

            Ok((min_length, max_length))
        } else if self.phy_type == Rtl8211 {
            // no cable length info on RTL8211, fake
            Ok((0, IGP_CABLE_LENGTH_50))
        } else if self.phy_type == Gg82563 {
            let phy_data = self.read_phy_reg(info, GG82563_PHY_DSP_DISTANCE)?;

            let cable_length = phy_data & GG82563_DSPD_CABLE_LENGTH;

            let (min_length, max_length) = match cable_length {
                GG_CABLE_LENGTH_60 => (0, IGP_CABLE_LENGTH_60),
                GG_CABLE_LENGTH_60_115 => (IGP_CABLE_LENGTH_60, IGP_CABLE_LENGTH_115),
                GG_CABLE_LENGTH_115_150 => (IGP_CABLE_LENGTH_115, IGP_CABLE_LENGTH_150),
                GG_CABLE_LENGTH_150 => (IGP_CABLE_LENGTH_150, IGP_CABLE_LENGTH_180),
                _ => return Err(IgbDriverErr::Phy),
            };

            Ok((min_length, max_length))
        } else if self.phy_type == Igp {
            let agc_reg_array = [
                IGP01E1000_PHY_AGC_A,
                IGP01E1000_PHY_AGC_B,
                IGP01E1000_PHY_AGC_C,
                IGP01E1000_PHY_AGC_D,
            ];

            // Read the AGC registers for all channels
            let mut agc_value = 0;
            let mut min_agc_value = IGP01E1000_AGC_LENGTH_TABLE_SIZE;
            for reg in agc_reg_array.iter() {
                let phy_data = self.read_phy_reg(info, *reg)?;

                let cur_agc_value = phy_data >> IGP01E1000_AGC_LENGTH_SHIFT;

                // Value bound check.
                if cur_agc_value >= IGP01E1000_AGC_LENGTH_TABLE_SIZE - 1 || cur_agc_value == 0 {
                    return Err(IgbDriverErr::Phy);
                }

                agc_value += cur_agc_value;

                // Update minimal AGC value.
                if min_agc_value > cur_agc_value {
                    min_agc_value = cur_agc_value;
                }
            }

            // Remove the minimal AGC result for length < 50m
            if agc_value < IGP01E1000_PHY_CHANNEL_NUM as u16 * IGP_CABLE_LENGTH_50 {
                agc_value -= min_agc_value;

                // Get the average length of the remaining 3 channels
                agc_value /= IGP01E1000_PHY_CHANNEL_NUM as u16 - 1;
            } else {
                // Get the average length of all 4 channels
                agc_value /= IGP01E1000_PHY_CHANNEL_NUM as u16;
            }

            // Set the range of the calculated length.
            let min_length = if IGP_CABLE_LENGTH_TABLE[agc_value as usize] > IGP01E1000_AGC_RANGE {
                IGP_CABLE_LENGTH_TABLE[agc_value as usize] - IGP01E1000_AGC_RANGE
            } else {
                0
            };

            let max_length = IGP_CABLE_LENGTH_TABLE[agc_value as usize] + IGP01E1000_AGC_RANGE;

            Ok((min_length, max_length))
        } else if self.phy_type == Igp2 || self.phy_type == Igp3 {
            let agc_reg_array = [
                IGP02E1000_PHY_AGC_A,
                IGP02E1000_PHY_AGC_B,
                IGP02E1000_PHY_AGC_C,
                IGP02E1000_PHY_AGC_D,
            ];

            // Read the AGC registers for all channels
            let mut min_agc_index = IGP02E1000_AGC_LENGTH_TABLE_SIZE - 1;
            let mut max_agc_index = 0;
            let mut agc_value = 0;
            for reg in agc_reg_array.iter() {
                let phy_data = self.read_phy_reg(info, *reg)?;

                // Getting bits 15:9, which represent the combination
                // of course and fine gain values.  The result is a
                // number that can be put into the lookup table to
                // obtain the approximate cable length.
                let cur_agc_index =
                    (phy_data >> IGP02E1000_AGC_LENGTH_SHIFT) & IGP02E1000_AGC_LENGTH_MASK;

                // Array index bound check.
                if cur_agc_index >= IGP02E1000_AGC_LENGTH_TABLE_SIZE || cur_agc_index == 0 {
                    return Err(IgbDriverErr::Phy);
                }

                // Remove min & max AGC values from calculation.
                min_agc_index = if IGP_2_CABLE_LENGTH_TABLE[min_agc_index as usize]
                    > IGP_2_CABLE_LENGTH_TABLE[cur_agc_index as usize]
                {
                    cur_agc_index
                } else {
                    min_agc_index
                };

                max_agc_index = if IGP_2_CABLE_LENGTH_TABLE[max_agc_index as usize]
                    < IGP_2_CABLE_LENGTH_TABLE[cur_agc_index as usize]
                {
                    cur_agc_index
                } else {
                    max_agc_index
                };

                agc_value += IGP_2_CABLE_LENGTH_TABLE[cur_agc_index as usize];
            }

            agc_value -= IGP_2_CABLE_LENGTH_TABLE[min_agc_index as usize]
                + IGP_2_CABLE_LENGTH_TABLE[max_agc_index as usize];
            agc_value /= IGP02E1000_PHY_CHANNEL_NUM as u16 - 2;

            // Calculate cable length with the error range of +/- 10 meters.
            let min_length = if agc_value > IGP02E1000_AGC_RANGE {
                agc_value - IGP02E1000_AGC_RANGE
            } else {
                0
            };

            let max_length = agc_value + IGP02E1000_AGC_RANGE;

            Ok((min_length, max_length))
        } else {
            Ok((0, 0))
        }
    }

    /// Force PHY speed and duplex settings to hw->forced_speed_duplex
    fn phy_force_speed_duplex(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use PhyType::*;

        // Turn off Flow control if we are forcing speed and duplex.
        self.fc = FC_NONE;

        // Read the Device Control Register.
        let mut ctrl = read_reg(info, CTRL)?;

        // Set the bits to Force Speed and Duplex in the Device Ctrl Reg.
        ctrl |= CTRL_FRCSPD | CTRL_FRCDPX;
        ctrl &= !(DEVICE_SPEED_MASK);

        // Clear the Auto Speed Detect Enable bit.
        ctrl &= !CTRL_ASDE;

        // Read the MII Control Register.
        let mut mii_ctrl_reg = self.read_phy_reg(info, PHY_CTRL)?;

        // We need to disable autoneg in order to force link and duplex.

        mii_ctrl_reg &= !MII_CR_AUTO_NEG_EN;

        // Are we forcing Full or Half Duplex?
        if self.forced_speed_duplex == SpeedDuplex::S100Full
            || self.forced_speed_duplex == SpeedDuplex::S10Full
        {
            // We want to force full duplex so we SET the full duplex
            // bits in the Device and MII Control Registers.
            ctrl |= CTRL_FD;
            mii_ctrl_reg |= MII_CR_FULL_DUPLEX;
        } else {
            // We want to force half duplex so we CLEAR the full duplex
            // bits in the Device and MII Control Registers.
            ctrl &= !CTRL_FD;
            mii_ctrl_reg &= !MII_CR_FULL_DUPLEX;
        }

        // Are we forcing 100Mbps???
        if self.forced_speed_duplex == SpeedDuplex::S100Full
            || self.forced_speed_duplex == SpeedDuplex::S100Half
        {
            // Set the 100Mb bit and turn off the 1000Mb and 10Mb bits.
            ctrl |= CTRL_SPD_100;
            mii_ctrl_reg |= MII_CR_SPEED_100;
            mii_ctrl_reg &= !(MII_CR_SPEED_1000 | MII_CR_SPEED_10);
        } else {
            // Set the 10Mb bit and turn off the 1000Mb and 100Mb bits.
            ctrl &= !(CTRL_SPD_1000 | CTRL_SPD_100);
            mii_ctrl_reg |= MII_CR_SPEED_10;
            mii_ctrl_reg &= !(MII_CR_SPEED_1000 | MII_CR_SPEED_100);
        }

        self.config_collision_dist(info)?;

        // Write the configured values back to the Device Control Reg.
        write_reg(info, CTRL, ctrl)?;

        if matches!(self.phy_type, M88 | Gg82563 | Bm | Oem | I82578) {
            let mut phy_data = self.read_phy_reg(info, M88E1000_PHY_SPEC_CTRL)?;

            // Clear Auto-Crossover to force MDI manually. M88E1000
            // requires MDI forced whenever speed are duplex are forced.
            phy_data &= !M88E1000_PSCR_AUTO_X_MODE;
            self.write_phy_reg(info, M88E1000_PHY_SPEC_CTRL, phy_data)?;

            // Need to reset the PHY or these changes will be ignored
            mii_ctrl_reg |= MII_CR_RESET;
        } else if self.phy_type == Rtl8211 {
            let mut phy_data = self.read_phy_reg_ex(info, RGEPHY_CR)?;

            // Clear Auto-Crossover to force MDI manually. RTL8211 requires
            // MDI forced whenever speed are duplex are forced.
            phy_data |= RGEPHY_CR_MDI_MASK; // enable MDIX
            self.write_phy_reg_ex(info, RGEPHY_CR, phy_data)?;
            mii_ctrl_reg |= MII_CR_RESET;
        } else if self.phy_type == Ife {
            let mut phy_data = self.read_phy_reg(info, IFE_PHY_MDIX_CONTROL)?;

            phy_data &= !IFE_PMC_AUTO_MDIX;
            phy_data &= !IFE_PMC_FORCE_MDIX;

            self.write_phy_reg(info, IFE_PHY_MDIX_CONTROL, phy_data)?;
        } else {
            // Clear Auto-Crossover to force MDI manually.  IGP requires
            // MDI forced whenever speed or duplex are forced.
            let mut phy_data = self.read_phy_reg(info, IGP01E1000_PHY_PORT_CTRL)?;

            phy_data &= !IGP01E1000_PSCR_AUTO_MDIX;
            phy_data &= !IGP01E1000_PSCR_FORCE_MDI_MDIX;

            self.write_phy_reg(info, IGP01E1000_PHY_PORT_CTRL, phy_data)?;
        }

        // Write back the modified PHY MII control register.
        self.write_phy_reg(info, PHY_CTRL, mii_ctrl_reg)?;

        awkernel_lib::delay::wait_microsec(1);

        if matches!(self.phy_type, M88 | Bm | Oem) {
            // Because we reset the PHY above, we need to re-force TX_CLK
            // in the Extended PHY Specific Control Register to 25MHz
            // clock.  This value defaults back to a 2.5MHz clock when
            // the PHY is reset.
            let mut phy_data = self.read_phy_reg(info, M88E1000_EXT_PHY_SPEC_CTRL)?;

            phy_data |= M88E1000_EPSCR_TX_CLK_25;
            self.write_phy_reg(info, M88E1000_EXT_PHY_SPEC_CTRL, phy_data)?;

            // In addition, because of the s/w reset above, we need to
            // duplex operation.
            // enable CRS on TX.  This must be set for both full and half
            let mut phy_data = self.read_phy_reg(info, M88E1000_PHY_SPEC_CTRL)?;

            if self.phy_id == M88E1141_E_PHY_ID {
                phy_data &= !M88E1000_PSCR_ASSERT_CRS_ON_TX
            } else {
                phy_data |= M88E1000_PSCR_ASSERT_CRS_ON_TX;
            }

            self.write_phy_reg(info, M88E1000_PHY_SPEC_CTRL, phy_data)?;

            if matches!(self.mac_type, MacType::Em82544 | MacType::Em82543)
                && !self.autoneg
                && matches!(
                    self.forced_speed_duplex,
                    SpeedDuplex::S10Full | SpeedDuplex::S10Half
                )
            {
                self.polarity_reversal_workaround(info)?;
            }
        } else if self.phy_type == Rtl8211 {
            // In addition, because of the s/w reset above, we need to enable
            // CRX on TX.  This must be set for both full and half duplex
            // operation.
            let mut phy_data = self.read_phy_reg_ex(info, RGEPHY_CR)?;

            phy_data &= !RGEPHY_CR_ASSERT_CRS;
            self.write_phy_reg_ex(info, RGEPHY_CR, phy_data)?;
        } else if self.phy_type == Gg82563 {
            // The TX_CLK of the Extended PHY Specific Control Register
            // defaults to 2.5MHz on a reset.  We need to re-force it
            // back to 25MHz, if we're not in a forced 10/duplex
            // configuration.
            let mut phy_data = self.read_phy_reg(info, GG82563_PHY_MAC_SPEC_CTRL)?;

            phy_data &= !GG82563_MSCR_TX_CLK_MASK;

            if matches!(
                self.forced_speed_duplex,
                SpeedDuplex::S10Full | SpeedDuplex::S10Half
            ) {
                phy_data |= GG82563_MSCR_TX_CLK_10MBPS_2_5MHZ
            } else {
                phy_data |= GG82563_MSCR_TX_CLK_1000MBPS_25MHZ;
            }

            // Also due to the reset, we need to enable CRS on Tx.
            phy_data |= GG82563_MSCR_ASSERT_CRS_ON_TX;

            self.write_phy_reg(info, GG82563_PHY_MAC_SPEC_CTRL, phy_data)?;
        }

        Ok(())
    }

    /// Setup auto-negotiation and flow control advertisements,
    /// and then perform auto-negotiation.
    fn copper_link_autoneg(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        // Perform some bounds checking on the hw->autoneg_advertised
        // parameter.  If this variable is zero, then set it to the default.
        self.autoneg_advertised &= AUTONEG_ADVERTISE_SPEED_DEFAULT;

        // If autoneg_advertised is zero, we assume it was not defaulted by
        // the calling code so we set to advertise full capability.
        if self.autoneg_advertised == 0 {
            self.autoneg_advertised = AUTONEG_ADVERTISE_SPEED_DEFAULT;
        }

        // IFE phy only supports 10/100
        if self.phy_type == PhyType::Ife {
            self.autoneg_advertised &= AUTONEG_ADVERTISE_10_100_ALL;
        }

        self.phy_setup_autoneg(info)?;

        // Restart auto-negotiation by setting the Auto Neg Enable bit and
        // the Auto Neg Restart bit in the PHY control register.
        let mut phy_data = self.read_phy_reg(info, PHY_CTRL)?;

        phy_data |= MII_CR_AUTO_NEG_EN | MII_CR_RESTART_AUTO_NEG;
        self.write_phy_reg(info, PHY_CTRL, phy_data)?;

        self.get_link_status = true;

        Ok(())
    }

    pub fn set_get_link_status(&mut self, flag: bool) {
        self.get_link_status = flag;
    }

    /// Configures PHY autoneg and flow control advertisement settings
    fn phy_setup_autoneg(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        // Read the MII Auto-Neg Advertisement Register (Address 4).
        let mut mii_autoneg_adv_reg = self.read_phy_reg(info, PHY_AUTONEG_ADV)?;

        let mut mii_1000t_ctrl_reg = if self.phy_type != PhyType::Ife {
            // Read the MII 1000Base-T Control Register (Address 9).
            self.read_phy_reg(info, PHY_1000T_CTRL)?
        } else {
            0
        };

        // Need to parse both autoneg_advertised and fc and set up the
        // appropriate PHY registers.  First we will parse for
        // autoneg_advertised software override.  Since we can advertise a
        // plethora of combinations, we need to check each bit individually.

        // First we clear all the 10/100 mb speed bits in the Auto-Neg
        // Advertisement Register (Address 4) and the 1000 mb speed bits in
        // the  1000Base-T Control Register (Address 9).
        mii_autoneg_adv_reg &= !REG4_SPEED_MASK;
        mii_1000t_ctrl_reg &= !REG9_SPEED_MASK;

        // Do we want to advertise 10 Mb Half Duplex?
        if self.autoneg_advertised & ADVERTISE_10_HALF != 0 {
            mii_autoneg_adv_reg |= NWAY_AR_10T_HD_CAPS;
        }

        // Do we want to advertise 10 Mb Full Duplex?
        if self.autoneg_advertised & ADVERTISE_10_FULL != 0 {
            mii_autoneg_adv_reg |= NWAY_AR_10T_FD_CAPS;
        }

        // Do we want to advertise 100 Mb Half Duplex?
        if self.autoneg_advertised & ADVERTISE_100_HALF != 0 {
            mii_autoneg_adv_reg |= NWAY_AR_100TX_HD_CAPS;
        }

        // Do we want to advertise 100 Mb Full Duplex?
        if self.autoneg_advertised & ADVERTISE_100_FULL != 0 {
            mii_autoneg_adv_reg |= NWAY_AR_100TX_FD_CAPS;
        }

        // We do not allow the Phy to advertise 1000 Mb Half Duplex
        if self.autoneg_advertised & ADVERTISE_1000_HALF != 0 {
            log::warn!("Advertise 1000mb Half duplex requested, request denied!");
        }

        // Do we want to advertise 1000 Mb Full Duplex?
        if self.autoneg_advertised & ADVERTISE_1000_FULL != 0 {
            mii_1000t_ctrl_reg |= CR_1000T_FD_CAPS;
            if self.phy_type == PhyType::Ife {
                log::warn!("PhyType::Ife is a 10/100 PHY. Gigabit speed is not supported.");
            }
        }

        // Check for a software override of the flow control settings, and
        // setup the PHY advertisement registers accordingly.  If
        // auto-negotiation is enabled, then software will have to set the
        // "PAUSE" bits to the correct value in the Auto-Negotiation
        // Advertisement Register (PHY_AUTONEG_ADV) and re-start
        // auto-negotiation.
        //
        // The possible values of the "fc" parameter are: 0:  Flow control is
        // completely disabled 1:  Rx flow control is enabled (we can receive
        // pause frames but not send pause frames). 2:  Tx flow control is
        // enabled (we can send pause frames but we do not support receiving
        // pause frames). 3:  Both Rx and TX flow control (symmetric) are
        // enabled. other:  No software override.  The flow control
        // configuration in the EEPROM is used.

        match self.fc {
            FC_NONE => {
                // Flow control is completely disabled.
                mii_autoneg_adv_reg &= !(NWAY_AR_ASM_DIR | NWAY_AR_PAUSE);
            }
            FC_RX_PAUSE => {
                // RX Flow control is enabled, and TX Flow control is
                // disabled, by a software over-ride.
                //
                // Since there really isn't a way to advertise that we are
                // capable of RX Pause ONLY, we will advertise that we
                // support both symmetric and asymmetric RX PAUSE.  Later (in
                // em_config_fc_after_link_up) we will disable the hw's
                // ability to send PAUSE frames.
                mii_autoneg_adv_reg |= NWAY_AR_ASM_DIR | NWAY_AR_PAUSE;
            }
            FC_TX_PAUSE => {
                // TX Flow control is enabled, and RX Flow control is
                // disabled, by a software over-ride.
                mii_autoneg_adv_reg |= NWAY_AR_ASM_DIR;
                mii_autoneg_adv_reg &= !NWAY_AR_PAUSE;
            }
            FC_FULL => {
                // Flow control is enabled, both TX and RX, by a software
                // over-ride.
                mii_autoneg_adv_reg |= NWAY_AR_ASM_DIR | NWAY_AR_PAUSE;
            }
            _ => return Err(IgbDriverErr::Config),
        }

        self.write_phy_reg(info, PHY_AUTONEG_ADV, mii_autoneg_adv_reg)?;

        if self.phy_type != PhyType::Ife {
            self.write_phy_reg(info, PHY_1000T_CTRL, mii_1000t_ctrl_reg)?;
        }

        Ok(())
    }

    fn polarity_reversal_workaround(&mut self, _info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        Err(IgbDriverErr::NotSupported)
    }

    /// Make sure we have a valid PHY and change PHY mode before link setup.
    fn copper_link_preconfig(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        let ctrl = read_reg(info, CTRL)?;

        // With 82543, we need to force speed and duplex on the MAC equal to
        // what the PHY speed and duplex configuration is. In addition, we
        // need to perform a hardware reset on the PHY to take it out of
        // reset.
        if self.mac_type as u32 > Em82543 as u32 {
            let mut ctrl = ctrl | CTRL_SLU;
            ctrl &= !(CTRL_FRCSPD | CTRL_FRCDPX);
            write_reg(info, CTRL, ctrl)?;
        } else {
            let ctrl = ctrl | CTRL_FRCSPD | CTRL_FRCDPX | CTRL_SLU;
            write_reg(info, CTRL, ctrl)?;
            self.phy_hw_reset(info)?;
        }

        // Set PHY to class A mode (if necessary)
        self.set_phy_mode(info)?;

        if self.mac_type == Em82545Rev3 || self.mac_type == Em82546Rev3 {
            let mut phy_data = self.read_phy_reg(info, M88E1000_PHY_SPEC_CTRL)?;
            phy_data |= 0x00000008;
            self.write_phy_reg(info, M88E1000_PHY_SPEC_CTRL, phy_data)?;
        }

        if (self.mac_type as u32) <= Em82543 as u32
            || self.mac_type == Em82541
            || self.mac_type == Em82547
            || self.mac_type == Em82541Rev2
            || self.mac_type == Em82547Rev2
        {
            self.phy_reset_disable = false;
        }

        if (self.mac_type == Em82575
            || self.mac_type == Em82580
            || self.mac_type == Em82576
            || self.mac_type == EmI210
            || self.mac_type == EmI350)
            && self.sgmii_active
        {
            // allow time for SFP cage time to power up phy
            awkernel_lib::delay::wait_millisec(300);

            // SFP documentation requires the following to configure the SFP module
            // to work on SGMII.  No further documentation is given.
            self.write_phy_reg(info, 0x1B, 0x8084)?;
            self.phy_hw_reset(info)?;
        }

        Ok(())
    }

    /// Set PHY to class A mode
    /// Assumes the following operations will follow to enable the new class mode.
    ///  1. Do a PHY soft reset
    ///  2. Restart auto-negotiation or force link.
    fn set_phy_mode(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if self.mac_type == Em82545Rev3 && self.media_type == MediaType::Copper {
            let mut eeprom_data = [0; 1];
            self.read_eeprom(info, EEPROM_PHY_CLASS_WORD, &mut eeprom_data)?;

            if eeprom_data[0] != EEPROM_RESERVED_WORD && eeprom_data[0] & EEPROM_PHY_CLASS_A != 0 {
                self.write_phy_reg(info, M88E1000_PHY_PAGE_SELECT, 0x000B)?;
                self.write_phy_reg(info, M88E1000_PHY_GEN_CONTROL, 0x8104)?;
                self.phy_reset_disable = false;
            }
        }

        Ok(())
    }

    /// Copper link setup for em_phy_igp series.
    fn copper_link_igp_setup(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if self.phy_reset_disable {
            return Ok(());
        }

        self.phy_reset(info)?;

        // Wait 15ms for MAC to configure PHY from eeprom settings
        awkernel_lib::delay::wait_millisec(15);

        if self.mac_type != EmIch8lan && self.mac_type != EmIch9lan && self.mac_type != EmIch10lan {
            // Configure activity LED after PHY reset
            let mut led_ctrl = read_reg(info, LEDCTL)?;
            led_ctrl &= IGP_ACTIVITY_LED_MASK;
            led_ctrl |= IGP_ACTIVITY_LED_ENABLE | IGP_LED3_MODE;
            write_reg(info, LEDCTL, led_ctrl)?;
        }

        // The NVM settings will configure LPLU in D3 for IGP2 and IGP3 PHYs
        if self.phy_type == PhyType::Igp {
            // disable lplu d3 during driver init
            self.set_d3_lplu_state(info, false)?;
        }

        // disable lplu d0 during driver init
        if self.mac_type == EmPchlan
            || self.mac_type == EmPch2lan
            || self.mac_type == EmPchLpt
            || self.mac_type == EmPchSpt
            || self.mac_type == EmPchCnp
            || self.mac_type == EmPchTgp
            || self.mac_type == EmPchAdp
        {
            self.set_lplu_state_pchlan(info, false)?;
        } else {
            self.set_d0_lplu_state(info, false)?;
        }

        // Configure mdi-mdix settings
        let mut phy_data = self.read_phy_reg(info, IGP01E1000_PHY_PORT_CTRL)?;

        if self.mac_type == Em82541 || self.mac_type == Em82547 {
            self.dsp_config_state = DspConfigState::Disabled;
            // Force MDI for earlier revs of the IGP PHY
            phy_data &= !(IGP01E1000_PSCR_AUTO_MDIX | IGP01E1000_PSCR_FORCE_MDI_MDIX);
        } else {
            self.dsp_config_state = DspConfigState::Enabled;
            phy_data &= !IGP01E1000_PSCR_AUTO_MDIX;
            phy_data |= IGP01E1000_PSCR_AUTO_MDIX;
        }

        self.write_phy_reg(info, IGP01E1000_PHY_PORT_CTRL, phy_data)?;

        // set auto-master slave resolution settings
        if self.autoneg {
            let phy_ms_setting = self.master_slave;
            if self.ffe_config_state == FfeConfig::Active {
                self.ffe_config_state = FfeConfig::Enabled;
            }

            if self.dsp_config_state == DspConfigState::Activated {
                self.dsp_config_state = DspConfigState::Enabled;
            }

            // when autonegotiation advertisement is only 1000Mbps then
            // we should disable SmartSpeed and enable Auto MasterSlave
            // resolution as hardware default.
            if self.autoneg_advertised == ADVERTISE_1000_FULL {
                // Disabled SmartSpeed
                let mut phy_data = self.read_phy_reg(info, IGP01E1000_PHY_PORT_CONFIG)?;
                phy_data &= !IGP01E1000_PSCFR_SMART_SPEED;
                self.write_phy_reg(info, IGP01E1000_PHY_PORT_CONFIG, phy_data)?;

                // Set auto Master/Slave resolution process
                let mut phy_data = self.read_phy_reg(info, PHY_1000T_CTRL)?;
                phy_data &= !CR_1000T_MS_ENABLE;
                self.write_phy_reg(info, PHY_1000T_CTRL, phy_data)?;
            }

            let mut phy_data = self.read_phy_reg(info, PHY_1000T_CTRL)?;

            // load defaults for future use
            self.original_master_slave = if phy_data & CR_1000T_MS_ENABLE != 0 {
                if phy_data & CR_1000T_MS_VALUE != 0 {
                    MSType::ForceMaster
                } else {
                    MSType::ForceSlave
                }
            } else {
                MSType::Auto
            };

            match phy_ms_setting {
                MSType::ForceMaster => {
                    phy_data |= CR_1000T_MS_ENABLE | CR_1000T_MS_VALUE;
                }
                MSType::ForceSlave => {
                    phy_data |= CR_1000T_MS_ENABLE;
                    phy_data &= !CR_1000T_MS_VALUE;
                }
                MSType::Auto => {
                    phy_data &= !CR_1000T_MS_ENABLE;
                }
                _ => (),
            }

            self.write_phy_reg(info, PHY_1000T_CTRL, phy_data)?;
        }

        Ok(())
    }

    /// This function sets the lplu d0 state according to the active flag.  When
    /// activating lplu this function also disables smart speed and vise versa.
    /// lplu will not be activated unless the device autonegotiation advertisement
    /// meets standards of either 10 or 10/100 or 10/100/1000 at all duplexes.
    fn set_d0_lplu_state(&mut self, info: &PCIeInfo, active: bool) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if (self.mac_type as u32) <= Em82547Rev2 as u32 {
            return Ok(());
        }

        fn active_post(hw: &mut IgbHw, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
            // When LPLU is enabled we should disable SmartSpeed
            let mut phy_data = hw.read_phy_reg(info, IGP01E1000_PHY_PORT_CONFIG)?;
            phy_data &= !IGP01E1000_PSCFR_SMART_SPEED;
            hw.write_phy_reg(info, IGP01E1000_PHY_PORT_CONFIG, phy_data)?;
            Ok(())
        }

        if is_ich8(&self.mac_type) {
            let mut phy_ctrl = read_reg(info, PHY_CTRL as usize)?;
            if active {
                phy_ctrl |= PHY_CTRL_D0A_LPLU;
                write_reg(info, PHY_CTRL as usize, phy_ctrl)?;
                active_post(self, info)?;
            } else {
                phy_ctrl &= !PHY_CTRL_D0A_LPLU;
                write_reg(info, PHY_CTRL as usize, phy_ctrl)?;
            }
        } else {
            let mut phy_data = self.read_phy_reg(info, IGP02E1000_PHY_POWER_MGMT)?;
            if active {
                phy_data |= IGP02E1000_PM_D0_LPLU;
                self.write_phy_reg(info, IGP02E1000_PHY_POWER_MGMT, phy_data)?;
                active_post(self, info)?;
            } else {
                phy_data &= !IGP02E1000_PM_D0_LPLU;
                self.write_phy_reg(info, IGP02E1000_PHY_POWER_MGMT, phy_data)?;
            }
        }

        Ok(())
    }

    /// This function sets the lplu state according to the active flag.  When
    /// activating lplu this function also disables smart speed and vise versa.
    /// lplu will not be activated unless the device autonegotiation advertisement
    /// meets standards of either 10 or 10/100 or 10/100/1000 at all duplexes.
    fn set_d3_lplu_state(&mut self, info: &PCIeInfo, active: bool) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if self.phy_type != PhyType::Igp
            && self.phy_type != PhyType::Igp2
            && self.phy_type != PhyType::Igp3
        {
            return Ok(());
        }

        fn active_post(hw: &mut IgbHw, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
            // When LPLU is enabled we should disable SmartSpeed
            let mut phy_data = hw.read_phy_reg(info, IGP01E1000_PHY_PORT_CONFIG)?;
            phy_data &= !IGP01E1000_PSCFR_SMART_SPEED;
            hw.write_phy_reg(info, IGP01E1000_PHY_PORT_CONFIG, phy_data)?;
            Ok(())
        }

        // During driver activity LPLU should not be used or it will attain
        // link from the lowest speeds starting from 10Mbps. The capability
        // is used for Dx transitions and states
        if matches!(self.mac_type, Em82541Rev2 | Em82547Rev2) {
            let mut phy_data = self.read_phy_reg(info, IGP01E1000_GMII_FIFO)?;

            if !active {
                phy_data &= !IGP01E1000_GMII_FLEX_SPD;
                self.write_phy_reg(info, IGP01E1000_GMII_FIFO, phy_data)?;
            } else if self.autoneg_advertised == AUTONEG_ADVERTISE_SPEED_DEFAULT
                || self.autoneg_advertised == AUTONEG_ADVERTISE_10_ALL
                || self.autoneg_advertised == AUTONEG_ADVERTISE_10_100_ALL
            {
                phy_data |= IGP01E1000_GMII_FLEX_SPD;
                self.write_phy_reg(info, IGP01E1000_GMII_FIFO, phy_data)?;

                active_post(self, info)?;
            }
        } else if is_ich8(&self.mac_type) {
            // MAC writes into PHY register based on the state transition
            // and start auto-negotiation. SW driver can overwrite the
            // settings in CSR PHY power control E1000_PHY_CTRL register.
            let mut phy_ctrl = read_reg(info, PHY_CTRL as usize)?;

            if !active {
                phy_ctrl &= !PHY_CTRL_NOND0A_LPLU;
                write_reg(info, PHY_CTRL as usize, phy_ctrl)?;
            } else if self.autoneg_advertised == AUTONEG_ADVERTISE_SPEED_DEFAULT
                || self.autoneg_advertised == AUTONEG_ADVERTISE_10_ALL
                || self.autoneg_advertised == AUTONEG_ADVERTISE_10_100_ALL
            {
                phy_ctrl |= PHY_CTRL_NOND0A_LPLU;
                write_reg(info, PHY_CTRL as usize, phy_ctrl)?;

                active_post(self, info)?;
            }
        } else {
            let mut phy_data = self.read_phy_reg(info, IGP02E1000_PHY_POWER_MGMT)?;

            if !active {
                phy_data &= !IGP02E1000_PM_D3_LPLU;
                self.write_phy_reg(info, IGP02E1000_PHY_POWER_MGMT, phy_data)?;
            } else if self.autoneg_advertised == AUTONEG_ADVERTISE_SPEED_DEFAULT
                || self.autoneg_advertised == AUTONEG_ADVERTISE_10_ALL
                || self.autoneg_advertised == AUTONEG_ADVERTISE_10_100_ALL
            {
                phy_data |= IGP02E1000_PM_D3_LPLU;
                self.write_phy_reg(info, IGP02E1000_PHY_POWER_MGMT, phy_data)?;

                active_post(self, info)?;
            }
        }

        Ok(())
    }

    /// Copper link setup for em_phy_m88 series.
    fn copper_link_mgp_setup(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if self.phy_reset_disable {
            return Ok(());
        }

        // disable lplu d0 during driver init
        if matches!(
            self.mac_type,
            EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp
        ) {
            self.set_lplu_state_pchlan(info, false)?;
        }

        // Enable CRS on TX. This must be set for half-duplex operation.
        let mut phy_data = self.read_phy_reg(info, M88E1000_PHY_SPEC_CTRL)?;
        if self.phy_id == M88E1141_E_PHY_ID {
            phy_data |= 0x00000008;
            self.write_phy_reg(info, M88E1000_PHY_SPEC_CTRL, phy_data)?;
            phy_data = self.read_phy_reg(info, M88E1000_PHY_SPEC_CTRL)?;
            phy_data &= !M88E1000_PSCR_ASSERT_CRS_ON_TX;
        }
        // For BM PHY this bit is downshift enable
        else if self.phy_type != PhyType::Bm {
            phy_data |= M88E1000_PSCR_ASSERT_CRS_ON_TX;
        }

        // Options: MDI/MDI-X = 0 (default) 0 - Auto for all speeds 1 - MDI
        // mode 2 - MDI-X mode 3 - Auto for 1000Base-T only (MDI-X for
        // 10/100Base-T modes)
        phy_data &= !M88E1000_PSCR_AUTO_X_MODE;
        phy_data |= M88E1000_PSCR_AUTO_X_MODE;

        // Options: disable_polarity_correction = 0 (default) Automatic
        // Correction for Reversed Cable Polarity 0 - Disabled 1 - Enabled
        phy_data &= !M88E1000_PSCR_POLARITY_REVERSAL;

        // Enable downshift on BM (disabled by default)
        if self.phy_type == PhyType::Bm {
            phy_data |= BME1000_PSCR_ENABLE_DOWNSHIFT;
        }

        self.write_phy_reg(info, M88E1000_PHY_SPEC_CTRL, phy_data)?;

        let phy_revision = self.phy_revision.ok_or(IgbDriverErr::Phy)?;

        if (self.phy_type == PhyType::M88
            && phy_revision < M88E1011_I_REV_4
            && self.phy_id != BME1000_E_PHY_ID)
            || self.phy_type == PhyType::Oem
        {
            // Force TX_CLK in the Extended PHY Specific Control Register
            // to 25MHz clock
            phy_data = self.read_phy_reg(info, M88E1000_EXT_PHY_SPEC_CTRL)?;

            if self.phy_type == PhyType::Oem {
                phy_data |= M88E1000_EPSCR_TX_TIME_CTRL;
                phy_data |= M88E1000_EPSCR_RX_TIME_CTRL;
            }

            phy_data |= M88E1000_EPSCR_TX_CLK_25;

            if phy_revision == E1000_REVISION_2 && self.phy_id == M88E1111_I_PHY_ID {
                // Vidalia Phy, set the downshift counter to 5x
                phy_data &= !M88EC018_EPSCR_DOWNSHIFT_COUNTER_MASK;
                phy_data |= M88EC018_EPSCR_DOWNSHIFT_COUNTER_5X;
                self.write_phy_reg(info, M88E1000_EXT_PHY_SPEC_CTRL, phy_data)?;
            } else {
                // Configure Master and Slave downshift values
                phy_data &=
                    !(M88E1000_EPSCR_MASTER_DOWNSHIFT_MASK | M88E1000_EPSCR_SLAVE_DOWNSHIFT_MASK);
                phy_data |= M88E1000_EPSCR_MASTER_DOWNSHIFT_1X | M88E1000_EPSCR_SLAVE_DOWNSHIFT_1X;
                self.write_phy_reg(info, M88E1000_EXT_PHY_SPEC_CTRL, phy_data)?;
            }
        }

        if self.phy_type == PhyType::Bm && phy_revision == 1 {
            // Set PHY page 0, register 29 to 0x0003
            // The next two writes are supposed to lower BER for gig connection
            self.write_phy_reg(info, BM_REG_BIAS1, 0x0003)?;

            // Set PHY page 0, register 30 to 0x0000
            self.write_phy_reg(info, BM_REG_BIAS2, 0x0000)?;
        }

        if self.phy_type == PhyType::I82578 {
            phy_data = self.read_phy_reg(info, M88E1000_EXT_PHY_SPEC_CTRL)?;

            // 82578 PHY - set the downshift count to 1x.
            phy_data |= I82578_EPSCR_DOWNSHIFT_ENABLE;
            phy_data &= !I82578_EPSCR_DOWNSHIFT_COUNTER_MASK;
            self.write_phy_reg(info, M88E1000_EXT_PHY_SPEC_CTRL, phy_data)?;
        }

        // SW Reset the PHY so all changes take effect
        self.phy_reset(info)?;

        Ok(())
    }

    /// Copper link setup for em_phy_gg82563 series.
    fn copper_link_ggp_setup(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if !self.phy_reset_disable {
            // Enable CRS on TX for half-duplex operation.
            let mut phy_data = self.read_phy_reg(info, GG82563_PHY_MAC_SPEC_CTRL)?;

            phy_data |= GG82563_MSCR_ASSERT_CRS_ON_TX;
            // Use 25MHz for both link down and 1000BASE-T for Tx clock
            phy_data |= GG82563_MSCR_TX_CLK_1000MBPS_25MHZ;

            self.write_phy_reg(info, GG82563_PHY_MAC_SPEC_CTRL, phy_data)?;

            // Options: MDI/MDI-X = 0 (default) 0 - Auto for all speeds 1
            // - MDI mode 2 - MDI-X mode 3 - Auto for 1000Base-T only
            // (MDI-X for 10/100Base-T modes)
            phy_data = self.read_phy_reg(info, GG82563_PHY_SPEC_CTRL)?;
            phy_data &= !GG82563_PSCR_CROSSOVER_MODE_MASK;
            phy_data |= GG82563_PSCR_CROSSOVER_MODE_AUTO;

            // Options: disable_polarity_correction = 0 (default)
            // Automatic Correction for Reversed Cable Polarity 0 -
            // Disabled 1 - Enabled
            phy_data &= !GG82563_PSCR_POLARITY_REVERSAL_DISABLE;
            self.write_phy_reg(info, GG82563_PHY_SPEC_CTRL, phy_data)?;

            // SW Reset the PHY so all changes take effect
            self.phy_reset(info)?;
        }

        if self.mac_type == MacType::Em80003es2lan {
            // Bypass RX and TX FIFO's
            self.write_kmrn_reg(
                info,
                KUMCTRLSTA_OFFSET_FIFO_CTRL,
                KUMCTRLSTA_FIFO_CTRL_RX_BYPASS | KUMCTRLSTA_FIFO_CTRL_TX_BYPASS,
            )?;

            let mut phy_data = self.read_phy_reg(info, GG82563_PHY_SPEC_CTRL_2)?;
            phy_data &= !GG82563_PSCR2_REVERSE_AUTO_NEG;
            self.write_phy_reg(info, GG82563_PHY_SPEC_CTRL_2, phy_data)?;

            let mut reg_data = read_reg(info, CTRL_EXT)?;
            reg_data &= !CTRL_EXT_LINK_MODE_MASK;
            write_reg(info, CTRL_EXT, reg_data)?;

            // Do not init these registers when the HW is in IAMT mode,
            // since the firmware will have already initialized them. We
            // only initialize them if the HW is not in IAMT mode.
            if self.check_mng_mode(info)? {
                // Enable Electrical Idle on the PHY
                phy_data = self.read_phy_reg(info, GG82563_PHY_PWR_MGMT_CTRL)?;
                phy_data |= GG82563_PMCR_ENABLE_ELECTRICAL_IDLE;
                self.write_phy_reg(info, GG82563_PHY_PWR_MGMT_CTRL, phy_data)?;

                phy_data = self.read_phy_reg(info, GG82563_PHY_KMRN_MODE_CTRL)?;
                phy_data &= !GG82563_KMCR_PASS_FALSE_CARRIER;
                self.write_phy_reg(info, GG82563_PHY_KMRN_MODE_CTRL, phy_data)?;
            }

            // Workaround: Disable padding in Kumeran interface in the
            // MAC and in the PHY to avoid CRC errors.
            phy_data = self.read_phy_reg(info, GG82563_PHY_INBAND_CTRL)?;
            phy_data |= GG82563_ICR_DIS_PADDING;
            self.write_phy_reg(info, GG82563_PHY_INBAND_CTRL, phy_data)?;
        }

        Ok(())
    }

    /// This function checks the mode of the firmware.
    fn check_mng_mode(&mut self, info: &PCIeInfo) -> Result<bool, IgbDriverErr> {
        let fwsm = read_reg(info, FWSM)?;

        if is_ich8(&self.mac_type) {
            if (fwsm & FWSM_MODE_MASK) == (MNG_ICH_IAMT_MODE << FWSM_MODE_SHIFT) {
                return Ok(true);
            }
        } else if (fwsm & FWSM_MODE_MASK) == (MNG_IAMT_MODE << FWSM_MODE_SHIFT) {
            return Ok(true);
        }

        Ok(false)
    }

    /// Copper link setup for em_phy_82577 series.
    fn copper_link_82577_setup(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if self.phy_reset_disable {
            return Ok(());
        }

        // Enable CRS on TX for half-duplex operation.
        let mut phy_data = self.read_phy_reg(info, I82577_PHY_CFG_REG)?;

        phy_data |= I82577_PHY_CFG_ENABLE_CRS_ON_TX | I82577_PHY_CFG_ENABLE_DOWNSHIFT;

        self.write_phy_reg(info, I82577_PHY_CFG_REG, phy_data)?;

        // Wait 15ms for MAC to configure PHY from eeprom settings
        awkernel_lib::delay::wait_millisec(15);

        // disable lplu d0 during driver init
        self.set_lplu_state_pchlan(info, false)?;

        write_reg(info, LEDCTL, self.ledctl_mode1)?;

        Ok(())
    }

    /// Set Low Power Link Up state
    ///
    /// Sets the LPLU state according to the active flag.  For PCH, if OEM write
    /// bit are disabled in the NVM, writing the LPLU bits in the MAC will not set
    /// the phy speed. This function will manually set the LPLU bit and restart
    /// auto-neg as hw would do. D3 and D0 LPLU will call the same function
    /// since it configures the same bit.
    fn set_lplu_state_pchlan(&mut self, info: &PCIeInfo, active: bool) -> Result<(), IgbDriverErr> {
        let mut oem_reg = self.read_phy_reg(info, HV_OEM_BITS)?;

        if active {
            oem_reg |= HV_OEM_BITS_LPLU;
        } else {
            oem_reg &= !HV_OEM_BITS_LPLU;
        }

        oem_reg |= HV_OEM_BITS_RESTART_AN;
        self.write_phy_reg(info, HV_OEM_BITS, oem_reg)?;

        Ok(())
    }

    fn copper_link_82580_setup(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if self.phy_reset_disable {
            return Ok(());
        }

        self.phy_hw_reset(info)?;

        // Enable CRS on TX. This must be set for half-duplex operation.
        let mut phy_data = self.read_phy_reg(info, I82580_CFG_REG)?;

        phy_data |= I82580_CFG_ASSERT_CRS_ON_TX | I82580_CFG_ENABLE_DOWNSHIFT;

        self.write_phy_reg(info, I82580_CFG_REG, phy_data)?;

        Ok(())
    }

    fn copper_link_rtl8211_setup(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        // SW Reset the PHY so all changes take effect
        self.phy_hw_reset(info)?;

        // Enable CRS on TX. This must be set for half-duplex operation.

        let mut phy_data = self.read_phy_reg_ex(info, RGEPHY_CR)?;
        phy_data |= RGEPHY_CR_ASSERT_CRS;
        self.write_phy_reg_ex(info, RGEPHY_CR, phy_data)?;

        // LED Control Register 0x18
        phy_data = self.read_phy_reg_ex(info, RGEPHY_LC)?;
        phy_data &= 0x80FF; // bit-15=0 disable, clear bit 8-10
        self.write_phy_reg_ex(info, RGEPHY_LC, phy_data)?;

        // LED Control and Definition Register 0x11, PHY spec status reg
        phy_data = self.read_phy_reg_ex(info, RGEPHY_SR)?;
        phy_data |= 0x0010; // LED active Low
        self.write_phy_reg_ex(info, RGEPHY_SR, phy_data)?;
        self.read_phy_reg_ex(info, RGEPHY_SR)?;

        // Switch to Page2
        phy_data = RGEPHY_PS_PAGE_2;
        self.write_phy_reg_ex(info, RGEPHY_PS, phy_data)?;

        phy_data = 0x0000;
        self.write_phy_reg_ex(info, RGEPHY_LC_P2, phy_data)?;

        awkernel_lib::delay::wait_microsec(5);

        // LED Configuration Control Reg for setting for 0x1A Register
        phy_data = self.read_phy_reg_ex(info, RGEPHY_LC_P2)?;
        phy_data &= 0xF000;
        phy_data |= 0x0F24;
        self.write_phy_reg_ex(info, RGEPHY_LC_P2, phy_data)?;
        self.read_phy_reg_ex(info, RGEPHY_LC_P2)?;

        // After setting Page2, go back to Page 0
        phy_data = 0;
        self.write_phy_reg_ex(info, RGEPHY_PS, phy_data)?;

        // pulse streching= 42-84ms, blink rate=84mm
        phy_data = 0x140 | RGEPHY_LC_PULSE_42MS | RGEPHY_LC_LINK | RGEPHY_LC_DUPLEX | RGEPHY_LC_RX;
        self.write_phy_reg_ex(info, RGEPHY_LC, phy_data)?;

        Ok(())
    }

    /// Sets up link for a fiber based or serdes based adapter
    ///
    /// Manipulates Physical Coding Sublayer functions in order to configure
    /// link. Assumes the hardware has been previously reset and the transmitter
    /// and receiver are not enabled.
    fn setup_fiber_serdes_link(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if self.media_type != MediaType::InternalSerdes && !self.sgmii_active {
            return Err(IgbDriverErr::Config);
        }

        // On 82571 and 82572 Fiber connections, SerDes loopback mode
        // persists until explicitly turned off or a power cycle is
        // performed.  A read to the register does not indicate its status.
        // Therefore, we ensure loopback mode is disabled during
        // initialization.

        if matches!(self.mac_type, Em82571 | Em82572) || (self.mac_type as u32) >= Em82575 as u32 {
            write_reg(info, SCTL, DISABLE_SERDES_LOOPBACK)?;
        }

        if (self.mac_type as u32) >= Em82575 as u32 {
            self.power_up_serdes_link_82575(info)?;
        }

        // On adapters with a MAC newer than 82544, SWDP 1 will be set when
        // the optics detect a signal. On older adapters, it will be cleared
        // when there is a signal.  This applies to fiber media only. If
        // we're on serdes media, adjust the output amplitude to value set in
        // the EEPROM.
        let mut ctrl = read_reg(info, CTRL)?;
        let signal = if self.media_type == MediaType::Fiber {
            if (self.mac_type as u32) > Em82544 as u32 {
                CTRL_SWDPIN1
            } else {
                0
            }
        } else {
            0
        };

        self.adjust_serdes_amplitude(info)?;

        // Take the link out of reset
        ctrl &= !CTRL_LRST;

        if (self.mac_type as u32) >= Em82575 as u32 {
            // set both sw defined pins on 82575/82576
            ctrl |= CTRL_SWDPIN0 | CTRL_SWDPIN1;

            let ctrl_ext = read_reg(info, CTRL_EXT)?;
            match ctrl_ext & CTRL_EXT_LINK_MODE_MASK {
                CTRL_EXT_LINK_MODE_1000BASE_KX | CTRL_EXT_LINK_MODE_PCIE_SERDES => {
                    // the backplane is always connected
                    let mut reg = read_reg(info, PCS_LCTL)?;
                    reg |= PCS_LCTL_FORCE_FCTRL;
                    reg |= PCS_LCTL_FSV_1000 | PCS_LCTL_FDV_FULL;
                    reg |= PCS_LCTL_FSD; // Force Speed

                    write_reg(info, PCS_LCTL, reg)?;
                    self.force_mac_fc(info)?;
                    self.autoneg_failed = false;
                    return Ok(());
                }
                _ => {
                    // Set switch control to serdes energy detect
                    let mut reg = read_reg(info, CONNSW)?;
                    reg |= CONNSW_ENRGSRC;
                    write_reg(info, CONNSW, reg)?;
                }
            }
        }

        // Adjust VCO speed to improve BER performance
        self.set_vco_speed(info)?;

        self.config_collision_dist(info)?;

        // Check for a software override of the flow control settings, and
        // setup the device accordingly.  If auto-negotiation is enabled,
        // then software will have to set the "PAUSE" bits to the correct
        // value in the Tranmsit Config Word Register (TXCW) and re-start
        // auto-negotiation.  However, if auto-negotiation is disabled, then
        // software will have to manually configure the two flow control
        // enable bits in the CTRL register.
        //
        // The possible values of the "fc" parameter are: 0:  Flow control is
        // completely disabled 1:  Rx flow control is enabled (we can receive
        // pause frames, but not send pause frames). 2:  Tx flow control is
        // enabled (we can send pause frames but we do not support receiving
        // pause frames). 3:  Both Rx and TX flow control (symmetric) are
        // enabled.

        let txcw = match self.fc {
            FC_NONE => {
                // Flow control is completely disabled by a software over-ride.
                TXCW_ANE | TXCW_FD
            }
            FC_RX_PAUSE => {
                // RX Flow control is enabled and TX Flow control is disabled
                // by a software over-ride. Since there really isn't a way to
                // advertise that we are capable of RX Pause ONLY, we will
                // advertise that we support both symmetric and asymmetric RX
                // PAUSE. Later, we will disable the adapter's ability to
                // send PAUSE frames.
                TXCW_ANE | TXCW_FD | TXCW_PAUSE_MASK
            }
            FC_TX_PAUSE => {
                // TX Flow control is enabled, and RX Flow control is
                // disabled, by a software over-ride.
                TXCW_ANE | TXCW_FD | TXCW_ASM_DIR
            }
            FC_FULL => {
                // Flow control (both RX and TX) is enabled by a software over-ride.
                TXCW_ANE | TXCW_FD | TXCW_PAUSE_MASK
            }
            _ => {
                return Err(IgbDriverErr::Config);
            }
        };

        // Since auto-negotiation is enabled, take the link out of reset (the
        // link will be in reset, because we previously reset the chip). This
        // will restart auto-negotiation.  If auto-negotiation is successful
        // then the link-up status bit will be set and the flow control
        // enable bits (RFCE and TFCE) will be set according to their
        // negotiated value.

        write_reg(info, TXCW, txcw)?;
        write_reg(info, CTRL, ctrl)?;
        write_flush(info)?;

        self.txcw = txcw;
        awkernel_lib::delay::wait_millisec(1);

        // If we have a signal (the cable is plugged in) then poll for a
        // "Link-Up" indication in the Device Status Register.  Time-out if a
        // link isn't seen in 500 milliseconds seconds (Auto-negotiation
        // should complete in less than 500 milliseconds even if the other
        // end is doing it in SW). For internal serdes, we just assume a
        // signal is present, then poll.
        if self.media_type == MediaType::InternalSerdes
            || read_reg(info, CTRL)? & CTRL_SWDPIN1 != signal
        {
            let mut i = 0;

            loop {
                awkernel_lib::delay::wait_millisec(10);
                let status = read_reg(info, STATUS)?;
                if status & STATUS_LU != 0 {
                    break;
                }

                i += 1;
                if i > 50 {
                    self.autoneg_failed = true;

                    // AutoNeg failed to achieve a link, so we'll call
                    // em_check_for_link. This routine will force the
                    // link up if we detect a signal. This will allow us
                    // to communicate with non-autonegotiating link
                    // partners.
                    self.check_for_link(info)?;

                    self.autoneg_failed = false;

                    break;
                }
            }
        }

        Ok(())
    }

    fn power_up_serdes_link_82575(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if self.media_type != MediaType::InternalSerdes && !self.sgmii_active {
            return Ok(());
        }

        // Enable PCS to turn on link
        let mut reg = read_reg(info, PCS_CFG0)?;
        reg |= PCS_CFG_PCS_EN;
        write_reg(info, PCS_CFG0, reg)?;

        // Power up the laser
        reg = read_reg(info, CTRL_EXT)?;
        reg &= !CTRL_EXT_SDP3_DATA;
        write_reg(info, CTRL_EXT, reg)?;

        write_flush(info)?;
        awkernel_lib::delay::wait_microsec(5);

        Ok(())
    }

    /// Adjust SERDES output amplitude based on EEPROM setting.
    fn adjust_serdes_amplitude(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if self.media_type != MediaType::InternalSerdes
            || (self.mac_type as u32) >= MacType::Em82575 as u32
        {
            return Ok(());
        }

        if !matches!(self.mac_type, MacType::Em82545Rev3 | MacType::Em82546Rev3) {
            return Ok(());
        }

        let mut eeprom_data = [0; 1];
        self.read_eeprom(info, EEPROM_SERDES_AMPLITUDE, &mut eeprom_data)?;

        if eeprom_data[0] != EEPROM_RESERVED_WORD {
            // Adjust SERDES output amplitude only.
            eeprom_data[0] &= EEPROM_SERDES_AMPLITUDE_MASK;
            self.write_phy_reg(info, M88E1000_PHY_EXT_CTRL, eeprom_data[0])?;
        }

        Ok(())
    }

    /// Change VCO speed register to improve Bit Error Rate performance of SERDES.
    fn set_vco_speed(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if !matches!(self.mac_type, MacType::Em82545Rev3 | MacType::Em82546Rev3) {
            return Ok(());
        }

        // Set PHY register 30, page 5, bit 8 to 0

        let default_page = self.read_phy_reg(info, M88E1000_PHY_PAGE_SELECT)?;

        self.write_phy_reg(info, M88E1000_PHY_PAGE_SELECT, 0x0005)?;

        let mut phy_data = self.read_phy_reg(info, M88E1000_PHY_GEN_CONTROL)?;
        phy_data &= !M88E1000_PHY_VCO_REG_BIT8;
        self.write_phy_reg(info, M88E1000_PHY_GEN_CONTROL, phy_data)?;

        // Set PHY register 30, page 4, bit 11 to 1
        self.write_phy_reg(info, M88E1000_PHY_PAGE_SELECT, 0x0004)?;

        let mut phy_data = self.read_phy_reg(info, M88E1000_PHY_GEN_CONTROL)?;

        phy_data |= M88E1000_PHY_VCO_REG_BIT11;
        self.write_phy_reg(info, M88E1000_PHY_GEN_CONTROL, phy_data)?;

        self.write_phy_reg(info, M88E1000_PHY_PAGE_SELECT, default_page)?;

        Ok(())
    }

    /// Initializes receive address filters.
    ///
    /// Places the MAC address in receive address register 0 and clears the rest
    /// of the receive address registers. Clears the multicast table. Assumes
    /// the receiver is in reset when the routine is called.
    fn init_rx_addrs(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if matches!(
            self.mac_type,
            EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp | EmPch2lan
        ) && self.phy_no_cable_workaround(info).is_err()
        {
            log::warn!(" ...failed to apply em_phy_no_cable_workaround.");
        }

        // Setup the receive address.
        self.rar_set(info, &self.mac_addr, 0)?;

        // Reserve a spot for the Locally Administered Address to work around
        // an 82571 issue in which a reset on one port will reload the MAC on
        // the other port.
        if self.mac_type == Em82571 {
            return Err(IgbDriverErr::NotSupported);
        }

        let rar_num = if is_ich8(&self.mac_type) {
            if self.mac_type == EmIch8lan {
                RAR_ENTRIES_ICH8LAN
            } else {
                RAR_ENTRIES_ICH8LAN - 1
            }
        } else {
            match self.mac_type {
                Em82580 => RAR_ENTRIES_82580,
                EmI210 => RAR_ENTRIES_82575,
                EmI350 => RAR_ENTRIES_I350,
                _ => RAR_ENTRIES,
            }
        };

        // Zero out the other 15 receive addresses.
        for i in 1..rar_num {
            write_reg_array(info, RA, i << 1, 0)?;
            write_flush(info)?;
            write_reg_array(info, RA, (i << 1) + 1, 0)?;
            write_flush(info)?;
        }

        Ok(())
    }

    /// Puts an ethernet address into a receive address register.
    fn rar_set(&self, info: &PCIeInfo, addr: &[u8], index: u32) -> Result<(), IgbDriverErr> {
        use MacType::*;

        // HW expects these in little endian so we reverse the byte order
        // from network order (big endian) to little endian
        let rar_low = (addr[0] as u32)
            | ((addr[1] as u32) << 8)
            | ((addr[2] as u32) << 16)
            | ((addr[3] as u32) << 24);
        let mut rar_high = (addr[4] as u32) | ((addr[5] as u32) << 8);

        // Disable Rx and flush all Rx frames before enabling RSS to avoid Rx
        // unit hang.
        //
        // Description: If there are any Rx frames queued up or otherwise
        // present in the HW before RSS is enabled, and then we enable RSS,
        // the HW Rx unit will hang.  To work around this issue, we have to
        // disable receives and flush out all Rx frames before we enable RSS.
        // To do so, we modify we redirect all Rx traffic to manageability
        // and then reset the HW. This flushes away Rx frames, and (since the
        // redirections to manageability persists across resets) keeps new
        // ones from coming in while we work.  Then, we clear the Address
        // Valid AV bit for all MAC addresses and undo the re-direction to
        // manageability. Now, frames are coming in again, but the MAC won't
        // accept them, so far so good.  We now proceed to initialize RSS (if
        // necessary) and configure the Rx unit.  Last, we re-enable the AV
        // bits and continue on our merry way.

        match self.mac_type {
            Em82571 | Em82572 | Em80003es2lan => (),
            _ => {
                // Indicate to hardware the Address is Valid.
                rar_high |= RAH_AV;
            }
        }

        write_reg_array(info, RA, (index << 1) as usize, rar_low)?;
        write_flush(info)?;
        write_reg_array(info, RA, ((index << 1) + 1) as usize, rar_high)?;
        write_flush(info)?;

        Ok(())
    }

    /// Explicitly disables jumbo frames and resets some PHY registers back to hw-
    /// defaults. This is necessary in case the ethernet cable was inserted AFTER
    /// the firmware initialized the PHY. Otherwise it is left in a state where
    /// it is possible to transmit but not receive packets. Observed on I217-LM and
    /// fixed in FreeBSD's sys/dev/e1000/e1000_ich8lan.c.
    fn phy_no_cable_workaround(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        // disable Rx path while enabling workaround
        let ctrl_reg = self.read_phy_reg(info, I2_DFT_CTRL)?;
        self.write_phy_reg(info, I2_DFT_CTRL, ctrl_reg | (1 << 14))?;

        fn inner(hw: &mut IgbHw, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
            // Write MAC register values back to h/w defaults
            let mut mac_reg = read_reg(info, FFLT_DBG)?;
            mac_reg &= !(0xF << 14);
            write_reg(info, FFLT_DBG, mac_reg)?;

            let mut mac_reg = read_reg(info, RCTL)?;
            mac_reg &= !RCTL_SECRC;
            write_reg(info, RCTL, mac_reg)?;

            let data = hw.read_kmrn_reg(info, KUMCTRLSTA_OFFSET_CTRL)?;
            hw.write_kmrn_reg(info, KUMCTRLSTA_OFFSET_CTRL, data & !(1 << 0))?;

            let mut data = hw.read_kmrn_reg(info, KUMCTRLSTA_OFFSET_HD_CTRL)?;
            data &= !(0xF << 8);
            data |= 0xB << 8;
            hw.write_kmrn_reg(info, KUMCTRLSTA_OFFSET_HD_CTRL, data)?;

            // Write PHY register values back to h/w defaults
            let mut data = hw.read_phy_reg(info, I2_SMBUS_CTRL)?;
            data &= !(0x7F << 5);
            hw.write_phy_reg(info, I2_SMBUS_CTRL, data)?;

            let mut data = hw.read_phy_reg(info, I2_MODE_CTRL)?;
            data |= 1 << 13;
            hw.write_phy_reg(info, I2_MODE_CTRL, data)?;

            // 776.20 and 776.23 are not documented in i217-ethernet-controller-datasheet.pdf...
            let mut data = hw.read_phy_reg(info, phy_reg(776, 20))?;
            data &= !(0x3FF << 2);
            data |= 0x8 << 2;
            hw.write_phy_reg(info, phy_reg(776, 20), data)?;

            hw.write_phy_reg(info, phy_reg(776, 23), 0x7E00)?;

            let data = hw.read_phy_reg(info, I2_PCIE_POWER_CTRL)?;
            hw.write_phy_reg(info, I2_PCIE_POWER_CTRL, data & !(1 << 10))?;

            Ok(())
        }

        let result = inner(self, info);

        // re-enable Rx path after enabling workaround
        self.write_phy_reg(info, I2_DFT_CTRL, ctrl_reg & !(1 << 14))?;

        result
    }

    fn read_kmrn_reg(&mut self, info: &PCIeInfo, reg_addr: u32) -> Result<u16, IgbDriverErr> {
        self.swfw_sync_mut(info, self.swfw, |_| {
            // Write register address
            let reg_val =
                ((reg_addr << KUMCTRLSTA_OFFSET_SHIFT) & KUMCTRLSTA_OFFSET) | KUMCTRLSTA_REN;

            write_reg(info, KUMCTRLSTA, reg_val)?;
            awkernel_lib::delay::wait_microsec(2);

            // Read the data returned
            Ok(read_reg(info, KUMCTRLSTA)? as u16)
        })
    }

    fn write_kmrn_reg(
        &mut self,
        info: &PCIeInfo,
        reg_addr: u32,
        data: u16,
    ) -> Result<(), IgbDriverErr> {
        self.swfw_sync_mut(info, self.swfw, |_| {
            let reg_val = ((reg_addr << KUMCTRLSTA_OFFSET_SHIFT) & KUMCTRLSTA_OFFSET) | data as u32;

            write_reg(info, KUMCTRLSTA, reg_val)?;
            awkernel_lib::delay::wait_microsec(2);

            Ok(())
        })
    }

    /// Clears the VLAN filer table
    fn clear_vfta(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if is_ich8(&self.mac_type) {
            return Ok(());
        }

        let (vfta_offset, vfta_bit_in_reg) = if matches!(self.mac_type, Em82573 | Em82574) {
            if self.mng_cookie.vlan_id != 0 {
                // The VFTA is a 4096b bit-field, each identifying a
                // single VLAN ID.  The following operations
                // determine which 32b entry (i.e. offset) into the
                // array we want to set the VLAN ID (i.e. bit) of the
                // manageability unit.
                let vfta_offset = (self.mng_cookie.vlan_id >> VFTA_ENTRY_SHIFT) & VFTA_ENTRY_MASK;
                let vfta_bit_in_reg = 1 << (self.mng_cookie.vlan_id & VFTA_ENTRY_BIT_SHIFT_MASK);
                (vfta_offset, vfta_bit_in_reg)
            } else {
                (0, 0)
            }
        } else {
            (0, 0)
        };

        for offset in 0..VLAN_FILTER_TBL_SIZE {
            // If the offset we want to clear is the same offset of the
            // manageability VLAN ID, then clear all bits except that of
            // the manageability unit
            let vfta_value = if offset == vfta_offset as usize {
                vfta_bit_in_reg
            } else {
                0
            };
            write_reg_array(info, VFTA, offset, vfta_value)?;
            write_flush(info)?;
        }

        Ok(())
    }

    pub fn get_initialize_hw_bits_disable(&self) -> bool {
        self.initialize_hw_bits_disable
    }

    /// Initialize a number of hardware-dependent bits
    fn initialize_hardware_bits(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if (self.mac_type as u32) >= Em82571 as u32 && !self.initialize_hw_bits_disable {
            // Settings common to all silicon
            let mut reg_tarc0 = read_reg(info, TARC0)?;
            reg_tarc0 &= !0x78000000; // Clear bits 30, 29, 28, and 27

            match self.mac_type {
                Em82571 | Em82572 => {
                    let mut reg_tarc1 = read_reg(info, TARC1)?;
                    let reg_tctl = read_reg(info, TCTL)?;

                    // Set the phy Tx compatible mode bits
                    reg_tarc1 &= !0x60000000; // Clear bits 30 and 29

                    reg_tarc0 |= 0x07800000; // Set TARC0 bits 23-26
                    reg_tarc1 |= 0x07000000; // Set TARC1 bits 24-26

                    if reg_tctl & TCTL_MULR != 0 {
                        // Clear bit 28 if MULR is 1b
                        reg_tarc1 &= !0x10000000;
                    } else {
                        // Set bit 28 if MULR is 0b
                        reg_tarc1 |= 0x10000000;
                    }

                    write_reg(info, TARC1, reg_tarc1)?;
                }
                Em82573 | Em82574 => {
                    let mut reg_ctrl_ext = read_reg(info, CTRL_EXT)?;
                    let mut reg_ctrl = read_reg(info, CTRL)?;

                    reg_ctrl_ext &= !0x00800000; // Clear bit 23
                    reg_ctrl_ext |= 0x00400000; // Set bit 22
                    reg_ctrl &= !0x20000000; // Clear bit 29

                    write_reg(info, CTRL_EXT, reg_ctrl_ext)?;
                    write_reg(info, CTRL, reg_ctrl)?;
                }
                Em80003es2lan => {
                    if matches!(
                        self.media_type,
                        MediaType::Fiber | MediaType::InternalSerdes
                    ) {
                        // Clear bit 20
                        reg_tarc0 &= !0x00100000;
                    }

                    let reg_tctl = read_reg(info, TCTL)?;
                    let mut reg_tarc1 = read_reg(info, TARC1)?;
                    if reg_tctl & TCTL_MULR != 0 {
                        // Clear bit 28 if MULR is 1b
                        reg_tarc1 &= !0x10000000;
                    } else {
                        // Set bit 28 if MULR is 0b
                        reg_tarc1 |= 0x10000000;
                    }

                    write_reg(info, TARC1, reg_tarc1)?;
                }
                EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt
                | EmPchCnp | EmPchTgp | EmPchAdp => {
                    if self.mac_type == EmIch8lan {
                        // Set TARC0 bits 29 and 28
                        reg_tarc0 |= 0x30000000;
                    }

                    let mut reg_ctrl_ext = read_reg(info, CTRL_EXT)?;
                    reg_ctrl_ext |= 0x00400000; // Set bit 22

                    // Enable PHY low-power state when MAC is at D3 w/o WoL
                    if (self.mac_type as u32) >= EmPchlan as u32 {
                        reg_ctrl_ext |= CTRL_EXT_PHYPDEN;
                    }
                    write_reg(info, CTRL_EXT, reg_ctrl_ext)?;

                    reg_tarc0 |= 0x0d800000; // Set TARC0 bits 23, 24, 16, 27

                    let mut reg_tarc1 = read_reg(info, TARC1)?;
                    let reg_tctl = read_reg(info, TCTL)?;

                    if reg_tctl & TCTL_MULR != 0 {
                        // Clear bit 28 if MULR is 1b
                        reg_tarc1 &= !0x10000000;
                    } else {
                        // Set bit 28 if MULR is 0b
                        reg_tarc1 |= 0x10000000;
                    }

                    reg_tarc1 |= 0x45000000; // Set bit 24, 26 and 30

                    write_reg(info, TARC1, reg_tarc1)?;
                }
                _ => (),
            }

            write_reg(info, TARC0, reg_tarc0)?;
        }

        Ok(())
    }

    /// em_disable_ulp_lpt_lp - unconfigure Ultra Low Power mode for LynxPoint-LP
    ///
    /// Un-configure ULP mode when link is up, the system is transitioned from
    /// Sx or the driver is unloaded.  If on a Manageability Engine (ME) enabled
    /// system, poll for an indication from ME that ULP has been un-configured.
    /// If not on an ME enabled system, un-configure the ULP mode by software.
    ///
    /// During nominal operation, this function is called when link is acquired
    /// to disable ULP mode (force=FALSE); otherwise, for example when unloading
    /// the driver or during Sx->S0 transitions, this is called with force=TRUE
    /// to forcibly disable ULP.
    fn disable_ulp_lpt_lp(&mut self, info: &PCIeInfo, force: bool) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if (self.mac_type as u32) < EmPchLpt as u32
            || matches!(
                info.id,
                E1000_DEV_ID_PCH_LPT_I217_LM
                    | E1000_DEV_ID_PCH_LPT_I217_V
                    | E1000_DEV_ID_PCH_I218_LM2
                    | E1000_DEV_ID_PCH_I218_V2
            )
        {
            return Ok(());
        }

        if read_reg(info, FWSM)? & FWSM_FW_VALID != 0 {
            if force {
                // Request ME un-configure ULP mode in the PHY
                let mut mac_reg = read_reg(info, H2ME)?;
                mac_reg &= !H2ME_ULP;
                mac_reg |= H2ME_ENFORCE_SETTINGS;
                write_reg(info, H2ME, mac_reg)?;
            }

            // Poll up to 300msec for ME to clear ULP_CFG_DONE.
            let mut i = 0;
            while read_reg(info, FWSM)? & FWSM_ULP_CFG_DONE != 0 {
                if i == 30 {
                    return Err(IgbDriverErr::Phy);
                }

                awkernel_lib::delay::wait_microsec(10);
                i += 1;
            }

            if force {
                let mut mac_reg = read_reg(info, H2ME)?;
                mac_reg &= !H2ME_ENFORCE_SETTINGS;
                write_reg(info, H2ME, mac_reg)?;
            } else {
                // Clear H2ME.ULP after ME ULP configuration
                let mut mac_reg = read_reg(info, H2ME)?;
                mac_reg &= !H2ME_ULP;
                write_reg(info, H2ME, mac_reg)?;
            }

            return Ok(());
        }

        self.acquire_software_flag(info, |hw| {
            if force {
                // Toggle LANPHYPC Value bit
                hw.toggle_lanphypc_pch_lpt(info)?;
            }

            // Unforce SMBus mode in PHY
            let phy_reg = if let Ok(phy_reg) = hw.read_phy_reg(info, CV_SMB_CTRL) {
                phy_reg
            } else {
                // The MAC might be in PCIe mode, so temporarily force to
                // SMBus mode in order to access the PHY.
                let mut mac_reg = read_reg(info, CTRL_EXT)?;
                mac_reg |= CTRL_EXT_FORCE_SMBUS;
                write_reg(info, CTRL_EXT, mac_reg)?;

                awkernel_lib::delay::wait_microsec(50);

                hw.read_phy_reg(info, CV_SMB_CTRL)?
            };

            let phy_reg = phy_reg & !CV_SMB_CTRL_FORCE_SMBUS;
            hw.write_phy_reg(info, CV_SMB_CTRL, phy_reg)?;

            // Unforce SMBus mode in PHY
            let mac_reg = read_reg(info, CTRL_EXT)?;
            let mac_reg = mac_reg & !CTRL_EXT_FORCE_SMBUS;
            write_reg(info, CTRL_EXT, mac_reg)?;

            // When ULP mode was previously entered, K1 was disabled by the
            // hardware.  Re-Enable K1 in the PHY when exiting ULP.
            let phy_reg = hw.read_phy_reg(info, HV_PM_CTRL)?;
            let phy_reg = phy_reg | HV_PM_CTRL_K1_ENABLE;
            hw.write_phy_reg(info, HV_PM_CTRL, phy_reg)?;

            // Clear ULP enabled configuration
            let phy_reg = hw.read_phy_reg(info, I218_ULP_CONFIG1)?;
            let phy_reg = phy_reg
                & !(I218_ULP_CONFIG1_IND
                    | I218_ULP_CONFIG1_STICKY_ULP
                    | I218_ULP_CONFIG1_RESET_TO_SMBUS
                    | I218_ULP_CONFIG1_WOL_HOST
                    | I218_ULP_CONFIG1_INBAND_EXIT
                    | I218_ULP_CONFIG1_EN_ULP_LANPHYPC
                    | I218_ULP_CONFIG1_DIS_CLR_STICKY_ON_PERST
                    | I218_ULP_CONFIG1_DISABLE_SMB_PERST);
            hw.write_phy_reg(info, I218_ULP_CONFIG1, phy_reg)?;

            // Commit ULP changes by starting auto ULP configuration
            let phy_reg = phy_reg | I218_ULP_CONFIG1_START;
            hw.write_phy_reg(info, I218_ULP_CONFIG1, phy_reg)?;

            // Clear Disable SMBus Release on PERST# in MAC
            let mac_reg = read_reg(info, FEXTNVM7)?;
            let mac_reg = mac_reg & !FEXTNVM7_DISABLE_SMB_PERST;
            write_reg(info, FEXTNVM7, mac_reg)?;
            Ok(())
        })?;

        if force {
            self.phy_reset(info)?;
            awkernel_lib::delay::wait_millisec(50);
        }

        Ok(())
    }

    /// toggle the LANPHYPC pin value
    ///
    /// Toggling the LANPHYPC pin value fully power-cycles the PHY and is
    /// used to reset the PHY to a quiescent state when necessary.
    fn toggle_lanphypc_pch_lpt(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        // Set Phy Config Counter to 50msec
        let mut mac_reg = read_reg(info, FEXTNVM3)?;
        mac_reg &= !FEXTNVM3_PHY_CFG_COUNTER_MASK;
        mac_reg |= FEXTNVM3_PHY_CFG_COUNTER_50MSEC;
        write_reg(info, FEXTNVM3, mac_reg)?;

        // Toggle LANPHYPC Value bit
        let mut mac_reg = read_reg(info, CTRL)?;
        mac_reg |= CTRL_LANPHYPC_OVERRIDE;
        mac_reg &= !CTRL_LANPHYPC_VALUE;
        write_reg(info, CTRL, mac_reg)?;
        write_flush(info)?;
        awkernel_lib::delay::wait_millisec(1);
        mac_reg &= !CTRL_LANPHYPC_OVERRIDE;
        write_reg(info, CTRL, mac_reg)?;
        write_flush(info)?;

        if (self.mac_type as u32) < MacType::EmPchLpt as u32 {
            awkernel_lib::delay::wait_millisec(50);
        } else {
            let mut count = 20;
            loop {
                awkernel_lib::delay::wait_millisec(5);
                if read_reg(info, CTRL_EXT)? & CTRL_EXT_LPCD != 0 {
                    break;
                }
                count -= 1;
                if count == 0 {
                    break;
                }
            }

            awkernel_lib::delay::wait_millisec(30);
        }

        Ok(())
    }

    /// Checks to see if the link status of the hardware has changed.
    ///
    /// Called by any function that needs to check the link status of the adapter.
    pub fn check_for_link(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if (self.mac_type as u32) >= Em82575 as u32 && self.media_type != MediaType::Copper {
            self.get_pcs_speed_and_duplex_82575(info)?;
            self.get_link_status = self.serdes_link_down;
            return Ok(());
        }

        let ctrl = read_reg(info, CTRL)?;
        let status = read_reg(info, STATUS)?;

        let mut rxcw = 0;
        let mut signal = 0;

        // On adapters with a MAC newer than 82544, SW Defineable pin 1 will
        // be set when the optics detect a signal. On older adapters, it will
        // be cleared when there is a signal.  This applies to fiber media
        // only.
        if matches!(
            self.media_type,
            MediaType::Fiber | MediaType::InternalSerdes
        ) {
            rxcw = read_reg(info, RXCW)?;

            if self.media_type == MediaType::Fiber {
                signal = if (self.mac_type as u32) > MacType::Em82544 as u32 {
                    CTRL_SWDPIN1
                } else {
                    0
                };

                if status & STATUS_LU != 0 {
                    self.get_link_status = false;
                }
            }
        }

        // If we have a copper PHY then we only want to go out to the PHY
        // registers to see if Auto-Neg has completed and/or if our link
        // status has changed.  The get_link_status flag will be set if we
        // receive a Link Status Change interrupt or we have Rx Sequence
        // Errors.

        if matches!(self.media_type, MediaType::Copper | MediaType::Oem) && self.get_link_status {
            // First we want to see if the MII Status Register reports
            // link.  If so, then we want to get the current speed/duplex
            // of the PHY. Read the register twice since the link bit is
            // sticky.
            self.read_phy_reg(info, PHY_STATUS)?;
            let phy_data = self.read_phy_reg(info, PHY_STATUS)?;

            self.icp_xxxx_is_link_up = phy_data & MII_SR_LINK_STATUS != 0;

            if self.mac_type == EmPchlan {
                self.k1_gig_workaround_hv(info, self.icp_xxxx_is_link_up)?;
            }

            if phy_data & MII_SR_LINK_STATUS != 0 {
                self.get_link_status = false;

                if self.phy_type == PhyType::I82578 {
                    self.link_stall_workaround_hv(info)?;
                }

                if self.mac_type == EmPch2lan {
                    self.k1_workaround_lv(info)?;
                }

                // Work-around I218 hang issue
                if matches!(
                    info.get_id(),
                    E1000_DEV_ID_PCH_LPTLP_I218_LM
                        | E1000_DEV_ID_PCH_LPTLP_I218_V
                        | E1000_DEV_ID_PCH_I218_LM3
                        | E1000_DEV_ID_PCH_I218_V3
                ) {
                    self.k1_workaround_lpt_lp(info, self.icp_xxxx_is_link_up)?;
                }

                // Check if there was DownShift, must be checked
                // immediately after link-up
                self.check_downshift(info)?;

                // Enable/Disable EEE after link up
                if matches!(
                    self.mac_type,
                    EmPch2lan | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp
                ) {
                    self.set_eee_pchlan(info)?;
                }

                // If we are on 82544 or 82543 silicon and
                // speed/duplex are forced to 10H or 10F, then we
                // will implement the polarity reversal workaround.
                // We disable interrupts first, and upon returning,
                // place the devices interrupt state to its previous
                // value except for the link status change interrupt
                // which will happen due to the execution of this
                // workaround.
                if matches!(self.mac_type, Em82543 | Em82544)
                    && !self.autoneg
                    && matches!(
                        self.forced_speed_duplex,
                        SpeedDuplex::S10Full | SpeedDuplex::S10Half
                    )
                {
                    return Err(IgbDriverErr::NotSupported);
                }
            } else {
                // No link detected
                self.config_dsp_after_link_change(info, false)?;
            }

            // If we are forcing speed/duplex, then we simply return
            // since we have already determined whether we have link or
            // not.
            if !self.autoneg {
                return Err(IgbDriverErr::Config);
            }

            // optimize the dsp settings for the igp phy
            self.config_dsp_after_link_change(info, true)?;

            // We have a M88E1000 PHY and Auto-Neg is enabled.  If we
            // have Si on board that is 82544 or newer, Auto Speed
            // Detection takes care of MAC speed/duplex configuration.
            // So we only need to configure Collision Distance in the
            // MAC.  Otherwise, we need to force speed/duplex on the MAC
            // to the current PHY speed/duplex settings.
            if (self.mac_type as u32) >= Em82544 as u32 && self.mac_type != EmICPxxxx {
                self.config_collision_dist(info)?;
            } else {
                self.config_mac_to_phy(info)?;
            }

            // Configure Flow Control now that Auto-Neg has completed.
            // First, we need to restore the desired flow control
            // settings because we may have had to re-autoneg with a
            // different link partner.
            self.config_fc_after_link_up(info)?;

            // At this point we know that we are on copper and we have
            // auto-negotiated link.  These are conditions for checking
            // the link partner capability register.  We use the link
            // speed to determine if TBI compatibility needs to be turned
            // on or off.  If the link is not at gigabit speed, then TBI
            // compatibility is not needed.  If we are at gigabit speed,
            // we turn on TBI compatibility.
            if self.tbi_compatibility_en {
                let (speed, _duplex) = self.get_speed_and_duplex(info)?;

                if speed != Speed::S1000Mbps {
                    // If link speed is not set to gigabit speed,
                    // we do not need to enable TBI
                    // compatibility.
                    if self.tbi_compatibility_on {
                        // If we previously were in the mode,
                        // turn it off.
                        let mut rctl = read_reg(info, RCTL)?;
                        rctl &= !RCTL_SBP;
                        write_reg(info, RCTL, rctl)?;
                        self.tbi_compatibility_on = false;
                    }
                } else if !self.tbi_compatibility_on {
                    // If TBI compatibility is was previously
                    // off, turn it on. For compatibility with a
                    // TBI link partner, we will store bad
                    // packets. Some frames have an additional
                    // byte on the end and will look like CRC
                    // errors to the hardware.
                    self.tbi_compatibility_on = true;
                    let mut rctl = read_reg(info, RCTL)?;
                    rctl |= RCTL_SBP;
                    write_reg(info, RCTL, rctl)?;
                }
            }
        } else if ((self.media_type == MediaType::Fiber && ctrl & CTRL_SWDPIN1 == signal)
            || self.media_type == MediaType::InternalSerdes)
            && status & STATUS_LU == 0
            && rxcw & RXCW_C == 0
        {
            // If we don't have link (auto-negotiation failed or link partner
            // cannot auto-negotiate), the cable is plugged in (we have signal),
            // and our link partner is not trying to auto-negotiate with us (we
            // are receiving idles or data), we need to force link up. We also
            // need to give auto-negotiation time to complete, in case the cable
            // was just plugged in. The autoneg_failed flag does this.

            if !self.autoneg_failed {
                self.autoneg_failed = true;
                return Ok(());
            }

            // Disable auto-negotiation in the TXCW register
            write_reg(info, TXCW, self.txcw & !TXCW_ANE)?;

            // Force link-up and also force full-duplex.
            let mut ctrl = read_reg(info, CTRL)?;
            ctrl |= CTRL_SLU | CTRL_FD;
            write_reg(info, CTRL, ctrl)?;

            // Configure Flow Control after forcing link up.
            self.config_fc_after_link_up(info)?;
        } else if matches!(
            self.media_type,
            MediaType::Fiber | MediaType::InternalSerdes
        ) && status & STATUS_LU != 0
            && rxcw & RXCW_C != 0
        {
            // If we are forcing link and we are receiving /C/ ordered sets,
            // re-enable auto-negotiation in the TXCW register and disable forced
            // link in the Device Control register in an attempt to
            // auto-negotiate with our link partner.

            write_reg(info, TXCW, self.txcw)?;
            write_reg(info, CTRL, ctrl & !CTRL_SLU)?;

            self.serdes_link_down = false;
        } else if self.media_type == MediaType::InternalSerdes
            && TXCW_ANE & read_reg(info, TXCW)? == 0
        {
            // If we force link for non-auto-negotiation switch, check link
            // status based on MAC synchronization for internal serdes media
            // type.

            // SYNCH bit and IV bit are sticky.
            awkernel_lib::delay::wait_microsec(10);

            if RXCW_SYNCH & read_reg(info, RXCW)? != 0 {
                if rxcw & RXCW_IV == 0 {
                    self.serdes_link_down = false;
                }
            } else {
                self.serdes_link_down = true;
            }
        }

        if self.media_type == MediaType::InternalSerdes && TXCW_ANE & read_reg(info, TXCW)? != 0 {
            self.serdes_link_down = STATUS_LU & read_reg(info, STATUS)? == 0;
        }

        Ok(())
    }

    /// Enable/disable EEE based on setting in dev_spec structure.  The bits in
    /// the LPI Control register will remain set only if/when link is up.
    fn set_eee_pchlan(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if matches!(self.phy_type, PhyType::I82579 | PhyType::I217) {
            return Ok(());
        }

        let mut phy_reg = self.read_phy_reg(info, I82579_LPI_CTRL)?;

        if self.eee_enable {
            phy_reg &= !I82579_LPI_CTRL_ENABLE_MASK;
        } else {
            phy_reg |= I82579_LPI_CTRL_ENABLE_MASK;
        }

        self.write_phy_reg(info, I82579_LPI_CTRL, phy_reg)?;

        Ok(())
    }

    /// Check if Downshift occurred
    ///
    /// For phy's older then IGP, this function reads the Downshift bit in the Phy
    /// Specific Status register.  For IGP phy's, it reads the Downgrade bit in the
    /// Link Health register.  In IGP this bit is latched high, so the driver must
    /// read it immediately after link is established.
    fn check_downshift(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use PhyType::*;

        if matches!(self.phy_type, Igp | Igp2 | Igp3) {
            let phy_data = self.read_phy_reg(info, IGP01E1000_PHY_LINK_HEALTH)?;
            self.speed_downgraded = phy_data & IGP01E1000_PLHR_SS_DOWNGRADE != 0;
        } else if matches!(self.phy_type, M88 | Gg82563 | Oem | I82578) {
            let phy_data = self.read_phy_reg(info, M88E1000_PHY_SPEC_STATUS)?;
            self.speed_downgraded =
                (phy_data & M88E1000_PSSR_DOWNSHIFT) >> M88E1000_PSSR_DOWNSHIFT_SHIFT != 0;
        } else if self.phy_type == Ife {
            // em_phy_ife supports 10/100 speed only
            self.speed_downgraded = false;
        }

        Ok(())
    }

    /// When K1 is enabled for 1Gbps, the MAC can miss 2 DMA completion indications
    /// preventing further DMA write requests.  Workaround the issue by disabling
    /// the de-assertion of the clock request when in 1Gbps mode.
    /// Also, set appropriate Tx re-transmission timeouts for 10 and 100Half link
    /// speeds in order to avoid Tx hangs.
    fn k1_workaround_lpt_lp(&mut self, info: &PCIeInfo, link: bool) -> Result<(), IgbDriverErr> {
        let fextnvm6 = read_reg(info, FEXTNVM6)?;
        let status = read_reg(info, STATUS)?;

        if link && status & STATUS_SPEED_1000 != 0 {
            let reg = self.read_kmrn_reg(info, KMRNCTRLSTA_K1_CONFIG)?;
            self.write_kmrn_reg(info, KMRNCTRLSTA_K1_CONFIG, reg & !KMRNCTRLSTA_K1_ENABLE)?;

            awkernel_lib::delay::wait_microsec(10);

            write_reg(info, FEXTNVM6, fextnvm6 | FEXTNVM6_REQ_PLL_CLK)?;

            self.write_kmrn_reg(info, KMRNCTRLSTA_K1_CONFIG, reg)?;
        } else {
            // clear FEXTNVM6 bit 8 on link down or 10/100
            let mut fextnvm6 = fextnvm6 & !FEXTNVM6_REQ_PLL_CLK;

            if !link || (status & STATUS_SPEED_100 != 0 && status & STATUS_FD != 0) {
                write_reg(info, FEXTNVM6, fextnvm6)?;
            } else {
                let mut reg = self.read_phy_reg(info, I217_INBAND_CTRL)?;

                // Clear link status transmit timeout
                reg &= !I217_INBAND_CTRL_LINK_STAT_TX_TIMEOUT_MASK;

                if status & STATUS_SPEED_100 != 0 {
                    // Set inband Tx timeout to 5x10us for 100Half
                    reg |= 5 << I217_INBAND_CTRL_LINK_STAT_TX_TIMEOUT_SHIFT;

                    // Do not extend the K1 entry latency for 100Half
                    fextnvm6 &= !FEXTNVM6_ENABLE_K1_ENTRY_CONDITION;
                } else {
                    // Set inband Tx timeout to 50x10us for 10Full/Half
                    reg |= 50 << I217_INBAND_CTRL_LINK_STAT_TX_TIMEOUT_SHIFT;

                    // Extend the K1 entry latency for 10 Mbps
                    fextnvm6 |= FEXTNVM6_ENABLE_K1_ENTRY_CONDITION;
                }

                self.write_phy_reg(info, I217_INBAND_CTRL, reg)?;
                write_reg(info, FEXTNVM6, fextnvm6)?;
            }
        }

        Ok(())
    }

    fn k1_gig_workaround_hv(&mut self, info: &PCIeInfo, link: bool) -> Result<(), IgbDriverErr> {
        if self.mac_type != MacType::EmPchlan {
            return Ok(());
        }

        let mut phy_data = [0; 1];
        self.read_eeprom_ich8(info, E1000_NVM_K1_CONFIG, &mut phy_data)?;

        let mut k1_enable = phy_data[0] & E1000_NVM_K1_ENABLE != 0;

        // Disable K1 when link is 1Gbps, otherwise use the NVM setting
        if link {
            if self.phy_type == PhyType::I82578 {
                let mut phy_data = self.read_phy_reg(info, BM_CS_STATUS)?;
                phy_data &= BM_CS_STATUS_LINK_UP | BM_CS_STATUS_RESOLVED | BM_CS_STATUS_SPEED_MASK;

                if phy_data
                    == (BM_CS_STATUS_LINK_UP | BM_CS_STATUS_RESOLVED | BM_CS_STATUS_SPEED_1000)
                {
                    k1_enable = false;
                }
            } else if self.phy_type == PhyType::I82577 {
                let mut phy_data = self.read_phy_reg(info, HV_M_STATUS)?;
                phy_data &=
                    HV_M_STATUS_LINK_UP | HV_M_STATUS_AUTONEG_COMPLETE | HV_M_STATUS_SPEED_MASK;

                if phy_data
                    == (HV_M_STATUS_LINK_UP | HV_M_STATUS_AUTONEG_COMPLETE | HV_M_STATUS_SPEED_1000)
                {
                    k1_enable = false;
                }
            }

            // Link stall fix for link up
            self.write_phy_reg(info, phy_reg(770, 19), 0x0100)?;
        } else {
            // Link stall fix for link down
            self.write_phy_reg(info, phy_reg(770, 19), 0x4100)?;
        }

        self.configure_k1_ich8lan(info, k1_enable)?;

        Ok(())
    }

    // Configure K1 power state
    //
    // Configure the K1 power state based on the provided parameter.
    // Assumes semaphore already acquired.
    fn configure_k1_ich8lan(
        &mut self,
        info: &PCIeInfo,
        k1_enable: bool,
    ) -> Result<(), IgbDriverErr> {
        let mut kmrn_reg = self.read_kmrn_reg(info, KMRNCTRLSTA_K1_CONFIG)?;

        if k1_enable {
            kmrn_reg |= KMRNCTRLSTA_K1_ENABLE;
        } else {
            kmrn_reg &= !KMRNCTRLSTA_K1_ENABLE;
        }

        self.write_kmrn_reg(info, KMRNCTRLSTA_K1_CONFIG, kmrn_reg)?;

        awkernel_lib::delay::wait_microsec(20);

        let ctrl_ext = read_reg(info, CTRL_EXT)?;
        let ctrl_reg = read_reg(info, CTRL)?;

        let mut reg = ctrl_reg & !(CTRL_SPD_1000 | CTRL_SPD_100);
        reg |= CTRL_FRCSPD;
        write_reg(info, CTRL, reg)?;

        write_reg(info, CTRL_EXT, ctrl_ext | CTRL_EXT_SPD_BYPS)?;
        awkernel_lib::delay::wait_microsec(20);
        write_reg(info, CTRL, ctrl_reg)?;
        write_reg(info, CTRL_EXT, ctrl_ext)?;
        awkernel_lib::delay::wait_microsec(20);

        Ok(())
    }

    /// Si workaround
    ///
    /// This function works around a Si bug where the link partner can get
    /// a link up indication before the PHY does.  If small packets are sent
    /// by the link partner they can be placed in the packet buffer without
    /// being properly accounted for by the PHY and will stall preventing
    /// further packets from being received.  The workaround is to clear the
    /// packet buffer after the PHY detects link up.
    fn link_stall_workaround_hv(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if self.phy_type != PhyType::I82578 {
            return Ok(());
        }

        // Do not apply workaround if in PHY loopback bit 14 set
        let phy_data = self.read_phy_reg(info, PHY_CTRL)?;
        if phy_data & PHY_CTRL_LOOPBACK != 0 {
            return Ok(());
        }

        // check if link is up and at 1Gbps
        let mut phy_data = self.read_phy_reg(info, BM_CS_STATUS)?;

        phy_data &= BM_CS_STATUS_LINK_UP | BM_CS_STATUS_RESOLVED | BM_CS_STATUS_SPEED_MASK;

        if phy_data != BM_CS_STATUS_LINK_UP | BM_CS_STATUS_RESOLVED | BM_CS_STATUS_SPEED_1000 {
            return Ok(());
        }

        awkernel_lib::delay::wait_millisec(200);

        // flush the packets in the fifo buffer
        self.write_phy_reg(
            info,
            HV_MUX_DATA_CTRL,
            HV_MUX_DATA_CTRL_GEN_TO_MAC | HV_MUX_DATA_CTRL_FORCE_SPEED,
        )?;

        self.write_phy_reg(info, HV_MUX_DATA_CTRL, HV_MUX_DATA_CTRL_GEN_TO_MAC)?;

        Ok(())
    }

    /// Workaround to set the K1 beacon duration for 82579 parts
    fn k1_workaround_lv(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        let phy_data = self.read_phy_reg(info, BM_CS_STATUS)?;

        if phy_data & (HV_M_STATUS_LINK_UP | HV_M_STATUS_AUTONEG_COMPLETE)
            == HV_M_STATUS_LINK_UP | HV_M_STATUS_AUTONEG_COMPLETE
        {
            let mut mac_reg = read_reg(info, FEXTNVM4)?;
            mac_reg &= !FEXTNVM4_BEACON_DURATION_MASK;

            if phy_data & HV_M_STATUS_SPEED_1000 != 0 {
                mac_reg |= FEXTNVM4_BEACON_DURATION_8USEC;
            } else {
                mac_reg |= FEXTNVM4_BEACON_DURATION_16USEC;
            }

            write_reg(info, FEXTNVM4, mac_reg)?;
        }

        Ok(())
    }

    /// Reset the transmit and receive units; mask and clear all interrupts.
    /// https://github.com/openbsd/src/blob/18bc31b7ebc17ab66d1354464ff2ee3ba31f7750/sys/dev/pci/if_em_hw.c#L925
    pub fn reset_hw(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if matches!(self.mac_type, Em82542Rev2_0) {
            return Err(IgbDriverErr::NotSupported);
        }

        // Prevent the PCI-E bus from sticking if there is no TLP
        // connection on the last TLP read/write transaction when MAC
        // is reset.
        disable_pciex_master(info)?;

        // Set the completion timeout for 82575 chips
        if matches!(self.mac_type, Em82575 | Em82580 | Em82576 | EmI210 | EmI350) {
            set_pciex_completion_timeout(info)?;
        }

        // Clear interrupt mask to stop board from generating interrupts
        write_reg(info, IMC, !0)?;

        // Disable the Transmit and Receive units.  Then delay to allow any
        // pending transactions to complete before we hit the MAC with the
        // global reset.
        write_reg(info, RCTL, 0)?;
        write_reg(info, TCTL, TCTL_PSP)?;
        write_flush(info)?;

        // The tbi_compatibility_on Flag must be cleared when Rctl is cleared.
        self.tbi_compatibility_on = false;

        // Delay to allow any outstanding PCI transactions to complete before resetting the device
        awkernel_lib::delay::wait_millisec(10);

        // Must reset the PHY before resetting the MAC
        if matches!(self.mac_type, Em82541 | Em82547) {
            return Err(IgbDriverErr::NotSupported);
        }

        // Must acquire the MDIO ownership before MAC reset. Ownership defaults to firmware after a reset.
        if matches!(self.mac_type, Em82573 | Em82574) {
            let mut extcnf_ctrl = read_reg(info, EXTCNF_CTRL)?;

            extcnf_ctrl |= EXTCNF_CTRL_MDIO_SW_OWNERSHIP;

            for _ in 0..10 {
                write_reg(info, EXTCNF_CTRL, extcnf_ctrl)?;

                if extcnf_ctrl & EXTCNF_CTRL_MDIO_SW_OWNERSHIP != 0 {
                    break;
                } else {
                    extcnf_ctrl |= EXTCNF_CTRL_MDIO_SW_OWNERSHIP;
                }

                awkernel_lib::delay::wait_millisec(2);
            }
        }

        // Workaround for ICH8 bit corruption issue in FIFO memory
        if matches!(self.mac_type, EmIch8lan) {
            // Set Tx and Rx buffer allocation to 8k apiece.
            write_reg(info, PBA, PBA_8K)?;

            // Set Packet Buffer Size to 16k.
            write_reg(info, PBS, PBS_16K)?;
        }

        match self.mac_type {
            Em82544 | Em82540 | Em82545 | Em82546 | Em82541 | Em82541Rev2 => {
                let ctrl = read_reg(info, CTRL)?;
                write_reg(info, CTRL, ctrl | CTRL_RST)?;
            }
            EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt
            | EmPchCnp | EmPchTgp | EmPchAdp => {
                let mut ctrl = read_reg(info, CTRL)?;

                if !self.phy_reset_disable && self.check_phy_reset_block(info).is_ok() {
                    // PHY HW reset requires MAC CORE reset at the same
                    // time to make sure the interface between MAC and
                    // the external PHY is reset.
                    ctrl |= CTRL_PHY_RST;

                    // Gate automatic PHY configuration by hardware on non-managed 82579
                    if matches!(self.mac_type, EmPch2lan)
                        && read_reg(info, FWSM)? & FWSM_FW_VALID == 0
                    {
                        self.gate_hw_phy_config_ich8lan(info, true)?;
                    }
                };

                self.get_software_flag(info)?;
                write_reg(info, CTRL, ctrl | CTRL_RST)?;

                // HW reset releases software_flag
                self.sw_flag = 0;
                awkernel_lib::delay::wait_millisec(20);

                // Ungate automatic PHY configuration on non-managed 82579
                if matches!(self.mac_type, EmPch2lan)
                    && !self.phy_reset_disable
                    && read_reg(info, FWSM)? & FWSM_FW_VALID == 0
                {
                    awkernel_lib::delay::wait_millisec(10);
                    self.gate_hw_phy_config_ich8lan(info, false)?;
                }
            }
            _ => {
                let ctrl = read_reg(info, CTRL)?;
                write_reg(info, CTRL, ctrl | CTRL_RST)?;
            }
        }

        if self.check_phy_reset_block(info).is_ok() {
            match &self.mac_type {
                EmPchlan => {
                    self.hv_phy_workarounds_ich8lan(info)?;
                }
                EmPch2lan => {
                    self.lv_phy_workarounds_ich8lan(info)?;
                }
                _ => (),
            }
        }

        // After MAC reset, force reload of EEPROM to restore power-on
        // settings to device.  Later controllers reload the EEPROM
        // automatically, so just wait for reload to complete.

        match self.mac_type {
            Em82542Rev2_0 | Em82542Rev2_1 | Em82543 | Em82544 => {
                // Wait for EEPROM reload
                awkernel_lib::delay::wait_microsec(10);
                let ctrl_ext = read_reg(info, CTRL_EXT)?;
                write_reg(info, CTRL_EXT, ctrl_ext | CTRL_EXT_EE_RST)?;
                write_flush(info)?;
                awkernel_lib::delay::wait_microsec(2);
            }
            Em82541 | Em82541Rev2 | Em82547 | Em82547Rev2 => {
                // Wait for EEPROM reload
                awkernel_lib::delay::wait_millisec(20);
            }
            Em82573 | Em82574 => {
                if !self.is_onboard_nvm_eeprom(info)? {
                    awkernel_lib::delay::wait_microsec(10);
                    let ctrl_ext = read_reg(info, CTRL_EXT)?;
                    write_reg(info, CTRL_EXT, ctrl_ext | CTRL_EXT_EE_RST)?;
                    write_flush(info)?;
                }

                // Auto read done will delay 5ms or poll based on mac type
                self.get_auto_rd_done(info)?;
            }
            _ => {
                // Wait for EEPROM reload (it happens automatically)
                awkernel_lib::delay::wait_millisec(5);
            }
        }

        // Disable HW ARPs on ASF enabled adapters
        if self.mac_type as u32 >= Em82540 as u32
            && self.mac_type as u32 <= Em82547Rev2 as u32
            && self.mac_type != EmICPxxxx
        {
            let manc = read_reg(info, MANC)?;
            write_reg(info, MANC, manc & !MANC_ARP_EN)?;
        }

        if matches!(self.mac_type, Em82541 | Em82547) {
            self.phy_init_script(info)?;

            // Configure activity LED after PHY reset
            let led_ctrl = read_reg(info, LEDCTL)?;
            let led_ctrl =
                (led_ctrl & IGP_ACTIVITY_LED_MASK) | IGP_ACTIVITY_LED_ENABLE | IGP_LED3_MODE;
            write_reg(info, LEDCTL, led_ctrl)?;
        }

        // For PCH, this write will make sure that any noise
        // will be detected as a CRC error and be dropped rather than show up
        // as a bad packet to the DMA engine.
        if self.mac_type == EmPchlan {
            write_reg(info, CRC_OFFSET, 0x65656565)?;
        }

        // Clear interrupt mask to stop board from generating interrupts
        write_reg(info, IMC, !0)?;

        // Clear any pending interrupt events.
        let _icr = read_reg(info, ICR)?;
        write_reg(info, ICR, !0)?;

        // If MWI was previously enabled, reenable it.
        if self.mac_type == Em82542Rev2_0 {
            // https://github.com/openbsd/src/blob/ccf5da69583c0d4369ab3dc89805c858d4b2e8dc/sys/dev/pci/if_em_hw.c#L1201-L1204
            return Err(IgbDriverErr::NotSupported);
        }

        if is_ich8(&self.mac_type) {
            let kab = read_reg(info, KABGTXD)?;
            write_reg(info, KABGTXD, kab | KABGTXD_BGSQLBIAS)?;
        }

        if matches!(self.mac_type, Em82580 | EmI350) {
            // clear global device reset status bit
            write_reg(info, STATUS, STATUS_DEV_RST_SET)?;

            fn nvm_82580_lan_func_offset(a: u8) -> u32 {
                if a != 0 {
                    (0x40 + (0x40 * a)) as u32
                } else {
                    0
                }
            }

            let mut nvm_data = [0u16; 1];
            self.read_eeprom(
                info,
                EEPROM_INIT_CONTROL3_PORT_A + nvm_82580_lan_func_offset(self.bus_func),
                &mut nvm_data,
            )?;

            let mut mdicnfg = read_reg(info, MDICNFG)?;
            if nvm_data[0] & NVM_WORD24_EXT_MDIO != 0 {
                mdicnfg |= MDICNFG_EXT_MDIO;
            }
            if nvm_data[0] & NVM_WORD24_COM_MDIO != 0 {
                mdicnfg |= MDICNFG_COM_MDIO;
            }
            write_reg(info, MDICNFG, mdicnfg)?;
        }

        if matches!(self.mac_type, EmI210 | EmI350) {
            self.set_eee_i350(info)?;
        }

        Ok(())
    }

    fn set_eee_i350(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if (self.mac_type as u32) < MacType::EmI350 as u32 || self.media_type != MediaType::Copper {
            return Ok(());
        }

        let mut ipcnfg = read_reg(info, IPCNFG)?;
        let mut eeer = read_reg(info, EEER)?;

        if self.eee_enable {
            ipcnfg |= IPCNFG_EEE_1G_AN | IPCNFG_EEE_100M_AN;
            eeer |= EEER_TX_LPI_EN | EEER_RX_LPI_EN | EEER_LPI_FC;
        } else {
            ipcnfg &= !(IPCNFG_EEE_1G_AN | IPCNFG_EEE_100M_AN);
            eeer &= !(EEER_TX_LPI_EN | EEER_RX_LPI_EN | EEER_LPI_FC);
        }

        write_reg(info, IPCNFG, ipcnfg)?;
        write_reg(info, EEER, eeer)?;
        let _ = read_reg(info, IPCNFG)?;
        let _ = read_reg(info, EEER)?;

        Ok(())
    }

    /// Determines if the onboard NVM is FLASH or EEPROM.
    fn is_onboard_nvm_eeprom(&self, info: &PCIeInfo) -> Result<bool, IgbDriverErr> {
        use MacType::*;

        if is_ich8(&self.mac_type) {
            return Ok(false);
        }

        if matches!(self.mac_type, Em82573 | Em82574) {
            let eecd = read_reg(info, EECD)?;

            // Isolate bits 15 & 16
            let eecd = (eecd >> 15) & 0x03;

            // If both bits are set, device is Flash type
            if eecd == 0x03 {
                return Ok(false);
            }
        }

        Ok(true)
    }

    /// Check for EEPROM Auto Read bit done.
    fn get_auto_rd_done(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        match self.mac_type {
            Em82571 | Em82572 | Em82573 | Em82574 | Em82575 | Em82576 | Em82580 | Em80003es2lan
            | EmI210 | EmI350 | EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan
            | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp => {
                let mut timeout = AUTO_READ_DONE_TIMEOUT;

                while timeout > 0 {
                    if read_reg(info, EECD)? & EECD_AUTO_RD != 0 {
                        break;
                    } else {
                        awkernel_lib::delay::wait_millisec(1);
                    }

                    timeout -= 1;
                }

                if timeout == 0 {
                    return Err(IgbDriverErr::Reset);
                }
            }
            _ => {
                awkernel_lib::delay::wait_millisec(5);
            }
        }

        // PHY configuration from NVM just starts after EECD_AUTO_RD sets to
        // high. Need to wait for PHY configuration completion before
        // accessing NVM and PHY.

        if matches!(self.mac_type, Em82573 | Em82574) {
            awkernel_lib::delay::wait_millisec(25);
        }

        Ok(())
    }

    /// Probes the expected PHY address for known PHY IDs
    fn detect_gig_phy(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if self.phy_id != 0 {
            return Ok(());
        }

        // default phy address, most phys reside here, but not all (ICH10)
        if self.mac_type != EmICPxxxx {
            self.phy_addr = 1;
        } else {
            self.phy_addr = 0; // There is a phy at phy_addr 0 on EP80579
        }

        // The 82571 firmware may still be configuring the PHY. In this
        // case, we cannot access the PHY until the configuration is done.
        // So we explicitly set the PHY values.

        if matches!(self.mac_type, Em82571 | Em82572) {
            self.phy_id = IGP01E1000_I_PHY_ID;
            self.phy_type = PhyType::Igp2;
            return Ok(());
        }

        // Some of the fiber cards dont have a phy, so we must exit cleanly here
        if matches!(self.media_type, MediaType::Fiber)
            && matches!(
                self.mac_type,
                Em82542Rev2_0 | Em82542Rev2_1 | Em82543 | Em82573 | Em82574 | Em80003es2lan
            )
        {
            self.phy_type = PhyType::Undefined;
            return Ok(());
        }

        if matches!(
            self.media_type,
            MediaType::InternalSerdes | MediaType::Fiber
        ) && self.mac_type as u32 >= Em82575 as u32
        {
            self.phy_type = PhyType::Undefined;
            return Ok(());
        }

        if self.mac_type as u32 <= Em82543 as u32 {
            self.phy_hw_reset(info)?;
        }

        // ESB-2 PHY reads require em_phy_gg82563 to be set because of a
        // workaround that forces PHY page 0 to be set or the reads fail.
        // The rest of the code in this routine uses em_read_phy_reg to read
        // the PHY ID. So for ESB-2 we need to have this set so our reads
        // won't fail.  If the attached PHY is not a em_phy_gg82563, the
        // routines below will figure this out as well.
        if matches!(self.mac_type, Em80003es2lan) {
            self.phy_type = PhyType::Gg82563;
        }

        // Power on SGMII phy if it is disabled
        if matches!(self.mac_type, Em82580 | EmI210 | EmI350) {
            let ctrl_ext = read_reg(info, CTRL_EXT)?;
            write_reg(info, CTRL_EXT, ctrl_ext & !CTRL_EXT_SDP3_DATA)?;
            write_flush(info)?;
            awkernel_lib::delay::wait_millisec(300);
        }

        // Read the PHY ID Registers to identify which PHY is onboard.
        for i in 1..8 {
            self.phy_addr = i;
            if self.match_gig_phy(info).is_ok() {
                return Ok(()); // Found a valid PHY address
            }
        }

        Err(IgbDriverErr::Phy)
    }

    /// Reads and matches the expected PHY address for known PHY IDs
    fn match_gig_phy(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        let phy_id_high = self.read_phy_reg(info, PHY_ID1)?;

        awkernel_lib::delay::wait_microsec(20);

        let phy_id_low = self.read_phy_reg(info, PHY_ID2)?;

        self.phy_id = (phy_id_high as u32) << 16 | (phy_id_low as u32 & PHY_REVISION_MASK);
        self.phy_revision = Some(phy_id_low as u32 & !PHY_REVISION_MASK);

        let mut is_match = false;
        match &self.mac_type {
            Em82543 => {
                if self.phy_id == M88E1000_E_PHY_ID {
                    is_match = true;
                }
            }
            Em82544 => {
                if self.phy_id == M88E1000_I_PHY_ID {
                    is_match = true
                }
            }
            Em82540 | Em82545 | Em82545Rev3 | Em82546 | Em82546Rev3 => {
                if self.phy_id == M88E1011_I_PHY_ID {
                    is_match = true;
                }
            }
            Em82541 | Em82541Rev2 | Em82547 | Em82547Rev2 => {
                if self.phy_id == IGP01E1000_I_PHY_ID {
                    is_match = true;
                }
            }
            Em82573 => {
                if self.phy_id == M88E1111_I_PHY_ID {
                    is_match = true;
                }
            }
            Em82574 => {
                if self.phy_id == BME1000_E_PHY_ID {
                    is_match = true;
                }
            }
            Em82575 | Em82576 => {
                if self.phy_id == M88E1000_E_PHY_ID
                    || self.phy_id == IGP01E1000_I_PHY_ID
                    || self.phy_id == IGP03E1000_E_PHY_ID
                {
                    is_match = true;
                }
            }
            Em82580 | EmI210 | EmI350 => {
                if self.phy_id == I82580_I_PHY_ID
                    || self.phy_id == I210_I_PHY_ID
                    || self.phy_id == I347AT4_E_PHY_ID
                    || self.phy_id == I350_I_PHY_ID
                    || self.phy_id == M88E1111_I_PHY_ID
                    || self.phy_id == M88E1112_E_PHY_ID
                    || self.phy_id == M88E1543_E_PHY_ID
                    || self.phy_id == M88E1512_E_PHY_ID
                {
                    let mut mdic = read_reg(info, MDICNFG)?;
                    if mdic & MDICNFG_EXT_MDIO != 0 {
                        mdic &= MDICNFG_PHY_MASK;
                        self.phy_addr = mdic >> MDICNFG_PHY_SHIFT;
                    }
                    is_match = true;
                }
            }
            Em80003es2lan => {
                if self.phy_id == GG82563_E_PHY_ID {
                    is_match = true;
                }
            }
            EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan => {
                if self.phy_id == IGP03E1000_E_PHY_ID
                    || self.phy_id == IFE_E_PHY_ID
                    || self.phy_id == IFE_PLUS_E_PHY_ID
                    || self.phy_id == IFE_C_E_PHY_ID
                    || self.phy_id == BME1000_E_PHY_ID
                    || self.phy_id == I82577_E_PHY_ID
                    || self.phy_id == I82578_E_PHY_ID
                    || self.phy_id == I82579_E_PHY_ID
                {
                    is_match = true;
                }
            }
            EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp => {
                if self.phy_id == I217_E_PHY_ID {
                    is_match = true;
                }
            }
            EmICPxxxx => {
                if self.phy_id == M88E1141_E_PHY_ID || self.phy_id == RTL8211_E_PHY_ID {
                    is_match = true;
                }
            }
            _ => {
                return Err(IgbDriverErr::Config);
            }
        }

        self.set_phy_type()?;

        if is_match {
            Ok(())
        } else {
            log::warn!("igb: Invalid PHY ID: {:#x}", self.phy_id);
            Err(IgbDriverErr::Phy)
        }
    }

    /// Set the phy type member in the hw struct.
    fn set_phy_type(&mut self) -> Result<(), IgbDriverErr> {
        use MacType::*;

        match self.phy_id {
            M88E1000_E_PHY_ID | M88E1000_I_PHY_ID | M88E1011_I_PHY_ID | M88E1111_I_PHY_ID
            | M88E1112_E_PHY_ID | M88E1543_E_PHY_ID | M88E1512_E_PHY_ID | I210_I_PHY_ID
            | I347AT4_E_PHY_ID => {
                self.phy_type = PhyType::M88;
            }
            IGP01E1000_I_PHY_ID => {
                if matches!(self.mac_type, Em82541 | Em82541Rev2 | Em82547 | Em82547Rev2) {
                    self.phy_type = PhyType::Igp;
                }
            }
            IGP03E1000_E_PHY_ID | IGP04E1000_E_PHY_ID => {
                self.phy_type = PhyType::Igp3;
            }
            IFE_E_PHY_ID | IFE_PLUS_E_PHY_ID | IFE_C_E_PHY_ID => {
                self.phy_type = PhyType::Ife;
            }
            M88E1141_E_PHY_ID => {
                self.phy_type = PhyType::Oem;
            }
            I82577_E_PHY_ID => {
                self.phy_type = PhyType::I82577;
            }
            I82578_E_PHY_ID => {
                self.phy_type = PhyType::I82578;
            }
            I82579_E_PHY_ID => {
                self.phy_type = PhyType::I82579;
            }
            I217_E_PHY_ID => {
                self.phy_type = PhyType::I217;
            }
            I82580_I_PHY_ID | I350_I_PHY_ID => {
                self.phy_type = PhyType::I82580;
            }
            RTL8211_E_PHY_ID => {
                self.phy_type = PhyType::Rtl8211;
            }
            _ => {
                if self.phy_id == BME1000_E_PHY_ID && self.phy_revision == Some(1) {
                    self.phy_type = PhyType::Bm;
                } else if self.phy_id == GG82563_E_PHY_ID && matches!(self.mac_type, Em80003es2lan)
                {
                    self.phy_type = PhyType::Gg82563;
                } else {
                    // Should never have loaded on this device
                    self.phy_type = PhyType::Undefined;
                    return Err(IgbDriverErr::PhyType);
                }
            }
        }

        Ok(())
    }

    /// Release software semaphore FLAG bit (SWFLAG).
    /// SWFLAG is used to synchronize the access to all shared resource between
    /// SW, FW and HW.
    fn release_software_flag(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if is_ich8(&self.mac_type) {
            assert!(self.sw_flag > 0);

            self.sw_flag -= 1;
            if self.sw_flag > 0 {
                return Ok(());
            }

            let extcnf_ctrl = read_reg(info, EXTCNF_CTRL)?;
            let extcnf_ctrl = extcnf_ctrl & !EXTCNF_CTRL_SWFLAG;
            write_reg(info, EXTCNF_CTRL, extcnf_ctrl)?;
        }

        Ok(())
    }

    /// Resets the PHY
    fn phy_reset(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;
        use PhyType::*;

        if self.check_phy_reset_block(info).is_err() {
            return Ok(());
        }

        match self.phy_type {
            Igp | Igp2 | Igp3 | Ife => {
                self.phy_hw_reset(info)?;
            }
            _ => {
                let mut phy_data = self.read_phy_reg(info, PHY_CTRL)?;
                phy_data |= MII_CR_RESET;
                self.write_phy_reg(info, PHY_CTRL, phy_data)?;
                awkernel_lib::delay::wait_microsec(1);
            }
        }

        // Allow time for h/w to get to a quiescent state after reset
        awkernel_lib::delay::wait_millisec(10);

        if matches!(self.phy_type, Igp | Igp2) {
            self.phy_init_script(info)?;
        }

        if matches!(self.mac_type, EmPchlan) {
            self.hv_phy_workarounds_ich8lan(info)?;
        } else if matches!(self.mac_type, EmPch2lan) {
            self.lv_phy_workarounds_ich8lan(info)?;
        }

        if self.mac_type as u32 >= EmPchlan as u32 {
            self.oem_bits_config_pchlan(info, true)?;
        }

        // Ungate automatic PHY configuration on non-managed 82579
        if matches!(self.mac_type, EmPch2lan) && read_reg(info, FWSM)? & FWSM_FW_VALID == 0 {
            awkernel_lib::delay::wait_millisec(10);
            self.gate_hw_phy_config_ich8lan(info, false)?;
        }

        if self.phy_id == M88E1512_E_PHY_ID {
            self.initialize_m88e1512_phy(info)?;
        }

        Ok(())
    }

    /// IGP phy init script - initializes the GbE PHY
    fn phy_init_script(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        awkernel_lib::delay::wait_millisec(20);

        // Save off the current value of register 0x2F5B to be restored at the end of this routine.
        let phy_saved_data = self.read_phy_reg(info, 0x2F5B)?;

        // Disabled the PHY transmitter
        self.write_phy_reg(info, 0x2F5B, 0x0003)?;
        awkernel_lib::delay::wait_millisec(20);
        self.write_phy_reg(info, 0x0000, 0x0140)?;
        awkernel_lib::delay::wait_millisec(5);

        match self.mac_type {
            MacType::Em82541 | MacType::Em82547 => {
                self.write_phy_reg(info, 0x1F95, 0x0001)?;
                self.write_phy_reg(info, 0x1F71, 0xBD21)?;
                self.write_phy_reg(info, 0x1F79, 0x0018)?;
                self.write_phy_reg(info, 0x1F30, 0x1600)?;
                self.write_phy_reg(info, 0x1F31, 0x0014)?;
                self.write_phy_reg(info, 0x1F32, 0x161C)?;
                self.write_phy_reg(info, 0x1F94, 0x0003)?;
                self.write_phy_reg(info, 0x1F96, 0x003F)?;
                self.write_phy_reg(info, 0x2010, 0x0008)?;
            }
            MacType::Em82541Rev2 | MacType::Em82547Rev2 => {
                self.write_phy_reg(info, 0x1F73, 0x0099)?;
            }
            _ => (),
        }

        self.write_phy_reg(info, 0x0000, 0x3300)?;
        awkernel_lib::delay::wait_millisec(20);

        // Now enable the transmitter
        self.write_phy_reg(info, 0x2F5B, phy_saved_data)?;

        if self.mac_type as u32 > MacType::Em82547 as u32 {
            // Move to analog registers page
            let fused = self.read_phy_reg(info, IGP01E1000_ANALOG_SPARE_FUSE_STATUS)?;

            if fused & IGP01E1000_ANALOG_SPARE_FUSE_ENABLED == 0 {
                let fused = self.read_phy_reg(info, IGP01E1000_ANALOG_FUSE_STATUS)?;

                let fine = fused & IGP01E1000_ANALOG_FUSE_FINE_MASK;
                let coarse = fused & IGP01E1000_ANALOG_FUSE_COARSE_MASK;

                let (coarse, fine) = match coarse.cmp(&IGP01E1000_ANALOG_FUSE_COARSE_THRESH) {
                    core::cmp::Ordering::Greater => (
                        coarse - IGP01E1000_ANALOG_FUSE_COARSE_10,
                        fine - IGP01E1000_ANALOG_FUSE_FINE_1,
                    ),
                    core::cmp::Ordering::Equal => (coarse, fine - IGP01E1000_ANALOG_FUSE_FINE_10),
                    core::cmp::Ordering::Less => (coarse, fine),
                };

                let fused = (fused & IGP01E1000_ANALOG_FUSE_POLY_MASK)
                    | (fine & IGP01E1000_ANALOG_FUSE_FINE_MASK)
                    | (coarse & IGP01E1000_ANALOG_FUSE_COARSE_MASK);

                self.write_phy_reg(info, IGP01E1000_ANALOG_FUSE_CONTROL, fused)?;

                self.write_phy_reg(
                    info,
                    IGP01E1000_ANALOG_FUSE_BYPASS,
                    IGP01E1000_ANALOG_FUSE_ENABLE_SW_CONTROL,
                )?;
            }
        }

        Ok(())
    }

    /// SW-based LCD Configuration.
    /// SW will configure Gbe Disable and LPLU based on the NVM. The four bits are
    /// collectively called OEM bits.  The OEM Write Enable bit and SW Config bit
    /// in NVM determines whether HW should configure LPLU and Gbe Disable.
    fn oem_bits_config_pchlan(
        &mut self,
        info: &PCIeInfo,
        d0_state: bool,
    ) -> Result<(), IgbDriverErr> {
        if (self.mac_type as u32) < (MacType::EmPchlan as u32) {
            return Ok(());
        }

        self.swfw_sync_mut(info, SWFW_PHY0_SM, |hw| {
            if matches!(hw.mac_type, MacType::EmPchlan) {
                let mac_reg = read_reg(info, EXTCNF_CTRL)?;
                if mac_reg & EXTCNF_CTRL_OEM_WRITE_ENABLE != 0 {
                    return Ok(());
                }
            }

            let mac_reg = read_reg(info, FEXTNVM)?;
            if mac_reg & FEXTNVM_SW_CONFIG_ICH8M == 0 {
                return Ok(());
            }

            let mac_reg = read_reg(info, PHY_CTRL as usize)?;
            let oem_reg = hw.read_phy_reg(info, HV_OEM_BITS)?;

            let mut oem_reg = oem_reg & !(HV_OEM_BITS_GBE_DIS | HV_OEM_BITS_LPLU);

            if d0_state {
                if mac_reg & PHY_CTRL_GBE_DISABLE != 0 {
                    oem_reg |= HV_OEM_BITS_GBE_DIS;
                }

                if mac_reg & PHY_CTRL_D0A_LPLU != 0 {
                    oem_reg |= HV_OEM_BITS_LPLU;
                }

                // Restart auto-neg to activate the bits
                if hw.check_phy_reset_block(info).is_err() {
                    oem_reg |= HV_OEM_BITS_RESTART_AN;
                }
            } else {
                if mac_reg & (PHY_CTRL_GBE_DISABLE | PHY_CTRL_NOND0A_GBE_DISABLE) != 0 {
                    oem_reg |= HV_OEM_BITS_GBE_DIS;
                }

                if mac_reg & (PHY_CTRL_D0A_LPLU | PHY_CTRL_NOND0A_LPLU) != 0 {
                    oem_reg |= HV_OEM_BITS_LPLU;
                }
            }

            hw.write_phy_reg(info, HV_OEM_BITS, oem_reg)?;

            Ok(())
        })
    }

    /// Returns the PHY to the power-on reset state
    fn phy_hw_reset(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        self.check_phy_reset_block(info)?;

        if self.mac_type as u32 >= Em82543 as u32 && !matches!(self.mac_type, EmICPxxxx) {
            self.swfw_sync_mut(info, self.swfw, |hw| {
                // Read the device control register and assert the
                // E1000_CTRL_PHY_RST bit. Then, take it out of reset. For
                // pre-em_82571 hardware, we delay for 10ms between the
                // assert and deassert.  For em_82571 hardware and later, we
                // instead delay for 50us between and 10ms after the
                // deassertion.
                let ctrl = read_reg(info, CTRL)?;
                write_reg(info, CTRL, ctrl | CTRL_PHY_RST)?;
                write_flush(info)?;

                if (hw.mac_type as u32) < Em82571 as u32 {
                    awkernel_lib::delay::wait_millisec(10);
                } else {
                    awkernel_lib::delay::wait_microsec(100);
                }

                write_reg(info, CTRL, ctrl)?;
                write_flush(info)?;

                if (hw.mac_type as u32) >= Em82571 as u32 {
                    awkernel_lib::delay::wait_millisec(10);
                }

                // the M88E1141_E_PHY_ID might need reset here, but nothing
                // proves it

                Ok(())
            })?;
        } else {
            // Read the Extended Device Control Register, assert the
            // PHY_RESET_DIR bit to put the PHY into reset. Then, take it
            // out of reset.
            let ctrl_ext = read_reg(info, CTRL_EXT)?;
            let ctrl_ext = ctrl_ext | CTRL_EXT_SDP4_DIR;
            let ctrl_ext = ctrl_ext & !CTRL_EXT_SDP4_DATA;

            write_reg(info, CTRL_EXT, ctrl_ext)?;
            write_flush(info)?;

            awkernel_lib::delay::wait_millisec(10);

            let ctrl_ext = ctrl_ext | CTRL_EXT_SDP4_DATA;

            write_reg(info, CTRL_EXT, ctrl_ext)?;
            write_flush(info)?;
        }

        awkernel_lib::delay::wait_microsec(50);

        if matches!(self.mac_type, Em82541 | Em82547) {
            // Configure activity LED after PHY reset
            let led_ctrl = read_reg(info, LEDCTL)?;
            let led_ctrl = led_ctrl & IGP_ACTIVITY_LED_MASK;
            let led_ctrl = led_ctrl | IGP_ACTIVITY_LED_ENABLE | IGP_LED3_MODE;
            write_reg(info, LEDCTL, led_ctrl)?;
        }

        // Wait for FW to finish PHY configuration.
        self.get_phy_cfg_done(info)?;

        self.release_software_semaphore(info)?;

        if matches!(self.mac_type, EmIch8lan) && matches!(self.phy_type, PhyType::Igp3) {
            self.init_lcd_from_nvm(info)?;
        }

        Ok(())
    }

    /// This function initializes the PHY from the NVM on ICH8 platforms. This
    /// is needed due to an issue where the NVM configuration is not properly
    /// autoloaded after power transitions. Therefore, after each PHY reset, we
    /// will load the configuration data out of the NVM manually.
    fn init_lcd_from_nvm(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if !matches!(self.phy_type, PhyType::Igp3) {
            return Ok(());
        }

        // Check if SW needs configure the PHY
        let sw_cfg_mask = if info.id == E1000_DEV_ID_ICH8_IGP_M_AMT
            || info.id == E1000_DEV_ID_ICH8_IGP_M
            || matches!(
                self.mac_type,
                EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp
            ) {
            FEXTNVM_SW_CONFIG_ICH8M
        } else {
            FEXTNVM_SW_CONFIG
        };

        let reg_data = read_reg(info, FEXTNVM)?;
        if reg_data & sw_cfg_mask == 0 {
            return Ok(());
        }

        // Wait for basic configuration completes before proceeding
        for _ in 0..50 {
            let reg_data = read_reg(info, STATUS)?;
            awkernel_lib::delay::wait_microsec(100);
            if reg_data & STATUS_LAN_INIT_DONE != 0 {
                break;
            }
        }

        // Clear the Init Done bit for the next init event
        let reg_data = read_reg(info, STATUS)?;
        let reg_data = reg_data & !STATUS_LAN_INIT_DONE;
        write_reg(info, STATUS, reg_data)?;

        // Make sure HW does not configure LCD from PHY extended
        // configuration before SW configuration
        let reg_data = read_reg(info, EXTCNF_CTRL)?;
        if reg_data & EXTCNF_CTRL_LCD_WRITE_ENABLE == 0 {
            let reg_data = read_reg(info, EXTCNF_SIZE)?;
            let cnf_size = reg_data & EXTCNF_SIZE_EXT_PCIE_LENGTH;
            let cnf_size = cnf_size >> 16;
            if cnf_size != 0 {
                let reg_data = read_reg(info, EXTCNF_CTRL)?;
                let cnf_base_addr = reg_data & EXTCNF_CTRL_EXT_CNF_POINTER;
                // cnf_base_addr is in DWORD
                let cnf_base_addr = cnf_base_addr >> 16;

                // Configure LCD from extended configuration region.
                self.init_lcd_from_nvm_config_region(info, cnf_base_addr, cnf_size)?;
            }
        }

        Ok(())
    }

    fn init_lcd_from_nvm_config_region(
        &mut self,
        info: &PCIeInfo,
        cnf_base_addr: u32,
        cnf_size: u32,
    ) -> Result<(), IgbDriverErr> {
        // cnf_base_addr is in DWORD
        let word_addr = cnf_base_addr << 1;

        // cnf_size is returned in size of dwords
        for i in 0..cnf_size {
            let mut reg_data = [0];
            let mut reg_addr = [0];

            self.read_eeprom(info, word_addr + i * 2, &mut reg_data)?;
            self.read_eeprom(info, word_addr + i * 2 + 1, &mut reg_addr)?;

            self.acquire_software_flag(info, |hw| {
                hw.write_phy_reg(info, reg_addr[0] as u32, reg_data[0])?;
                Ok(())
            })?;
        }

        Ok(())
    }

    /// Parent function for writing words to the different EEPROM types.
    ///
    /// If em_update_eeprom_checksum is not called after this function, the
    /// EEPROM will most likely contain an invalid checksum.
    fn write_eeprom(
        &mut self,
        info: &PCIeInfo,
        offset: u32,
        data: &[u16],
    ) -> Result<(), IgbDriverErr> {
        // A check for invalid values:  offset too large, too many words, and
        // not enough words.
        if offset >= self.eeprom.word_size as u32
            || data.len() > (self.eeprom.word_size as u32 - offset) as usize
            || data.is_empty()
        {
            return Err(IgbDriverErr::EEPROM);
        }

        // 82573/4 writes only through eewr
        if self.eeprom.use_eewr {
            return self.write_eeprom_eewr(info, offset, data);
        }

        if matches!(self.eeprom.eeprom_type, EEPROMType::Ich8) {
            return self.write_eeprom_ich8(info, offset, data);
        }

        // Prepare the EEPROM for writing
        self.acquire_eeprom(info, |hw| {
            if matches!(hw.eeprom.eeprom_type, EEPROMType::Microwire) {
                hw.write_eeprom_microwire(info, offset, data)?;
            } else {
                hw.write_eeprom_spi(info, offset, data)?;
                awkernel_lib::delay::wait_millisec(10);
            }

            Ok(())
        })
    }

    /// Reads a 16 bit word from the EEPROM.
    fn read_eeprom(
        &mut self,
        info: &PCIeInfo,
        offset: u32,
        data: &mut [u16],
    ) -> Result<(), IgbDriverErr> {
        // A check for invalid values:  offset too large, too many words, and
        // not enough words.
        if offset >= self.eeprom.word_size as u32
            || data.len() > (self.eeprom.word_size as u32 - offset) as usize
            || data.is_empty()
        {
            return Err(IgbDriverErr::EEPROM);
        }

        if self.eeprom.use_eerd {
            return self.read_eeprom_eerd(info, offset, data);
        }

        if matches!(self.eeprom.eeprom_type, EEPROMType::Ich8) {
            return self.read_eeprom_ich8(info, offset, data);
        }

        if matches!(self.eeprom.eeprom_type, EEPROMType::Invm) {
            return self.read_invm_i210(info, offset, data);
        }

        // EEPROM's that don't use EERD to read require us to bit-bang the
        // SPI directly. In this case, we need to acquire the EEPROM so that
        // FW or other port software does not interrupt.
        assert!(
            is_onboard_nvm_eeprom(&self.mac_type, info)?
                && get_flash_presence_i210(&self.mac_type, info)?
                && !self.eeprom.use_eerd
        );

        self.acquire_eeprom(info, |hw| {
            // Set up the SPI or Microwire EEPROM for bit-bang reading.  We have
            // acquired the EEPROM at this point, so any returns should release it
            match &hw.eeprom.eeprom_type {
                EEPROMType::Spi => {
                    hw.spi_eeprom_ready(info)?;
                    hw.standby_eeprom(info)?;

                    let read_opcode = EEPROM_READ_OPCODE_SPI;

                    // Some SPI eeproms use the 8th address bit embedded in the
                    // opcode
                    let read_opcode = if (hw.eeprom.address_bits == 8) && (offset >= 128) {
                        read_opcode | EEPROM_A8_OPCODE_SPI
                    } else {
                        read_opcode
                    };

                    // Send the READ command (opcode + addr)
                    hw.shift_out_ee_bits(info, read_opcode, hw.eeprom.opcode_bits)?;
                    hw.shift_out_ee_bits(info, (offset * 2) as u16, hw.eeprom.address_bits)?;

                    // Read the data.  The address of the eeprom internally
                    // increments with each byte (spi) being read, saving on the
                    // overhead of eeprom setup and tear-down.  The address
                    // counter will roll over if reading beyond the size of the
                    // eeprom, thus allowing the entire memory to be read
                    // starting from any offset.
                    for d in data.iter_mut() {
                        let word_in = hw.shift_in_ee_bits(info, 16)?;
                        *d = word_in.rotate_left(8);
                    }

                    Ok(())
                }
                EEPROMType::Microwire => {
                    for (i, d) in data.iter_mut().enumerate() {
                        // Send the READ command (opcode + addr)
                        hw.shift_out_ee_bits(
                            info,
                            EEPROM_READ_OPCODE_MICROWIRE,
                            hw.eeprom.opcode_bits,
                        )?;
                        hw.shift_out_ee_bits(
                            info,
                            (offset + i as u32) as u16,
                            hw.eeprom.address_bits,
                        )?;

                        // Read the data.  For microwire, each word requires
                        // the overhead of eeprom setup and tear-down.
                        *d = hw.shift_in_ee_bits(info, 16)?;
                        hw.standby_eeprom(info)?;
                    }

                    Ok(())
                }
                _ => Err(IgbDriverErr::EEPROM),
            }
        })
    }

    fn initialize_m88e1512_phy(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        // Check if this is correct PHY.
        if self.phy_id != M88E1512_E_PHY_ID {
            return Ok(());
        }

        // Switch to PHY page 0xFF.
        self.write_phy_reg(info, M88E1543_PAGE_ADDR, 0x00FF)?;
        self.write_phy_reg(info, M88E1512_CFG_REG_2, 0x214B)?;
        self.write_phy_reg(info, M88E1512_CFG_REG_1, 0x2144)?;
        self.write_phy_reg(info, M88E1512_CFG_REG_2, 0x0C28)?;
        self.write_phy_reg(info, M88E1512_CFG_REG_1, 0x2146)?;
        self.write_phy_reg(info, M88E1512_CFG_REG_2, 0xB233)?;
        self.write_phy_reg(info, M88E1512_CFG_REG_1, 0x214D)?;
        self.write_phy_reg(info, M88E1512_CFG_REG_2, 0xCC0C)?;
        self.write_phy_reg(info, M88E1512_CFG_REG_1, 0x2159)?;

        // Switch to PHY page 0xFB.
        self.write_phy_reg(info, M88E1543_PAGE_ADDR, 0x00FB)?;
        self.write_phy_reg(info, M88E1512_CFG_REG_3, 0x000D)?;

        // Switch to PHY page 0x12.
        self.write_phy_reg(info, M88E1543_PAGE_ADDR, 0x12)?;

        // Change mode to SGMII-to-Copper
        self.write_phy_reg(info, M88E1512_MODE, 0x8001)?;

        // Return the PHY to page 0.
        self.write_phy_reg(info, M88E1543_PAGE_ADDR, 0)?;

        self.phy_hw_reset(info)?;

        awkernel_lib::delay::wait_millisec(1000);

        Ok(())
    }

    /// Writes a 16 bit word from the EEPROM using the EEWR register.
    fn write_eeprom_eewr(
        &mut self,
        info: &PCIeInfo,
        offset: u32,
        data: &[u16],
    ) -> Result<(), IgbDriverErr> {
        self.swfw_sync_mut(info, SWFW_EEP_SM, |hw| {
            for (i, d) in data.iter().enumerate() {
                let register_value = ((*d as u32) << EEPROM_RW_REG_DATA)
                    | ((offset + i as u32) << EEPROM_RW_ADDR_SHIFT)
                    | EEPROM_RW_REG_START;

                hw.poll_eerd_eewr_done(info, EEPROM_POLL_WRITE)?;

                write_reg(info, EEWR, register_value)?;

                hw.poll_eerd_eewr_done(info, EEPROM_POLL_WRITE)?;
            }

            Ok(())
        })
    }

    /// Writes a 16 bit word to a given offset in an SPI EEPROM.
    fn write_eeprom_spi(
        &mut self,
        info: &PCIeInfo,
        offset: u32,
        data: &[u16],
    ) -> Result<(), IgbDriverErr> {
        let mut widx = 0;

        while widx < data.len() {
            let write_opcode = EEPROM_WRITE_OPCODE_SPI;
            self.spi_eeprom_ready(info)?;

            self.standby_eeprom(info)?;

            // Send the WRITE ENABLE command (8 bit opcode)
            self.shift_out_ee_bits(info, EEPROM_WREN_OPCODE_SPI, self.eeprom.opcode_bits)?;

            self.standby_eeprom(info)?;

            // Some SPI eeproms use the 8th address bit embedded in the opcode
            let write_opcode = if (self.eeprom.address_bits == 8) && (offset >= 128) {
                write_opcode | EEPROM_A8_OPCODE_SPI
            } else {
                write_opcode
            };

            // Send the Write command (8-bit opcode + addr)
            self.shift_out_ee_bits(info, write_opcode, self.eeprom.opcode_bits)?;

            self.shift_out_ee_bits(
                info,
                ((offset + widx as u32) * 2) as u16,
                self.eeprom.address_bits,
            )?;

            // Send the data
            // Loop to allow for up to whole page write (32 bytes) of eeprom
            while widx < data.len() {
                let word_out = data[widx];
                let word_out = word_out.rotate_left(8);
                self.shift_out_ee_bits(info, word_out, 16)?;
                widx += 1;

                // Some larger eeprom sizes are capable of a 32-byte PAGE WRITE
                // operation, while the smaller eeproms are capable of an
                // 8-byte PAGE WRITE operation.  Break the inner loop to pass
                // new address
                if (((offset + widx as u32) * 2)
                    % self.eeprom.page_size.ok_or(IgbDriverErr::EEPROM)? as u32)
                    == 0
                {
                    self.standby_eeprom(info)?;
                    break;
                }
            }
        }

        Ok(())
    }

    /// Writes a 16 bit word to a given offset in a Microwire EEPROM.
    fn write_eeprom_microwire(
        &mut self,
        info: &PCIeInfo,
        offset: u32,
        data: &[u16],
    ) -> Result<(), IgbDriverErr> {
        // Send the write enable command to the EEPROM (3-bit opcode plus
        // 6/8-bit dummy address beginning with 11).  It's less work to
        // include the 11 of the dummy address as part of the opcode than it
        // is to shift it over the correct number of bits for the address.
        // This puts the EEPROM into write/erase mode.
        self.shift_out_ee_bits(
            info,
            EEPROM_EWEN_OPCODE_MICROWIRE,
            self.eeprom.opcode_bits + 2,
        )?;

        self.shift_out_ee_bits(info, 0, self.eeprom.address_bits - 2)?;

        // Prepare the EEPROM
        self.standby_eeprom(info)?;

        let mut words_written = 0;
        while words_written < data.len() {
            // Send the Write command (3-bit opcode + addr)
            self.shift_out_ee_bits(info, EEPROM_WRITE_OPCODE_MICROWIRE, self.eeprom.opcode_bits)?;

            self.shift_out_ee_bits(
                info,
                (offset + words_written as u32) as u16,
                self.eeprom.address_bits,
            )?;

            // Send the data
            self.shift_out_ee_bits(info, data[words_written], 16)?;

            // Toggle the CS line.  This in effect tells the EEPROM to
            // execute the previous command.
            self.standby_eeprom(info)?;

            // Read DO repeatedly until it is high (equal to '1').  The
            // EEPROM will signal that the command has been completed by
            // raising the DO signal. If DO does not go high in 10
            // milliseconds, then error out.
            let mut i = 0;
            loop {
                let eecd = read_reg(info, EECD)?;
                if eecd & EECD_DO != 0 {
                    break;
                }
                awkernel_lib::delay::wait_microsec(50);

                i += 1;
                if i >= 200 {
                    return Err(IgbDriverErr::EEPROM);
                }
            }

            // Recover from write
            self.standby_eeprom(info)?;

            words_written += 1;
        }

        // Send the write disable command to the EEPROM (3-bit opcode plus
        // 6/8-bit dummy address beginning with 10).  It's less work to
        // include the 10 of the dummy address as part of the opcode than it
        // is to shift it over the correct number of bits for the address.
        // This takes the EEPROM out of write/erase mode.
        self.shift_out_ee_bits(
            info,
            EEPROM_EWDS_OPCODE_MICROWIRE,
            self.eeprom.opcode_bits + 2,
        )?;

        self.shift_out_ee_bits(info, 0, self.eeprom.address_bits - 2)?;

        Ok(())
    }

    /// Reads a 16 bit word from the EEPROM using the EERD register.
    fn read_eeprom_eerd(
        &mut self,
        info: &PCIeInfo,
        offset: u32,
        data: &mut [u16],
    ) -> Result<(), IgbDriverErr> {
        for (i, d) in data.iter_mut().enumerate() {
            let eerd = ((offset + i as u32) << EEPROM_RW_ADDR_SHIFT) | EEPROM_RW_REG_START;

            write_reg(info, EERD, eerd)?;
            self.poll_eerd_eewr_done(info, EEPROM_POLL_READ)?;

            *d = (read_reg(info, EERD)? >> EEPROM_RW_REG_DATA) as u16;
        }

        Ok(())
    }

    /// Polls the status bit (bit 1) of the EERD to determine when the read is done.
    fn poll_eerd_eewr_done(&mut self, info: &PCIeInfo, eerd: u32) -> Result<(), IgbDriverErr> {
        let attempts = 100000;
        for _ in 0..attempts {
            let reg = if eerd == EEPROM_POLL_READ {
                read_reg(info, EERD)?
            } else {
                read_reg(info, EEWR)?
            };

            if reg & EEPROM_RW_REG_DONE != 0 {
                return Ok(());
            }

            awkernel_lib::delay::wait_microsec(5);
        }

        Err(IgbDriverErr::EEPROM)
    }

    /// Writes a 16 bit word or words to the EEPROM using the ICH8's flash access
    /// register.  Actually, writes are written to the shadow ram cache in the hw
    /// structure hw->em_shadow_ram.  em_commit_shadow_ram flushes this to
    /// the NVM, which occurs when the NVM checksum is updated.
    fn write_eeprom_ich8(
        &self,
        _info: &PCIeInfo,
        _offset: u32,
        _data: &[u16],
    ) -> Result<(), IgbDriverErr> {
        // A driver can write to the NVM only if it has eeprom_shadow_ram
        // allocated.  Subsequent reads to the modified words are read from
        // this cached structure as well.  Writes will only go into this
        // cached structure unless it's followed by a call to
        // em_update_eeprom_checksum() where it will commit the changes and
        // clear the "modified" field.

        Err(IgbDriverErr::EEPROM)
    }

    fn read_eeprom_ich8(
        &mut self,
        info: &PCIeInfo,
        offset: u32,
        data: &mut [u16],
    ) -> Result<(), IgbDriverErr> {
        // We need to know which is the valid flash bank.  In the event that
        // we didn't allocate eeprom_shadow_ram, we may not be managing
        // flash_bank.  So it cannot be trusted and needs to be updated with
        // each read.

        if (self.mac_type as u32) >= (MacType::EmPchSpt as u32) {
            return self.read_eeprom_spt(info, offset, data);
        }

        self.acquire_software_flag(info, |hw| {
            let flash_bank = if let Ok(bank) = hw.valid_nvm_bank_detect_ich8lan(info) {
                bank
            } else {
                0
            };

            // Adjust offset appropriately if we're on bank 1 - adjust for word size
            let bank_offset =
                flash_bank * (hw.flash_bank_size.ok_or(IgbDriverErr::EEPROM)? * 2) as u32;

            for (i, d) in data.iter_mut().enumerate() {
                // The NVM part needs a byte offset, hence * 2
                let act_offset = bank_offset + ((offset + i as u32) * 2);
                *d = hw.read_ich8_word(act_offset)?;
            }

            Ok(())
        })
    }

    fn read_eeprom_spt(
        &mut self,
        info: &PCIeInfo,
        offset: u32,
        data: &mut [u16],
    ) -> Result<(), IgbDriverErr> {
        // We need to know which is the valid flash bank.  In the event that
        // we didn't allocate eeprom_shadow_ram, we may not be managing
        // flash_bank.  So it cannot be trusted and needs to be updated with
        // each read.

        if (self.mac_type as u32) < (MacType::EmPchSpt as u32) {
            return Err(IgbDriverErr::EEPROM);
        }

        self.acquire_software_flag(info, |hw| {
            let flash_bank = if let Ok(bank) = hw.valid_nvm_bank_detect_ich8lan(info) {
                bank
            } else {
                0
            };

            // Adjust offset appropriately if we're on bank 1 - adjust for word size
            let bank_offset =
                flash_bank as usize * (hw.flash_bank_size.ok_or(IgbDriverErr::EEPROM)? * 2);

            let mut i = 0;
            let mut add;
            while i < data.len() {
                let act_offset = if (offset + i as u32) % 2 != 0 {
                    add = 1;
                    bank_offset as u32 + (offset + i as u32 - 1) * 2
                } else {
                    add = 2;
                    bank_offset as u32 + (offset + i as u32) * 2
                };

                let dword = hw.read_ich8_dword(act_offset)?;

                if add == 1 {
                    data[i] = (dword >> 16) as u16;
                } else {
                    data[i] = (dword & 0xFFFF) as u16;
                }

                if !(add == 1 || data.len() - i == 1) {
                    data[i + 1] = (dword >> 16) as u16;
                }

                i += add;
            }

            Ok(())
        })
    }

    /// finds out the valid bank 0 or 1
    ///
    /// Reads signature byte from the NVM using the flash access registers.
    /// Word 0x13 bits 15:14 = 10b indicate a valid signature for that bank.
    fn valid_nvm_bank_detect_ich8lan(&mut self, info: &PCIeInfo) -> Result<u32, IgbDriverErr> {
        use MacType::*;

        match self.mac_type {
            EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp => {
                let bank1_offset = self.flash_bank_size.ok_or(IgbDriverErr::EEPROM)? * 2;
                let act_offset = ICH_NVM_SIG_WORD * 2;

                // Check bank 0
                let nvm_dword = self.read_ich8_dword(act_offset)?;
                let sig_byte = (nvm_dword & 0xFF00) >> 8;
                if (sig_byte & ICH_NVM_VALID_SIG_MASK) == ICH_NVM_SIG_VALUE {
                    return Ok(0);
                }

                // Check bank 1
                let nvm_dword = self.read_ich8_dword(act_offset + bank1_offset as u32)?;
                let sig_byte = (nvm_dword & 0xFF00) >> 8;
                if (sig_byte & ICH_NVM_VALID_SIG_MASK) == ICH_NVM_SIG_VALUE {
                    return Ok(1);
                }

                return Err(IgbDriverErr::EEPROM);
            }
            EmIch8lan | EmIch9lan => {
                let eecd = read_reg(info, EECD)?;
                if (eecd & EECD_SEC1VAL_VALID_MASK) == EECD_SEC1VAL_VALID_MASK {
                    if eecd & EECD_SEC1VAL != 0 {
                        return Ok(1);
                    } else {
                        return Ok(0);
                    }
                }
            }
            _ => (),
        }

        let act_offset = ICH_NVM_SIG_WORD * 2 + 1;

        // Check bank 0
        let sig_byte = self.read_ich8_byte(act_offset)? as u32;

        if (sig_byte & ICH_NVM_VALID_SIG_MASK) == ICH_NVM_SIG_VALUE {
            return Ok(0);
        }

        // Check bank 1
        let bank1_offset =
            self.flash_bank_size.ok_or(IgbDriverErr::EEPROM)? * core::mem::size_of::<u16>();
        let sig_byte = self.read_ich8_byte(act_offset + bank1_offset as u32)? as u32;

        if (sig_byte & ICH_NVM_VALID_SIG_MASK) == ICH_NVM_SIG_VALUE {
            return Ok(1);
        }

        Err(IgbDriverErr::EEPROM)
    }

    /// Reads a dword from the NVM using the ICH8 flash access registers.
    #[inline(always)]
    fn read_ich8_dword(&mut self, index: u32) -> Result<u32, IgbDriverErr> {
        self.read_ich8_data32(index)
    }

    /// Reads a word from the NVM using the ICH8 flash access registers.
    #[inline(always)]
    fn read_ich8_word(&mut self, index: u32) -> Result<u16, IgbDriverErr> {
        let mut data = [0u16; 1];
        self.read_ich8_data(index, DataSize::Word, &mut data)?;
        Ok(data[0])
    }

    /// Reads a single byte from the NVM using the ICH8 flash access registers.
    fn read_ich8_byte(&mut self, index: u32) -> Result<u8, IgbDriverErr> {
        if self.mac_type as u32 >= MacType::EmPchSpt as u32 {
            return Err(IgbDriverErr::EEPROM);
        }

        let mut word = [0u16; 1];

        self.read_ich8_data(index, DataSize::Byte, &mut word)?;

        Ok(word[0] as u8)
    }

    /// Reads a byte or word from the NVM using the ICH8 flash access registers.
    ///
    /// size - Size of data to read, 1=byte 2=word
    fn read_ich8_data(
        &mut self,
        index: u32,
        size: DataSize,
        data: &mut [u16],
    ) -> Result<(), IgbDriverErr> {
        if index > ICH_FLASH_LINEAR_ADDR_MASK {
            return Err(IgbDriverErr::EEPROM);
        }

        let flash_linear_address = (ICH_FLASH_LINEAR_ADDR_MASK & index)
            + self.flash_base_address.ok_or(IgbDriverErr::EEPROM)? as u32;

        for _ in 0..ICH_FLASH_CYCLE_REPEAT_COUNT {
            awkernel_lib::delay::wait_microsec(1);
            // Steps
            self.ich8_cycle_init()?;

            let regval = self.read_ich_flash_reg16(ICH_FLASH_HSFCTL)?;
            // 0b/1b corresponds to 1 or 2 byte size, respectively.
            let regval = (regval & !(0b11 << 8)) | ((size as u16 - 1) << 8);
            let regval = (regval & !(0b11 << 2)) | (ICH_CYCLE_READ << 2);
            self.write_ich_flash_reg16(ICH_FLASH_HSFCTL, regval)?;

            // Write the last 24 bits of index into Flash Linear address
            // field in Flash Address
            // TODO: TBD maybe check the index against the size of flash

            self.write_ich_flash_reg32(ICH_FLASH_FADDR, flash_linear_address)?;

            // Check if FCERR is set to 1, if set to 1, clear it and try
            // the whole sequence a few more times, else read in (shift
            // in) the Flash Data0, the order is least significant byte
            // first msb to lsb

            if self.ich8_flash_cycle(ICH_FLASH_COMMAND_TIMEOUT).is_ok() {
                let flash_data = self.read_ich_flash_reg(ICH_FLASH_FDATA0)?;
                if size == DataSize::Byte {
                    data[0] = (flash_data & 0x000000FF) as u16;
                } else {
                    data[0] = (flash_data & 0x0000FFFF) as u16;
                }

                return Ok(());
            } else {
                // If we've gotten here, then things are probably
                // completely hosed, but if the error condition is
                // detected, it won't hurt to give it another
                // try...ICH_FLASH_CYCLE_REPEAT_COUNT times.
                let regval = self.read_ich_flash_reg16(ICH_FLASH_HSFSTS)?;
                let hsf_status = Ich8HwsFlashStatus::from_bits_truncate(regval);
                if !hsf_status.contains(Ich8HwsFlashStatus::FLCERR)
                    && !hsf_status.contains(Ich8HwsFlashStatus::FLCDONE)
                {
                    log::warn!("igb: Timeout error - flash cycle did not complete.");
                    break;
                }
            }
        }

        Err(IgbDriverErr::EEPROM)
    }

    fn read_ich8_data32(&mut self, offset: u32) -> Result<u32, IgbDriverErr> {
        if (self.mac_type as u32) < MacType::EmPchSpt as u32 {
            return Err(IgbDriverErr::EEPROM);
        }

        if offset > ICH_FLASH_LINEAR_ADDR_MASK {
            return Err(IgbDriverErr::EEPROM);
        }

        let flash_linear_address = (ICH_FLASH_LINEAR_ADDR_MASK & offset)
            + self.flash_base_address.ok_or(IgbDriverErr::EEPROM)? as u32;

        for _ in 0..ICH_FLASH_CYCLE_REPEAT_COUNT {
            awkernel_lib::delay::wait_microsec(1);

            // Steps
            self.ich8_cycle_init()?;

            // 32 bit accesses in SPT.
            let hsflctl = (self.read_ich_flash_reg32(ICH_FLASH_HSFSTS)? >> 16) as u16;

            let hsflctl =
                (hsflctl & !(0b11 << 8)) | (((core::mem::size_of::<u32>() - 1) as u16 & 0b11) << 8);
            let hsflctl = (hsflctl & !(0b11 << 1)) | (ICH_CYCLE_READ & 0b11 << 1);

            self.write_ich_flash_reg32(ICH_FLASH_HSFSTS, (hsflctl as u32) << 16)?;

            // Write the last 24 bits of offset into Flash Linear address
            // field in Flash Address

            self.write_ich_flash_reg32(ICH_FLASH_FADDR, flash_linear_address)?;

            // Check if FCERR is set to 1, if set to 1, clear it and try
            // the whole sequence a few more times, else read in (shift
            // in) the Flash Data0, the order is least significant byte
            // first msb to lsb
            if self.ich8_flash_cycle(ICH_FLASH_COMMAND_TIMEOUT).is_ok() {
                return self.read_ich_flash_reg32(ICH_FLASH_FDATA0);
            } else {
                // If we've gotten here, then things are probably
                // completely hosed, but if the error condition is
                // detected, it won't hurt to give it another
                // try...ICH_FLASH_CYCLE_REPEAT_COUNT times.
                let regval = self.read_ich_flash_reg16(ICH_FLASH_HSFSTS)?;
                let hsfsts = Ich8HwsFlashStatus::from_bits_truncate(regval);

                if !hsfsts.contains(Ich8HwsFlashStatus::FLCERR)
                    && !hsfsts.contains(Ich8HwsFlashStatus::FLCDONE)
                {
                    log::warn!("Timeout error - flash cycle did not complete.");
                    break;
                }
            }
        }

        Err(IgbDriverErr::EEPROM)
    }

    /// This function starts a flash cycle and waits for its completion.
    fn ich8_flash_cycle(&mut self, timeout: u32) -> Result<(), IgbDriverErr> {
        // Start a cycle by writing 1 in Flash Cycle Go in Hw Flash Control
        let regval = if self.mac_type as u32 >= MacType::EmPchSpt as u32 {
            (self.read_ich_flash_reg32(ICH_FLASH_HSFSTS)? >> 16) as u16
        } else {
            self.read_ich_flash_reg16(ICH_FLASH_HSFCTL)?
        };

        let hsf_ctrl = regval | 1;

        if self.mac_type as u32 >= MacType::EmPchSpt as u32 {
            self.write_ich_flash_reg32(ICH_FLASH_HSFSTS, (hsf_ctrl as u32) << 16)?;
        } else {
            self.write_ich_flash_reg16(ICH_FLASH_HSFCTL, hsf_ctrl)?;
        }

        // wait till FDONE bit is set to 1
        for _ in 0..timeout {
            let regval = if self.mac_type as u32 >= MacType::EmPchSpt as u32 {
                (self.read_ich_flash_reg32(ICH_FLASH_HSFSTS)? & 0xFFFF) as u16
            } else {
                self.read_ich_flash_reg16(ICH_FLASH_HSFSTS)?
            };

            let hsf_status = Ich8HwsFlashStatus::from_bits_truncate(regval);
            if hsf_status.contains(Ich8HwsFlashStatus::FLCDONE) {
                if hsf_status.contains(Ich8HwsFlashStatus::FLCERR) {
                    return Err(IgbDriverErr::EEPROM);
                } else {
                    return Ok(());
                }
            }

            awkernel_lib::delay::wait_microsec(1);
        }

        Err(IgbDriverErr::EEPROM)
    }

    // This function does initial flash setup so that a new read/write/erase cycle can be started.
    fn ich8_cycle_init(&mut self) -> Result<(), IgbDriverErr> {
        let regval = if self.mac_type as u32 >= MacType::EmPchSpt as u32 {
            self.read_ich_flash_reg32(ICH_FLASH_HSFSTS)? as u16
        } else {
            self.read_ich_flash_reg16(ICH_FLASH_HSFSTS)?
        };

        let stat = Ich8HwsFlashStatus::from_bits_truncate(regval);

        // May be check the Flash Des Valid bit in Hw status
        if !stat.contains(Ich8HwsFlashStatus::FLDESVALID) {
            log::warn!("igb: Flash descriptor invalid. SW Sequencing must be used.");
            return Err(IgbDriverErr::EEPROM);
        }

        // Clear FCERR in Hw status by writing 1
        // Clear DAEL in Hw status by writing a 1
        let stat = stat | Ich8HwsFlashStatus::FLCERR | Ich8HwsFlashStatus::DAEL;
        if self.mac_type as u32 >= MacType::EmPchSpt as u32 {
            self.write_ich_flash_reg32(ICH_FLASH_HSFSTS, stat.bits() as u32)?;
        } else {
            self.write_ich_flash_reg16(ICH_FLASH_HSFSTS, stat.bits())?;
        }

        // Either we should have a hardware SPI cycle in progress bit to
        // check against, in order to start a new cycle or FDONE bit should
        // be changed in the hardware so that it is 1 after hardware reset,
        // which can then be used as an indication whether a cycle is in
        // progress or has been completed .. we should also have some
        // software semaphore mechanism to guard FDONE or the cycle in
        // progress bit so that two threads access to those bits can be
        // sequentiallized or a way so that 2 threads dont start the cycle at
        // the same time

        if !stat.contains(Ich8HwsFlashStatus::FLCINPROG) {
            // There is no cycle running at present, so we can start a cycle
            // Begin by setting Flash Cycle Done.
            let stat = stat | Ich8HwsFlashStatus::FLCDONE;
            if self.mac_type as u32 >= MacType::EmPchSpt as u32 {
                self.write_ich_flash_reg32(ICH_FLASH_HSFSTS, stat.bits() as u32)?;
            } else {
                self.write_ich_flash_reg16(ICH_FLASH_HSFSTS, stat.bits())?;
            }

            Ok(())
        } else {
            // otherwise poll for sometime so the current cycle has a
            // chance to end before giving up.
            for _ in 0..ICH_FLASH_COMMAND_TIMEOUT {
                let regval = if self.mac_type as u32 >= MacType::EmPchSpt as u32 {
                    self.read_ich_flash_reg32(ICH_FLASH_HSFSTS)? as u16
                } else {
                    self.read_ich_flash_reg16(ICH_FLASH_HSFSTS)?
                };

                let stat = Ich8HwsFlashStatus::from_bits_truncate(regval);
                if !stat.contains(Ich8HwsFlashStatus::FLCINPROG) {
                    // Successful in waiting for previous cycle to
                    // timeout, now set the Flash Cycle Done.
                    let stat = stat | Ich8HwsFlashStatus::FLCDONE;
                    if self.mac_type as u32 >= MacType::EmPchSpt as u32 {
                        self.write_ich_flash_reg32(ICH_FLASH_HSFSTS, stat.bits() as u32)?;
                    } else {
                        self.write_ich_flash_reg16(ICH_FLASH_HSFSTS, stat.bits())?;
                    }

                    return Ok(());
                }

                awkernel_lib::delay::wait_microsec(1);
            }

            log::warn!("igb: Timeout waiting for flash cycle to complete.");
            Err(IgbDriverErr::EEPROM)
        }
    }

    /// Reads 16-bit words from the OTP. Return error when the word is not stored in OTP.
    fn read_invm_i210(
        &mut self,
        info: &PCIeInfo,
        offset: u32,
        data: &mut [u16],
    ) -> Result<(), IgbDriverErr> {
        match offset {
            EEPROM_MAC_ADDR_WORD0 | EEPROM_MAC_ADDR_WORD1 | EEPROM_MAC_ADDR_WORD2 => {
                // Generate random MAC address if there's none.
                if let Ok(d) = self.read_invm_word_i210(info, offset as u16) {
                    data[0] = d;
                } else {
                    data[0] = 0xFFFF;
                }

                Ok(())
            }
            EEPROM_INIT_CONTROL2_REG => {
                if let Ok(d) = self.read_invm_word_i210(info, offset as u16) {
                    data[0] = d;
                } else {
                    data[0] = NVM_INIT_CTRL_2_DEFAULT_I211;
                }

                Ok(())
            }
            EEPROM_INIT_CONTROL4_REG => {
                if let Ok(d) = self.read_invm_word_i210(info, offset as u16) {
                    data[0] = d;
                } else {
                    data[0] = NVM_INIT_CTRL_4_DEFAULT_I211;
                }

                Ok(())
            }
            EEPROM_LED_1_CFG => {
                if let Ok(d) = self.read_invm_word_i210(info, offset as u16) {
                    data[0] = d;
                } else {
                    data[0] = NVM_LED_1_CFG_DEFAULT_I211;
                }

                Ok(())
            }
            EEPROM_LED_0_2_CFG => {
                if let Ok(d) = self.read_invm_word_i210(info, offset as u16) {
                    data[0] = d;
                } else {
                    data[0] = NVM_LED_0_2_CFG_DEFAULT_I211;
                }

                Ok(())
            }
            EEPROM_ID_LED_SETTINGS => {
                if let Ok(d) = self.read_invm_word_i210(info, offset as u16) {
                    data[0] = d;
                } else {
                    data[0] = ID_LED_RESERVED_FFFF;
                }

                Ok(())
            }
            _ => {
                log::warn!("igb: NVM word {:#x} is not mapped.", offset);
                data[0] = NVM_RESERVED_WORD;
                Ok(())
            }
        }
    }

    /// Reads 16-bit words from the OTP. Return error when the word is not stored in OTP.
    fn read_invm_word_i210(&mut self, info: &PCIeInfo, address: u16) -> Result<u16, IgbDriverErr> {
        let mut i = 0;
        while i < INVM_SIZE {
            let invm_dword = read_reg(info, invm_data_reg(i as usize))?;
            let record_type = invm_dward_to_recored_type(invm_dword);
            if record_type == INVM_UNINITIALIZED_STRUCTURE {
                return Err(IgbDriverErr::NotSupported);
            }

            if record_type == INVM_CSR_AUTOLOAD_STRUCTURE {
                i += INVM_CSR_AUTOLOAD_DATA_SIZE_IN_DWORDS;
            }

            if record_type == INVM_RSA_KEY_SHA256_STRUCTURE {
                i += INVM_RSA_KEY_SHA256_DATA_SIZE_IN_DWORDS;
            }

            if record_type == INVM_WORD_AUTOLOAD_STRUCTURE {
                let word_address = invm_dward_to_dword_address(invm_dword);
                if word_address == address {
                    return Ok(invm_dward_to_dword_data(invm_dword));
                }
            }

            i += 1;
        }

        Err(IgbDriverErr::NotSupported)
    }

    /// Reads a 16 bit word from the EEPROM.
    fn spi_eeprom_ready(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        // Read "Status Register" repeatedly until the LSB is cleared.  The
        // EEPROM will signal that the command has been completed by clearing
        // bit 0 of the internal status register.  If it's not cleared within
        // 5 milliseconds, then error out.
        let mut retry_count = 0;
        loop {
            self.shift_out_ee_bits(info, EEPROM_RDSR_OPCODE_SPI, self.eeprom.opcode_bits)?;
            let spi_stat_reg = self.shift_in_ee_bits(info, 8)?;
            if spi_stat_reg & EEPROM_STATUS_RDY_SPI == 0 {
                break;
            }

            awkernel_lib::delay::wait_microsec(5);
            retry_count += 5;

            self.standby_eeprom(info)?;

            if retry_count >= EEPROM_MAX_RETRY_SPI {
                return Err(IgbDriverErr::EEPROM);
            }
        }

        // ATMEL SPI write time could vary from 0-20mSec on 3.3V devices (and
        // only 0-5mSec on 5V devices)

        if retry_count >= EEPROM_MAX_RETRY_SPI {
            log::warn!("igb: SPI EEPROM Status error");
            return Err(IgbDriverErr::EEPROM);
        }

        Ok(())
    }

    /// Returns EEPROM to a "standby" state
    fn standby_eeprom(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        let mut eecd = read_reg(info, EECD)?;

        match self.eeprom.eeprom_type {
            EEPROMType::Microwire => {
                eecd &= !(EECD_CS | EECD_SK);
                write_reg(info, EECD, eecd)?;
                write_flush(info)?;
                awkernel_lib::delay::wait_microsec(self.eeprom.delay_usec as u64);

                // Clock high
                eecd |= EECD_SK;
                write_reg(info, EECD, eecd)?;
                write_flush(info)?;
                awkernel_lib::delay::wait_microsec(self.eeprom.delay_usec as u64);

                // Select EEPROM
                eecd |= EECD_CS;
                write_reg(info, EECD, eecd)?;
                write_flush(info)?;
                awkernel_lib::delay::wait_microsec(self.eeprom.delay_usec as u64);

                // Clock low
                eecd &= !EECD_SK;
                write_reg(info, EECD, eecd)?;
                write_flush(info)?;
                awkernel_lib::delay::wait_microsec(self.eeprom.delay_usec as u64);

                Ok(())
            }
            EEPROMType::Spi => {
                // Toggle CS to flush commands
                eecd |= EECD_CS;
                write_reg(info, EECD, eecd)?;
                write_flush(info)?;
                awkernel_lib::delay::wait_microsec(self.eeprom.delay_usec as u64);

                eecd &= !EECD_CS;
                write_reg(info, EECD, eecd)?;
                write_flush(info)?;
                awkernel_lib::delay::wait_microsec(self.eeprom.delay_usec as u64);

                Ok(())
            }
            _ => Err(IgbDriverErr::EEPROM),
        }
    }

    /// Shift data bits out to the EEPROM.
    fn shift_out_ee_bits(
        &mut self,
        info: &PCIeInfo,
        data: u16,
        count: u16,
    ) -> Result<(), IgbDriverErr> {
        // We need to shift "count" bits out to the EEPROM. So, value in the
        // "data" parameter will be shifted out to the EEPROM one bit at a
        // time. In order to do this, "data" must be broken down into bits.
        let mut mask = 1 << (count - 1);
        let mut eecd = read_reg(info, EECD)?;
        match self.eeprom.eeprom_type {
            EEPROMType::Microwire => {
                eecd &= !EECD_DO;
            }
            EEPROMType::Spi => {
                eecd |= EECD_DO;
            }
            _ => (),
        }

        loop {
            // A "1" is shifted out to the EEPROM by setting bit "DI" to
            // a "1", and then raising and then lowering the clock (the
            // SK bit controls the clock input to the EEPROM).  A "0" is
            // shifted out to the EEPROM by setting "DI" to "0" and then
            // raising and then lowering the clock.
            eecd &= !EECD_DI;

            if data & mask != 0 {
                eecd |= EECD_DI;
            }

            write_reg(info, EECD, eecd)?;
            write_flush(info)?;

            awkernel_lib::delay::wait_microsec(self.eeprom.delay_usec as u64);

            self.raise_ee_clk(info, &mut eecd)?;
            self.lower_ee_clk(info, &mut eecd)?;

            mask >>= 1;

            if mask == 0 {
                break;
            }
        }

        // We leave the "DI" bit set to "0" when we leave this routine.
        eecd &= !EECD_DI;
        write_reg(info, EECD, eecd)?;

        Ok(())
    }

    /// Shift data bits in from the EEPROM
    fn shift_in_ee_bits(&mut self, info: &PCIeInfo, count: u16) -> Result<u16, IgbDriverErr> {
        // In order to read a register from the EEPROM, we need to shift
        // 'count' bits in from the EEPROM. Bits are "shifted in" by raising
        // the clock input to the EEPROM (setting the SK bit), and then
        // reading the value of the "DO" bit.  During this "shifting in"
        // process the "DI" bit should always be clear.

        let eecd = read_reg(info, EECD)?;
        let mut eecd = eecd & !(EECD_DO | EECD_DI);

        let mut data = 0;
        for _ in 0..count {
            data <<= 1;
            self.raise_ee_clk(info, &mut eecd)?;

            eecd = read_reg(info, EECD)?;
            eecd &= !(EECD_DI);

            if eecd & EECD_DO != 0 {
                data |= 1;
            }

            self.lower_ee_clk(info, &mut eecd)?;
        }

        Ok(data)
    }

    /// Lowers the EEPROM's clock input.
    fn lower_ee_clk(&mut self, info: &PCIeInfo, eecd: &mut u32) -> Result<(), IgbDriverErr> {
        // Lower the clock input to the EEPROM (by clearing the SK bit), and
        // then wait 50 microseconds.
        *eecd &= !EECD_SK;
        write_reg(info, EECD, *eecd)?;
        write_flush(info)?;
        awkernel_lib::delay::wait_microsec(self.eeprom.delay_usec as u64);

        Ok(())
    }

    /// Raises the EEPROM's clock input.
    fn raise_ee_clk(&mut self, info: &PCIeInfo, eecd: &mut u32) -> Result<(), IgbDriverErr> {
        // Raise the clock input to the EEPROM (by setting the SK bit), and
        // then wait <delay> microseconds.
        *eecd |= EECD_SK;
        write_reg(info, EECD, *eecd)?;
        write_flush(info)?;
        awkernel_lib::delay::wait_microsec(self.eeprom.delay_usec as u64);

        Ok(())
    }

    #[inline(always)]
    fn read_ich_flash_reg32(&mut self, reg: usize) -> Result<u32, IgbDriverErr> {
        let Some(flash_memory) = &self.flash_memory else {
            return Err(IgbDriverErr::ReadFailure);
        };

        flash_memory
            .base_address
            .read32(reg + flash_memory.offset)
            .ok_or(IgbDriverErr::ReadFailure)
    }

    #[inline(always)]
    fn read_ich_flash_reg16(&mut self, reg: usize) -> Result<u16, IgbDriverErr> {
        let Some(flash_memory) = &self.flash_memory else {
            return Err(IgbDriverErr::ReadFailure);
        };

        flash_memory
            .base_address
            .read16(reg + flash_memory.offset)
            .ok_or(IgbDriverErr::ReadFailure)
    }

    #[inline(always)]
    fn read_ich_flash_reg(&mut self, reg: usize) -> Result<u32, IgbDriverErr> {
        self.read_ich_flash_reg32(reg)
    }

    #[inline(always)]
    fn write_ich_flash_reg32(&mut self, reg: usize, value: u32) -> Result<(), IgbDriverErr> {
        let Some(flash_memory) = &mut self.flash_memory else {
            return Err(IgbDriverErr::ReadFailure);
        };

        flash_memory
            .base_address
            .write32(reg + flash_memory.offset, value);

        Ok(())
    }

    #[inline(always)]
    fn write_ich_flash_reg16(&mut self, reg: usize, value: u16) -> Result<(), IgbDriverErr> {
        let Some(flash_memory) = &mut self.flash_memory else {
            return Err(IgbDriverErr::ReadFailure);
        };

        flash_memory
            .base_address
            .write16(reg + flash_memory.offset, value);

        Ok(())
    }

    fn acquire_eeprom<T, F>(&mut self, info: &PCIeInfo, f: F) -> Result<T, IgbDriverErr>
    where
        F: FnOnce(&mut Self) -> Result<T, IgbDriverErr>,
    {
        use MacType::*;

        self.swfw_sync_mut(info, SWFW_EEP_SM, move |hw| {
            let eecd = read_reg(info, EECD)?;

            // !!(!A && !B) == !(A || B)

            if !matches!(hw.mac_type, Em82573 | Em82574) {
                // Request EEPROM Access
                if hw.mac_type as u32 > Em82544 as u32 {
                    write_reg(info, EECD, eecd | EECD_REQ)?;
                    let mut eecd = read_reg(info, EECD)?;
                    let mut i = 0;

                    while eecd & EECD_GNT == 0 && i < EEPROM_GRANT_ATTEMPTS {
                        i += 1;
                        awkernel_lib::delay::wait_microsec(5);
                        eecd = read_reg(info, EECD)?;
                    }

                    if eecd & EECD_GNT == 0 {
                        write_reg(info, EECD, eecd & !EECD_REQ)?;
                        log::warn!("igb: Could not acquire EEPROM grant");
                        return Err(IgbDriverErr::EEPROM);
                    }
                }
            }

            // Setup EEPROM for Read/Write
            match hw.eeprom.eeprom_type {
                EEPROMType::Microwire => {
                    let eecd = read_reg(info, EECD)?;
                    let eecd = eecd & !(EECD_DI | EECD_SK);
                    // Clear SK and DI
                    write_reg(info, EECD, eecd)?;

                    // Set CS
                    let eecd = eecd | EECD_CS;
                    write_reg(info, EECD, eecd)?;
                }
                EEPROMType::Spi => {
                    // Clear SK and CS
                    let eecd = read_reg(info, EECD)?;
                    let eecd = eecd & !(EECD_CS | EECD_SK);
                    write_reg(info, EECD, eecd)?;
                    awkernel_lib::delay::wait_microsec(1);
                }
                _ => (),
            }

            let result = f(hw);

            // release eeprom
            let eecd = read_reg(info, EECD)?;

            match hw.eeprom.eeprom_type {
                EEPROMType::Spi => {
                    let eecd = eecd | EECD_CS; // Pull CS high
                    let eecd = eecd & !EECD_SK; // Lower SCK
                    write_reg(info, EECD, eecd)?;
                    awkernel_lib::delay::wait_microsec(hw.eeprom.delay_usec as u64);
                }
                EEPROMType::Microwire => {
                    // cleanup eeprom
                    // CS on Microwire is active-high
                    let eecd = eecd & !(EECD_CS | EECD_DI);
                    write_reg(info, EECD, eecd)?;

                    // Rising edge of clock
                    let eecd = eecd | EECD_SK;
                    write_reg(info, EECD, eecd)?;
                    write_flush(info)?;
                    awkernel_lib::delay::wait_microsec(hw.eeprom.delay_usec as u64);

                    // Falling edge of clock
                    let eecd = eecd & !EECD_SK;
                    write_reg(info, EECD, eecd)?;
                    write_flush(info)?;
                    awkernel_lib::delay::wait_microsec(hw.eeprom.delay_usec as u64);
                }
                _ => (),
            }

            // Stop requesting EEPROM access
            if hw.mac_type as u32 > Em82544 as u32 {
                let eecd = read_reg(info, EECD)?;
                let eecd = eecd & !EECD_REQ;
                write_reg(info, EECD, eecd)?;
            }

            result
        })
    }

    /// Checks if the PHY configuration is done
    fn get_phy_cfg_done(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        let cfg_mask = if matches!(
            self.mac_type,
            Em80003es2lan | Em82575 | Em82576 | Em82580 | EmI350
        ) {
            let cfg_mask = match self.bus_func {
                1 => NVM_CFG_DONE_PORT_1,
                2 => NVM_CFG_DONE_PORT_2,
                3 => NVM_CFG_DONE_PORT_3,
                _ => NVM_CFG_DONE_PORT_0,
            };
            Some(cfg_mask)
        } else if matches!(self.mac_type, Em82571 | Em82572) {
            Some(NVM_CFG_DONE_PORT_0)
        } else {
            None
        };

        if let Some(cfg_mask) = cfg_mask {
            let mut timeout = PHY_CFG_TIMEOUT;

            while timeout > 0 {
                if read_reg(info, EEMNGCTL)? & cfg_mask != 0 {
                    break;
                } else {
                    awkernel_lib::delay::wait_millisec(1);
                }

                timeout -= 1;
            }

            if timeout == 0 {
                log::warn!("igb: MNG configuration cycle has not completed.");
            }
        } else {
            awkernel_lib::delay::wait_millisec(10);
        }

        Ok(())
    }

    /// A series of Phy workarounds to be done after every PHY reset.
    fn hv_phy_workarounds_ich8lan(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if !matches!(self.mac_type, MacType::EmPchlan) {
            return Ok(());
        }

        // Set MDIO slow mode before any other MDIO access
        if matches!(self.phy_type, PhyType::I82577 | PhyType::I82578) {
            self.set_mdio_slow_mode_hv(info)?;
        }

        // Hanksville M Phy init for IEEE.
        if info.revision_id == 2
            && matches!(self.phy_type, PhyType::I82577)
            && self.phy_revision == Some(2)
            || self.phy_revision == Some(3)
        {
            self.write_phy_reg(info, 0x10, 0x8823)?;
            self.write_phy_reg(info, 0x11, 0x0018)?;
            self.write_phy_reg(info, 0x10, 0x8824)?;
            self.write_phy_reg(info, 0x11, 0x0016)?;
            self.write_phy_reg(info, 0x10, 0x8825)?;
            self.write_phy_reg(info, 0x11, 0x001A)?;
            self.write_phy_reg(info, 0x10, 0x888C)?;
            self.write_phy_reg(info, 0x11, 0x0007)?;
            self.write_phy_reg(info, 0x10, 0x888D)?;
            self.write_phy_reg(info, 0x11, 0x0007)?;
            self.write_phy_reg(info, 0x10, 0x888E)?;
            self.write_phy_reg(info, 0x11, 0x0007)?;
            self.write_phy_reg(info, 0x10, 0x8827)?;
            self.write_phy_reg(info, 0x11, 0x0001)?;
            self.write_phy_reg(info, 0x10, 0x8835)?;
            self.write_phy_reg(info, 0x11, 0x0001)?;
            self.write_phy_reg(info, 0x10, 0x8834)?;
            self.write_phy_reg(info, 0x11, 0x0001)?;
            self.write_phy_reg(info, 0x10, 0x8833)?;
            self.write_phy_reg(info, 0x11, 0x0002)?;
        }

        if (matches!(self.phy_type, PhyType::I82577)
            && (self.phy_revision == Some(1) || self.phy_revision == Some(2)))
            || (matches!(self.phy_type, PhyType::I82578) && self.phy_revision == Some(1))
        {
            // Disable generation of early preamble
            self.write_phy_reg(info, phy_reg(769, 25), 0x4431)?;

            // Preamble tuning for SSC
            self.write_phy_reg(info, phy_reg(770, 16), 0xA204)?;
        }

        if matches!(self.phy_type, PhyType::I82578) {
            // Return registers to default by doing a soft reset then
            // writing 0x3140 to the control register.
            if self.phy_revision < Some(2) {
                self.phy_reset(info)?;
                self.write_phy_reg(info, PHY_CTRL, 0x3140)?;
            }
        }

        if info.revision_id == 2
            && matches!(self.phy_type, PhyType::I82577)
            && (self.phy_revision == Some(2) || self.phy_revision == Some(3))
        {
            // Workaround for OEM (GbE) not operating after reset -
            // restart AN (twice)
            self.write_phy_reg(info, phy_reg(0, 25), 0x0400)?;
            self.write_phy_reg(info, phy_reg(0, 25), 0x0400)?;
        }

        let swfw = SWFW_PHY0_SM;

        // select page 0
        self.swfw_sync_mut(info, swfw, move |hw| {
            hw.phy_addr = 1;
            hw.write_phy_reg(info, IGP01E1000_PHY_PAGE_SELECT, 0)?;
            Ok(())
        })?;

        // Workaround for link disconnects on a busy hub in half duplex
        let phy_data = self.read_phy_reg(info, phy_reg(BM_PORT_CTRL_PAGE, 17))?;
        self.write_phy_reg(info, phy_reg(BM_PORT_CTRL_PAGE, 17), phy_data & 0x00FF)?;

        Ok(())
    }

    /// em_lv_phy_workarounds_ich8lan - A series of Phy workarounds to be
    /// done after every PHY reset.
    fn lv_phy_workarounds_ich8lan(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if !matches!(self.mac_type, MacType::EmPch2lan) {
            return Ok(());
        }

        // Set MDIO slow mode before any other MDIO access
        self.set_mdio_slow_mode_hv(info)?;

        let swfw = SWFW_PHY0_SM;
        self.swfw_sync_mut(info, swfw, |hw| {
            hw.write_phy_reg(info, I82579_EMI_ADDR, I82579_MSE_THRESHOLD)?;

            // set MSE higher to enable link to stay up when noise is high
            hw.write_phy_reg(info, I82579_EMI_DATA, 0x0034)?;

            hw.write_phy_reg(info, I82579_EMI_ADDR, I82579_MSE_LINK_DOWN)?;

            // drop link after 5 times MSE threshold was reached
            hw.write_phy_reg(info, I82579_EMI_DATA, 0x0005)?;

            Ok(())
        })
    }

    /// Set slow MDIO access mode
    fn set_mdio_slow_mode_hv(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        let data = self.read_phy_reg(info, HV_KMRN_MODE_CTRL)?;
        self.write_phy_reg(info, HV_KMRN_MODE_CTRL, data)?;
        Ok(())
    }

    /// Writes a value to a PHY register
    pub fn write_phy_reg(
        &mut self,
        info: &PCIeInfo,
        reg_addr: u32,
        phy_data: u16,
    ) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if matches!(
            self.mac_type,
            EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp
        ) {
            return self.access_phy_reg_hv_write(info, reg_addr, phy_data);
        }

        self.swfw_sync_mut(info, self.swfw, |hw| {
            if matches!(hw.phy_type, PhyType::Igp | PhyType::Igp2 | PhyType::Igp3)
                && (reg_addr > MAX_PHY_MULTI_PAGE_REG)
            {
                hw.write_phy_reg_ex(info, IGP01E1000_PHY_PAGE_SELECT, reg_addr as u16)?;
            } else if matches!(hw.phy_type, PhyType::Gg82563)
                && ((reg_addr & MAX_PHY_REG_ADDRESS) > MAX_PHY_MULTI_PAGE_REG
                    || matches!(hw.mac_type, Em80003es2lan))
            {
                // Select Configuration Page
                if (reg_addr & MAX_PHY_REG_ADDRESS) < GG82563_MIN_ALT_REG {
                    hw.write_phy_reg_ex(
                        info,
                        GG82563_PHY_PAGE_SELECT,
                        (reg_addr >> GG82563_PAGE_SHIFT) as u16,
                    )?;
                } else {
                    // Use Alternative Page Select register to access registers 30 and 31
                    hw.write_phy_reg_ex(
                        info,
                        GG82563_PHY_PAGE_SELECT_ALT,
                        (reg_addr >> GG82563_PAGE_SHIFT) as u16,
                    )?;
                }
            } else if matches!(hw.phy_type, PhyType::Bm)
                && hw.phy_revision == Some(1)
                && reg_addr > MAX_PHY_MULTI_PAGE_REG
            {
                hw.write_phy_reg_ex(
                    info,
                    BM_PHY_PAGE_SELECT,
                    (reg_addr >> PHY_PAGE_SHIFT) as u16,
                )?;
            }

            hw.write_phy_reg_ex(info, MAX_PHY_REG_ADDRESS & reg_addr, phy_data)?;

            Ok(())
        })
    }

    /// Reads the value from a PHY register, if the value is on a specific non zero
    /// page, sets the page first.
    pub fn read_phy_reg(&mut self, info: &PCIeInfo, reg_addr: u32) -> Result<u16, IgbDriverErr> {
        use MacType::*;

        if matches!(
            self.mac_type,
            EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp
        ) {
            return self.access_phy_reg_hv_read(info, reg_addr);
        }

        let swfw = if matches!(self.mac_type, Em80003es2lan | Em82575 | Em82576)
            && read_reg(info, STATUS)? & STATUS_FUNC_1 != 0
        {
            SWFW_PHY1_SM
        } else {
            SWFW_PHY0_SM
        };

        self.swfw_sync_mut(info, swfw, move |hw| {
            use PhyType::*;

            if matches!(hw.phy_type, Igp | Igp2 | Igp3) && reg_addr > MAX_PHY_MULTI_PAGE_REG {
                hw.write_phy_reg_ex(info, IGP01E1000_PHY_PAGE_SELECT, reg_addr as u16)?;
            } else if matches!(hw.phy_type, Gg82563) {
                if reg_addr & MAX_PHY_REG_ADDRESS > MAX_PHY_MULTI_PAGE_REG
                    || matches!(hw.mac_type, Em80003es2lan)
                {
                    // Select Configuration Page
                    if reg_addr & MAX_PHY_REG_ADDRESS < GG82563_MIN_ALT_REG {
                        hw.write_phy_reg_ex(
                            info,
                            GG82563_PHY_PAGE_SELECT,
                            (reg_addr >> GG82563_PAGE_SHIFT) as u16,
                        )?;
                    } else {
                        // Use Alternative Page Select register to access registers 30 and 31
                        hw.write_phy_reg_ex(
                            info,
                            GG82563_PHY_PAGE_SELECT_ALT,
                            (reg_addr >> GG82563_PAGE_SHIFT) as u16,
                        )?;
                    }
                }
            } else if matches!(hw.phy_type, Bm)
                && hw.phy_revision == Some(1)
                && reg_addr > MAX_PHY_MULTI_PAGE_REG
            {
                hw.write_phy_reg_ex(
                    info,
                    BM_PHY_PAGE_SELECT,
                    (reg_addr >> PHY_PAGE_SHIFT) as u16,
                )?;
            }

            hw.read_phy_reg_ex(info, MAX_PHY_REG_ADDRESS & reg_addr)
        })
    }

    /// Reads or writes the value from a PHY register, if the value is on a specific non zero page, sets the page first.
    /// https://github.com/openbsd/src/blob/d9ecc40d45e66a0a0b11c895967c9bb8f737e659/sys/dev/pci/if_em_hw.c#L5064
    fn access_phy_reg_hv_read(
        &mut self,
        info: &PCIeInfo,
        reg_addr: u32,
    ) -> Result<u16, IgbDriverErr> {
        let swfw = SWFW_PHY0_SM;

        self.swfw_sync_mut(info, swfw, |hw| {
            let page = bm_phy_reg_page(reg_addr);
            if page == BM_WUC_PAGE {
                let result = hw.access_phy_wakeup_reg_bm(info, reg_addr, true, None)?;
                return Ok(result.unwrap());
            }

            if page >= HV_INTC_FC_PAGE_START {
                hw.phy_addr = 1;
            } else {
                hw.phy_addr = 2;
            }

            let page = if page == HV_INTC_FC_PAGE_START {
                0
            } else {
                page
            };

            if reg_addr > MAX_PHY_MULTI_PAGE_REG {
                hw.write_phy_reg_ex(info, IGP01E1000_PHY_PAGE_SELECT, page << PHY_PAGE_SHIFT)?;
            }

            let reg = bm_phy_reg_num(reg_addr) as u32;
            let result = hw.read_phy_reg_ex(info, MAX_PHY_REG_ADDRESS & reg)?;

            Ok(result)
        })
    }

    fn access_phy_reg_hv_write(
        &mut self,
        info: &PCIeInfo,
        reg_addr: u32,
        phy_data: u16,
    ) -> Result<(), IgbDriverErr> {
        let swfw = SWFW_PHY0_SM;

        self.swfw_sync_mut(info, swfw, |hw| {
            let page = bm_phy_reg_page(reg_addr);
            if page == BM_WUC_PAGE {
                hw.access_phy_wakeup_reg_bm(info, reg_addr, false, Some(phy_data))?;
                return Ok(());
            }

            if page >= HV_INTC_FC_PAGE_START {
                hw.phy_addr = 1;
            } else {
                hw.phy_addr = 2;
            }

            let reg = bm_phy_reg_num(reg_addr) as u32;

            // Workaround MDIO accesses being disabled after entering IEEE Power
            // Down (whenever bit 11 of the PHY Control register is set)
            if matches!(hw.phy_type, PhyType::I82578)
                && matches!(hw.phy_revision, Some(1))
                && hw.phy_addr == 2
                && (MAX_PHY_REG_ADDRESS & reg) == 0
                && phy_data & (1 << 11) != 0
            {
                let data2 = 0x7EFF;
                hw.access_phy_debug_regs_hv(info, (1 << 6) | 0x3, Some(data2), false)?;
            }

            let page = if page == HV_INTC_FC_PAGE_START {
                0
            } else {
                page
            };

            if reg_addr > MAX_PHY_MULTI_PAGE_REG {
                hw.write_phy_reg_ex(info, IGP01E1000_PHY_PAGE_SELECT, page << PHY_PAGE_SHIFT)?;
            }

            hw.write_phy_reg_ex(info, MAX_PHY_REG_ADDRESS & reg, phy_data)?;

            Ok(())
        })
    }

    /// Read HV PHY vendor specific high registers
    pub fn access_phy_debug_regs_hv(
        &mut self,
        info: &PCIeInfo,
        reg_addr: u32,
        phy_data: Option<u16>,
        read: bool,
    ) -> Result<Option<u16>, IgbDriverErr> {
        // This takes care of the difference with desktop vs mobile phy
        let addr_reg = if matches!(self.phy_type, PhyType::I82578) {
            I82578_PHY_ADDR_REG
        } else {
            I82577_PHY_ADDR_REG
        };

        let data_reg = addr_reg + 1;

        // All operations in this function are phy address 2
        self.phy_addr = 2;

        // masking with 0x3F to remove the page from offset
        self.write_phy_reg_ex(info, addr_reg, (reg_addr & 0x3F) as u16)?;

        // Read or write the data value next
        if read {
            Ok(Some(self.read_phy_reg_ex(info, data_reg)?))
        } else {
            self.write_phy_reg_ex(info, data_reg, phy_data.unwrap())?;
            Ok(None)
        }
    }

    /// Read BM PHY wakeup register.  It works as such:
    /// 1) Set page 769, register 17, bit 2 = 1
    /// 2) Set page to 800 for host (801 if we were manageability)
    /// 3) Write the address using the address opcode (0x11)
    /// 4) Read or write the data using the data opcode (0x12)
    /// 5) Restore 769_17.2 to its original value
    fn access_phy_wakeup_reg_bm(
        &mut self,
        info: &PCIeInfo,
        reg_addr: u32,
        read: bool,
        write_data: Option<u16>,
    ) -> Result<Option<u16>, IgbDriverErr> {
        // All operations in this function are phy address 1
        self.phy_addr = 1;

        // Set page 769
        self.write_phy_reg_ex(
            info,
            IGP01E1000_PHY_PAGE_SELECT,
            BM_WUC_ENABLE_PAGE << PHY_PAGE_SHIFT,
        )?;

        let mut phy_reg = self.read_phy_reg_ex(info, BM_WUC_ENABLE_REG)?;

        // First clear bit 4 to avoid a power state change
        phy_reg &= !BM_WUC_HOST_WU_BIT;
        self.write_phy_reg_ex(info, BM_WUC_ENABLE_REG, phy_reg)?;

        // Write bit 2 = 1, and clear bit 4 to 769_17
        self.write_phy_reg_ex(info, BM_WUC_ENABLE_REG, phy_reg | BM_WUC_ENABLE_BIT)?;

        // Select page 800
        self.write_phy_reg_ex(
            info,
            IGP01E1000_PHY_PAGE_SELECT,
            BM_WUC_PAGE << PHY_PAGE_SHIFT,
        )?;

        // Write the page 800 offset value using opcode 0x11
        let reg = bm_phy_reg_num(reg_addr);
        self.write_phy_reg_ex(info, BM_WUC_ADDRESS_OPCODE, reg)?;

        let result = if read {
            // Read the page 800 value using opcode 0x12
            Some(self.read_phy_reg_ex(info, BM_WUC_DATA_OPCODE)?)
        } else {
            // Write the page 800 value using opcode 0x12
            self.write_phy_reg_ex(info, BM_WUC_DATA_OPCODE, write_data.unwrap())?;
            None
        };

        // Restore 769_17.2 to its original value
        // Set page 769
        self.write_phy_reg_ex(
            info,
            IGP01E1000_PHY_PAGE_SELECT,
            BM_WUC_ENABLE_PAGE << PHY_PAGE_SHIFT,
        )?;

        // Clear 769_17.2
        self.write_phy_reg_ex(info, BM_WUC_ENABLE_REG, phy_reg)?;

        Ok(result)
    }

    fn write_phy_reg_ex(
        &self,
        info: &PCIeInfo,
        reg_addr: u32,
        phy_data: u16,
    ) -> Result<(), IgbDriverErr> {
        // SGMII active is only set on some specific chips
        if self.sgmii_active && !self.sgmii_uses_mdio_82575(info)? {
            if reg_addr > MAX_SGMII_PHY_REG_ADDR {
                return Err(IgbDriverErr::Param);
            }
            return self.write_phy_reg_i2c(info, reg_addr, phy_data);
        }

        if reg_addr > MAX_PHY_REG_ADDRESS {
            return Err(IgbDriverErr::Param);
        }

        if matches!(self.mac_type, MacType::EmICPxxxx) {
            return Err(IgbDriverErr::NotSupported);
        }

        if self.mac_type as usize > MacType::Em82543 as usize {
            // Set up Op-code, Phy Address, register address, and data
            // intended for the PHY register in the MDI Control register.
            // The MAC will take care of interfacing with the PHY to send
            // the desired data.

            let mdic = (phy_data as u32)
                | (reg_addr << MDIC_REG_SHIFT)
                | (self.phy_addr << MDIC_PHY_SHIFT)
                | MDIC_OP_WRITE;

            write_reg(info, MDIC, mdic)?;

            // Poll the ready bit to see if the MDI read completed
            let mut mdic = 0;
            for _ in 0..641 {
                awkernel_lib::delay::wait_microsec(5);
                mdic = read_reg(info, MDIC)?;
                if mdic & MDIC_READY != 0 {
                    break;
                }
            }

            if mdic & MDIC_READY == 0 {
                return Err(IgbDriverErr::Phy);
            }

            if matches!(
                self.mac_type,
                MacType::EmPch2lan
                    | MacType::EmPchLpt
                    | MacType::EmPchSpt
                    | MacType::EmPchCnp
                    | MacType::EmPchTgp
                    | MacType::EmPchAdp
            ) {
                awkernel_lib::delay::wait_microsec(100);
            }

            Ok(())
        } else {
            Err(IgbDriverErr::NotSupported)
        }
    }

    /// em_sgmii_uses_mdio_82575 - Determine if I2C pins are for external MDIO
    ///
    /// Called to determine if the I2C pins are being used for I2C or as an
    /// external MDIO interface since the two options are mutually exclusive.
    fn sgmii_uses_mdio_82575(&self, info: &PCIeInfo) -> Result<bool, IgbDriverErr> {
        match self.mac_type {
            MacType::Em82575 | MacType::Em82576 => {
                let reg = read_reg(info, MDIC)?;
                Ok(reg & MDIC_DEST != 0)
            }
            MacType::Em82580 | MacType::EmI350 | MacType::EmI210 => {
                let reg = read_reg(info, MDICNFG)?;
                Ok(reg & MDICNFG_EXT_MDIO != 0)
            }
            _ => Ok(false),
        }
    }

    /// em_write_phy_reg_i2c - Write PHY register using i2c.
    /// Writes the data to PHY register at the offset using the i2c interface.
    fn write_phy_reg_i2c(
        &self,
        info: &PCIeInfo,
        offset: u32,
        data: u16,
    ) -> Result<(), IgbDriverErr> {
        // Prevent overwriting SFP I2C EEPROM which is at A0 address.
        if self.phy_addr == 0 || self.phy_addr > 7 {
            log::warn!("igb: PHY I2C Address {} is out of range.", self.phy_addr);
            return Err(IgbDriverErr::Config);
        }

        // Swap the data bytes for the I2C interface
        let phy_data_swapped = ((data >> 8) & 0x00FF) | ((data << 8) & 0xFF00);

        // Set up Op-code, Phy Address, and register address in the I2CCMD
        // register.  The MAC will take care of interfacing with the
        // PHY to retrieve the desired data.
        let i2ccmd = (offset << I2CCMD_REG_ADDR_SHIFT)
            | (self.phy_addr << I2CCMD_PHY_ADDR_SHIFT)
            | I2CCMD_OPCODE_WRITE
            | phy_data_swapped as u32;

        write_reg(info, I2CCMD, i2ccmd)?;

        // Poll the ready bit to see if the I2C read completed
        let mut i2ccmd = 0;
        for _ in 0..I2CCMD_PHY_TIMEOUT {
            awkernel_lib::delay::wait_microsec(50);
            i2ccmd = read_reg(info, I2CCMD)?;
            if i2ccmd & I2CCMD_READY != 0 {
                break;
            }
        }

        if i2ccmd & I2CCMD_READY == 0 {
            log::warn!("igb: I2CCMD Write did not complete.");
            return Err(IgbDriverErr::Phy);
        }

        if i2ccmd & I2CCMD_ERROR != 0 {
            log::warn!("igb: I2CCMD Error bit set.");
            return Err(IgbDriverErr::Phy);
        }

        Ok(())
    }

    /// em_read_phy_reg_i2c - Read PHY register using i2c
    ///
    /// Reads the PHY register at offset using the i2c interface and stores the
    /// retrieved information in data.
    fn read_phy_reg_i2c(&self, info: &PCIeInfo, offset: u32) -> Result<u16, IgbDriverErr> {
        // Set up Op-code, Phy Address, and register address in the I2CCMD
        // register. The MAC will take care of interfacing with the
        // PHY to retrieve the desired data.
        let i2ccmd = (offset << I2CCMD_REG_ADDR_SHIFT)
            | (self.phy_addr << I2CCMD_PHY_ADDR_SHIFT)
            | I2CCMD_OPCODE_READ;

        write_reg(info, I2CCMD, i2ccmd)?;

        // Poll the ready bit to see if the I2C read completed
        let mut i2ccmd = 0;
        for _ in 0..I2CCMD_PHY_TIMEOUT {
            awkernel_lib::delay::wait_microsec(50);
            i2ccmd = read_reg(info, I2CCMD)?;
            if i2ccmd & I2CCMD_READY != 0 {
                break;
            }
        }

        if i2ccmd & I2CCMD_READY == 0 {
            log::warn!("igb: I2CCMD Read did not complete.");
            return Err(IgbDriverErr::Phy);
        }

        if i2ccmd & I2CCMD_ERROR != 0 {
            log::warn!("igb: I2CCMD Error bit set.");
            return Err(IgbDriverErr::Phy);
        }

        // Need to byte-swap the 16-bit value.
        let data = ((i2ccmd >> 8) & 0x00FF) | ((i2ccmd << 8) & 0xFF00);
        Ok(data as u16)
    }

    fn read_phy_reg_ex(&self, info: &PCIeInfo, reg_addr: u32) -> Result<u16, IgbDriverErr> {
        // SGMII active is only set on some specific chips
        if self.sgmii_active && !self.sgmii_uses_mdio_82575(info)? {
            if reg_addr > MAX_SGMII_PHY_REG_ADDR {
                return Err(IgbDriverErr::Param);
            }
            return self.read_phy_reg_i2c(info, reg_addr);
        }

        if reg_addr > MAX_PHY_REG_ADDRESS {
            return Err(IgbDriverErr::Param);
        }

        if matches!(self.mac_type, MacType::EmICPxxxx) {
            return Err(IgbDriverErr::NotSupported);
        }

        if self.mac_type as usize > MacType::Em82543 as usize {
            // Set up Op-code, Phy Address, and register address in the MDI Control register.
            // The MAC will take care of interfacing with the PHY to retrieve the desired data.
            let mdic =
                (reg_addr << MDIC_REG_SHIFT) | (self.phy_addr << MDIC_PHY_SHIFT) | (MDIC_OP_READ);

            write_reg(info, MDIC, mdic)?;

            // Poll the ready bit to see if the MDI read completed
            let mut mdic = 0;
            for _ in 0..1960 {
                awkernel_lib::delay::wait_microsec(50);
                mdic = read_reg(info, MDIC)?;
                if mdic & MDIC_READY != 0 {
                    break;
                }
            }

            if mdic & MDIC_READY == 0 {
                log::warn!("igb: MDI Read did not complete.");
                return Err(IgbDriverErr::Phy);
            }

            if mdic & MDIC_ERROR != 0 {
                log::warn!("igb: MDI Error bit set.");
                return Err(IgbDriverErr::Phy);
            }

            if matches!(
                self.mac_type,
                MacType::EmPch2lan
                    | MacType::EmPchLpt
                    | MacType::EmPchSpt
                    | MacType::EmPchCnp
                    | MacType::EmPchTgp
                    | MacType::EmPchAdp
            ) {
                awkernel_lib::delay::wait_microsec(100);
            }

            Ok(mdic as u16)
        } else {
            Err(IgbDriverErr::NotSupported)
        }
    }

    fn swfw_sync_mut<T, F>(&mut self, info: &PCIeInfo, mask: u16, f: F) -> Result<T, IgbDriverErr>
    where
        F: FnOnce(&mut Self) -> Result<T, IgbDriverErr>,
    {
        self.swfw_sync_acquire(info, mask)?;
        let result = f(self);
        self.swfw_sync_release(info, mask)?;
        result
    }

    /// https://github.com/openbsd/src/blob/d9ecc40d45e66a0a0b11c895967c9bb8f737e659/sys/dev/pci/if_em_hw.c#L4869
    fn swfw_sync_acquire(&mut self, info: &PCIeInfo, mask: u16) -> Result<(), IgbDriverErr> {
        if self.swfwhw_semaphore_present {
            return self.get_software_flag(info);
        }

        if !self.swfw_sync_present {
            return self.get_hw_eeprom_semaphore(info);
        }

        let mut swfw_sync = 0;
        let swmask = mask as u32;
        let fwmask = (mask as u32) << 16;
        let mut timeout = 200;

        while timeout > 0 {
            self.get_hw_eeprom_semaphore(info)?;

            swfw_sync = read_reg(info, SW_FW_SYNC)?;

            if swfw_sync & (fwmask | swmask) == 0 {
                break;
            }

            self.put_hw_eeprom_semaphore(info)?;
            awkernel_lib::delay::wait_millisec(5);
            timeout -= 1;
        }

        if timeout == 0 {
            log::warn!("igb: Driver can't access resource, SW_FW_SYNC timeout.");
            return Err(IgbDriverErr::SwfwSync);
        }

        swfw_sync |= swmask;
        write_reg(info, SW_FW_SYNC, swfw_sync)?;

        self.put_hw_eeprom_semaphore(info)?;

        Ok(())
    }

    fn swfw_sync_release(&mut self, info: &PCIeInfo, mask: u16) -> Result<(), IgbDriverErr> {
        if self.swfwhw_semaphore_present {
            return self.release_software_flag(info);
        }

        if !self.swfw_sync_present {
            return self.put_hw_eeprom_semaphore(info);
        }

        while self.get_hw_eeprom_semaphore(info).is_err() {}

        let swfw_sync = read_reg(info, SW_FW_SYNC)?;
        let swfw_sync = swfw_sync & !(mask as u32);
        write_reg(info, SW_FW_SYNC, swfw_sync)?;

        self.put_hw_eeprom_semaphore(info)
    }

    /// Using the combination of SMBI and SWESMBI semaphore bits when resetting adapter or Eeprom access.
    /// https://github.com/openbsd/src/blob/d9ecc40d45e66a0a0b11c895967c9bb8f737e659/sys/dev/pci/if_em_hw.c#L9719
    fn get_hw_eeprom_semaphore(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if !self.eeprom_semaphore_present {
            return Ok(());
        }

        if self.mac_type == MacType::Em80003es2lan {
            // Get the SW semaphore.
            return self.get_software_semaphore(info);
        }

        // Get the FW semaphore.
        let mut timeout = self.eeprom.word_size + 1;

        while timeout > 0 {
            let swsm = read_reg(info, SWSM)? | SWSM_SWESMBI;
            write_reg(info, SWSM, swsm)?;

            // If we managed to set the bit we got the semaphore.
            let swsm = read_reg(info, SWSM)?;
            if swsm & SWSM_SWESMBI != 0 {
                break;
            }

            awkernel_lib::delay::wait_microsec(50);
            timeout -= 1;
        }

        if timeout == 0 {
            // Release semaphores
            self.put_hw_eeprom_semaphore(info)?;
            log::warn!("igb: Driver can't access the Eeprom - SWESMBI bit is set.");
            Err(IgbDriverErr::Reset)
        } else {
            Ok(())
        }
    }

    fn put_hw_eeprom_semaphore(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if !self.eeprom_semaphore_present {
            return Ok(());
        }

        let swsm = read_reg(info, SWSM)?;
        if matches!(self.mac_type, MacType::Em80003es2lan) {
            // Release both semaphores.
            write_reg(info, SWSM, swsm & !(SWSM_SMBI | SWSM_SWESMBI))?;
        } else {
            write_reg(info, SWSM, swsm & !(SWSM_SWESMBI))?;
        };

        Ok(())
    }

    pub fn legacy_irq_quirk_spt(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if self.mac_type != EmPchSpt
            && self.mac_type != EmPchCnp
            && self.mac_type != EmPchTgp
            && self.mac_type != EmPchAdp
        {
            return Ok(());
        }

        if !self.legacy_irq {
            return Ok(());
        }

        let mut reg = read_reg(info, FEXTNVM7)?;
        reg |= FEXTNVM7_SIDE_CLK_UNGATE;
        write_reg(info, FEXTNVM7, reg)?;

        let mut reg = read_reg(info, FEXTNVM9)?;
        reg |= FEXTNVM9_IOSFSB_CLKGATE_DIS | FEXTNVM9_IOSFSB_CLKREQ_DIS;
        write_reg(info, FEXTNVM9, reg)?;

        Ok(())
    }

    /// Release semaphore bit (SMBI).
    fn release_software_semaphore(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if !matches!(self.mac_type, MacType::Em80003es2lan) {
            return Ok(());
        }

        let swsm = read_reg(info, SWSM)?;

        // Release the SW semaphores.
        let swsm = swsm & !SWSM_SMBI;
        write_reg(info, SWSM, swsm)?;

        Ok(())
    }

    /// Obtaining software semaphore bit (SMBI) before resetting PHY.
    fn get_software_semaphore(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if matches!(self.mac_type, MacType::Em80003es2lan) {
            return Ok(());
        }

        let mut timeout = self.eeprom.word_size + 1;
        while timeout > 0 {
            let swsm = read_reg(info, SWSM)?;

            // If SMBI bit cleared, it is now set and we hold the semaphore
            if swsm & SWSM_SMBI == 0 {
                break;
            }

            awkernel_lib::delay::wait_millisec(1);
            timeout -= 1;
        }

        if timeout == 0 {
            log::warn!("igb: Driver can't access device - SMBI bit is set.");
            Err(IgbDriverErr::Reset)
        } else {
            Ok(())
        }
    }

    fn acquire_software_flag<T, F>(&mut self, info: &PCIeInfo, f: F) -> Result<T, IgbDriverErr>
    where
        F: FnOnce(&mut Self) -> Result<T, IgbDriverErr>,
    {
        self.get_software_flag(info)?;
        let result = f(self);
        self.release_software_flag(info)?;

        result
    }

    /// Get software semaphore FLAG bit (SWFLAG).
    /// SWFLAG is used to synchronize the access to all shared resource between
    /// SW, FW and HW.
    fn get_software_flag(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        let mut timeout = SW_FLAG_TIMEOUT;

        if is_ich8(&self.mac_type) {
            if self.sw_flag != 0 {
                self.sw_flag += 1;
                return Ok(());
            }

            let mut extcnf_ctrl = 0;
            while timeout > 0 {
                extcnf_ctrl = read_reg(info, EXTCNF_CTRL)?;

                if extcnf_ctrl & EXTCNF_CTRL_SWFLAG == 0 {
                    break;
                }

                awkernel_lib::delay::wait_millisec(1);
                timeout -= 1;
            }

            if timeout == 0 {
                log::warn!("igb: SW has already locked the resource?");
                return Err(IgbDriverErr::Config);
            }

            timeout = SW_FLAG_TIMEOUT;
            extcnf_ctrl |= EXTCNF_CTRL_SWFLAG;
            write_reg(info, EXTCNF_CTRL, extcnf_ctrl)?;

            while timeout > 0 {
                extcnf_ctrl = read_reg(info, EXTCNF_CTRL)?;

                if extcnf_ctrl & EXTCNF_CTRL_SWFLAG != 0 {
                    break;
                }

                awkernel_lib::delay::wait_millisec(1);
                timeout -= 1;
            }

            if timeout == 0 {
                log::warn!("igb: Failed to acquire the semaphore, FW or HW has it.");
                extcnf_ctrl &= !EXTCNF_CTRL_SWFLAG;
                write_reg(info, EXTCNF_CTRL, extcnf_ctrl)?;
                return Err(IgbDriverErr::Config);
            }
        }

        self.sw_flag += 1;

        Ok(())
    }

    /// Checks if PHY reset is blocked due to SOL/IDER session, for example.
    /// Returning E1000_BLK_PHY_RESET isn't necessarily an error.  But it's up to
    /// the caller to figure out how to deal with it.
    pub fn check_phy_reset_block(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if is_ich8(&self.mac_type) {
            let mut i = 0;
            let mut blocked = true;

            while blocked && i < 30 {
                let fwsm = read_reg(info, FWSM)?;
                i += 1;

                if (fwsm & FWSM_RSPCIPHY) == 0 {
                    blocked = true;
                    awkernel_lib::delay::wait_millisec(10);
                } else {
                    blocked = false;
                }
            }

            if blocked {
                return Err(IgbDriverErr::PhyReset);
            } else {
                return Ok(());
            }
        }

        let manc = if self.mac_type as u32 > MacType::Em82547Rev2 as u32 {
            read_reg(info, MANC)?
        } else {
            0
        };

        if manc & MANC_BLK_PHY_RST_ON_IDE != 0 {
            Err(IgbDriverErr::PhyReset)
        } else {
            Ok(())
        }
    }

    /// e1000_gate_hw_phy_config_ich8lan - disable PHY config via hardware
    /// - gate: boolean set to TRUE to gate, FALSE to ungate
    ///
    /// Gate/ungate the automatic PHY configuration via hardware; perform
    /// the configuration via software instead.
    fn gate_hw_phy_config_ich8lan(&self, info: &PCIeInfo, gate: bool) -> Result<(), IgbDriverErr> {
        if !matches!(self.mac_type, MacType::EmPch2lan) {
            return Ok(());
        }

        let mut extcnf_ctrl = read_reg(info, EXTCNF_CTRL)?;

        if gate {
            extcnf_ctrl |= EXTCNF_CTRL_GATE_PHY_CFG
        } else {
            extcnf_ctrl &= !EXTCNF_CTRL_GATE_PHY_CFG;
        }

        write_reg(info, EXTCNF_CTRL, extcnf_ctrl)?;

        Ok(())
    }

    /// Reads the adapter's part number from the EEPROM
    pub fn read_part_num(&mut self, info: &PCIeInfo) -> Result<u32, IgbDriverErr> {
        // Get word 0 from EEPROM
        let mut data = [0; 1];
        self.read_eeprom(info, EEPROM_PBA_BYTE_1, &mut data)?;

        // Save word 0 in upper half of part_num
        let mut part_num = (data[0] as u32) << 16;

        // Get word 1 from EEPROM
        self.read_eeprom(info, EEPROM_PBA_BYTE_1 + 1, &mut data)?;

        // Save word 1 in lower half of part_num
        part_num |= data[0] as u32;

        Ok(part_num)
    }

    /// Verifies that the EEPROM has a valid checksum
    ///
    /// Reads the first 64 16 bit words of the EEPROM and sums the values read.
    /// If the sum of the 64 16 bit words is 0xBABA, the EEPROM's checksum is
    /// valid.
    pub fn validate_eeprom_checksum(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        if matches!(self.mac_type, Em82573 | Em82574) && !self.is_onboard_nvm_eeprom(info)? {
            // Check bit 4 of word 10h.  If it is 0, firmware is done
            // updating 10h-12h.  Checksum may need to be fixed.
            let mut eeprom_data = [0; 1];
            self.read_eeprom(info, 0x10, &mut eeprom_data)?;
            if (eeprom_data[0] & 0x10) == 0 {
                // Read 0x23 and check bit 15.  This bit is a 1 when
                // the checksum has already been fixed.  If the
                // checksum is still wrong and this bit is a 1, we
                // need to return bad checksum.  Otherwise, we need
                // to set this bit to a 1 and update the checksum.
                self.read_eeprom(info, 0x23, &mut eeprom_data)?;
                if (eeprom_data[0] & 0x8000) == 0 {
                    eeprom_data[0] |= 0x8000;
                    self.write_eeprom(info, 0x23, &eeprom_data)?;
                    self.update_eeprom_checksum(info)?;
                }
            }
        }

        if is_ich8(&self.mac_type) {
            // Drivers must allocate the shadow ram structure for the
            // EEPROM checksum to be updated.  Otherwise, this bit as
            // well as the checksum must both be set correctly for this
            // validation to pass.
            let (word, valid_csum_mask) = match self.mac_type {
                EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp => {
                    (EEPROM_COMPAT, EEPROM_COMPAT_VALID_CSUM)
                }
                _ => (
                    EEPROM_FUTURE_INIT_WORD1,
                    EEPROM_FUTURE_INIT_WORD1_VALID_CSUM,
                ),
            };

            let mut eeprom_data = [0; 1];
            self.read_eeprom(info, word, &mut eeprom_data)?;
            if (eeprom_data[0] & valid_csum_mask) == 0 {
                eeprom_data[0] |= valid_csum_mask;
                self.write_eeprom(info, word, &eeprom_data)?;
                self.update_eeprom_checksum(info)?;
            }
        }

        let checksum_reg = if self.mac_type != EmICPxxxx {
            EEPROM_CHECKSUM_REG
        } else {
            EEPROM_CHECKSUM_REG_ICP_XXXX
        };

        let mut checksum: u16 = 0;
        for i in 0..=checksum_reg {
            let mut eeprom_data = [0; 1];
            self.read_eeprom(info, i, &mut eeprom_data)?;
            checksum = checksum.wrapping_add(eeprom_data[0]);
        }

        if checksum == EEPROM_SUM {
            Ok(())
        } else {
            Err(IgbDriverErr::EEPROM)
        }
    }

    /// Calculates the EEPROM checksum and writes it to the EEPROM
    ///
    /// Sums the first 63 16 bit words of the EEPROM. Subtracts the sum from 0xBABA.
    /// Writes the difference to word offset 63 of the EEPROM.
    fn update_eeprom_checksum(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        let mut checksum: u16 = 0;
        for i in 0..EEPROM_CHECKSUM_REG {
            let mut eeprom_data = [0; 1];
            self.read_eeprom(info, i, &mut eeprom_data)?;
            checksum += eeprom_data[0];
        }

        let checksum = EEPROM_SUM - checksum;
        self.write_eeprom(info, EEPROM_CHECKSUM_REG, &[checksum])?;

        if self.eeprom.eeprom_type == EEPROMType::Flash {
            self.commit_shadow_ram(info)?;
        } else if self.eeprom.eeprom_type == EEPROMType::Ich8 {
            self.commit_shadow_ram(info)?;

            // Reload the EEPROM, or else modifications will not appear
            // until after next adapter reset.
            let ctrl_ext = read_reg(info, CTRL_EXT)?;
            write_reg(info, CTRL_EXT, ctrl_ext | CTRL_EXT_EE_RST)?;
            awkernel_lib::delay::wait_millisec(10);
        }

        Ok(())
    }

    /// Flushes the cached eeprom to NVM. This is done by saving the modified values
    /// in the eeprom cache and the non modified values in the currently active bank
    /// to the new bank.
    fn commit_shadow_ram(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if matches!(self.mac_type, MacType::Em82573 | MacType::Em82574) {
            // The flop register will be used to determine if flash type is STM
            let flop = read_reg(info, FLOP)?;
            let mut i = 0;
            let mut eecd;
            loop {
                eecd = read_reg(info, EECD)?;
                if eecd & EECD_FLUPD == 0 {
                    break;
                }
                awkernel_lib::delay::wait_microsec(5);

                i += 1;
                if i == 100000 {
                    return Err(IgbDriverErr::EEPROM);
                }
            }

            // If STM opcode located in bits 15:8 of flop, reset firmware
            if (flop & 0xFF00) == STM_OPCODE {
                write_reg(info, HICR, HICR_FW_RESET)?;
            }

            // Perform the flash update
            write_reg(info, EECD, eecd | EECD_FLUPD)?;

            loop {
                eecd = read_reg(info, EECD)?;
                if eecd & EECD_FLUPD == 0 {
                    break;
                }
                awkernel_lib::delay::wait_microsec(5);

                i += 1;
                if i == 100000 {
                    return Err(IgbDriverErr::EEPROM);
                }
            }
        }

        Ok(())
    }

    /// Reads the adapter's MAC address from the EEPROM and inverts the LSB for the
    /// second function of dual function devices
    pub fn read_mac_addr(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        let ia_base_addr = if self.mac_type == EmICPxxxx {
            return Err(IgbDriverErr::NotSupported);
        } else if matches!(self.mac_type, Em82580 | EmI350) {
            nvm_82580_lan_func_offset(self.bus_func)
        } else {
            0
        };

        for i in (0..NODE_ADDRESS_SIZE).step_by(2) {
            let offset = i >> 1;
            let mut eeprom_data = [0; 1];
            self.read_eeprom(info, offset as u32 + ia_base_addr as u32, &mut eeprom_data)?;
            self.perm_mac_addr[i] = (eeprom_data[0] & 0x00FF) as u8;
            self.perm_mac_addr[i + 1] = (eeprom_data[0] >> 8) as u8;
        }

        match self.mac_type {
            Em82546 | Em82546Rev3 | Em82571 | Em82575 | Em82576 | Em80003es2lan => {
                if read_reg(info, STATUS)? & STATUS_FUNC_1 != 0 {
                    self.perm_mac_addr[5] ^= 0x01;
                }
            }
            _ => {}
        }

        for i in 0..NODE_ADDRESS_SIZE {
            self.mac_addr[i] = self.perm_mac_addr[i];
        }

        Ok(())
    }

    pub fn get_mac_addr(&self) -> [u8; NODE_ADDRESS_SIZE] {
        self.mac_addr
    }

    pub fn get_media_type(&self) -> MediaType {
        self.media_type
    }

    pub fn get_tbi_compatibility_on(&self) -> bool {
        self.tbi_compatibility_on
    }

    pub fn set_phy_reset_disable(&mut self, flag: bool) {
        self.phy_reset_disable = flag;
    }

    #[inline]
    pub fn tbi_accept(&self, status: u8, errors: u8, length: u16, addr: VirtAddr) -> bool {
        let ptr = addr.as_ptr::<u8>();
        let buf = unsafe { &*core::ptr::slice_from_raw_parts(ptr, length as usize) };
        let last_byte = buf[length as usize - 1];

        self.tbi_compatibility_on
            && errors & RXD_ERR_FRAME_ERR_MASK == RXD_ERR_CE
            && last_byte == CARRIER_EXTENSION
            && if status & RXD_STAT_VP != 0 {
                length as u32 > self.min_frame_size - VLAN_TAG_SIZE
                    && length as u32 <= self.max_frame_size + 1
            } else {
                length as u32 > self.min_frame_size
                    && length as u32 <= self.max_frame_size + VLAN_TAG_SIZE + 1
            }
    }

    pub fn hash_mc_addr(&self, mac_addr: &[u8; NODE_ADDRESS_SIZE]) -> u32 {
        let mut hash_value = if is_ich8(&self.mac_type) {
            // [47:38] i.e. 0x158 for above example address
            mac_addr[4] as u32 >> 6 | (mac_addr[5] as u32) << 2
        } else {
            // [47:36] i.e. 0x563 for above example address
            mac_addr[4] as u32 >> 4 | (mac_addr[5] as u32) << 4
        };

        hash_value &= 0xFFF;
        if is_ich8(&self.mac_type) {
            hash_value &= 0x3FF;
        }

        hash_value
    }

    /// Sets the bit in the multicast table corresponding to the hash value.
    ///
    /// hw - Struct containing variables accessed by shared code
    /// hash_value - Multicast address hash value
    pub fn mta_set(&self, info: &PCIeInfo, hash_value: u32) -> Result<(), IgbDriverErr> {
        // The MTA is a register array of 128 32-bit registers. It is treated
        // like an array of 4096 bits.  We want to set bit
        // BitArray[hash_value]. So we figure out what register the bit is
        // in, read it, OR in the new bit, then write back the new value.
        // The register is determined by the upper 7 bits of the hash value
        // and the bit within that register are determined by the lower 5
        // bits of the value.
        let mut hash_reg = (hash_value >> 5) & 0x7F;
        if is_ich8(&self.mac_type) {
            hash_reg &= 0x1F;
        }

        let hash_bit = hash_value & 0x1F;

        let mut mta = read_reg_array(info, MTA, hash_reg as usize)?;
        mta |= 1 << hash_bit;

        // If we are on an 82544 and we are trying to write an odd offset in
        // the MTA, save off the previous entry before writing and restore
        // the old value after writing.
        if self.mac_type == MacType::Em82544 && (hash_reg & 0x1) == 1 {
            let temp = read_reg_array(info, MTA, (hash_reg - 1) as usize)?;
            write_reg_array(info, MTA, hash_reg as usize, mta)?;
            write_flush(info)?;
            write_reg_array(info, MTA, (hash_reg - 1) as usize, temp)?;
            write_flush(info)?;
        } else {
            write_reg_array(info, MTA, hash_reg as usize, mta)?;
            write_flush(info)?;
        }

        Ok(())
    }

    pub fn clear_mta(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        let num_mta_entry = if is_ich8(&self.mac_type) {
            NUM_MTA_REGISTERS_ICH8LAN
        } else {
            NUM_MTA_REGISTERS
        };

        for i in 0..num_mta_entry {
            write_reg_array(info, MTA, i, 0)?;
            write_flush(info)?;
        }

        Ok(())
    }
}

fn nvm_82580_lan_func_offset(a: u8) -> u16 {
    if a == 0 {
        0
    } else {
        0x40 + (0x40 * a as u16)
    }
}

/// The defaults for 82575 and 82576 should be in the range of 50us to 50ms,
/// however the hardware default for these parts is 500us to 1ms which is less
/// than the 10ms recommended by the pci-e spec.  To address this we need to
/// increase the value to either 10ms to 200ms for capability version 1 config,
/// or 16ms to 55ms for version 2.
fn set_pciex_completion_timeout(info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    let mut gcr = read_reg(info, GCR)?;

    // Only take action if timeout value is not set by system BIOS
    //
    // If capabilities version is type 1 we can write the
    // timeout of 10ms to 200ms through the GCR register
    if gcr & GCR_CMPL_TMOUT_MASK == 0 && gcr & GCR_CAP_VER2 == 0 {
        gcr |= GCR_CMPL_TMOUT_10_MS;
    }

    // Disable completion timeout resend
    gcr &= GCR_CMPL_TMOUT_RESEND;

    write_reg(info, GCR, gcr)?;

    Ok(())
}

/// https://github.com/openbsd/src/blob/da407c5b03f3f213fdfa21192733861c3bdeeb5f/sys/dev/pci/if_em_hw.c#L9559
fn disable_pciex_master(info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    set_pcie_express_master_disable(info)?;

    for _ in 0..MASTER_DISABLE_TIMEOUT {
        if read_reg(info, CTRL)? & CTRL_GIO_MASTER_DISABLE != 0 {
            return Ok(());
        }
    }

    Err(IgbDriverErr::MasterDisableTimeout)
}

/// https://github.com/openbsd/src/blob/da407c5b03f3f213fdfa21192733861c3bdeeb5f/sys/dev/pci/if_em_hw.c#L9533
fn set_pcie_express_master_disable(info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    let ctrl = read_reg(info, CTRL)?;
    write_reg(info, CTRL, ctrl | CTRL_GIO_MASTER_DISABLE)?;

    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum EEPROMType {
    Microwire,
    Spi,
    Flash,
    Ich8,
    Invm,
}

#[derive(Debug)]
struct Eeprom {
    eeprom_type: EEPROMType,
    page_size: Option<u16>,
    word_size: u16,
    address_bits: u16,
    delay_usec: u16,
    opcode_bits: u16,
    use_eerd: bool,
    use_eewr: bool,
}

impl Eeprom {
    /// Return `(EEPROM, flash_base_address, flash_bank_size)`.
    ///
    /// https://github.com/openbsd/src/blob/8e9ff1e61e136829a715052f888f67d3617fc787/sys/dev/pci/if_em_hw.c#L6280
    fn new(
        mac_type: &MacType,
        flash_memory: &Option<FlashMemory>,
        info: &PCIeInfo,
    ) -> Result<(Self, Option<usize>, Option<usize>), IgbDriverErr> {
        use MacType::*;

        let mut bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
        let eecd = bar0.read32(EECD).ok_or(IgbDriverErr::ReadFailure)?;

        let mut result = match mac_type {
            Em82542Rev2_0 | Em82542Rev2_1 | Em82543 | Em82544 => (
                Self {
                    eeprom_type: EEPROMType::Microwire,
                    page_size: None,
                    word_size: 64,
                    address_bits: 6,
                    delay_usec: 50,
                    opcode_bits: 3,
                    use_eerd: false,
                    use_eewr: false,
                },
                None,
                None,
            ),
            Em82540 | Em82545 | Em82545Rev3 | Em82546 | Em82546Rev3 => {
                let (word_size, address_bits) = if eecd & EECD_SIZE != 0 {
                    (256, 8)
                } else {
                    (64, 6)
                };

                (
                    Self {
                        eeprom_type: EEPROMType::Microwire,
                        opcode_bits: 3,
                        page_size: None,
                        delay_usec: 50,
                        word_size,
                        address_bits,
                        use_eerd: false,
                        use_eewr: false,
                    },
                    None,
                    None,
                )
            }
            Em82541 | Em82541Rev2 | Em82547 | Em82547Rev2 => {
                if eecd & EECD_TYPE != 0 {
                    let (page_size, address_bits) = if eecd & EECD_ADDR_BITS != 0 {
                        (32, 16)
                    } else {
                        (8, 8)
                    };

                    (
                        Self {
                            eeprom_type: EEPROMType::Spi,
                            opcode_bits: 8,
                            delay_usec: 1,
                            page_size: Some(page_size),
                            word_size: 0, // SPI's word size will be set later.
                            address_bits,
                            use_eerd: false,
                            use_eewr: false,
                        },
                        None,
                        None,
                    )
                } else {
                    let (word_size, address_bits) = if eecd & EECD_ADDR_BITS != 0 {
                        (256, 8)
                    } else {
                        (64, 6)
                    };

                    (
                        Self {
                            eeprom_type: EEPROMType::Microwire,
                            opcode_bits: 3,
                            delay_usec: 50,
                            page_size: None,
                            word_size,
                            address_bits,
                            use_eerd: false,
                            use_eewr: false,
                        },
                        None,
                        None,
                    )
                }
            }
            Em82571 | Em82572 => {
                let (page_size, address_bits) = if eecd & EECD_ADDR_BITS != 0 {
                    (32, 16)
                } else {
                    (8, 8)
                };

                (
                    Self {
                        eeprom_type: EEPROMType::Spi,
                        opcode_bits: 8,
                        delay_usec: 1,
                        word_size: 0, // SPI's word size will be set later.
                        page_size: Some(page_size),
                        address_bits,
                        use_eerd: false,
                        use_eewr: false,
                    },
                    None,
                    None,
                )
            }
            Em82573 | Em82574 | Em82575 | Em82576 | Em82580 | EmI210 | EmI350 => {
                let (page_size, address_bits) = if eecd & EECD_ADDR_BITS != 0 {
                    (32, 16)
                } else {
                    (8, 8)
                };

                let (eeprom_type, word_size, use_eerd, use_eewr) =
                    if !get_flash_presence_i210(mac_type, info)? {
                        (EEPROMType::Invm, INVM_SIZE, false, false)
                    } else if !is_onboard_nvm_eeprom(mac_type, info)? {
                        let eecd = eecd & !EECD_AUPDEN;
                        bar0.write32(EECD, eecd);

                        (EEPROMType::Flash, 2048, true, true)
                    } else {
                        // SPI's word size will be set later.
                        (EEPROMType::Spi, 0, true, true)
                    };

                (
                    Self {
                        eeprom_type,
                        opcode_bits: 8,
                        delay_usec: 1,
                        page_size: Some(page_size),
                        word_size,
                        address_bits,
                        use_eerd,
                        use_eewr,
                    },
                    None,
                    None,
                )
            }
            Em80003es2lan => {
                let (page_size, address_bits) = if eecd & EECD_ADDR_BITS != 0 {
                    (32, 16)
                } else {
                    (8, 8)
                };

                (
                    Self {
                        eeprom_type: EEPROMType::Spi,
                        opcode_bits: 8,
                        delay_usec: 1,
                        page_size: Some(page_size),
                        word_size: 0, // SPI's word size will be set later.
                        address_bits,
                        use_eerd: true,
                        use_eewr: false,
                    },
                    None,
                    None,
                )
            }
            EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan | EmPchLpt => {
                let flash_memory = flash_memory.as_ref().ok_or(IgbDriverErr::ReadFailure)?;

                let flash_size = flash_memory
                    .base_address
                    .read32(ICH_FLASH_GFPREG + flash_memory.offset)
                    .ok_or(IgbDriverErr::ReadFailure)?;

                // https://github.com/openbsd/src/blob/4ff40062e57fb8a42d28dcb700c25b8254514628/sys/dev/pci/if_em_hw.c#L6434C12-L6434C29
                // `eeprom_shadow_ram` may not be used?

                let flash_base_addr = (flash_size & ICH_GFPREG_BASE_MASK) * ICH_FLASH_SECTOR_SIZE;

                let mut flash_bank_size = ((flash_size >> 16) & ICH_GFPREG_BASE_MASK) + 1;
                flash_bank_size -= flash_size & ICH_GFPREG_BASE_MASK;
                flash_bank_size *= ICH_FLASH_SECTOR_SIZE;
                flash_bank_size /= 2 * core::mem::size_of::<u16>() as u32;

                (
                    Self {
                        eeprom_type: EEPROMType::Ich8,
                        opcode_bits: 0,
                        delay_usec: 0,
                        page_size: None,
                        word_size: SHADOW_RAM_WORDS,
                        address_bits: 0,
                        use_eerd: false,
                        use_eewr: false,
                    },
                    Some(flash_base_addr as usize),
                    Some(flash_bank_size as usize),
                )
            }
            EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp => {
                let flash_size = bar0
                    .read32(0xc /* STRAP */)
                    .ok_or(IgbDriverErr::ReadFailure)?;

                let mut flash_size = (flash_size >> 1 & 0x1f) + 1;
                flash_size *= 1024;

                (
                    Self {
                        eeprom_type: EEPROMType::Ich8,
                        opcode_bits: 0,
                        delay_usec: 0,
                        page_size: None,
                        word_size: SHADOW_RAM_WORDS,
                        address_bits: 0,
                        use_eerd: false,
                        use_eewr: false,
                    },
                    Some(0),
                    Some(flash_size as usize),
                )
            }
            EmICPxxxx => {
                return Err(IgbDriverErr::NotSupported);
            }
        };

        if matches!(result.0.eeprom_type, EEPROMType::Spi) {
            if *mac_type as u32 <= Em82547Rev2 as u32 {
                return Err(IgbDriverErr::NotSupported);
            }

            let eecd = bar0.read32(EECD).ok_or(IgbDriverErr::ReadFailure)?;
            let eeprom_size = (eecd & EECD_SIZE_EX_MASK) >> EECD_SIZE_EX_SHIFT;

            // EEPROM access above 16k is unsupported
            if eeprom_size + EEPROM_WORD_SIZE_SHIFT > EEPROM_WORD_SIZE_SHIFT_MAX {
                result.0.word_size = 1 << EEPROM_WORD_SIZE_SHIFT_MAX;
            } else {
                result.0.word_size = 1 << (eeprom_size + EEPROM_WORD_SIZE_SHIFT);
            }
        }

        Ok(result)
    }
}

fn is_onboard_nvm_eeprom(mac_type: &MacType, info: &PCIeInfo) -> Result<bool, IgbDriverErr> {
    use MacType::*;

    if is_ich8(mac_type) {
        return Ok(false);
    }

    if matches!(mac_type, Em82573 | Em82574) {
        let eecd = read_reg(info, EECD)?;

        // Isolate bits 15 & 16
        let eecd = (eecd >> 15) & 0x03;

        // If both bits are set, device is Flash type
        if eecd == 0x03 {
            return Ok(false);
        }
    }

    Ok(true)
}

pub fn get_flash_presence_i210(mac_type: &MacType, info: &PCIeInfo) -> Result<bool, IgbDriverErr> {
    if *mac_type != MacType::EmI210 {
        return Ok(true);
    }

    let eecd = read_reg(info, EECD)?;
    Ok(eecd & EECD_FLUPD != 0)
}

/// Set media type and TBI compatibility.
/// Return `(tbi_compatibility_en, media_type, sgmii_active)`.
fn set_media_type(
    mac_type: &MacType,
    info: &PCIeInfo,
) -> Result<(bool, MediaType, bool), IgbDriverErr> {
    use MacType::*;

    let mut tbi_compatibility_en = true;
    let mut sgmii_active = false;

    if matches!(mac_type, Em82543) {
        // tbi_compatibility is only valid on 82543
        tbi_compatibility_en = false;
    }

    if matches!(mac_type, Em82575 | Em82580 | Em82576 | EmI210 | EmI350) {
        let mut media_type = MediaType::Copper;
        let mut ctrl_ext = read_reg(info, CTRL_EXT)?;
        let mode = ctrl_ext & CTRL_EXT_LINK_MODE_MASK;

        match mode {
            CTRL_EXT_LINK_MODE_1000BASE_KX => {
                media_type = MediaType::InternalSerdes;
                ctrl_ext |= CTRL_I2C_ENA;
            }
            CTRL_EXT_LINK_MODE_SGMII | CTRL_EXT_LINK_MODE_PCIE_SERDES => {
                if mode == CTRL_EXT_LINK_MODE_SGMII {
                    let mdic = read_reg(info, MDICNFG)?;

                    ctrl_ext |= CTRL_I2C_ENA;

                    if mdic & MDICNFG_EXT_MDIO != 0 {
                        sgmii_active = true;
                    }
                }

                ctrl_ext |= CTRL_I2C_ENA;

                match set_sfp_media_type_82575(info) {
                    Ok((media_type_ret, sgmii_active_ret)) => {
                        media_type = media_type_ret;
                        sgmii_active = sgmii_active_ret;
                    }
                    _ => {
                        media_type = MediaType::InternalSerdes;

                        if (ctrl_ext & CTRL_EXT_LINK_MODE_MASK) == CTRL_EXT_LINK_MODE_SGMII {
                            media_type = MediaType::Copper;
                            sgmii_active = true;
                        }
                    }
                }

                ctrl_ext &= !CTRL_EXT_LINK_MODE_MASK;

                if sgmii_active {
                    ctrl_ext |= CTRL_EXT_LINK_MODE_SGMII;
                } else {
                    ctrl_ext |= CTRL_EXT_LINK_MODE_PCIE_SERDES;
                }
            }
            _ => {
                ctrl_ext &= !CTRL_I2C_ENA;
            }
        }

        write_reg(info, CTRL_EXT, ctrl_ext)?;
        return Ok((tbi_compatibility_en, media_type, sgmii_active));
    }

    match info.get_id() {
        E1000_DEV_ID_82545GM_SERDES
        | E1000_DEV_ID_82546GB_SERDES
        | E1000_DEV_ID_82571EB_SERDES
        | E1000_DEV_ID_82571EB_SERDES_DUAL
        | E1000_DEV_ID_82571EB_SERDES_QUAD
        | E1000_DEV_ID_82572EI_SERDES
        | E1000_DEV_ID_80003ES2LAN_SERDES_DPT => Ok((
            tbi_compatibility_en,
            MediaType::InternalSerdes,
            sgmii_active,
        )),
        E1000_DEV_ID_EP80579_LAN_1
        | E1000_DEV_ID_EP80579_LAN_2
        | E1000_DEV_ID_EP80579_LAN_3
        | E1000_DEV_ID_EP80579_LAN_4
        | E1000_DEV_ID_EP80579_LAN_5
        | E1000_DEV_ID_EP80579_LAN_6 => Ok((tbi_compatibility_en, MediaType::Copper, sgmii_active)),
        _ => match mac_type {
            Em82542Rev2_0 | Em82542Rev2_1 => {
                Ok((tbi_compatibility_en, MediaType::Fiber, sgmii_active))
            }
            EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt
            | EmPchCnp | EmPchTgp | EmPchAdp | Em82573 | Em82574 => {
                Ok((tbi_compatibility_en, MediaType::Copper, sgmii_active))
            }
            _ => {
                let status = read_reg(info, STATUS)?;

                if status & STATUS_TBIMODE != 0 {
                    // tbi_compatibility is not valid on fiber
                    Ok((false, MediaType::Fiber, sgmii_active))
                } else {
                    Ok((tbi_compatibility_en, MediaType::Copper, sgmii_active))
                }
            }
        },
    }
}

bitflags::bitflags! {
    // Flags for SFP modules compatible with ETH up to 1Gb
    struct SfpE1000Flags: u8 {
        const E1000_BASE_SX = 1;
        const E1000_BASE_LX = 1 << 1;
        const E1000_BASE_CX = 1 << 2;
        const E1000_BASE_T = 1 << 3;
        const E100_BASE_LX = 1 << 4;
        const E100_BASE_FX = 1 << 5;
        const E10_BASE_BX10 = 1 << 6;
        const E10_BASE_PX = 1 << 7;
    }
}

/// em_set_sfp_media_type_82575 - derives SFP module media type.
/// Return `(media_type, sgmii_active)`.
fn set_sfp_media_type_82575(info: &PCIeInfo) -> Result<(MediaType, bool), IgbDriverErr> {
    // Turn I2C interface ON and power on sfp cage
    let ctrl_ext = read_reg(info, CTRL_EXT)?;
    let ctrl_ext = ctrl_ext & !CTRL_EXT_SDP3_DATA;
    write_reg(info, CTRL_EXT, ctrl_ext)?;

    write_flush(info)?;

    // Read SFP module data
    let mut timeout = 3;
    let mut transceiver_type = 0;
    while timeout > 0 {
        match read_sfp_data_byte(info, i2ccd_sfp_data_addr(SFF_IDENTIFIER_OFFSET)) {
            Ok(val) => {
                transceiver_type = val;
                break;
            }
            Err(_) => {
                awkernel_lib::delay::wait_millisec(100);
                timeout -= 1;
            }
        }
    }

    if timeout == 0 {
        write_reg(info, CTRL_EXT, ctrl_ext)?;
        return Err(IgbDriverErr::Phy);
    }

    let Ok(eth_flags) = read_sfp_data_byte(info, i2ccd_sfp_data_addr(SFF_ETH_FLAGS_OFFSET)) else {
        write_reg(info, CTRL_EXT, ctrl_ext)?;
        return Err(IgbDriverErr::Phy);
    };

    let eth_flags = SfpE1000Flags::from_bits_truncate(eth_flags);

    // Check if there is some SFP module plugged and powered
    let result = if transceiver_type == SFF_IDENTIFIER_SFP || transceiver_type == SFF_IDENTIFIER_SFF
    {
        if eth_flags.contains(SfpE1000Flags::E1000_BASE_LX)
            || eth_flags.contains(SfpE1000Flags::E1000_BASE_SX)
        {
            (MediaType::InternalSerdes, false)
        } else if eth_flags.contains(SfpE1000Flags::E100_BASE_FX)
            || eth_flags.contains(SfpE1000Flags::E100_BASE_LX)
        {
            (MediaType::InternalSerdes, true)
        } else if eth_flags.contains(SfpE1000Flags::E1000_BASE_T) {
            (MediaType::Copper, true)
        } else {
            write_reg(info, CTRL_EXT, ctrl_ext)?;
            return Err(IgbDriverErr::Config);
        }
    } else {
        write_reg(info, CTRL_EXT, ctrl_ext)?;
        return Err(IgbDriverErr::Config);
    };

    write_reg(info, CTRL_EXT, ctrl_ext)?;
    Ok(result)
}

fn read_sfp_data_byte(info: &PCIeInfo, offset: u32) -> Result<u8, IgbDriverErr> {
    if offset > i2ccd_sfp_data_addr(255) {
        return Err(IgbDriverErr::Phy);
    }

    // Set up Op-code, EEPROM Address, in the I2CCMD register.
    // The MAC will take care of interfacing with the EEPROM to retrieve the desired data.
    let i2ccmd = (offset << I2CCMD_REG_ADDR_SHIFT) | I2CCMD_OPCODE_READ;
    write_reg(info, I2CCMD, i2ccmd)?;

    let mut data_local = 0;

    // Poll the ready bit to see if the I2C read completed
    for _ in 0..I2CCMD_PHY_TIMEOUT {
        awkernel_lib::delay::wait_microsec(50);

        data_local = read_reg(info, I2CCMD)?;
        if data_local & I2CCMD_READY != 0 {
            break;
        }
    }

    if data_local & I2CCMD_READY == 0 {
        return Err(IgbDriverErr::Phy);
    }

    if data_local & I2CCMD_ERROR != 0 {
        return Err(IgbDriverErr::Phy);
    }

    Ok((data_local & 0xFF) as u8)
}

fn i2ccd_sfp_data_addr(a: u32) -> u32 {
    0x100 + a
}

#[inline(always)]
pub fn write_reg(info: &PCIeInfo, offset: usize, value: u32) -> Result<(), IgbDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
    bar0.write32(offset, value);
    Ok(())
}

#[inline(always)]
pub fn write_reg_array(
    info: &PCIeInfo,
    offset: usize,
    index: usize,
    value: u32,
) -> Result<(), IgbDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
    bar0.write32(offset + (index << 2), value);
    Ok(())
}

#[inline(always)]
pub fn read_reg(info: &PCIeInfo, offset: usize) -> Result<u32, IgbDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
    bar0.read32(offset).ok_or(IgbDriverErr::ReadFailure)
}

#[inline(always)]
pub fn read_reg_array(info: &PCIeInfo, offset: usize, index: usize) -> Result<u32, IgbDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
    bar0.read32(offset + (index << 2))
        .ok_or(IgbDriverErr::ReadFailure)
}

#[inline(always)]
pub fn write_flush(info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
    bar0.read32(STATUS).ok_or(IgbDriverErr::ReadFailure)?;
    Ok(())
}

fn bm_phy_reg_num(offset: u32) -> u16 {
    ((offset & MAX_PHY_REG_ADDRESS)
        | ((offset >> (PHY_UPPER_SHIFT - PHY_PAGE_SHIFT)) & !MAX_PHY_REG_ADDRESS)) as u16
}

fn bm_phy_reg_page(offset: u32) -> u16 {
    ((offset >> PHY_PAGE_SHIFT) & 0xFFFF) as u16
}

#[inline(always)]
fn invm_data_reg(reg: usize) -> usize {
    0x12120 + 4 * reg
}

#[inline(always)]
fn invm_dward_to_recored_type(dword: u32) -> u8 {
    (dword & 0x7) as u8
}

#[inline(always)]
fn invm_dward_to_dword_address(dword: u32) -> u16 {
    ((dword & 0x0000FE00) >> 9) as u16
}

#[inline(always)]
fn invm_dward_to_dword_data(dword: u32) -> u16 {
    ((dword & 0xFFFF0000) >> 16) as u16
}

/// Due to hw errata, if the host tries to configure the VFTA register
/// while performing queries from the BMC or DMA, then the VFTA in some
/// cases won't be written.
fn clear_vfta_i350(info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    for offset in 0..VLAN_FILTER_TBL_SIZE {
        for _ in 0..10 {
            write_reg_array(info, VFTA, offset, 0)?;
        }
        write_flush(info)?;
    }

    Ok(())
}

/// This function calculates the checksum.
fn calculate_mng_checksum(buffer: &HostMngDhcpCookie) -> u8 {
    let buffer: &[u8; 16] = unsafe { core::mem::transmute(buffer) };

    let mut sum: u8 = 0;
    for buf in buffer.iter() {
        sum = sum.wrapping_add(*buf);
    }

    let z: u8 = 0;
    z.wrapping_sub(sum)
}

pub fn get_num_queues(mac_type: &MacType) -> usize {
    use MacType::*;

    match mac_type {
        Em82576 | Em82580 | EmI350 => 8,
        Em82575 | EmI210 => 4,
        Em82574 => 2,
        _ => 1,
    }
}
