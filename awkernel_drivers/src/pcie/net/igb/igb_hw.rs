use crate::pcie::{pcie_id::INTEL_VENDOR_ID, BaseAddress, PCIeInfo};

use super::IgbDriverErr;

const E1000_DEV_ID_82543GC_FIBER: u16 = 0x1001;
const E1000_DEV_ID_82542: u16 = 0x1000;
const E1000_DEV_ID_82543GC_COPPER: u16 = 0x1004;
const E1000_DEV_ID_82544EI_COPPER: u16 = 0x1008;
const E1000_DEV_ID_82544EI_FIBER: u16 = 0x1009;
const E1000_DEV_ID_82544GC_COPPER: u16 = 0x100C;
const E1000_DEV_ID_82544GC_LOM: u16 = 0x100D;
const E1000_DEV_ID_82540EM: u16 = 0x100E;
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

// PBA constants
const E1000_PBA_8K: u32 = 0x0008; /* 8KB, default Rx allocation */
const _E1000_PBA_10K: u32 = 0x000A;
const _E1000_PBA_12K: u32 = 0x000C; /* 12KB, default Rx allocation */
const _E1000_PBA_14K: u32 = 0x000E; /* 14KB */
const E1000_PBA_16K: u32 = 0x0010; /* 16KB, default TX allocation */
const _E1000_PBA_20K: u32 = 0x0014;
const _E1000_PBA_22K: u32 = 0x0016;
const _E1000_PBA_24K: u32 = 0x0018;
const _E1000_PBA_26K: u32 = 0x001A;
const _E1000_PBA_30K: u32 = 0x001E;
const _E1000_PBA_32K: u32 = 0x0020;
const _E1000_PBA_34K: u32 = 0x0022;
const _E1000_PBA_38K: u32 = 0x0026;
const _E1000_PBA_40K: u32 = 0x0028;
const _E1000_PBA_48K: u32 = 0x0030; /* 48KB, default RX allocation */

const E1000_PBS_16K: u32 = E1000_PBA_16K;

const SW_FLAG_TIMEOUT: usize = 100;

#[derive(Debug)]
pub struct IgbHw {
    mac_type: MacType,
    initialize_hw_bits_disable: bool,
    eee_enable: bool,
    icp_intel_vendor_idx_port_num: u8,
    swfwhw_semaphore_present: bool,
    asf_firmware_present: bool,
    swfw_sync_present: bool,
    eeprom_semaphore_present: bool,
    phy_reset_disable: bool,
    flash_memory: Option<(BaseAddress, usize)>, // (base address, offset)
    flash_bank_size: Option<usize>,
    flash_base_address: Option<usize>,
    eeprom: EEPROM,
    tbi_compatibility_on: bool,
    sw_flag: isize,
}

#[derive(Debug, Clone)]
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

/// Return `(MacType, initialize_hw_bits_disable, eee_enable, icp_intel_vendor_idx_port_num)`.
///
/// https://github.com/openbsd/src/blob/f058c8dbc8e3b2524b639ac291b898c7cc708996/sys/dev/pci/if_em_hw.c#L403
fn get_mac_type(device: u16, info: &PCIeInfo) -> Result<(MacType, bool, bool, u8), IgbDriverErr> {
    use MacType::*;

    let mut initialize_hw_bits_disable = false;
    let mut eee_enable = false;
    let mut icp_intel_vendor_idx_port_num = 0;

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
        | E1000_DEV_ID_82540EP_LP => Em82540,
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
            icp_intel_vendor_idx_port_num = 0;
            EmICPxxxx
        }
        E1000_DEV_ID_EP80579_LAN_2 | E1000_DEV_ID_EP80579_LAN_4 => {
            icp_intel_vendor_idx_port_num = 1;
            EmICPxxxx
        }
        E1000_DEV_ID_EP80579_LAN_3 | E1000_DEV_ID_EP80579_LAN_5 => {
            icp_intel_vendor_idx_port_num = 2;
            EmICPxxxx
        }
        E1000_DEV_ID_EP80579_LAN_6 => {
            icp_intel_vendor_idx_port_num = 3;
            EmICPxxxx
        }
        _ => return Err(IgbDriverErr::UnknownDeviceID),
    };

    Ok((
        result,
        initialize_hw_bits_disable,
        eee_enable,
        icp_intel_vendor_idx_port_num,
    ))
}

/// Return (swfwhw_semaphore_present, asf_firmware_present, swfw_sync_present, eeprom_semaphore_present).
fn get_hw_info(mac_type: &MacType) -> (bool, bool, bool, bool) {
    use MacType::*;

    let mut swfwhw_semaphore_present = false;
    let mut asf_firmware_present = false;
    let mut swfw_sync_present = false;
    let mut eeprom_semaphore_present = false;

    match mac_type {
        EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt
        | EmPchCnp | EmPchTgp | EmPchAdp => {
            swfwhw_semaphore_present = true;
            asf_firmware_present = true;
        }
        Em80003es2lan | Em82575 | Em82576 | Em82580 | EmI350 | EmI210 => {
            swfw_sync_present = true;
        }
        Em82571 | Em82572 | Em82573 | Em82574 => {
            eeprom_semaphore_present = true;
        }
        Em82547 | Em82542Rev2_1 | Em82547Rev2 => {
            asf_firmware_present = true;
        }
        _ => (),
    }

    (
        swfwhw_semaphore_present,
        asf_firmware_present,
        swfw_sync_present,
        eeprom_semaphore_present,
    )
}

/// Reject non-PCI Express devices.
///
/// https://github.com/openbsd/src/blob/d88178ae581240e08c6acece5c276298d1ac6c90/sys/dev/pci/if_em_hw.c#L8381
fn check_pci_express(mac_type: &MacType) -> Result<(), IgbDriverErr> {
    use MacType::*;

    match mac_type {
        Em82571 | Em82572 | Em82573 | Em82574 | Em82575 | Em82576 | Em82580 | Em80003es2lan
        | EmI210 | EmI350 | EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan
        | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp => Ok(()),
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

impl IgbHw {
    pub fn new(info: &mut PCIeInfo) -> Result<Self, IgbDriverErr> {
        let (mac_type, initialize_hw_bits_disable, eee_enable, icp_intel_vendor_idx_port_num) =
            get_mac_type(info.get_id(), info)?;

        check_pci_express(&mac_type)?;

        let (
            swfwhw_semaphore_present,
            asf_firmware_present,
            swfw_sync_present,
            eeprom_semaphore_present,
        ) = get_hw_info(&mac_type);

        if matches!(mac_type, MacType::EmPchlan) {
            info.set_revision_id((info.get_id() & 0x0f) as u8);
        }

        // https://github.com/openbsd/src/blob/d88178ae581240e08c6acece5c276298d1ac6c90/sys/dev/pci/if_em.c#L1720-L1740
        let flash_memory = if matches!(mac_type, MacType::EmPchSpt) {
            Some((info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?, 0xe000))
        } else if is_ich8(&mac_type) {
            let bar1 = info.get_bar(1).ok_or(IgbDriverErr::NoBar1)?;
            if matches!(bar1, BaseAddress::MMIO { .. }) {
                Some((bar1, 0))
            } else {
                return Err(IgbDriverErr::Bar1IsNotMMIO);
            }
        } else {
            None
        };

        let (eeprom, flash_base_address, flash_bank_size) =
            EEPROM::new(&mac_type, &flash_memory, info)?;

        let hw = Self {
            mac_type,
            initialize_hw_bits_disable,
            eee_enable,
            icp_intel_vendor_idx_port_num,
            swfwhw_semaphore_present,
            asf_firmware_present,
            swfw_sync_present,
            eeprom_semaphore_present,
            phy_reset_disable: false,
            flash_memory,
            flash_base_address,
            flash_bank_size,
            eeprom,
            tbi_compatibility_on: false,
            sw_flag: 0,
        };

        Ok(hw)
    }

    pub fn get_mac_type(&self) -> MacType {
        self.mac_type.clone()
    }

    /// https://github.com/openbsd/src/blob/f058c8dbc8e3b2524b639ac291b898c7cc708996/sys/dev/pci/if_em_hw.c#L1559
    fn init_hw(info: &PCIeInfo) {
        todo!();
    }

    /// https://github.com/openbsd/src/blob/18bc31b7ebc17ab66d1354464ff2ee3ba31f7750/sys/dev/pci/if_em_hw.c#L925
    pub fn reset_hw(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        use MacType::*;

        let mut bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;

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
        bar0.write(super::IMC, !0);

        // Disable the Transmit and Receive units.  Then delay to allow any
        // pending transactions to complete before we hit the MAC with the
        // global reset.
        bar0.write(super::RCTL, 0);
        bar0.write(super::TCTL, super::TCTL_PSP);
        bar0.read(super::STATUS); // flush

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
            let mut extcnf_ctrl = bar0
                .read(super::EXTCNF_CTRL)
                .ok_or(IgbDriverErr::ReadFailure)?;

            extcnf_ctrl |= super::EXTCNF_CTRL_MDIO_SW_OWNERSHIP;

            for _ in 0..10 {
                bar0.write(super::EXTCNF_CTRL, extcnf_ctrl);

                if extcnf_ctrl & super::EXTCNF_CTRL_MDIO_SW_OWNERSHIP != 0 {
                    break;
                } else {
                    extcnf_ctrl |= super::EXTCNF_CTRL_MDIO_SW_OWNERSHIP;
                }

                awkernel_lib::delay::wait_millisec(2);
            }
        }

        // Workaround for ICH8 bit corruption issue in FIFO memory
        if matches!(self.mac_type, EmIch8lan) {
            // Set Tx and Rx buffer allocation to 8k apiece.
            bar0.write(super::PBA, E1000_PBA_8K);

            // Set Packet Buffer Size to 16k.
            bar0.write(super::PBS, E1000_PBS_16K);
        }

        match self.mac_type {
            EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt
            | EmPchCnp | EmPchTgp | EmPchAdp => {
                let mut ctrl = bar0.read(super::CTRL).ok_or(IgbDriverErr::ReadFailure)?;

                if !self.phy_reset_disable && self.check_phy_reset_block(info).is_ok() {
                    // PHY HW reset requires MAC CORE reset at the same
                    // time to make sure the interface between MAC and
                    // the external PHY is reset.
                    ctrl |= super::CTRL_PHY_RST;

                    // Gate automatic PHY configuration by hardware on non-managed 82579
                    if matches!(self.mac_type, EmPch2lan)
                        && bar0.read(super::FWSM).ok_or(IgbDriverErr::ReadFailure)?
                            & super::FWSM_FW_VALID
                            == 0
                    {
                        self.gate_hw_phy_config_ich8lan(info, true)?;
                    }
                };

                self.get_software_flag(info)?;
                bar0.write(super::CTRL, ctrl | super::CTRL_RST);

                // HW reset releases software_flag
                self.sw_flag = 0;
                awkernel_lib::delay::wait_millisec(20);

                // Ungate automatic PHY configuration on non-managed 82579
                if matches!(self.mac_type, EmPch2lan)
                    && !self.phy_reset_disable
                    && bar0.read(super::FWSM).ok_or(IgbDriverErr::ReadFailure)?
                        & super::FWSM_FW_VALID
                        == 0
                {
                    awkernel_lib::delay::wait_millisec(10);
                    self.gate_hw_phy_config_ich8lan(info, false)?;
                }
            }
            _ => {
                let ctrl = bar0.read(super::CTRL).ok_or(IgbDriverErr::ReadFailure)?;
                bar0.write(super::CTRL, ctrl | super::CTRL_RST);
            }
        }

        // TODO
        // https://github.com/openbsd/src/blob/310206ba8923a6e59fdbb6eae66d8488b45fe1d8/sys/dev/pci/if_em_hw.c#L1095-L1106

        Ok(())
    }

    /// Get software semaphore FLAG bit (SWFLAG).
    /// SWFLAG is used to synchronize the access to all shared resource between
    /// SW, FW and HW.
    fn get_software_flag(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        let mut timeout = SW_FLAG_TIMEOUT;
        let mut bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;

        if is_ich8(&self.mac_type) {
            if self.sw_flag != 0 {
                self.sw_flag -= 1;
                return Ok(());
            }

            let mut extcnf_ctrl = 0;
            while timeout > 0 {
                extcnf_ctrl = bar0
                    .read(super::EXTCNF_CTRL)
                    .ok_or(IgbDriverErr::ReadFailure)?;

                if extcnf_ctrl & super::EXTCNF_CTRL_SWFLAG == 0 {
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
            extcnf_ctrl |= super::EXTCNF_CTRL_SWFLAG;
            bar0.write(super::EXTCNF_CTRL, extcnf_ctrl);

            while timeout > 0 {
                extcnf_ctrl = bar0
                    .read(super::EXTCNF_CTRL)
                    .ok_or(IgbDriverErr::ReadFailure)?;

                if extcnf_ctrl & super::EXTCNF_CTRL_SWFLAG != 0 {
                    break;
                }

                awkernel_lib::delay::wait_millisec(1);
                timeout -= 1;
            }

            if timeout == 0 {
                log::warn!("igb: Failed to acquire the semaphore, FW or HW has it.");
                extcnf_ctrl &= !super::EXTCNF_CTRL_SWFLAG;
                bar0.write(super::EXTCNF_CTRL, extcnf_ctrl);
                return Err(IgbDriverErr::Config);
            }
        }

        self.sw_flag += 1;

        Ok(())
    }

    /// Checks if PHY reset is blocked due to SOL/IDER session, for example.
    /// Returning E1000_BLK_PHY_RESET isn't necessarily an error.  But it's up to
    /// the caller to figure out how to deal with it.
    fn check_phy_reset_block(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        let bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;

        if is_ich8(&self.mac_type) {
            let mut i = 0;
            let mut blocked = true;

            while blocked && i < 30 {
                let fwsm = bar0.read(super::FWSM).ok_or(IgbDriverErr::ReadFailure)?;
                i += 1;

                if (fwsm & super::FWSM_RSPCIPHY) == 0 {
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

        let manc = if self.mac_type.clone() as u32 > MacType::Em82547Rev2 as u32 {
            bar0.read(super::MANC).ok_or(IgbDriverErr::ReadFailure)?
        } else {
            0
        };

        if manc & super::MANC_BLK_PHY_RST_ON_IDE != 0 {
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

        let mut bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;

        let mut extcnf_ctrl = bar0
            .read(super::EXTCNF_CTRL)
            .ok_or(IgbDriverErr::ReadFailure)?;

        if gate {
            extcnf_ctrl |= super::EXTCNF_CTRL_GATE_PHY_CFG
        } else {
            extcnf_ctrl &= !super::EXTCNF_CTRL_GATE_PHY_CFG;
        }

        bar0.write(super::EXTCNF_CTRL, extcnf_ctrl);

        Ok(())
    }
}

const MASTER_DISABLE_TIMEOUT: u32 = 800;

/// The defaults for 82575 and 82576 should be in the range of 50us to 50ms,
/// however the hardware default for these parts is 500us to 1ms which is less
/// than the 10ms recommended by the pci-e spec.  To address this we need to
/// increase the value to either 10ms to 200ms for capability version 1 config,
/// or 16ms to 55ms for version 2.
fn set_pciex_completion_timeout(info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;

    let mut gcr = bar0.read(super::GCR).ok_or(IgbDriverErr::ReadFailure)?;

    // Only take action if timeout value is not set by system BIOS
    //
    // If capabilities version is type 1 we can write the
    // timeout of 10ms to 200ms through the GCR register
    if gcr & super::GCR_CMPL_TMOUT_MASK == 0 && gcr & super::GCR_CAP_VER2 != 0 {
        gcr |= super::GCR_CMPL_TMOUT_10_MS;
    }

    // Disable completion timeout resend
    gcr &= super::GCR_CMPL_TMOUT_RESEND;

    bar0.write(super::GCR, gcr);

    Ok(())
}

/// https://github.com/openbsd/src/blob/da407c5b03f3f213fdfa21192733861c3bdeeb5f/sys/dev/pci/if_em_hw.c#L9559
fn disable_pciex_master(info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;

    set_pcie_express_master_disable(info)?;

    for _ in 0..MASTER_DISABLE_TIMEOUT {
        if bar0.read(super::CTRL).ok_or(IgbDriverErr::ReadFailure)? & super::CTRL_GIO_MASTER_DISABLE
            != 0
        {
            return Ok(());
        }
    }

    Err(IgbDriverErr::MasterDisableTimeout)
}

/// https://github.com/openbsd/src/blob/da407c5b03f3f213fdfa21192733861c3bdeeb5f/sys/dev/pci/if_em_hw.c#L9533
fn set_pcie_express_master_disable(info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
    let ctrl = bar0.read(super::CTRL).ok_or(IgbDriverErr::ReadFailure)?;
    bar0.write(super::CTRL, ctrl | super::CTRL_GIO_MASTER_DISABLE);

    Ok(())
}

#[derive(Debug, Clone)]
enum EEPROMType {
    Microwire,
    SPI,
    Flash,
    Ich8,
    Invm,
}

#[derive(Debug)]
struct EEPROM {
    eeprom_type: EEPROMType,
    page_size: Option<u16>,
    word_size: u16,
    address_bits: u16,
    delay_usec: u16,
    opcode_bits: u16,
    use_eerd: bool,
    use_eewr: bool,
}

const E1000_EECD_SIZE: u32 = 0x00000200;
const E1000_EECD_ADDR_BITS: u32 = 0x00000400;
const E1000_EECD_TYPE: u32 = 0x00002000;
const E1000_EECD_FLUPD: u32 = 0x00080000;
const E1000_EECD_AUPDEN: u32 = 0x00100000;

const E1000_EECD_SIZE_EX_MASK: u32 = 0x00007800;
const E1000_EECD_SIZE_EX_SHIFT: u32 = 11;
const EEPROM_WORD_SIZE_SHIFT: u32 = 6;
const EEPROM_WORD_SIZE_SHIFT_MAX: u32 = 14;

const E1000_SHADOW_RAM_WORDS: u16 = 2048;

const INVM_SIZE: u16 = 64;

const ICH_FLASH_GFPREG: usize = 0x0000;

const ICH_GFPREG_BASE_MASK: u32 = 0x1FFF;
const ICH_FLASH_SECTOR_SIZE: u32 = 4096;

impl EEPROM {
    /// Return `(EEPROM, flash_base_address, flash_bank_size)`.
    ///
    /// https://github.com/openbsd/src/blob/8e9ff1e61e136829a715052f888f67d3617fc787/sys/dev/pci/if_em_hw.c#L6280
    fn new(
        mac_type: &MacType,
        flash_memory: &Option<(BaseAddress, usize)>,
        info: &PCIeInfo,
    ) -> Result<(Self, Option<usize>, Option<usize>), IgbDriverErr> {
        use MacType::*;

        let mut bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
        let eecd = bar0.read(super::EECD).ok_or(IgbDriverErr::ReadFailure)?;

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
                let (word_size, address_bits) = if eecd & E1000_EECD_SIZE != 0 {
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
                if eecd & E1000_EECD_TYPE != 0 {
                    let (page_size, address_bits) = if eecd & E1000_EECD_ADDR_BITS != 0 {
                        (32, 16)
                    } else {
                        (8, 8)
                    };

                    (
                        Self {
                            eeprom_type: EEPROMType::SPI,
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
                    let (word_size, address_bits) = if eecd & E1000_EECD_ADDR_BITS != 0 {
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
                let (page_size, address_bits) = if eecd & E1000_EECD_ADDR_BITS != 0 {
                    (32, 16)
                } else {
                    (8, 8)
                };

                (
                    Self {
                        eeprom_type: EEPROMType::SPI,
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
                let (page_size, address_bits) = if eecd & E1000_EECD_ADDR_BITS != 0 {
                    (32, 16)
                } else {
                    (8, 8)
                };

                let (eeprom_type, word_size, use_eerd, use_eewr) =
                    if !get_flash_presence_i210(mac_type, info)? {
                        (EEPROMType::Invm, INVM_SIZE, false, false)
                    } else if !is_onboard_nvm_eeprom(mac_type, info)? {
                        let eecd = eecd & !E1000_EECD_AUPDEN;
                        bar0.write(super::EECD, eecd);

                        (EEPROMType::Flash, 2048, true, true)
                    } else {
                        // SPI's word size will be set later.
                        (EEPROMType::SPI, 0, true, true)
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
                let (page_size, address_bits) = if eecd & E1000_EECD_ADDR_BITS != 0 {
                    (32, 16)
                } else {
                    (8, 8)
                };

                (
                    Self {
                        eeprom_type: EEPROMType::SPI,
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
                let (flash_memory, offset) =
                    flash_memory.as_ref().ok_or(IgbDriverErr::ReadFailure)?;

                let flash_size = flash_memory
                    .read(*offset + ICH_FLASH_GFPREG)
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
                        word_size: E1000_SHADOW_RAM_WORDS,
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
                    .read(0xc /* STRAP */)
                    .ok_or(IgbDriverErr::ReadFailure)?;

                let mut flash_size = (flash_size >> 1 & 0x1f) + 1;
                flash_size *= 1024;

                (
                    Self {
                        eeprom_type: EEPROMType::Ich8,
                        opcode_bits: 0,
                        delay_usec: 0,
                        page_size: None,
                        word_size: E1000_SHADOW_RAM_WORDS,
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

        if matches!(result.0.eeprom_type, EEPROMType::SPI) {
            if mac_type.clone() as u32 <= Em82547Rev2 as u32 {
                return Err(IgbDriverErr::NotSupported);
            }

            let eecd = bar0.read(super::EECD).ok_or(IgbDriverErr::ReadFailure)?;
            let eeprom_size = (eecd & E1000_EECD_SIZE_EX_MASK) >> E1000_EECD_SIZE_EX_SHIFT;

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
        let bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
        let eecd = bar0.read(super::EECD).ok_or(IgbDriverErr::ReadFailure)?;

        // Isolate bits 15 & 16
        let eecd = (eecd >> 15) & 0x03;

        // If both bits are set, device is Flash type
        if eecd == 0x03 {
            return Ok(false);
        }
    }

    Ok(true)
}

fn get_flash_presence_i210(mac_type: &MacType, info: &PCIeInfo) -> Result<bool, IgbDriverErr> {
    if matches!(mac_type, MacType::EmI210) {
        return Ok(true);
    }

    let bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
    let eecd = bar0.read(super::EECD).ok_or(IgbDriverErr::ReadFailure)?;

    if eecd & E1000_EECD_FLUPD != 0 {
        Ok(true)
    } else {
        Ok(false)
    }
}
