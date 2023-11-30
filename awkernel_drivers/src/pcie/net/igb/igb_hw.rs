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

const MAX_PHY_REG_ADDRESS: u32 = 0x1F; // 5 bit address bus (0-0x1F)

// IGP01E1000 Specific Registers
const _IGP01E1000_PHY_PORT_CONFIG: u32 = 0x10; /* PHY Specific Port Config Register */
const _IGP01E1000_PHY_PORT_STATUS: u32 = 0x11; /* PHY Specific Status Register */
const _IGP01E1000_PHY_PORT_CTRL: u32 = 0x12; /* PHY Specific Control Register */
const _IGP01E1000_PHY_LINK_HEALTH: u32 = 0x13; /* PHY Link Health Register */
const _IGP01E1000_GMII_FIFO: u32 = 0x14; /* GMII FIFO Register */
const _IGP01E1000_PHY_CHANNEL_QUALITY: u32 = 0x15; /* PHY Channel Quality Register */
const _IGP02E1000_PHY_POWER_MGMT: u32 = 0x19;
const IGP01E1000_PHY_PAGE_SELECT: u32 = 0x1F; /* PHY Page Select Core Register */

// BM/HV Specific Registers
const BM_PORT_CTRL_PAGE: u16 = 769;
const _BM_PCIE_PAGE: u16 = 770;
const BM_WUC_PAGE: u16 = 800;
const BM_WUC_ADDRESS_OPCODE: u32 = 0x11;
const BM_WUC_DATA_OPCODE: u32 = 0x12;
const BM_WUC_ENABLE_PAGE: u16 = BM_PORT_CTRL_PAGE;
const BM_WUC_ENABLE_REG: u32 = 17;
const BM_WUC_ENABLE_BIT: u16 = 1 << 2;
const BM_WUC_HOST_WU_BIT: u16 = 1 << 4;

const PHY_PAGE_SHIFT: u32 = 5;
const PHY_UPPER_SHIFT: u32 = 21;

// SW_W_SYNC definitions
const _SWFW_EEP_SM: u16 = 0x0001;
const SWFW_PHY0_SM: u16 = 0x0002;
const _SWFW_PHY1_SM: u16 = 0x0004;
const _SWFW_MAC_CSR_SM: u16 = 0x0008;
const _SWFW_PHY2_SM: u16 = 0x0020;
const _SWFW_PHY3_SM: u16 = 0x0040;

#[derive(Debug)]
pub enum MediaType {
    Copper,
    Fiber,
    InternalSerdes,
    OEM,
}

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
    tbi_compatibility_en: bool,
    media_type: MediaType,
    sgmii_active: bool,
    sw_flag: isize,
    phy_addr: u32,
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

        let (tbi_compatibility_en, media_type, sgmii_active) = set_media_type(&mac_type, info)?;

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
            tbi_compatibility_en,
            media_type,
            sgmii_active,
            sw_flag: 0,
            phy_addr: 0,
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

        // TODO
        // https://github.com/openbsd/src/blob/310206ba8923a6e59fdbb6eae66d8488b45fe1d8/sys/dev/pci/if_em_hw.c#L1113

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

            let extcnf_ctrl = read_reg(info, super::EXTCNF_CTRL)?;
            let extcnf_ctrl = extcnf_ctrl & !super::EXTCNF_CTRL_SWFLAG;
            write_reg(info, super::EXTCNF_CTRL, extcnf_ctrl)?;
        }

        Ok(())
    }

    /// A series of Phy workarounds to be done after every PHY reset.
    fn hv_phy_workarounds_ich8lan(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        todo!()
    }

    /// em_lv_phy_workarounds_ich8lan - A series of Phy workarounds to be
    /// done after every PHY reset.
    fn lv_phy_workarounds_ich8lan(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        todo!()
    }

    /// Set slow MDIO access mode
    fn set_mdio_slow_mode_hv(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        todo!()
    }

    fn read_phy_reg(&self) -> Result<(), IgbDriverErr> {
        todo!()
    }

    /// Reads or writes the value from a PHY register, if the value is on a specific non zero page, sets the page first.
    /// https://github.com/openbsd/src/blob/d9ecc40d45e66a0a0b11c895967c9bb8f737e659/sys/dev/pci/if_em_hw.c#L5064
    fn access_phy_reg_hv(
        &mut self,
        info: &PCIeInfo,
        reg_addr: u32,
        read: bool,
    ) -> Result<Option<u16>, IgbDriverErr> {
        let swfw = SWFW_PHY0_SM;

        self.swfw_sync_acquire(info, swfw)?;

        let page = bm_phy_reg_page(reg_addr);

        todo!()
    }

    //     5063 int32_t
    // 5064 em_access_phy_reg_hv(struct em_hw *hw, uint32_t reg_addr, uint16_t *phy_data,
    //      /* [previous][next][first][last][top][bottom][index][help]  */
    // 5065     boolean_t read)
    // 5066 {
    // 5067         uint32_t ret_val;
    // 5068         uint16_t swfw;
    // 5069         uint16_t page = BM_PHY_REG_PAGE(reg_addr);
    // 5070         uint16_t reg = BM_PHY_REG_NUM(reg_addr);
    // 5071
    // 5072         DEBUGFUNC("em_access_phy_reg_hv");
    // 5073
    // 5074         swfw = E1000_SWFW_PHY0_SM;
    // 5075
    // 5076         if (em_swfw_sync_acquire(hw, swfw))
    // 5077                 return -E1000_ERR_SWFW_SYNC;
    // 5078
    // 5079         if (page == BM_WUC_PAGE) {
    // 5080                 ret_val = em_access_phy_wakeup_reg_bm(hw, reg_addr,
    // 5081                     phy_data, read);
    // 5082                 goto release;
    // 5083         }
    // 5084
    // 5085         if (page >= HV_INTC_FC_PAGE_START)
    // 5086                 hw->phy_addr = 1;
    // 5087         else
    // 5088                 hw->phy_addr = 2;
    // 5089
    // 5090         if (page == HV_INTC_FC_PAGE_START)
    // 5091                 page = 0;
    // 5092
    // 5093         /*
    // 5094          * Workaround MDIO accesses being disabled after entering IEEE Power
    // 5095          * Down (whenever bit 11 of the PHY Control register is set)
    // 5096          */
    // 5097         if (!read &&
    // 5098             (hw->phy_type == em_phy_82578) &&
    // 5099             (hw->phy_revision >= 1) &&
    // 5100             (hw->phy_addr == 2) &&
    // 5101             ((MAX_PHY_REG_ADDRESS & reg) == 0) &&
    // 5102             (*phy_data & (1 << 11))) {
    // 5103                 uint16_t data2 = 0x7EFF;
    // 5104
    // 5105                 ret_val = em_access_phy_debug_regs_hv(hw, (1 << 6) | 0x3,
    // 5106                     &data2, FALSE);
    // 5107                 if (ret_val)
    // 5108                         return ret_val;
    // 5109         }
    // 5110
    // 5111         if (reg_addr > MAX_PHY_MULTI_PAGE_REG) {
    // 5112                 ret_val = em_write_phy_reg_ex(hw, IGP01E1000_PHY_PAGE_SELECT,
    // 5113                     (page << PHY_PAGE_SHIFT));
    // 5114                 if (ret_val)
    // 5115                         return ret_val;
    // 5116         }
    // 5117         if (read)
    // 5118                 ret_val = em_read_phy_reg_ex(hw, MAX_PHY_REG_ADDRESS & reg,
    // 5119                     phy_data);
    // 5120         else
    // 5121                 ret_val = em_write_phy_reg_ex(hw, MAX_PHY_REG_ADDRESS & reg,
    // 5122                     *phy_data);
    // 5123 release:
    // 5124         em_swfw_sync_release(hw, swfw);
    // 5125         return ret_val;
    // 5126 }

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
            if reg_addr > super::MAX_SGMII_PHY_REG_ADDR {
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

        if self.mac_type.clone() as usize > MacType::Em82543 as usize {
            // Set up Op-code, Phy Address, register address, and data
            // intended for the PHY register in the MDI Control register.
            // The MAC will take care of interfacing with the PHY to send
            // the desired data.

            let mdic = ((phy_data as u32)
                | (reg_addr << super::MDIC_REG_SHIFT)
                | (self.phy_addr << super::MDIC_PHY_SHIFT)
                | (super::MDIC_OP_WRITE)) as u32;

            write_reg(info, super::MDIC, mdic)?;

            // Poll the ready bit to see if the MDI read completed
            let mut mdic = 0;
            for _ in 0..641 {
                awkernel_lib::delay::wait_microsec(5);
                mdic = read_reg(info, super::MDIC)?;
                if mdic & super::MDIC_READY != 0 {
                    break;
                }
            }

            if mdic & super::MDIC_READY == 0 {
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
                let reg = read_reg(info, super::MDIC)?;
                Ok(reg & super::MDIC_DEST != 0)
            }
            MacType::Em82580 | MacType::EmI350 | MacType::EmI210 => {
                let reg = read_reg(info, super::MDICNFG)?;
                Ok(reg & super::MDICNFG_EXT_MDIO != 0)
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
        let i2ccmd = (offset << super::I2CCMD_REG_ADDR_SHIFT)
            | (self.phy_addr << super::I2CCMD_PHY_ADDR_SHIFT)
            | super::I2CCMD_OPCODE_WRITE
            | phy_data_swapped as u32;

        write_reg(info, super::I2CCMD, i2ccmd)?;

        // Poll the ready bit to see if the I2C read completed
        let mut i2ccmd = 0;
        for _ in 0..super::I2CCMD_PHY_TIMEOUT {
            awkernel_lib::delay::wait_microsec(50);
            i2ccmd = read_reg(info, super::I2CCMD)?;
            if i2ccmd & super::I2CCMD_READY != 0 {
                break;
            }
        }

        if i2ccmd & super::I2CCMD_READY == 0 {
            log::warn!("igb: I2CCMD Write did not complete.");
            return Err(IgbDriverErr::Phy);
        }

        if i2ccmd & super::I2CCMD_ERROR != 0 {
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
        let i2ccmd = (offset << super::I2CCMD_REG_ADDR_SHIFT)
            | (self.phy_addr << super::I2CCMD_PHY_ADDR_SHIFT)
            | super::I2CCMD_OPCODE_READ;

        write_reg(info, super::I2CCMD, i2ccmd)?;

        // Poll the ready bit to see if the I2C read completed
        let mut i2ccmd = 0;
        for _ in 0..super::I2CCMD_PHY_TIMEOUT {
            awkernel_lib::delay::wait_microsec(50);
            i2ccmd = read_reg(info, super::I2CCMD)?;
            if i2ccmd & super::I2CCMD_READY != 0 {
                break;
            }
        }

        if i2ccmd & super::I2CCMD_READY == 0 {
            log::warn!("igb: I2CCMD Read did not complete.");
            return Err(IgbDriverErr::Phy);
        }

        if i2ccmd & super::I2CCMD_ERROR != 0 {
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
            if reg_addr > super::MAX_SGMII_PHY_REG_ADDR {
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

        if self.mac_type.clone() as usize > MacType::Em82543 as usize {
            // Set up Op-code, Phy Address, and register address in the MDI Control register.
            // The MAC will take care of interfacing with the PHY to retrieve the desired data.
            let mdic = ((reg_addr << super::MDIC_REG_SHIFT)
                | (self.phy_addr << super::MDIC_PHY_SHIFT)
                | (super::MDIC_OP_READ)) as u32;

            write_reg(info, super::MDIC, mdic)?;

            // Poll the ready bit to see if the MDI read completed
            let mut mdic = 0;
            for _ in 0..1960 {
                awkernel_lib::delay::wait_microsec(50);
                mdic = read_reg(info, super::MDIC)?;
                if mdic & super::MDIC_READY != 0 {
                    break;
                }
            }

            if mdic & super::MDIC_READY == 0 {
                log::warn!("igb: MDI Read did not complete.");
                return Err(IgbDriverErr::Phy);
            }

            if mdic & super::MDIC_ERROR != 0 {
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
        let fwmask = (mask << 16) as u32;
        let mut timeout = 200;

        while timeout > 0 {
            if self.get_hw_eeprom_semaphore(info).is_ok() {
                return Err(IgbDriverErr::SwfwSync);
            }

            swfw_sync = read_reg(info, super::SW_FW_SYNC)?;

            if swfw_sync & (fwmask | swmask) != 0 {
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
        write_reg(info, super::SW_FW_SYNC, swfw_sync)?;

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

        let swfw_sync = read_reg(info, super::SW_FW_SYNC)?;
        let swfw_sync = swfw_sync & !(mask as u32);
        write_reg(info, super::SW_FW_SYNC, swfw_sync)?;

        self.put_hw_eeprom_semaphore(info)
    }

    /// Using the combination of SMBI and SWESMBI semaphore bits when resetting adapter or Eeprom access.
    /// https://github.com/openbsd/src/blob/d9ecc40d45e66a0a0b11c895967c9bb8f737e659/sys/dev/pci/if_em_hw.c#L9719
    fn get_hw_eeprom_semaphore(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if self.eeprom_semaphore_present {
            return Ok(());
        }

        if matches!(self.mac_type, MacType::Em80003es2lan) {
            // Get the SW semaphore.
            return self.get_software_semaphore(info);
        }

        // Get the FW semaphore.
        let mut timeout = self.eeprom.word_size + 1;

        while timeout > 0 {
            let swsm = read_reg(info, super::SWSM)? | super::SWSM_SWESMBI;
            write_reg(info, super::SWSM, swsm)?;

            // If we managed to set the bit we got the semaphore.
            let swsm = read_reg(info, super::SWSM)?;
            if swsm & super::SWSM_SWESMBI != 0 {
                break;
            }

            awkernel_lib::delay::wait_microsec(50);
            timeout -= 1;
        }

        if timeout == 0 {
            // Release semaphores
            self.put_hw_eeprom_semaphore(info)?;
            log::warn!("igb: Driver can't access the Eeprom - SWESMBI bit is set.");
            return Err(IgbDriverErr::Reset);
        } else {
            Ok(())
        }
    }

    fn put_hw_eeprom_semaphore(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if !self.eeprom_semaphore_present {
            return Ok(());
        }

        let swsm = read_reg(info, super::SWSM)?;
        if matches!(self.mac_type, MacType::Em80003es2lan) {
            // Release both semaphores.
            write_reg(
                info,
                super::SWSM,
                swsm & !(super::SWSM_SMBI | super::SWSM_SWESMBI),
            )?;
        } else {
            write_reg(info, super::SWSM, swsm & !(super::SWSM_SWESMBI))?;
        };

        Ok(())
    }

    /// Obtaining software semaphore bit (SMBI) before resetting PHY.
    fn get_software_semaphore(&self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        if matches!(self.mac_type, MacType::Em80003es2lan) {
            return Ok(());
        }

        let mut timeout = self.eeprom.word_size + 1;
        while timeout > 0 {
            let swsm = read_reg(info, super::SWSM)?;

            // If SMBI bit cleared, it is now set and we hold the semaphore
            if swsm & super::SWSM_SMBI == 0 {
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

    /// Get software semaphore FLAG bit (SWFLAG).
    /// SWFLAG is used to synchronize the access to all shared resource between
    /// SW, FW and HW.
    fn get_software_flag(&mut self, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
        let mut timeout = SW_FLAG_TIMEOUT;

        if is_ich8(&self.mac_type) {
            if self.sw_flag != 0 {
                self.sw_flag -= 1;
                return Ok(());
            }

            let mut extcnf_ctrl = 0;
            while timeout > 0 {
                extcnf_ctrl = read_reg(info, super::EXTCNF_CTRL)?;

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
            write_reg(info, super::EXTCNF_CTRL, extcnf_ctrl)?;

            while timeout > 0 {
                extcnf_ctrl = read_reg(info, super::EXTCNF_CTRL)?;

                if extcnf_ctrl & super::EXTCNF_CTRL_SWFLAG != 0 {
                    break;
                }

                awkernel_lib::delay::wait_millisec(1);
                timeout -= 1;
            }

            if timeout == 0 {
                log::warn!("igb: Failed to acquire the semaphore, FW or HW has it.");
                extcnf_ctrl &= !super::EXTCNF_CTRL_SWFLAG;
                write_reg(info, super::EXTCNF_CTRL, extcnf_ctrl)?;
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
        if is_ich8(&self.mac_type) {
            let mut i = 0;
            let mut blocked = true;

            while blocked && i < 30 {
                let fwsm = read_reg(info, super::FWSM)?;
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
            read_reg(info, super::MANC)?
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

        let mut extcnf_ctrl = read_reg(info, super::EXTCNF_CTRL)?;

        if gate {
            extcnf_ctrl |= super::EXTCNF_CTRL_GATE_PHY_CFG
        } else {
            extcnf_ctrl &= !super::EXTCNF_CTRL_GATE_PHY_CFG;
        }

        write_reg(info, super::EXTCNF_CTRL, extcnf_ctrl)?;

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
    let mut gcr = read_reg(info, super::GCR)?;

    // Only take action if timeout value is not set by system BIOS
    //
    // If capabilities version is type 1 we can write the
    // timeout of 10ms to 200ms through the GCR register
    if gcr & super::GCR_CMPL_TMOUT_MASK == 0 && gcr & super::GCR_CAP_VER2 != 0 {
        gcr |= super::GCR_CMPL_TMOUT_10_MS;
    }

    // Disable completion timeout resend
    gcr &= super::GCR_CMPL_TMOUT_RESEND;

    write_reg(info, super::GCR, gcr)?;

    Ok(())
}

/// https://github.com/openbsd/src/blob/da407c5b03f3f213fdfa21192733861c3bdeeb5f/sys/dev/pci/if_em_hw.c#L9559
fn disable_pciex_master(info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    set_pcie_express_master_disable(info)?;

    for _ in 0..MASTER_DISABLE_TIMEOUT {
        if read_reg(info, super::CTRL)? & super::CTRL_GIO_MASTER_DISABLE != 0 {
            return Ok(());
        }
    }

    Err(IgbDriverErr::MasterDisableTimeout)
}

/// https://github.com/openbsd/src/blob/da407c5b03f3f213fdfa21192733861c3bdeeb5f/sys/dev/pci/if_em_hw.c#L9533
fn set_pcie_express_master_disable(info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    let ctrl = read_reg(info, super::CTRL)?;
    write_reg(info, super::CTRL, ctrl | super::CTRL_GIO_MASTER_DISABLE)?;

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
        let eecd = read_reg(info, super::EECD)?;

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

    let eecd = read_reg(info, super::EECD)?;

    if eecd & E1000_EECD_FLUPD != 0 {
        Ok(true)
    } else {
        Ok(false)
    }
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
        let mut ctrl_ext = read_reg(info, super::CTRL_EXT)?;

        match ctrl_ext & super::CTRL_EXT_LINK_MODE_MASK {
            super::CTRL_EXT_LINK_MODE_1000BASE_KX => {
                media_type = MediaType::InternalSerdes;
                ctrl_ext |= super::CTRL_I2C_ENA;
            }
            super::CTRL_EXT_LINK_MODE_SGMII => {
                let mdic = read_reg(info, super::MDICNFG)?;

                ctrl_ext |= super::CTRL_I2C_ENA;

                if mdic & super::MDICNFG_EXT_MDIO != 0 {
                    media_type = MediaType::Copper;
                    sgmii_active = true;
                }

                // FALLTHROUGH
            }
            super::CTRL_EXT_LINK_MODE_PCIE_SERDES => {
                ctrl_ext |= super::CTRL_I2C_ENA;

                match set_sfp_media_type_82575(info) {
                    Ok((media_type_ret, sgmii_active_ret)) => {
                        media_type = media_type_ret;
                        sgmii_active = sgmii_active_ret;
                    }
                    _ => {
                        media_type = MediaType::InternalSerdes;

                        if (ctrl_ext & super::CTRL_EXT_LINK_MODE_MASK)
                            == super::CTRL_EXT_LINK_MODE_SGMII
                        {
                            media_type = MediaType::Copper;
                            sgmii_active = true;
                        }
                    }
                }

                ctrl_ext &= !super::CTRL_EXT_LINK_MODE_MASK;

                if sgmii_active {
                    ctrl_ext |= super::CTRL_EXT_LINK_MODE_SGMII;
                } else {
                    ctrl_ext |= super::CTRL_EXT_LINK_MODE_PCIE_SERDES;
                }
            }
            _ => {
                ctrl_ext &= !super::CTRL_I2C_ENA;
            }
        }

        write_reg(info, super::CTRL_EXT, ctrl_ext)?;
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
                let status = read_reg(info, super::STATUS)?;

                if status & super::STATUS_TBIMODE != 0 {
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
    let ctrl_ext = read_reg(info, super::CTRL_EXT)?;
    let ctrl_ext = ctrl_ext & !super::CTRL_EXT_SDP3_DATA;
    write_reg(info, super::CTRL_EXT, ctrl_ext)?;

    write_flush(info)?;

    // Read SFP module data
    let mut timeout = 3;
    let mut transceiver_type = 0;
    while timeout > 0 {
        match read_sfp_data_byte(info, i2ccd_sfp_data_addr(super::SFF_IDENTIFIER_OFFSET)) {
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
        write_reg(info, super::CTRL_EXT, ctrl_ext)?;
        return Err(IgbDriverErr::Phy);
    }

    let Ok(eth_flags) = read_sfp_data_byte(info, i2ccd_sfp_data_addr(super::SFF_ETH_FLAGS_OFFSET)) else {
        write_reg(info, super::CTRL_EXT, ctrl_ext)?;
        return Err(IgbDriverErr::Phy);
    };

    let eth_flags = SfpE1000Flags::from_bits_truncate(eth_flags);

    // Check if there is some SFP module plugged and powered
    let result = if transceiver_type == super::SFF_IDENTIFIER_SFP
        || transceiver_type == super::SFF_IDENTIFIER_SFF
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
            write_reg(info, super::CTRL_EXT, ctrl_ext)?;
            return Err(IgbDriverErr::Config);
        }
    } else {
        write_reg(info, super::CTRL_EXT, ctrl_ext)?;
        return Err(IgbDriverErr::Config);
    };

    write_reg(info, super::CTRL_EXT, ctrl_ext)?;
    Ok(result)
}

fn read_sfp_data_byte(info: &PCIeInfo, offset: u32) -> Result<u8, IgbDriverErr> {
    if offset > i2ccd_sfp_data_addr(255) {
        return Err(IgbDriverErr::Phy);
    }

    // Set up Op-code, EEPROM Address, in the I2CCMD register.
    // The MAC will take care of interfacing with the EEPROM to retrieve the desired data.
    let i2ccmd = (offset << super::I2CCMD_REG_ADDR_SHIFT) | super::I2CCMD_OPCODE_READ;
    write_reg(info, super::I2CCMD, i2ccmd)?;

    let mut data_local = 0;

    // Poll the ready bit to see if the I2C read completed
    for _ in 0..super::I2CCMD_PHY_TIMEOUT {
        awkernel_lib::delay::wait_microsec(50);

        data_local = read_reg(info, super::I2CCMD)?;
        if data_local & super::I2CCMD_READY != 0 {
            break;
        }
    }

    if data_local & super::I2CCMD_READY == 0 {
        return Err(IgbDriverErr::Phy);
    }

    if data_local & super::I2CCMD_ERROR != 0 {
        return Err(IgbDriverErr::Phy);
    }

    Ok((data_local & 0xFF) as u8)
}

fn i2ccd_sfp_data_addr(a: u32) -> u32 {
    0x100 + a
}

#[inline(always)]
fn write_reg(info: &PCIeInfo, offset: usize, value: u32) -> Result<(), IgbDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
    bar0.write(offset, value);
    Ok(())
}

#[inline(always)]
fn read_reg(info: &PCIeInfo, offset: usize) -> Result<u32, IgbDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
    Ok(bar0.read(offset).ok_or(IgbDriverErr::ReadFailure)?)
}

#[inline(always)]
fn write_flush(info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;
    bar0.read(super::STATUS).ok_or(IgbDriverErr::ReadFailure)?;
    Ok(())
}

fn bm_phy_reg_num(offset: u32) -> u16 {
    ((offset & MAX_PHY_REG_ADDRESS)
        | ((offset >> (PHY_UPPER_SHIFT - PHY_PAGE_SHIFT)) & !MAX_PHY_REG_ADDRESS)) as u16
}

fn bm_phy_reg_page(offset: u32) -> u16 {
    ((offset >> PHY_PAGE_SHIFT) & 0xFFFF) as u16
}
