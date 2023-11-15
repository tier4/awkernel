use crate::pcie::{pcie_id::INTEL_VENDOR_ID, BaseAddress, DeviceInfo};

use super::E1000DriverErr;

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

#[derive(Debug)]
pub struct E1000Hw {
    mac_type: MacType,
    initialize_hw_bits_disable: bool,
    eee_enable: bool,
    icp_intel_vendor_idx_port_num: u8,
    swfwhw_semaphore_present: bool,
    asf_firmware_present: bool,
    swfw_sync_present: bool,
    eeprom_semaphore_present: bool,
    phy_init_script: bool,
    flash_memory: Option<(BaseAddress, usize)>, // (base address, offset)
}

#[derive(Debug, Clone)]
enum MacType {
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
fn get_mac_type(
    device: u16,
    info: &DeviceInfo,
) -> Result<(MacType, bool, bool, u8), E1000DriverErr> {
    use MacType::*;

    let mut initialize_hw_bits_disable = false;
    let mut eee_enable = false;
    let mut icp_intel_vendor_idx_port_num = 0;

    let result = match device {
        E1000_DEV_ID_82542 => match info.get_revision_id() {
            E1000_82542_2_0_REV_ID => Em82542Rev2_0,
            E1000_82542_2_1_REV_ID => Em82542Rev2_1,
            _ => return Err(E1000DriverErr::UnknownRevisionD),
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
        _ => return Err(E1000DriverErr::UnknownDeviceID),
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

fn get_phy_init(mac_type: &MacType) -> bool {
    use MacType::*;

    match mac_type {
        Em82541 | Em82541Rev2 | Em82547 | Em82547Rev2 => true,
        _ => false,
    }
}

/// Reject non-PCI Express devices.
///
/// https://github.com/openbsd/src/blob/d88178ae581240e08c6acece5c276298d1ac6c90/sys/dev/pci/if_em_hw.c#L8381
fn check_pci_express(mac_type: &MacType) -> Result<(), E1000DriverErr> {
    use MacType::*;

    match mac_type {
        Em82571 | Em82572 | Em82573 | Em82574 | Em82575 | Em82576 | Em82580 | Em80003es2lan
        | EmI210 | EmI350 | EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan
        | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp => Ok(()),
        _ => Err(E1000DriverErr::NotPciExpress),
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

impl E1000Hw {
    pub fn new(info: &mut DeviceInfo) -> Result<Self, E1000DriverErr> {
        let (mac_type, initialize_hw_bits_disable, eee_enable, icp_intel_vendor_idx_port_num) =
            get_mac_type(info.get_id(), info)?;

        check_pci_express(&mac_type)?;

        let (
            swfwhw_semaphore_present,
            asf_firmware_present,
            swfw_sync_present,
            eeprom_semaphore_present,
        ) = get_hw_info(&mac_type);

        let phy_init_script = get_phy_init(&mac_type);

        if matches!(mac_type, MacType::EmPchlan) {
            info.set_revision_id((info.get_id() & 0x0f) as u8);
        }

        // https://github.com/openbsd/src/blob/d88178ae581240e08c6acece5c276298d1ac6c90/sys/dev/pci/if_em.c#L1720-L1740
        let flash_memory = if matches!(mac_type, MacType::EmPchSpt) {
            Some((info.get_bar(0).ok_or(E1000DriverErr::NoBar0)?, 0xe000))
        } else if is_ich8(&mac_type) {
            let bar1 = info.get_bar(1).ok_or(E1000DriverErr::NoBar1)?;
            if matches!(bar1, BaseAddress::MMIO { .. }) {
                Some((bar1, 0))
            } else {
                return Err(E1000DriverErr::Bar1IsNotMMIO);
            }
        } else {
            None
        };

        Ok(Self {
            mac_type,
            initialize_hw_bits_disable,
            eee_enable,
            icp_intel_vendor_idx_port_num,
            swfwhw_semaphore_present,
            asf_firmware_present,
            swfw_sync_present,
            eeprom_semaphore_present,
            phy_init_script,
            flash_memory,
        })
    }

    /// https://github.com/openbsd/src/blob/f058c8dbc8e3b2524b639ac291b898c7cc708996/sys/dev/pci/if_em_hw.c#L1559
    pub fn init_hw(info: &DeviceInfo) {
        todo!();
    }
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
    page_size: u16,
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

const INVM_SIZE: u16 = 64;

impl EEPROM {
    /// https://github.com/openbsd/src/blob/8e9ff1e61e136829a715052f888f67d3617fc787/sys/dev/pci/if_em_hw.c#L6280
    fn new(hw: &E1000Hw, info: &DeviceInfo) -> Result<Self, E1000DriverErr> {
        use MacType::*;

        let mut bar0 = info.get_bar(0).ok_or(E1000DriverErr::NoBar0)?;
        let eecd = bar0.read(super::EECD).ok_or(E1000DriverErr::ReadFailure)?;

        let result = match hw.mac_type {
            Em82542Rev2_0 | Em82542Rev2_1 | Em82543 | Em82544 => Self {
                eeprom_type: EEPROMType::Microwire,
                page_size: 0,
                word_size: 64,
                address_bits: 6,
                delay_usec: 50,
                opcode_bits: 3,
                use_eerd: false,
                use_eewr: false,
            },
            Em82540 | Em82545 | Em82545Rev3 | Em82546 | Em82546Rev3 => {
                let (word_size, address_bits) = if eecd & E1000_EECD_SIZE != 0 {
                    (256, 8)
                } else {
                    (64, 6)
                };

                Self {
                    eeprom_type: EEPROMType::Microwire,
                    opcode_bits: 3,
                    page_size: 0,
                    delay_usec: 50,
                    word_size,
                    address_bits,
                    use_eerd: false,
                    use_eewr: false,
                }
            }
            Em82541 | Em82541Rev2 | Em82547 | Em82547Rev2 => {
                if eecd & E1000_EECD_TYPE != 0 {
                    let (page_size, address_bits) = if eecd & E1000_EECD_ADDR_BITS != 0 {
                        (32, 16)
                    } else {
                        (8, 8)
                    };

                    Self {
                        eeprom_type: EEPROMType::SPI,
                        opcode_bits: 8,
                        delay_usec: 1,
                        page_size: 0,
                        word_size: 0, // SPI's word size will be set later.
                        address_bits,
                        use_eerd: false,
                        use_eewr: false,
                    }
                } else {
                    let (word_size, address_bits) = if eecd & E1000_EECD_ADDR_BITS != 0 {
                        (256, 8)
                    } else {
                        (64, 6)
                    };

                    Self {
                        eeprom_type: EEPROMType::Microwire,
                        opcode_bits: 3,
                        delay_usec: 50,
                        page_size: 0,
                        word_size,
                        address_bits,
                        use_eerd: false,
                        use_eewr: false,
                    }
                }
            }
            Em82571 | Em82572 => {
                let (page_size, address_bits) = if eecd & E1000_EECD_ADDR_BITS != 0 {
                    (32, 16)
                } else {
                    (8, 8)
                };

                Self {
                    eeprom_type: EEPROMType::SPI,
                    opcode_bits: 8,
                    delay_usec: 1,
                    word_size: 0,
                    page_size, // SPI's word size will be set later.
                    address_bits,
                    use_eerd: false,
                    use_eewr: false,
                }
            }
            Em82573 | Em82574 | Em82575 | Em82576 | Em82580 | EmI210 | EmI350 => {
                let (page_size, address_bits) = if eecd & E1000_EECD_ADDR_BITS != 0 {
                    (32, 16)
                } else {
                    (8, 8)
                };

                let (eeprom_type, word_size, use_eerd, use_eewr) =
                    if !get_flash_presence_i210(hw, info)? {
                        (EEPROMType::Invm, INVM_SIZE, false, false)
                    } else if !is_onboard_nvm_eeprom(hw, info)? {
                        let eecd = eecd & !E1000_EECD_AUPDEN;
                        bar0.write_bar(super::EECD, eecd);

                        (EEPROMType::Flash, 2048, true, true)
                    } else {
                        // SPI's word size will be set later.
                        (EEPROMType::SPI, 0, true, true)
                    };

                Self {
                    eeprom_type,
                    opcode_bits: 8,
                    delay_usec: 1,
                    page_size,
                    word_size,
                    address_bits,
                    use_eerd,
                    use_eewr,
                }
            }
            Em80003es2lan => {
                let (page_size, address_bits) = if eecd & E1000_EECD_ADDR_BITS != 0 {
                    (32, 16)
                } else {
                    (8, 8)
                };

                Self {
                    eeprom_type: EEPROMType::SPI,
                    opcode_bits: 8,
                    delay_usec: 1,
                    page_size,
                    word_size: 0, // SPI's word size will be set later.
                    address_bits,
                    use_eerd: true,
                    use_eewr: false,
                }
            }
            EmIch8lan | EmIch9lan | EmIch10lan | EmPchlan | EmPch2lan | EmPchLpt => {
                todo!()
            }
            EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp => {
                todo!()
            }
            EmICPxxxx => {
                return Err(E1000DriverErr::NotSupported);
            }
        };

        if matches!(result.eeprom_type, EEPROMType::SPI) {
            if hw.mac_type.clone() as u32 <= Em82547Rev2 as u32 {
                return Err(E1000DriverErr::NotSupported);
            }

            todo!();
        }

        Ok(result)
    }
}

fn is_onboard_nvm_eeprom(hw: &E1000Hw, info: &DeviceInfo) -> Result<bool, E1000DriverErr> {
    use MacType::*;

    if is_ich8(&hw.mac_type) {
        return Ok(false);
    }

    if matches!(hw.mac_type, Em82573 | Em82574) {
        let bar0 = info.get_bar(0).ok_or(E1000DriverErr::NoBar0)?;
        let eecd = bar0.read(super::EECD).ok_or(E1000DriverErr::ReadFailure)?;

        // Isolate bits 15 & 16
        let eecd = (eecd >> 15) & 0x03;

        // If both bits are set, device is Flash type
        if eecd == 0x03 {
            return Ok(false);
        }
    }

    Ok(true)
}

fn get_flash_presence_i210(hw: &E1000Hw, info: &DeviceInfo) -> Result<bool, E1000DriverErr> {
    if matches!(hw.mac_type, MacType::EmI210) {
        return Ok(true);
    }

    let bar0 = info.get_bar(0).ok_or(E1000DriverErr::NoBar0)?;
    let eecd = bar0.read(super::EECD).ok_or(E1000DriverErr::ReadFailure)?;

    if eecd & E1000_EECD_FLUPD != 0 {
        Ok(true)
    } else {
        Ok(false)
    }
}

// int32_t
// em_init_eeprom_params(struct em_hw *hw)
// {
// 	struct em_eeprom_info *eeprom = &hw->eeprom;
// 	uint32_t eecd = E1000_READ_REG(hw, EECD);
// 	int32_t  ret_val = E1000_SUCCESS;
// 	uint16_t eeprom_size;
// 	DEBUGFUNC("em_init_eeprom_params");

// 	switch (hw->mac_type) {
// 	case em_82542_rev2_0:
// 	case em_82542_rev2_1:
// 	case em_82543:
// 	case em_82544:
// 		eeprom->type = em_eeprom_microwire;
// 		eeprom->word_size = 64;
// 		eeprom->opcode_bits = 3;
// 		eeprom->address_bits = 6;
// 		eeprom->delay_usec = 50;
// 		eeprom->use_eerd = FALSE;
// 		eeprom->use_eewr = FALSE;
// 		break;
// 	case em_82540:
// 	case em_82545:
// 	case em_82545_rev_3:
// 	case em_icp_xxxx:
// 	case em_82546:
// 	case em_82546_rev_3:
// 		eeprom->type = em_eeprom_microwire;
// 		eeprom->opcode_bits = 3;
// 		eeprom->delay_usec = 50;
// 		if (eecd & E1000_EECD_SIZE) {
// 			eeprom->word_size = 256;
// 			eeprom->address_bits = 8;
// 		} else {
// 			eeprom->word_size = 64;
// 			eeprom->address_bits = 6;
// 		}
// 		eeprom->use_eerd = FALSE;
// 		eeprom->use_eewr = FALSE;
// 		break;
// 	case em_82541:
// 	case em_82541_rev_2:
// 	case em_82547:
// 	case em_82547_rev_2:
// 		if (eecd & E1000_EECD_TYPE) {
// 			eeprom->type = em_eeprom_spi;
// 			eeprom->opcode_bits = 8;
// 			eeprom->delay_usec = 1;
// 			if (eecd & E1000_EECD_ADDR_BITS) {
// 				eeprom->page_size = 32;
// 				eeprom->address_bits = 16;
// 			} else {
// 				eeprom->page_size = 8;
// 				eeprom->address_bits = 8;
// 			}
// 		} else {
// 			eeprom->type = em_eeprom_microwire;
// 			eeprom->opcode_bits = 3;
// 			eeprom->delay_usec = 50;
// 			if (eecd & E1000_EECD_ADDR_BITS) {
// 				eeprom->word_size = 256;
// 				eeprom->address_bits = 8;
// 			} else {
// 				eeprom->word_size = 64;
// 				eeprom->address_bits = 6;
// 			}
// 		}
// 		eeprom->use_eerd = FALSE;
// 		eeprom->use_eewr = FALSE;
// 		break;
// 	case em_82571:
// 	case em_82572:
// 		eeprom->type = em_eeprom_spi;
// 		eeprom->opcode_bits = 8;
// 		eeprom->delay_usec = 1;
// 		if (eecd & E1000_EECD_ADDR_BITS) {
// 			eeprom->page_size = 32;
// 			eeprom->address_bits = 16;
// 		} else {
// 			eeprom->page_size = 8;
// 			eeprom->address_bits = 8;
// 		}
// 		eeprom->use_eerd = FALSE;
// 		eeprom->use_eewr = FALSE;
// 		break;
// 	case em_82573:
// 	case em_82574:
// 	case em_82575:
// 	case em_82576:
// 	case em_82580:
// 	case em_i210:
// 	case em_i350:
// 		eeprom->type = em_eeprom_spi;
// 		eeprom->opcode_bits = 8;
// 		eeprom->delay_usec = 1;
// 		if (eecd & E1000_EECD_ADDR_BITS) {
// 			eeprom->page_size = 32;
// 			eeprom->address_bits = 16;
// 		} else {
// 			eeprom->page_size = 8;
// 			eeprom->address_bits = 8;
// 		}
// 		eeprom->use_eerd = TRUE;
// 		eeprom->use_eewr = TRUE;
// 		if (em_is_onboard_nvm_eeprom(hw) == FALSE) {
// 			eeprom->type = em_eeprom_flash;
// 			eeprom->word_size = 2048;
// 			/*
// 			 * Ensure that the Autonomous FLASH update bit is
// 			 * cleared due to Flash update issue on parts which
// 			 * use a FLASH for NVM.
// 			 */
// 			eecd &= ~E1000_EECD_AUPDEN;
// 			E1000_WRITE_REG(hw, EECD, eecd);
// 		}
// 		if (em_get_flash_presence_i210(hw) == FALSE) {
// 			eeprom->type = em_eeprom_invm;
// 			eeprom->word_size = INVM_SIZE;
// 			eeprom->use_eerd = FALSE;
// 			eeprom->use_eewr = FALSE;
// 		}
// 		break;
// 	case em_80003es2lan:
// 		eeprom->type = em_eeprom_spi;
// 		eeprom->opcode_bits = 8;
// 		eeprom->delay_usec = 1;
// 		if (eecd & E1000_EECD_ADDR_BITS) {
// 			eeprom->page_size = 32;
// 			eeprom->address_bits = 16;
// 		} else {
// 			eeprom->page_size = 8;
// 			eeprom->address_bits = 8;
// 		}
// 		eeprom->use_eerd = TRUE;
// 		eeprom->use_eewr = FALSE;
// 		break;
// 	case em_ich8lan:
// 	case em_ich9lan:
// 	case em_ich10lan:
// 	case em_pchlan:
// 	case em_pch2lan:
// 	case em_pch_lpt:
// 		{
// 		int32_t         i = 0;
// 		uint32_t        flash_size =
// 		    E1000_READ_ICH_FLASH_REG(hw, ICH_FLASH_GFPREG);
// 			eeprom->type = em_eeprom_ich8;
// 			eeprom->use_eerd = FALSE;
// 			eeprom->use_eewr = FALSE;
// 			eeprom->word_size = E1000_SHADOW_RAM_WORDS;
// 			/*
// 			 * Zero the shadow RAM structure. But don't load it
// 			 * from NVM so as to save time for driver init
// 			 */
// 			if (hw->eeprom_shadow_ram != NULL) {
// 				for (i = 0; i < E1000_SHADOW_RAM_WORDS; i++) {
// 					hw->eeprom_shadow_ram[i].modified =
// 					    FALSE;
// 					hw->eeprom_shadow_ram[i].eeprom_word =
// 					    0xFFFF;
// 				}
// 			}
// 			hw->flash_base_addr = (flash_size &
// 			    ICH_GFPREG_BASE_MASK) * ICH_FLASH_SECTOR_SIZE;

// 			hw->flash_bank_size = ((flash_size >> 16) &
// 			    ICH_GFPREG_BASE_MASK) + 1;
// 			hw->flash_bank_size -= (flash_size &
// 			    ICH_GFPREG_BASE_MASK);

// 			hw->flash_bank_size *= ICH_FLASH_SECTOR_SIZE;

// 			hw->flash_bank_size /= 2 * sizeof(uint16_t);

// 			break;
// 		}
// 	case em_pch_spt:
// 	case em_pch_cnp:
// 	case em_pch_tgp:
// 	case em_pch_adp:
// 		{
// 			int32_t         i = 0;
// 			uint32_t        flash_size = EM_READ_REG(hw, 0xc /* STRAP */);

// 			eeprom->type = em_eeprom_ich8;
// 			eeprom->use_eerd = FALSE;
// 			eeprom->use_eewr = FALSE;
// 			eeprom->word_size = E1000_SHADOW_RAM_WORDS;
// 			/*
// 			 * Zero the shadow RAM structure. But don't load it
// 			 * from NVM so as to save time for driver init
// 			 */
// 			if (hw->eeprom_shadow_ram != NULL) {
// 				for (i = 0; i < E1000_SHADOW_RAM_WORDS; i++) {
// 					hw->eeprom_shadow_ram[i].modified =
// 					    FALSE;
// 					hw->eeprom_shadow_ram[i].eeprom_word =
// 					    0xFFFF;
// 				}
// 			}
// 			hw->flash_base_addr = 0;
// 			flash_size = ((flash_size >> 1) & 0x1f) + 1;
// 			flash_size *= 4096;
// 			hw->flash_bank_size = flash_size / 4;
// 		}
// 		break;
// 	default:
// 		break;
// 	}

// 	if (eeprom->type == em_eeprom_spi) {
// 		/*
// 		 * eeprom_size will be an enum [0..8] that maps to eeprom
// 		 * sizes 128B to 32KB (incremented by powers of 2).
// 		 */
// 		if (hw->mac_type <= em_82547_rev_2) {
// 			/* Set to default value for initial eeprom read. */
// 			eeprom->word_size = 64;
// 			ret_val = em_read_eeprom(hw, EEPROM_CFG, 1,
// 			    &eeprom_size);
// 			if (ret_val)
// 				return ret_val;
// 			eeprom_size = (eeprom_size & EEPROM_SIZE_MASK) >>
// 			    EEPROM_SIZE_SHIFT;
// 			/*
// 			 * 256B eeprom size was not supported in earlier
// 			 * hardware, so we bump eeprom_size up one to ensure
// 			 * that "1" (which maps to 256B) is never the result
// 			 * used in the shifting logic below.
// 			 */
// 			if (eeprom_size)
// 				eeprom_size++;
// 		} else {
// 			eeprom_size = (uint16_t) (
// 			    (eecd & E1000_EECD_SIZE_EX_MASK) >>
// 			    E1000_EECD_SIZE_EX_SHIFT);
// 		}

// 		/* EEPROM access above 16k is unsupported */
// 		if (eeprom_size + EEPROM_WORD_SIZE_SHIFT >
// 		    EEPROM_WORD_SIZE_SHIFT_MAX) {
// 			eeprom->word_size = 1 << EEPROM_WORD_SIZE_SHIFT_MAX;
// 		} else {
// 			eeprom->word_size = 1 <<
// 			    (eeprom_size + EEPROM_WORD_SIZE_SHIFT);
// 		}
// 	}
// 	return ret_val;
// }
