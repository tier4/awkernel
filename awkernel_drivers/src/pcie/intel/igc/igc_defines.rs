// Wake Up Filter Control
pub(super) const IGC_WUFC_LNKC: u32 = 0x00000001; // Link Status Change Wakeup Enable
pub(super) const IGC_WUFC_MAG: u32 = 0x00000002; // Magic Packet Wakeup Enable
pub(super) const IGC_WUFC_EX: u32 = 0x00000004; // Directed Exact Wakeup Enable
pub(super) const IGC_WUFC_MC: u32 = 0x00000008; // Directed Multicast Wakeup Enable
pub(super) const IGC_WUFC_BC: u32 = 0x00000010; // Broadcast Wakeup Enable
pub(super) const IGC_WUFC_ARP: u32 = 0x00000020; // ARP Request Packet Wakeup Enable
pub(super) const IGC_WUFC_IPV4: u32 = 0x00000040; // Directed IPv4 Packet Wakeup Enable

// Wake Up Status
pub(super) const IGC_WUS_LNKC: u32 = IGC_WUFC_LNKC;
pub(super) const IGC_WUS_MAG: u32 = IGC_WUFC_MAG;
pub(super) const IGC_WUS_EX: u32 = IGC_WUFC_EX;
pub(super) const IGC_WUS_MC: u32 = IGC_WUFC_MC;
pub(super) const IGC_WUS_BC: u32 = IGC_WUFC_BC;

// Packet types that are enabled for wake packet delivery
pub(super) const WAKE_PKT_WUS: u32 =
    IGC_WUS_EX | IGC_WUS_ARPD | IGC_WUS_IPV4 | IGC_WUS_IPV6 | IGC_WUS_NSD;

pub(super) const IGC_WUS_ARPD: u32 = 0x00000020; // Directed ARP Request
pub(super) const IGC_WUS_IPV4: u32 = 0x00000040; // Directed IPv4
pub(super) const IGC_WUS_IPV6: u32 = 0x00000080; // Directed IPv6
pub(super) const IGC_WUS_NSD: u32 = 0x00000400; // Directed IPv6 Neighbor Solicitation

// Extended Device Control
pub(super) const IGC_CTRL_EXT_LPCD: u32 = 0x00000004; // LCD Power Cycle Done
pub(super) const IGC_CTRL_EXT_SDP4_DATA: u32 = 0x00000010; // SW Definable Pin 4 data
pub(super) const IGC_CTRL_EXT_SDP6_DATA: u32 = 0x00000040; // SW Definable Pin 6 data
pub(super) const IGC_CTRL_EXT_SDP3_DATA: u32 = 0x00000080; // SW Definable Pin 3 data
pub(super) const IGC_CTRL_EXT_SDP6_DIR: u32 = 0x00000400; // Direction of SDP6 0=in 1=out
pub(super) const IGC_CTRL_EXT_SDP3_DIR: u32 = 0x00000800; // Direction of SDP3 0=in 1=out
pub(super) const IGC_CTRL_EXT_EE_RST: u32 = 0x00002000; // Reinitialize from EEPROM
pub(super) const IGC_CTRL_EXT_SPD_BYPS: u32 = 0x00008000; // Speed Select Bypass
pub(super) const IGC_CTRL_EXT_RO_DIS: u32 = 0x00020000; // Relaxed Ordering disable
pub(super) const IGC_CTRL_EXT_DMA_DYN_CLK_EN: u32 = 0x00080000; // DMA Dynamic Clk Gating
pub(super) const IGC_CTRL_EXT_LINK_MODE_PCIE_SERDES: u32 = 0x00C00000;
pub(super) const IGC_CTRL_EXT_EIAME: u32 = 0x01000000;
pub(super) const IGC_CTRL_EXT_DRV_LOAD: u32 = 0x10000000; // Drv loaded bit for FW
pub(super) const IGC_CTRL_EXT_IAME: u32 = 0x08000000; // Int ACK Auto-mask
pub(super) const IGC_CTRL_EXT_PBA_CLR: u32 = 0x80000000; // PBA Clear
pub(super) const IGC_CTRL_EXT_PHYPDEN: u32 = 0x00100000;
pub(super) const IGC_IVAR_VALID: u32 = 0x80;
pub(super) const IGC_GPIE_NSICR: u32 = 0x00000001;
pub(super) const IGC_GPIE_MSIX_MODE: u32 = 0x00000010;
pub(super) const IGC_GPIE_EIAME: u32 = 0x40000000;
pub(super) const IGC_GPIE_PBA: u32 = 0x80000000;

// Receive Descriptor bit definitions
pub(super) const IGC_RXD_STAT_DD: u32 = 0x01; // Descriptor Done
pub(super) const IGC_RXD_STAT_EOP: u32 = 0x02; // End of Packet
pub(super) const IGC_RXD_STAT_IXSM: u32 = 0x04; // Ignore checksum
pub(super) const IGC_RXD_STAT_VP: u32 = 0x08; // IEEE VLAN Packet
pub(super) const IGC_RXD_STAT_UDPCS: u32 = 0x10; // UDP xsum calculated
pub(super) const IGC_RXD_STAT_TCPCS: u32 = 0x20; // TCP xsum calculated
pub(super) const IGC_RXD_STAT_IPCS: u32 = 0x40; // IP xsum calculated
pub(super) const IGC_RXD_STAT_PIF: u32 = 0x80; // passed in-exact filter
pub(super) const IGC_RXD_STAT_IPIDV: u32 = 0x200; // IP identification valid
pub(super) const IGC_RXD_STAT_UDPV: u32 = 0x400; // Valid UDP checksum
pub(super) const IGC_RXD_ERR_CE: u32 = 0x01; // CRC Error
pub(super) const IGC_RXD_ERR_SE: u32 = 0x02; // Symbol Error
pub(super) const IGC_RXD_ERR_SEQ: u32 = 0x04; // Sequence Error
pub(super) const IGC_RXD_ERR_CXE: u32 = 0x10; // Carrier Extension Error
pub(super) const IGC_RXD_ERR_TCPE: u32 = 0x20; // TCP/UDP Checksum Error
pub(super) const IGC_RXD_ERR_IPE: u32 = 0x40; // IP Checksum Error
pub(super) const IGC_RXD_ERR_RXE: u32 = 0x80; // Rx Data Error
pub(super) const IGC_RXD_SPC_VLAN_MASK: u32 = 0x0FFF; // VLAN ID is in lower 12 bits

pub(super) const IGC_RXDEXT_STATERR_TST: u32 = 0x00000100; // Time Stamp taken
pub(super) const IGC_RXDEXT_STATERR_LB: u32 = 0x00040000;
pub(super) const IGC_RXDEXT_STATERR_L4E: u32 = 0x20000000;
pub(super) const IGC_RXDEXT_STATERR_IPE: u32 = 0x40000000;
pub(super) const IGC_RXDEXT_STATERR_RXE: u32 = 0x80000000;

// Same mask, but for extended and packet split descriptors
pub(super) const IGC_MRQC_RSS_FIELD_MASK: u32 = 0xFFFF0000;
pub(super) const IGC_MRQC_RSS_FIELD_IPV4_TCP: u32 = 0x00010000;
pub(super) const IGC_MRQC_RSS_FIELD_IPV4: u32 = 0x00020000;
pub(super) const IGC_MRQC_RSS_FIELD_IPV6_TCP_EX: u32 = 0x00040000;
pub(super) const IGC_MRQC_RSS_FIELD_IPV6: u32 = 0x00100000;
pub(super) const IGC_MRQC_RSS_FIELD_IPV6_TCP: u32 = 0x00200000;

// Management Control
pub(super) const IGC_MANC_SMBUS_EN: u32 = 0x00000001; // SMBus Enabled - RO
pub(super) const IGC_MANC_ASF_EN: u32 = 0x00000002; // ASF Enabled - RO
pub(super) const IGC_MANC_ARP_EN: u32 = 0x00002000; // Enable ARP Request Filtering
pub(super) const IGC_MANC_RCV_TCO_EN: u32 = 0x00020000; // Receive TCO Packets Enabled
pub(super) const IGC_MANC_BLK_PHY_RST_ON_IDE: u32 = 0x00040000; // Block phy resets

// Receive Control
pub(super) const IGC_RCTL_RST: u32 = 0x00000001; // Software reset
pub(super) const IGC_RCTL_EN: u32 = 0x00000002; // enable
pub(super) const IGC_RCTL_SBP: u32 = 0x00000004; // store bad packet
pub(super) const IGC_RCTL_UPE: u32 = 0x00000008; // unicast promisc enable
pub(super) const IGC_RCTL_MPE: u32 = 0x00000010; // multicast promisc enable
pub(super) const IGC_RCTL_LPE: u32 = 0x00000020; // long packet enable
pub(super) const IGC_RCTL_LBM_NO: u32 = 0x00000000; // no loopback mode
pub(super) const IGC_RCTL_LBM_MAC: u32 = 0x00000040; // MAC loopback mode
pub(super) const IGC_RCTL_LBM_TCVR: u32 = 0x000000C0; // tcvr loopback mode
pub(super) const IGC_RCTL_DTYP_PS: u32 = 0x00000400; // Packet Split descriptor
pub(super) const IGC_RCTL_RDMTS_HALF: u32 = 0x00000000; // Rx desc min thresh size
pub(super) const IGC_RCTL_RDMTS_HEX: u32 = 0x00010000;
pub(super) const IGC_RCTL_RDMTS1_HEX: u32 = IGC_RCTL_RDMTS_HEX;
pub(super) const IGC_RCTL_MO_SHIFT: u32 = 12; // multicast offset shift
pub(super) const IGC_RCTL_MO_3: u32 = 0x00003000; // multicast offset 15:4
pub(super) const IGC_RCTL_BAM: u32 = 0x00008000; // broadcast enable

// these buffer sizes are valid if IGC_RCTL_BSEX is 0
pub(super) const IGC_RCTL_SZ_2048: u32 = 0x00000000; // Rx buffer size 2048
pub(super) const IGC_RCTL_SZ_1024: u32 = 0x00010000; // Rx buffer size 1024
pub(super) const IGC_RCTL_SZ_512: u32 = 0x00020000; // Rx buffer size 512
pub(super) const IGC_RCTL_SZ_256: u32 = 0x00030000; // Rx buffer size 256

// these buffer sizes are valid if IGC_RCTL_BSEX is 1
pub(super) const IGC_RCTL_SZ_16384: u32 = 0x00010000; // Rx buffer size 16384
pub(super) const IGC_RCTL_SZ_8192: u32 = 0x00020000; // Rx buffer size 8192
pub(super) const IGC_RCTL_SZ_4096: u32 = 0x00030000; // Rx buffer size 4096
pub(super) const IGC_RCTL_VFE: u32 = 0x00040000; // vlan filter enable
pub(super) const IGC_RCTL_CFIEN: u32 = 0x00080000; // canonical form enable
pub(super) const IGC_RCTL_CFI: u32 = 0x00100000; // canonical form indicator
pub(super) const IGC_RCTL_DPF: u32 = 0x00400000; // discard pause frames
pub(super) const IGC_RCTL_PMCF: u32 = 0x00800000; // pass MAC control frames
pub(super) const IGC_RCTL_BSEX: u32 = 0x02000000; // Buffer size extension
pub(super) const IGC_RCTL_SECRC: u32 = 0x04000000; // Strip Ethernet CRC

// SWFW_SYNC Definitions
pub(super) const IGC_SWFW_EEP_SM: u16 = 0x01;
pub(super) const IGC_SWFW_PHY0_SM: u16 = 0x02;
pub(super) const IGC_SWFW_PHY1_SM: u16 = 0x04;
pub(super) const IGC_SWFW_CSR_SM: u16 = 0x08;
pub(super) const IGC_SWFW_SW_MNG_SM: u16 = 0x400;

// Device Control
pub(super) const IGC_CTRL_FD: u32 = 0x00000001; // Full duplex.0=half; 1=full
pub(super) const IGC_CTRL_PRIOR: u32 = 0x00000004; // Priority on PCI. 0=rx,1=fair
pub(super) const IGC_CTRL_GIO_MASTER_DISABLE: u32 = 0x00000004; // Blocks new Master reqs
pub(super) const IGC_CTRL_LRST: u32 = 0x00000008; // Link reset. 0=normal,1=reset
pub(super) const IGC_CTRL_ASDE: u32 = 0x00000020; // Auto-speed detect enable
pub(super) const IGC_CTRL_SLU: u32 = 0x00000040; // Set link up (Force Link)
pub(super) const IGC_CTRL_ILOS: u32 = 0x00000080; // Invert Loss-Of Signal
pub(super) const IGC_CTRL_SPD_SEL: u32 = 0x00000300; // Speed Select Mask
pub(super) const IGC_CTRL_SPD_10: u32 = 0x00000000; // Force 10Mb
pub(super) const IGC_CTRL_SPD_100: u32 = 0x00000100; // Force 100Mb
pub(super) const IGC_CTRL_SPD_1000: u32 = 0x00000200; // Force 1Gb
pub(super) const IGC_CTRL_FRCSPD: u32 = 0x00000800; // Force Speed
pub(super) const IGC_CTRL_FRCDPX: u32 = 0x00001000; // Force Duplex
pub(super) const IGC_CTRL_SWDPIN0: u32 = 0x00040000; // SWDPIN 0 value
pub(super) const IGC_CTRL_SWDPIN1: u32 = 0x00080000; // SWDPIN 1 value
pub(super) const IGC_CTRL_SWDPIN2: u32 = 0x00100000; // SWDPIN 2 value
pub(super) const IGC_CTRL_ADVD3WUC: u32 = 0x00100000; // D3 WUC
pub(super) const IGC_CTRL_SWDPIN3: u32 = 0x00200000; // SWDPIN 3 value
pub(super) const IGC_CTRL_SWDPIO0: u32 = 0x00400000; // SWDPIN 0 Input or output
pub(super) const IGC_CTRL_DEV_RST: u32 = 0x20000000; // Device reset
pub(super) const IGC_CTRL_RST: u32 = 0x04000000; // Global reset
pub(super) const IGC_CTRL_RFCE: u32 = 0x08000000; // Receive Flow Control enable
pub(super) const IGC_CTRL_TFCE: u32 = 0x10000000; // Transmit flow control enable
pub(super) const IGC_CTRL_VME: u32 = 0x40000000; // IEEE VLAN mode enable
pub(super) const IGC_CTRL_PHY_RST: u32 = 0x80000000; // PHY Reset

// Device Status
pub(super) const IGC_STATUS_FD: u32 = 0x00000001; // Duplex 0=half 1=full
pub(super) const IGC_STATUS_LU: u32 = 0x00000002; // Link up.0=no,1=link
pub(super) const IGC_STATUS_FUNC_MASK: u32 = 0x0000000C; // PCI Function Mask
pub(super) const IGC_STATUS_FUNC_SHIFT: u32 = 2;
pub(super) const IGC_STATUS_FUNC_1: u32 = 0x00000004; // Function 1
pub(super) const IGC_STATUS_TXOFF: u32 = 0x00000010; // transmission paused
pub(super) const IGC_STATUS_SPEED_MASK: u32 = 0x000000C0;
pub(super) const IGC_STATUS_SPEED_10: u32 = 0x00000000; // Speed 10Mb/s
pub(super) const IGC_STATUS_SPEED_100: u32 = 0x00000040; // Speed 100Mb/s
pub(super) const IGC_STATUS_SPEED_1000: u32 = 0x00000080; // Speed 1000Mb/s
pub(super) const IGC_STATUS_SPEED_2500: u32 = 0x00400000; // Speed 2.5Gb/s
pub(super) const IGC_STATUS_LAN_INIT_DONE: u32 = 0x00000200; // Lan Init Compltn by NVM
pub(super) const IGC_STATUS_PHYRA: u32 = 0x00000400; // PHY Reset Asserted
pub(super) const IGC_STATUS_GIO_MASTER_ENABLE: u32 = 0x00080000; // Master request status
pub(super) const IGC_STATUS_2P5_SKU: u32 = 0x00001000; // Val of 2.5GBE SKU strap
pub(super) const IGC_STATUS_2P5_SKU_OVER: u32 = 0x00002000; // Val of 2.5GBE SKU Over
pub(super) const IGC_STATUS_PCIM_STATE: u32 = 0x40000000; // PCIm function state

pub(super) const SPEED_10: u32 = 10;
pub(super) const SPEED_100: u32 = 100;
pub(super) const SPEED_1000: u32 = 1000;
pub(super) const SPEED_2500: u32 = 2500;
pub(super) const HALF_DUPLEX: u32 = 1;
pub(super) const FULL_DUPLEX: u32 = 2;

pub(super) const ADVERTISE_10_HALF: u32 = 0x0001;
pub(super) const ADVERTISE_10_FULL: u32 = 0x0002;
pub(super) const ADVERTISE_100_HALF: u32 = 0x0004;
pub(super) const ADVERTISE_100_FULL: u32 = 0x0008;
pub(super) const ADVERTISE_1000_HALF: u32 = 0x0010; // Not used, just FYI
pub(super) const ADVERTISE_1000_FULL: u32 = 0x0020;
pub(super) const ADVERTISE_2500_HALF: u32 = 0x0040; // NOT used, just FYI
pub(super) const ADVERTISE_2500_FULL: u32 = 0x0080;

// 1000/H is not supported, nor spec-compliant.
pub(super) const IGC_ALL_SPEED_DUPLEX: u32 = ADVERTISE_10_HALF
    | ADVERTISE_10_FULL
    | ADVERTISE_100_HALF
    | ADVERTISE_100_FULL
    | ADVERTISE_1000_FULL;
pub(super) const IGC_ALL_SPEED_DUPLEX_2500: u32 = ADVERTISE_10_HALF
    | ADVERTISE_10_FULL
    | ADVERTISE_100_HALF
    | ADVERTISE_100_FULL
    | ADVERTISE_1000_FULL
    | ADVERTISE_2500_FULL;
pub(super) const AUTONEG_ADVERTISE_SPEED_DEFAULT: u32 = IGC_ALL_SPEED_DUPLEX;
pub(super) const AUTONEG_ADVERTISE_SPEED_DEFAULT_2500: u32 = IGC_ALL_SPEED_DUPLEX_2500;

// Transmit Descriptor bit definitions
pub(super) const IGC_TXD_DTYP_D: u32 = 0x00100000; // Data Descriptor
pub(super) const IGC_TXD_DTYP_C: u32 = 0x00000000; // Context Descriptor
pub(super) const IGC_TXD_POPTS_IXSM: u32 = 0x01; // Insert IP checksum
pub(super) const IGC_TXD_POPTS_TXSM: u32 = 0x02; // Insert TCP/UDP checksum
pub(super) const IGC_TXD_CMD_EOP: u32 = 0x01000000; // End of Packet
pub(super) const IGC_TXD_CMD_IFCS: u32 = 0x02000000; // Insert FCS (Ethernet CRC)
pub(super) const IGC_TXD_CMD_IC: u32 = 0x04000000; // Insert Checksum
pub(super) const IGC_TXD_CMD_RS: u32 = 0x08000000; // Report Status
pub(super) const IGC_TXD_CMD_RPS: u32 = 0x10000000; // Report Packet Sent
pub(super) const IGC_TXD_CMD_DEXT: u32 = 0x20000000; // Desc extension (0 = legacy)
pub(super) const IGC_TXD_CMD_VLE: u32 = 0x40000000; // Add VLAN tag
pub(super) const IGC_TXD_CMD_IDE: u32 = 0x80000000; // Enable Tidv register
pub(super) const IGC_TXD_STAT_DD: u32 = 0x00000001; // Descriptor Done
pub(super) const IGC_TXD_CMD_TCP: u32 = 0x01000000; // TCP packet
pub(super) const IGC_TXD_CMD_IP: u32 = 0x02000000; // IP packet
pub(super) const IGC_TXD_CMD_TSE: u32 = 0x04000000; // TCP Seg enable
pub(super) const IGC_TXD_EXTCMD_TSTAMP: u32 = 0x00000010; // IEEE1588 Timestamp packet

// Transmit Control
pub(super) const IGC_TCTL_EN: u32 = 0x00000002; // enable Tx
pub(super) const IGC_TCTL_PSP: u32 = 0x00000008; // pad short packets
pub(super) const IGC_TCTL_CT: u32 = 0x00000ff0; // collision threshold
pub(super) const IGC_TCTL_COLD: u32 = 0x003ff000; // collision distance
pub(super) const IGC_TCTL_RTLC: u32 = 0x01000000; // Re-transmit on late collision
pub(super) const IGC_TCTL_MULR: u32 = 0x10000000; // Multiple request support

// Receive Checksum Control
pub(super) const IGC_RXCSUM_IPOFL: u32 = 0x00000100; // IPv4 checksum offload
pub(super) const IGC_RXCSUM_TUOFL: u32 = 0x00000200; // TCP / UDP checksum offload
pub(super) const IGC_RXCSUM_CRCOFL: u32 = 0x00000800; // CRC32 offload enable
pub(super) const IGC_RXCSUM_IPPCSE: u32 = 0x00001000; // IP payload checksum enable
pub(super) const IGC_RXCSUM_PCSD: u32 = 0x00002000; // packet checksum disabled

// GPY211 - I225 defines
pub(super) const GPY_MMD_MASK: u32 = 0xFFFF0000;
pub(super) const GPY_MMD_SHIFT: u32 = 16;
pub(super) const GPY_REG_MASK: u32 = 0x0000FFFF;

// Collision related configuration parameters
pub(super) const IGC_CT_SHIFT: u32 = 4;
pub(super) const IGC_COLLISION_THRESHOLD: u32 = 15;
pub(super) const IGC_COLLISION_DISTANCE: u32 = 63;
pub(super) const IGC_COLD_SHIFT: u32 = 12;

// Default values for the transmit IPG register
pub(super) const DEFAULT_82543_TIPG_IPGT_FIBER: u32 = 9;

pub(super) const IGC_TIPG_IPGT_MASK: u32 = 0x000003FF;

pub(super) const DEFAULT_82543_TIPG_IPGR1: u32 = 8;
pub(super) const IGC_TIPG_IPGR1_SHIFT: u32 = 10;

pub(super) const DEFAULT_82543_TIPG_IPGR2: u32 = 6;
pub(super) const DEFAULT_80003ES2LAN_TIPG_IPGR2: u32 = 7;
pub(super) const IGC_TIPG_IPGR2_SHIFT: u32 = 20;

// Ethertype field values
pub(super) const ETHERNET_FCS_SIZE: u32 = 4;
pub(super) const MAX_JUMBO_FRAME_SIZE: u32 = 9216;
pub(super) const IGC_TX_PTR_GAP: u32 = 0x1F;

// PBA constants
pub(super) const IGC_PBA_8K: u32 = 0x0008; // 8KB
pub(super) const IGC_PBA_10K: u32 = 0x000A; // 10KB
pub(super) const IGC_PBA_12K: u32 = 0x000C; // 12KB
pub(super) const IGC_PBA_14K: u32 = 0x000E; // 14KB
pub(super) const IGC_PBA_16K: u32 = 0x0010; // 16KB
pub(super) const IGC_PBA_18K: u32 = 0x0012;
pub(super) const IGC_PBA_20K: u32 = 0x0014;
pub(super) const IGC_PBA_22K: u32 = 0x0016;
pub(super) const IGC_PBA_24K: u32 = 0x0018;
pub(super) const IGC_PBA_26K: u32 = 0x001A;
pub(super) const IGC_PBA_30K: u32 = 0x001E;
pub(super) const IGC_PBA_32K: u32 = 0x0020;
pub(super) const IGC_PBA_34K: u32 = 0x0022;
pub(super) const IGC_PBA_35K: u32 = 0x0023;
pub(super) const IGC_PBA_38K: u32 = 0x0026;
pub(super) const IGC_PBA_40K: u32 = 0x0028;
pub(super) const IGC_PBA_48K: u32 = 0x0030; // 48KB
pub(super) const IGC_PBA_64K: u32 = 0x0040; // 64KB

pub(super) const IGC_PBA_RXA_MASK: u32 = 0xFFFF;

pub(super) const IGC_PBS_16K: u32 = IGC_PBA_16K;

// SW Semaphore Register
pub(super) const IGC_SWSM_SMBI: u32 = 0x00000001; // Driver Semaphore bit
pub(super) const IGC_SWSM_SWESMBI: u32 = 0x00000002; // FW Semaphore bit
pub(super) const IGC_SWSM_DRV_LOAD: u32 = 0x00000008; // Driver Loaded Bit

pub(super) const IGC_SWSM2_LOCK: u32 = 0x00000002; // Secondary driver semaphore bit

// Interrupt Cause Read
pub(super) const IGC_ICR_TXDW: u32 = 0x00000001; // Transmit desc written back
pub(super) const IGC_ICR_TXQE: u32 = 0x00000002; // Transmit Queue empty
pub(super) const IGC_ICR_LSC: u32 = 0x00000004; // Link Status Change
pub(super) const IGC_ICR_RXSEQ: u32 = 0x00000008; // Rx sequence error
pub(super) const IGC_ICR_RXDMT0: u32 = 0x00000010; // Rx desc min. threshold (0)
pub(super) const IGC_ICR_RXO: u32 = 0x00000040; // Rx overrun
pub(super) const IGC_ICR_RXT0: u32 = 0x00000080; // Rx timer intr (ring 0)
pub(super) const IGC_ICR_RXCFG: u32 = 0x00000400; // Rx /c/ ordered set
pub(super) const IGC_ICR_GPI_EN0: u32 = 0x00000800; // GP Int 0
pub(super) const IGC_ICR_GPI_EN1: u32 = 0x00001000; // GP Int 1
pub(super) const IGC_ICR_GPI_EN2: u32 = 0x00002000; // GP Int 2
pub(super) const IGC_ICR_GPI_EN3: u32 = 0x00004000; // GP Int 3
pub(super) const IGC_ICR_TXD_LOW: u32 = 0x00008000;
pub(super) const IGC_ICR_ECCER: u32 = 0x00400000; // Uncorrectable ECC Error
pub(super) const IGC_ICR_TS: u32 = 0x00080000; // Time Sync Interrupt
pub(super) const IGC_ICR_DRSTA: u32 = 0x40000000; // Device Reset Asserted

// If this bit asserted, the driver should claim the interrupt
pub(super) const IGC_ICR_INT_ASSERTED: u32 = 0x80000000;
pub(super) const IGC_ICR_DOUTSYNC: u32 = 0x10000000; // NIC DMA out of sync
pub(super) const IGC_ICR_FER: u32 = 0x00400000; // Fatal Error

// Extended Interrupt Cause Read
pub(super) const IGC_EICR_RX_QUEUE0: u32 = 0x00000001; // Rx Queue 0 Interrupt
pub(super) const IGC_EICR_RX_QUEUE1: u32 = 0x00000002; // Rx Queue 1 Interrupt
pub(super) const IGC_EICR_RX_QUEUE2: u32 = 0x00000004; // Rx Queue 2 Interrupt
pub(super) const IGC_EICR_RX_QUEUE3: u32 = 0x00000008; // Rx Queue 3 Interrupt
pub(super) const IGC_EICR_TX_QUEUE0: u32 = 0x00000100; // Tx Queue 0 Interrupt
pub(super) const IGC_EICR_TX_QUEUE1: u32 = 0x00000200; // Tx Queue 1 Interrupt
pub(super) const IGC_EICR_TX_QUEUE2: u32 = 0x00000400; // Tx Queue 2 Interrupt
pub(super) const IGC_EICR_TX_QUEUE3: u32 = 0x00000800; // Tx Queue 3 Interrupt
pub(super) const IGC_EICR_TCP_TIMER: u32 = 0x40000000; // TCP Timer
pub(super) const IGC_EICR_OTHER: u32 = 0x80000000; // Interrupt Cause Active

// This defines the bits that are set in the Interrupt Mask
// Set/Read Register.  Each bit is documented below:
//   o RXT0   = Receiver Timer Interrupt (ring 0)
//   o TXDW   = Transmit Descriptor Written Back
//   o RXDMT0 = Receive Descriptor Minimum Threshold hit (ring 0)
//   o RXSEQ  = Receive Sequence Error
//   o LSC    = Link Status Change
pub(super) const IMS_ENABLE_MASK: u32 =
    IGC_IMS_RXT0 | IGC_IMS_TXDW | IGC_IMS_RXDMT0 | IGC_IMS_RXSEQ | IGC_IMS_LSC;

// Interrupt Mask Set
pub(super) const IGC_IMS_TXDW: u32 = IGC_ICR_TXDW; // Tx desc written back
pub(super) const IGC_IMS_LSC: u32 = IGC_ICR_LSC; // Link Status Change
pub(super) const IGC_IMS_RXSEQ: u32 = IGC_ICR_RXSEQ; // Rx sequence error
pub(super) const IGC_IMS_RXDMT0: u32 = IGC_ICR_RXDMT0; // Rx desc min. threshold
pub(super) const IGC_QVECTOR_MASK: u32 = 0x7FFC; // Q-vector mask
pub(super) const IGC_ITR_VAL_MASK: u32 = 0x04; // ITR value mask
pub(super) const IGC_IMS_RXO: u32 = IGC_ICR_RXO; // Rx overrun
pub(super) const IGC_IMS_RXT0: u32 = IGC_ICR_RXT0; // Rx timer intr
pub(super) const IGC_IMS_TXD_LOW: u32 = IGC_ICR_TXD_LOW;
pub(super) const IGC_IMS_ECCER: u32 = IGC_ICR_ECCER; // Uncorrectable ECC Error
pub(super) const IGC_IMS_TS: u32 = IGC_ICR_TS; // Time Sync Interrupt
pub(super) const IGC_IMS_DRSTA: u32 = IGC_ICR_DRSTA; // Device Reset Asserted
pub(super) const IGC_IMS_DOUTSYNC: u32 = IGC_ICR_DOUTSYNC; // NIC DMA out of sync
pub(super) const IGC_IMS_FER: u32 = IGC_ICR_FER; // Fatal Error

// Extended Interrupt Mask Set
pub(super) const IGC_EIMS_RX_QUEUE0: u32 = IGC_EICR_RX_QUEUE0; // Rx Queue 0 Interrupt
pub(super) const IGC_EIMS_RX_QUEUE1: u32 = IGC_EICR_RX_QUEUE1; // Rx Queue 1 Interrupt
pub(super) const IGC_EIMS_RX_QUEUE2: u32 = IGC_EICR_RX_QUEUE2; // Rx Queue 2 Interrupt
pub(super) const IGC_EIMS_RX_QUEUE3: u32 = IGC_EICR_RX_QUEUE3; // Rx Queue 3 Interrupt
pub(super) const IGC_EIMS_TX_QUEUE0: u32 = IGC_EICR_TX_QUEUE0; // Tx Queue 0 Interrupt
pub(super) const IGC_EIMS_TX_QUEUE1: u32 = IGC_EICR_TX_QUEUE1; // Tx Queue 1 Interrupt
pub(super) const IGC_EIMS_TX_QUEUE2: u32 = IGC_EICR_TX_QUEUE2; // Tx Queue 2 Interrupt
pub(super) const IGC_EIMS_TX_QUEUE3: u32 = IGC_EICR_TX_QUEUE3; // Tx Queue 3 Interrupt
pub(super) const IGC_EIMS_TCP_TIMER: u32 = IGC_EICR_TCP_TIMER; // TCP Timer
pub(super) const IGC_EIMS_OTHER: u32 = IGC_EICR_OTHER; // Interrupt Cause Active

// Interrupt Cause Set
pub(super) const IGC_ICS_LSC: u32 = IGC_ICR_LSC; // Link Status Change
pub(super) const IGC_ICS_RXSEQ: u32 = IGC_ICR_RXSEQ; // Rx sequence error
pub(super) const IGC_ICS_RXDMT0: u32 = IGC_ICR_RXDMT0; // Rx desc min. threshold

// Extended Interrupt Cause Set
pub(super) const IGC_EICS_RX_QUEUE0: u32 = IGC_EICR_RX_QUEUE0; // Rx Queue 0 Interrupt
pub(super) const IGC_EICS_RX_QUEUE1: u32 = IGC_EICR_RX_QUEUE1; // Rx Queue 1 Interrupt
pub(super) const IGC_EICS_RX_QUEUE2: u32 = IGC_EICR_RX_QUEUE2; // Rx Queue 2 Interrupt
pub(super) const IGC_EICS_RX_QUEUE3: u32 = IGC_EICR_RX_QUEUE3; // Rx Queue 3 Interrupt
pub(super) const IGC_EICS_TX_QUEUE0: u32 = IGC_EICR_TX_QUEUE0; // Tx Queue 0 Interrupt
pub(super) const IGC_EICS_TX_QUEUE1: u32 = IGC_EICR_TX_QUEUE1; // Tx Queue 1 Interrupt
pub(super) const IGC_EICS_TX_QUEUE2: u32 = IGC_EICR_TX_QUEUE2; // Tx Queue 2 Interrupt
pub(super) const IGC_EICS_TX_QUEUE3: u32 = IGC_EICR_TX_QUEUE3; // Tx Queue 3 Interrupt
pub(super) const IGC_EICS_TCP_TIMER: u32 = IGC_EICR_TCP_TIMER; // TCP Timer
pub(super) const IGC_EICS_OTHER: u32 = IGC_EICR_OTHER; // Interrupt Cause Active

// IGC_EITR_CNT_IGNR is only for 82576 and newer
pub(super) const IGC_EITR_CNT_IGNR: u32 = 0x80000000; // Don't reset counters on write

// Transmit Descriptor Control
pub(super) const IGC_TXDCTL_PTHRESH: u32 = 0x0000003F; // TXDCTL Prefetch Threshold
pub(super) const IGC_TXDCTL_HTHRESH: u32 = 0x00003F00; // TXDCTL Host Threshold
pub(super) const IGC_TXDCTL_WTHRESH: u32 = 0x003F0000; // TXDCTL Writeback Threshold
pub(super) const IGC_TXDCTL_GRAN: u32 = 0x01000000; // TXDCTL Granularity
pub(super) const IGC_TXDCTL_FULL_TX_DESC_WB: u32 = 0x01010000; // GRAN=1, WTHRESH=1
pub(super) const IGC_TXDCTL_MAX_TX_DESC_PREFETCH: u32 = 0x0100001F; // GRAN=1, PTHRESH=31

// Flow Control Constants
pub(super) const FLOW_CONTROL_ADDRESS_LOW: u32 = 0x00C28001;
pub(super) const FLOW_CONTROL_ADDRESS_HIGH: u32 = 0x00000100;
pub(super) const FLOW_CONTROL_TYPE: u32 = 0x8808;

// 802.1q VLAN Packet Size
pub(super) const VLAN_TAG_SIZE: u32 = 4; // 802.3ac tag (not DMA'd)
pub(super) const IGC_VLAN_FILTER_TBL_SIZE: u32 = 128; // VLAN Filter Table (4096 bits)

// Receive Address
// Number of high/low register pairs in the RAR. The RAR (Receive Address
// Registers) holds the directed and multicast addresses that we monitor.
// Technically, we have 16 spots.  However, we reserve one of these spots
// (RAR[15]) for our directed address used by controllers with
// manageability enabled, allowing us room for 15 multicast addresses.
pub(super) const IGC_RAR_ENTRIES: u32 = 15;
pub(super) const IGC_RAH_AV: u32 = 0x80000000; // Receive descriptor valid
pub(super) const IGC_RAL_MAC_ADDR_LEN: usize = 4;
pub(super) const IGC_RAH_MAC_ADDR_LEN: usize = 2;

// Loop limit on how long we wait for auto-negotiation to complete
pub(super) const COPPER_LINK_UP_LIMIT: u32 = 10;
pub(super) const PHY_AUTO_NEG_LIMIT: u32 = 45;

// Number of 100 microseconds we wait for PCI Express master disable
pub(super) const MASTER_DISABLE_TIMEOUT: u32 = 800;

// Number of milliseconds we wait for PHY configuration done after MAC reset
pub(super) const PHY_CFG_TIMEOUT: u32 = 100;

// Number of 2 milliseconds we wait for acquiring MDIO ownership.
pub(super) const MDIO_OWNERSHIP_TIMEOUT: u32 = 10;

// Number of milliseconds for NVM auto read done after MAC reset.
pub(super) const AUTO_READ_DONE_TIMEOUT: u32 = 10;

// Time Sync Interrupt Cause/Mask Register Bits
pub(super) const TSINTR_SYS_WRAP: u32 = 1 << 0; // SYSTIM Wrap around.
pub(super) const TSINTR_TXTS: u32 = 1 << 1; // Transmit Timestamp.
pub(super) const TSINTR_TT0: u32 = 1 << 3; // Target Time 0 Trigger.
pub(super) const TSINTR_TT1: u32 = 1 << 4; // Target Time 1 Trigger.
pub(super) const TSINTR_AUTT0: u32 = 1 << 5; // Auxiliary Timestamp 0 Taken.
pub(super) const TSINTR_AUTT1: u32 = 1 << 6; // Auxiliary Timestamp 1 Taken.

// EEE defines
pub(super) const IGC_IPCNFG_EEE_2_5G_AN: u32 = 0x00000010; // IPCNFG EEE Ena 2.5G AN
pub(super) const IGC_IPCNFG_EEE_1G_AN: u32 = 0x00000008; // IPCNFG EEE Ena 1G AN
pub(super) const IGC_IPCNFG_EEE_100M_AN: u32 = 0x00000004; // IPCNFG EEE Ena 100M AN
pub(super) const IGC_EEER_TX_LPI_EN: u32 = 0x00010000; // EEER Tx LPI Enable
pub(super) const IGC_EEER_RX_LPI_EN: u32 = 0x00020000; // EEER Rx LPI Enable
pub(super) const IGC_EEER_LPI_FC: u32 = 0x00040000; // EEER Ena on Flow Cntrl

// EEE status
pub(super) const IGC_EEER_EEE_NEG: u32 = 0x20000000; // EEE capability nego
pub(super) const IGC_EEER_RX_LPI_STATUS: u32 = 0x40000000; // Rx in LPI state
pub(super) const IGC_EEER_TX_LPI_STATUS: u32 = 0x80000000; // Tx in LPI state
pub(super) const IGC_EEE_LP_ADV_ADDR_I350: u32 = 0x040F; // EEE LP Advertisement
pub(super) const IGC_M88E1543_PAGE_ADDR: u32 = 0x16; // Page Offset Register
pub(super) const IGC_M88E1543_EEE_CTRL_1: u32 = 0x0;
pub(super) const IGC_M88E1543_EEE_CTRL_1_MS: u32 = 0x0001; // EEE Master/Slave
pub(super) const IGC_M88E1543_FIBER_CTRL: u32 = 0x0; // Fiber Control Register
pub(super) const IGC_EEE_ADV_DEV_I354: u32 = 7;
pub(super) const IGC_EEE_ADV_ADDR_I354: u32 = 60;
pub(super) const IGC_EEE_ADV_100_SUPPORTED: u32 = 1 << 1; // 100BaseTx EEE Supported
pub(super) const IGC_EEE_ADV_1000_SUPPORTED: u32 = 1 << 2; // 1000BaseT EEE Supported
pub(super) const IGC_PCS_STATUS_DEV_I354: u32 = 3;
pub(super) const IGC_PCS_STATUS_ADDR_I354: u32 = 1;
pub(super) const IGC_PCS_STATUS_RX_LPI_RCVD: u32 = 0x0400;
pub(super) const IGC_PCS_STATUS_TX_LPI_RCVD: u32 = 0x0800;
pub(super) const IGC_M88E1512_CFG_REG_1: u32 = 0x0010;
pub(super) const IGC_M88E1512_CFG_REG_2: u32 = 0x0011;
pub(super) const IGC_M88E1512_CFG_REG_3: u32 = 0x0007;
pub(super) const IGC_M88E1512_MODE: u32 = 0x0014;
pub(super) const IGC_EEE_SU_LPI_CLK_STP: u32 = 0x00800000; // EEE LPI Clock Stop
pub(super) const IGC_EEE_LP_ADV_DEV_I225: u32 = 7; // EEE LP Adv Device
pub(super) const IGC_EEE_LP_ADV_ADDR_I225: u32 = 61; // EEE LP Adv Register

pub(super) const IGC_MMDAC_FUNC_DATA: u16 = 0x4000; // Data, no post increment

// PHY Control Register
pub(super) const MII_CR_SPEED_SELECT_MSB: u16 = 0x0040; // bits 6,13: 10=1000, 01=100, 00=10
pub(super) const MII_CR_COLL_TEST_ENABLE: u16 = 0x0080; // Collision test enable
pub(super) const MII_CR_FULL_DUPLEX: u16 = 0x0100; // FDX =1, half duplex =0
pub(super) const MII_CR_RESTART_AUTO_NEG: u16 = 0x0200; // Restart auto negotiation
pub(super) const MII_CR_ISOLATE: u16 = 0x0400; // Isolate PHY from MII
pub(super) const MII_CR_POWER_DOWN: u16 = 0x0800; // Power down
pub(super) const MII_CR_AUTO_NEG_EN: u16 = 0x1000; // Auto Neg Enable
pub(super) const MII_CR_SPEED_SELECT_LSB: u16 = 0x2000; // bits 6,13: 10=1000, 01=100, 00=10
pub(super) const MII_CR_LOOPBACK: u16 = 0x4000; // 0 = normal, 1 = loopback
pub(super) const MII_CR_RESET: u16 = 0x8000; // 0 = normal, 1 = PHY reset
pub(super) const MII_CR_SPEED_1000: u16 = 0x0040;
pub(super) const MII_CR_SPEED_100: u16 = 0x2000;
pub(super) const MII_CR_SPEED_10: u16 = 0x0000;

// PHY Status Register
pub(super) const MII_SR_EXTENDED_CAPS: u32 = 0x0001; // Extended register capabilities
pub(super) const MII_SR_JABBER_DETECT: u32 = 0x0002; // Jabber Detected
pub(super) const MII_SR_LINK_STATUS: u32 = 0x0004; // Link Status 1 = link
pub(super) const MII_SR_AUTONEG_CAPS: u32 = 0x0008; // Auto Neg Capable
pub(super) const MII_SR_REMOTE_FAULT: u32 = 0x0010; // Remote Fault Detect
pub(super) const MII_SR_AUTONEG_COMPLETE: u32 = 0x0020; // Auto Neg Complete
pub(super) const MII_SR_PREAMBLE_SUPPRESS: u32 = 0x0040; // Preamble may be suppressed
pub(super) const MII_SR_EXTENDED_STATUS: u32 = 0x0100; // Ext. status info in Reg 0x0F
pub(super) const MII_SR_100T2_HD_CAPS: u32 = 0x0200; // 100T2 Half Duplex Capable
pub(super) const MII_SR_100T2_FD_CAPS: u32 = 0x0400; // 100T2 Full Duplex Capable
pub(super) const MII_SR_10T_HD_CAPS: u32 = 0x0800; // 10T   Half Duplex Capable
pub(super) const MII_SR_10T_FD_CAPS: u32 = 0x1000; // 10T   Full Duplex Capable
pub(super) const MII_SR_100X_HD_CAPS: u32 = 0x2000; // 100X  Half Duplex Capable
pub(super) const MII_SR_100X_FD_CAPS: u32 = 0x4000; // 100X  Full Duplex Capable
pub(super) const MII_SR_100T4_CAPS: u32 = 0x8000; // 100T4 Capable

// Autoneg Advertisement Register
pub(super) const NWAY_AR_SELECTOR_FIELD: u32 = 0x0001; // indicates IEEE 802.3 CSMA/CD
pub(super) const NWAY_AR_10T_HD_CAPS: u32 = 0x0020; // 10T   Half Duplex Capable
pub(super) const NWAY_AR_10T_FD_CAPS: u32 = 0x0040; // 10T   Full Duplex Capable
pub(super) const NWAY_AR_100TX_HD_CAPS: u32 = 0x0080; // 100TX Half Duplex Capable
pub(super) const NWAY_AR_100TX_FD_CAPS: u32 = 0x0100; // 100TX Full Duplex Capable
pub(super) const NWAY_AR_100T4_CAPS: u32 = 0x0200; // 100T4 Capable
pub(super) const NWAY_AR_PAUSE: u32 = 0x0400; // Pause operation desired
pub(super) const NWAY_AR_ASM_DIR: u32 = 0x0800; // Asymmetric Pause Direction bit
pub(super) const NWAY_AR_REMOTE_FAULT: u32 = 0x2000; // Remote Fault detected
pub(super) const NWAY_AR_NEXT_PAGE: u32 = 0x8000; // Next Page ability supported

// Link Partner Ability Register (Base Page)
pub(super) const NWAY_LPAR_SELECTOR_FIELD: u32 = 0x0000; // LP protocol selector field
pub(super) const NWAY_LPAR_10T_HD_CAPS: u32 = 0x0020; // LP 10T Half Dplx Capable
pub(super) const NWAY_LPAR_10T_FD_CAPS: u32 = 0x0040; // LP 10T Full Dplx Capable
pub(super) const NWAY_LPAR_100TX_HD_CAPS: u32 = 0x0080; // LP 100TX Half Dplx Capable
pub(super) const NWAY_LPAR_100TX_FD_CAPS: u32 = 0x0100; // LP 100TX Full Dplx Capable
pub(super) const NWAY_LPAR_100T4_CAPS: u32 = 0x0200; // LP is 100T4 Capable
pub(super) const NWAY_LPAR_PAUSE: u32 = 0x0400; // LP Pause operation desired
pub(super) const NWAY_LPAR_ASM_DIR: u32 = 0x0800; // LP Asym Pause Direction bit
pub(super) const NWAY_LPAR_REMOTE_FAULT: u32 = 0x2000; // LP detected Remote Fault
pub(super) const NWAY_LPAR_ACKNOWLEDGE: u32 = 0x4000; // LP rx'd link code word
pub(super) const NWAY_LPAR_NEXT_PAGE: u32 = 0x8000; // Next Page ability supported

// Autoneg Expansion Register
pub(super) const NWAY_ER_LP_NWAY_CAPS: u32 = 0x0001; // LP has Auto Neg Capability
pub(super) const NWAY_ER_PAGE_RXD: u32 = 0x0002; // LP 10T Half Dplx Capable
pub(super) const NWAY_ER_NEXT_PAGE_CAPS: u32 = 0x0004; // LP 10T Full Dplx Capable
pub(super) const NWAY_ER_LP_NEXT_PAGE_CAPS: u32 = 0x0008; // LP 100TX Half Dplx Capable
pub(super) const NWAY_ER_PAR_DETECT_FAULT: u32 = 0x0010; // LP 100TX Full Dplx Capable

// 1000BASE-T Control Register
pub(super) const CR_1000T_ASYM_PAUSE: u32 = 0x0080; // Advertise asymmetric pause bit
pub(super) const CR_1000T_HD_CAPS: u32 = 0x0100; // Advertise 1000T HD capability
pub(super) const CR_1000T_FD_CAPS: u32 = 0x0200; // Advertise 1000T FD capability
                                                 // 1=Repeater/switch device port 0=DTE device
pub(super) const CR_1000T_REPEATER_DTE: u32 = 0x0400;
// 1=Configure PHY as Master 0=Configure PHY as Slave
pub(super) const CR_1000T_MS_VALUE: u32 = 0x0800;
// 1=Master/Slave manual config value 0=Automatic Master/Slave config
pub(super) const CR_1000T_MS_ENABLE: u32 = 0x1000;
pub(super) const CR_1000T_TEST_MODE_NORMAL: u32 = 0x0000; /* Normal Operation */
pub(super) const CR_1000T_TEST_MODE_1: u32 = 0x2000; // Transmit Waveform test
pub(super) const CR_1000T_TEST_MODE_2: u32 = 0x4000; // Master Transmit Jitter test
pub(super) const CR_1000T_TEST_MODE_3: u32 = 0x6000; // Slave Transmit Jitter test
pub(super) const CR_1000T_TEST_MODE_4: u32 = 0x8000; // Transmitter Distortion test

// 1000BASE-T Status Register
pub(super) const SR_1000T_IDLE_ERROR_CNT: u32 = 0x00FF; // Num idle err since last rd
pub(super) const SR_1000T_ASYM_PAUSE_DIR: u32 = 0x0100; // LP asym pause direction bit
pub(super) const SR_1000T_LP_HD_CAPS: u32 = 0x0400; // LP is 1000T HD capable
pub(super) const SR_1000T_LP_FD_CAPS: u32 = 0x0800; // LP is 1000T FD capable
pub(super) const SR_1000T_REMOTE_RX_STATUS: u32 = 0x1000; // Remote receiver OK
pub(super) const SR_1000T_LOCAL_RX_STATUS: u32 = 0x2000; // Local receiver OK
pub(super) const SR_1000T_MS_CONFIG_RES: u32 = 0x4000; // 1=Local Tx Master, 0=Slave
pub(super) const SR_1000T_MS_CONFIG_FAULT: u32 = 0x8000; // Master/Slave config fault

pub(super) const SR_1000T_PHY_EXCESSIVE_IDLE_ERR_COUNT: u32 = 5;

// PHY 1000 MII Register/Bit Definitions
// PHY Registers defined by IEEE
pub(super) const PHY_CONTROL: u32 = 0x00; // Control Register
pub(super) const PHY_STATUS: u32 = 0x01; // Status Register
pub(super) const PHY_ID1: u32 = 0x02; // Phy Id Reg (word 1)
pub(super) const PHY_ID2: u32 = 0x03; // Phy Id Reg (word 2)
pub(super) const PHY_AUTONEG_ADV: u32 = 0x04; // Autoneg Advertisement
pub(super) const PHY_LP_ABILITY: u32 = 0x05; // Link Partner Ability (Base Page)
pub(super) const PHY_AUTONEG_EXP: u32 = 0x06; // Autoneg Expansion Reg
pub(super) const PHY_NEXT_PAGE_TX: u32 = 0x07; // Next Page Tx
pub(super) const PHY_LP_NEXT_PAGE: u32 = 0x08; // Link Partner Next Page
pub(super) const PHY_1000T_CTRL: u32 = 0x09; // 1000Base-T Control Reg
pub(super) const PHY_1000T_STATUS: u32 = 0x0A; // 1000Base-T Status Reg
pub(super) const PHY_EXT_STATUS: u32 = 0x0F; // Extended Status Reg

// PHY GPY 211 registers
pub(super) const STANDARD_AN_REG_MASK: u32 = 0x0007; // MMD
pub(super) const ANEG_MULTIGBT_AN_CTRL: u32 = 0x0020; // MULTI GBT AN Control Register
pub(super) const MMD_DEVADDR_SHIFT: u32 = 16; // Shift MMD to higher bits
pub(super) const CR_2500T_FD_CAPS: u32 = 0x0080; // Advertise 2500T FD capability

pub(super) const PHY_CONTROL_LB: u32 = 0x4000; // PHY Loopback bit

// NVM Control
pub(super) const IGC_EECD_SK: u32 = 0x00000001; // NVM Clock
pub(super) const IGC_EECD_CS: u32 = 0x00000002; // NVM Chip Select
pub(super) const IGC_EECD_DI: u32 = 0x00000004; // NVM Data In
pub(super) const IGC_EECD_DO: u32 = 0x00000008; // NVM Data Out
pub(super) const IGC_EECD_REQ: u32 = 0x00000040; // NVM Access Request
pub(super) const IGC_EECD_GNT: u32 = 0x00000080; // NVM Access Grant
pub(super) const IGC_EECD_PRES: u32 = 0x00000100; // NVM Present
pub(super) const IGC_EECD_SIZE: u32 = 0x00000200; // NVM Size (0=64 word 1=256 word)

// NVM Addressing bits based on type 0=small, 1=large
pub(super) const IGC_EECD_ADDR_BITS: u32 = 0x00000400;
pub(super) const IGC_NVM_GRANT_ATTEMPTS: u32 = 1000; // NVM # attempts to gain grant
pub(super) const IGC_EECD_AUTO_RD: u32 = 0x00000200; // NVM Auto Read done
pub(super) const IGC_EECD_SIZE_EX_MASK: u32 = 0x00007800; // NVM Size
pub(super) const IGC_EECD_SIZE_EX_SHIFT: u32 = 11;
pub(super) const IGC_EECD_FLUPD: u32 = 0x00080000; // Update FLASH
pub(super) const IGC_EECD_AUPDEN: u32 = 0x00100000; // Ena Auto FLASH update
pub(super) const IGC_EECD_SEC1VAL: u32 = 0x00400000; // Sector One Valid
pub(super) const IGC_EECD_SEC1VAL_VALID_MASK: u32 = IGC_EECD_AUTO_RD | IGC_EECD_PRES;

pub(super) const IGC_EECD_FLUPD_I225: u32 = 0x00800000; // Update FLASH
pub(super) const IGC_EECD_FLUDONE_I225: u32 = 0x04000000; // Update FLASH done
pub(super) const IGC_EECD_FLASH_DETECTED_I225: u32 = 0x00080000; // FLASH detected
pub(super) const IGC_FLUDONE_ATTEMPTS: u32 = 20000;
pub(super) const IGC_EERD_EEWR_MAX_COUNT: u32 = 512; // buffered EEPROM words rw
pub(super) const IGC_EECD_SEC1VAL_I225: u32 = 0x02000000; // Sector One Valid
pub(super) const IGC_FLSECU_BLK_SW_ACCESS_I225: u32 = 0x00000004; // Block SW access
pub(super) const IGC_FWSM_FW_VALID_I225: u32 = 0x8000; // FW valid bit

pub(super) const IGC_NVM_RW_REG_DATA: u32 = 16; // Offset to data in NVM read/write regs
pub(super) const IGC_NVM_RW_REG_DONE: u32 = 2; // Offset to READ/WRITE done bit
pub(super) const IGC_NVM_RW_REG_START: u32 = 1; // Start operation
pub(super) const IGC_NVM_RW_ADDR_SHIFT: u32 = 2; // Shift to the address bits
pub(super) const IGC_NVM_POLL_WRITE: u32 = 1; // Flag for polling for write complete
pub(super) const IGC_NVM_POLL_READ: u32 = 0; // Flag for polling for read complete
pub(super) const IGC_FLASH_UPDATES: u32 = 2000;

// NVM Word Offsets
pub(super) const NVM_COMPAT: u16 = 0x0003;
pub(super) const NVM_ID_LED_SETTINGS: u32 = 0x0004;
pub(super) const NVM_FUTURE_INIT_WORD1: u32 = 0x0019;
pub(super) const NVM_COMPAT_VALID_CSUM: u32 = 0x0001;
pub(super) const NVM_FUTURE_INIT_WORD1_VALID_CSUM: u32 = 0x0040;

pub(super) const NVM_INIT_CONTROL2_REG: u32 = 0x000F;
pub(super) const NVM_INIT_CONTROL3_PORT_B: u32 = 0x0014;
pub(super) const NVM_INIT_3GIO_3: u32 = 0x001A;
pub(super) const NVM_SWDEF_PINS_CTRL_PORT_0: u32 = 0x0020;
pub(super) const NVM_INIT_CONTROL3_PORT_A: u32 = 0x0024;
pub(super) const NVM_CFG: u32 = 0x0012;
pub(super) const NVM_ALT_MAC_ADDR_PTR: u16 = 0x0037;
pub(super) const NVM_CHECKSUM_REG: u32 = 0x003F;

// PBA (printed board assembly) number words
pub(super) const NVM_PBA_OFFSET_0: u32 = 8;
pub(super) const NVM_PBA_OFFSET_1: u32 = 9;
pub(super) const NVM_PBA_PTR_GUARD: u32 = 0xFAFA;
pub(super) const NVM_WORD_SIZE_BASE_SHIFT: u32 = 6;

// Word definitions for ID LED Settings
pub(super) const ID_LED_RESERVED_0000: u32 = 0x0000;
pub(super) const ID_LED_RESERVED_FFFF: u32 = 0xFFFF;
pub(super) const ID_LED_DEFAULT: u32 = (ID_LED_OFF1_ON2 << 12)
    | (ID_LED_OFF1_OFF2 << 8)
    | (ID_LED_DEF1_DEF2 << 4)
    | (ID_LED_DEF1_DEF2);
pub(super) const ID_LED_DEF1_DEF2: u32 = 0x1;
pub(super) const ID_LED_DEF1_ON2: u32 = 0x2;
pub(super) const ID_LED_DEF1_OFF2: u32 = 0x3;
pub(super) const ID_LED_ON1_DEF2: u32 = 0x4;
pub(super) const ID_LED_ON1_ON2: u32 = 0x5;
pub(super) const ID_LED_ON1_OFF2: u32 = 0x6;
pub(super) const ID_LED_OFF1_DEF2: u32 = 0x7;
pub(super) const ID_LED_OFF1_ON2: u32 = 0x8;
pub(super) const ID_LED_OFF1_OFF2: u32 = 0x9;

pub(super) const IGP_ACTIVITY_LED_MASK: u32 = 0xFFFFF0FF;
pub(super) const IGP_ACTIVITY_LED_ENABLE: u32 = 0x0300;
pub(super) const IGP_LED3_MODE: u32 = 0x07000000;

// PCI/PCI-X/PCI-EX Config space
pub(super) const PCIX_COMMAND_REGISTER: u32 = 0xE6;
pub(super) const PCIX_STATUS_REGISTER_LO: u32 = 0xE8;
pub(super) const PCIX_STATUS_REGISTER_HI: u32 = 0xEA;
pub(super) const PCI_HEADER_TYPE_REGISTER: u32 = 0x0E;
pub(super) const PCIE_LINK_STATUS: u32 = 0x12;

pub(super) const PCIX_COMMAND_MMRBC_MASK: u32 = 0x000C;
pub(super) const PCIX_COMMAND_MMRBC_SHIFT: u32 = 0x2;
pub(super) const PCIX_STATUS_HI_MMRBC_MASK: u32 = 0x0060;
pub(super) const PCIX_STATUS_HI_MMRBC_SHIFT: u32 = 0x5;
pub(super) const PCIX_STATUS_HI_MMRBC_4K: u32 = 0x3;
pub(super) const PCIX_STATUS_HI_MMRBC_2K: u32 = 0x2;
pub(super) const PCIX_STATUS_LO_FUNC_MASK: u32 = 0x7;
pub(super) const PCI_HEADER_TYPE_MULTIFUNC: u32 = 0x80;
pub(super) const PCIE_LINK_WIDTH_MASK: u32 = 0x3F0;
pub(super) const PCIE_LINK_WIDTH_SHIFT: u32 = 4;
pub(super) const PCIE_LINK_SPEED_MASK: u32 = 0x0F;
pub(super) const PCIE_LINK_SPEED_2500: u32 = 0x01;
pub(super) const PCIE_LINK_SPEED_5000: u32 = 0x02;

pub(super) const PHY_REVISION_MASK: u32 = 0xFFFFFFF0;
pub(super) const MAX_PHY_REG_ADDRESS: u32 = 0x1F; // 5 bit address bus (0-0x1F)
pub(super) const MAX_PHY_MULTI_PAGE_REG: u32 = 0xF;

// Bit definitions for valid PHY IDs.
// I = Integrated
// E = External
pub(super) const M88IGC_E_PHY_ID: u32 = 0x01410C50;
pub(super) const M88IGC_I_PHY_ID: u32 = 0x01410C30;
pub(super) const M88E1011_I_PHY_ID: u32 = 0x01410C20;
pub(super) const IGP01IGC_I_PHY_ID: u32 = 0x02A80380;
pub(super) const M88E1111_I_PHY_ID: u32 = 0x01410CC0;
pub(super) const GG82563_E_PHY_ID: u32 = 0x01410CA0;
pub(super) const IGP03IGC_E_PHY_ID: u32 = 0x02A80390;
pub(super) const IFE_E_PHY_ID: u32 = 0x02A80330;
pub(super) const IFE_PLUS_E_PHY_ID: u32 = 0x02A80320;
pub(super) const IFE_C_E_PHY_ID: u32 = 0x02A80310;
pub(super) const I225_I_PHY_ID: u32 = 0x67C9DC00;

// M88EC018 Rev 2 specific DownShift settings
pub(super) const M88EC018_EPSCR_DOWNSHIFT_COUNTER_MASK: u32 = 0x0E00;
pub(super) const M88EC018_EPSCR_DOWNSHIFT_COUNTER_5X: u32 = 0x0800;

// Bits...
// 15-5: page
// 4-0: register offset
pub(super) const GG82563_PAGE_SHIFT: u32 = 5;

const fn cg82563_reg(page: u32, reg: u32) -> u32 {
    ((page) << GG82563_PAGE_SHIFT) | ((reg) & MAX_PHY_REG_ADDRESS)
}

pub(super) const GG82563_MIN_ALT_REG: u32 = 30;

// GG82563 Specific Registers
pub(super) const GG82563_PHY_SPEC_CTRL: u32 = cg82563_reg(0, 16); // PHY Spec Cntrl
pub(super) const GG82563_PHY_PAGE_SELECT: u32 = cg82563_reg(0, 22); // Page Select
pub(super) const GG82563_PHY_SPEC_CTRL_2: u32 = cg82563_reg(0, 26); // PHY Spec Cntrl2
pub(super) const GG82563_PHY_PAGE_SELECT_ALT: u32 = cg82563_reg(0, 29); // Alt Page Select

// MAC Specific Control Register
pub(super) const GG82563_PHY_MAC_SPEC_CTRL: u32 = cg82563_reg(2, 21);

pub(super) const GG82563_PHY_DSP_DISTANCE: u32 = cg82563_reg(5, 26); // DSP Distance

// Page 193 - Port Control Registers
// Kumeran Mode Control
pub(super) const GG82563_PHY_KMRN_MODE_CTRL: u32 = cg82563_reg(193, 16);
pub(super) const GG82563_PHY_PWR_MGMT_CTRL: u32 = cg82563_reg(193, 20); // Pwr Mgt Ctrl

// Page 194 - KMRN Registers */
pub(super) const GG82563_PHY_INBAND_CTRL: u32 = cg82563_reg(194, 18); // Inband Ctrl

// MDI Control
pub(super) const IGC_MDIC_DATA_MASK: u32 = 0x0000FFFF;
pub(super) const IGC_MDIC_INT_EN: u32 = 0x20000000;
pub(super) const IGC_MDIC_REG_MASK: u32 = 0x001F0000;
pub(super) const IGC_MDIC_REG_SHIFT: u32 = 16;
pub(super) const IGC_MDIC_PHY_SHIFT: u32 = 21;
pub(super) const IGC_MDIC_OP_WRITE: u32 = 0x04000000;
pub(super) const IGC_MDIC_OP_READ: u32 = 0x08000000;
pub(super) const IGC_MDIC_READY: u32 = 0x10000000;
pub(super) const IGC_MDIC_ERROR: u32 = 0x40000000;

// SerDes Control
pub(super) const IGC_GEN_POLL_TIMEOUT: u32 = 640;

// DMA Coalescing register fields
// DMA Coalescing Watchdog Timer
pub(super) const IGC_DMACR_DMACWT_MASK: u32 = 0x00003FFF;

// DMA Coalescing Rx Threshold
pub(super) const IGC_DMACR_DMACTHR_MASK: u32 = 0x00FF0000;
pub(super) const IGC_DMACR_DMACTHR_SHIFT: u32 = 16;

// Lx when no PCIe transactions
pub(super) const IGC_DMACR_DMAC_LX_MASK: u32 = 0x30000000;
pub(super) const IGC_DMACR_DMAC_LX_SHIFT: u32 = 28;
pub(super) const IGC_DMACR_DMAC_EN: u32 = 0x80000000; // Enable DMA Coalescing

// Flow ctrl Rx Threshold High val
pub(super) const IGC_FCRTC_RTH_COAL_MASK: u32 = 0x0003FFF0;
pub(super) const IGC_FCRTC_RTH_COAL_SHIFT: u32 = 4;

// Lx power decision based on DMA coal
pub(super) const IGC_PCIEMISC_LX_DECISION: u32 = 0x00000080;

pub(super) const IGC_RXPBS_CFG_TS_EN: u32 = 0x80000000; // Timestamp in Rx buffer
pub(super) const IGC_RXPBS_SIZE_I210_MASK: u32 = 0x0000003F; // Rx packet buffer size
pub(super) const IGC_TXPB0S_SIZE_I210_MASK: u32 = 0x0000003F; // Tx packet buffer 0 size
pub(super) const I210_RXPBSIZE_DEFAULT: u32 = 0x000000A2; // RXPBSIZE default
pub(super) const I210_TXPBSIZE_DEFAULT: u32 = 0x04000014; // TXPBSIZE default

pub(super) const IGC_LTRC_EEEMS_EN: u32 = 0x00000020; // Enable EEE LTR max send

// Minimum time for 1000BASE-T where no data will be transmit following move out
// of EEE LPI Tx state
pub(super) const IGC_TW_SYSTEM_1000_MASK: u32 = 0x000000FF;

// Minimum time for 100BASE-T where no data will be transmit following move out
// of EEE LPI Tx state
pub(super) const IGC_TW_SYSTEM_100_MASK: u32 = 0x0000FF00;
pub(super) const IGC_TW_SYSTEM_100_SHIFT: u32 = 8;
pub(super) const IGC_LTRMINV_LTRV_MASK: u32 = 0x000003FF; // LTR minimum value
pub(super) const IGC_LTRMAXV_LTRV_MASK: u32 = 0x000003FF; // LTR maximum value
pub(super) const IGC_LTRMINV_SCALE_MASK: u32 = 0x00001C00; // LTR minimum scale
pub(super) const IGC_LTRMINV_SCALE_SHIFT: u32 = 10;
// Reg val to set scale to 1024 nsec
pub(super) const IGC_LTRMINV_SCALE_1024: u32 = 2;
// Reg val to set scale to 32768 nsec
pub(super) const IGC_LTRMINV_SCALE_32768: u32 = 3;
pub(super) const IGC_LTRMINV_LSNP_REQ: u32 = 0x00008000; // LTR Snoop Requirement
pub(super) const IGC_LTRMAXV_SCALE_MASK: u32 = 0x00001C00; // LTR maximum scale
pub(super) const IGC_LTRMAXV_SCALE_SHIFT: u32 = 10;
// Reg val to set scale to 1024 nsec
pub(super) const IGC_LTRMAXV_SCALE_1024: u32 = 2;
// Reg val to set scale to 32768 nsec
pub(super) const IGC_LTRMAXV_SCALE_32768: u32 = 3;
pub(super) const IGC_LTRMAXV_LSNP_REQ: u32 = 0x00008000; // LTR Snoop Requirement

pub(super) const I225_RXPBSIZE_DEFAULT: u32 = 0x000000A2; // RXPBSIZE default
pub(super) const I225_TXPBSIZE_DEFAULT: u32 = 0x04000014; // TXPBSIZE default
pub(super) const IGC_RXPBS_SIZE_I225_MASK: u32 = 0x0000003F; // Rx packet buffer size
pub(super) const IGC_TXPB0S_SIZE_I225_MASK: u32 = 0x0000003F; // Tx packet buffer 0 size
pub(super) const IGC_STM_OPCODE: u32 = 0xDB00;
pub(super) const IGC_EEPROM_FLASH_SIZE_WORD: u32 = 0x11;
pub(super) const INVM_DWORD_TO_RECORD_TYPE: fn(u32) -> u8 = |invm_dword| (invm_dword & 0x7) as u8;
pub(super) const INVM_DWORD_TO_WORD_ADDRESS: fn(u32) -> u8 =
    |invm_dword| ((invm_dword & 0x0000FE00) >> 9) as u8;
pub(super) const INVM_DWORD_TO_WORD_DATA: fn(u32) -> u16 =
    |invm_dword| ((invm_dword & 0xFFFF0000) >> 16) as u16;
pub(super) const IGC_INVM_RSA_KEY_SHA256_DATA_SIZE_IN_DWORDS: u32 = 8;
pub(super) const IGC_INVM_CSR_AUTOLOAD_DATA_SIZE_IN_DWORDS: u32 = 1;
pub(super) const IGC_INVM_ULT_BYTES_SIZE: u32 = 8;
pub(super) const IGC_INVM_RECORD_SIZE_IN_BYTES: u32 = 4;
pub(super) const IGC_INVM_VER_FIELD_ONE: u32 = 0x1FF8;
pub(super) const IGC_INVM_VER_FIELD_TWO: u32 = 0x7FE000;
pub(super) const IGC_INVM_IMGTYPE_FIELD: u32 = 0x1F800000;

pub(super) const IGC_INVM_MAJOR_MASK: u32 = 0x3F0;
pub(super) const IGC_INVM_MINOR_MASK: u32 = 0xF;
pub(super) const IGC_INVM_MAJOR_SHIFT: u32 = 4;
