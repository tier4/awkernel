pub const CTRL: usize = 0x00000; // Device Control Register
pub const EECD: usize = 0x00010; // EEPROM Control Register
pub const EERD: usize = 0x00014; // EEPROM Read Register
pub const SCTL: usize = 0x00024; // SerDes Control - RW
pub const FEXTNVM: usize = 0x00028; // Future Extended NVM register
pub const FEXTNVM3: usize = 0x0003C; // Future Extended NVM 3 - RW
pub const FEXTNVM4: usize = 0x00024; // Future Extended NVM 4 - RW
pub const FEXTNVM6: usize = 0x00010; // Future Extended NVM 6 - RW
pub const KUMCTRLSTA: usize = 0x00034; // MAC-PHY interface - RW
pub const VET: usize = 0x00038; // VLAN Ether Type - RW
pub const FCAL: usize = 0x00028; // Flow Control Address Low - RW
pub const FCAH: usize = 0x0002C; // Flow Control Address High -RW
pub const FCT: usize = 0x00030; // Flow Control Type - RW
pub const CONNSW: usize = 0x00034; // Copper/Fiber switch control - RW
pub const ICR: usize = 0x000C0; // Interrupt Cause Read Register
pub const ITR: usize = 0x000C4; // Interrupt Throttling Rate Register
pub const _ICS: usize = 0x000C8; // Interrupt Cause Set Register
pub const IMC: usize = 0x000D8; // Interrupt Mask Clear Register
pub const FCTTV: usize = 0x00170; // Flow Control Transmit Timer Value - RW
pub const TXCW: usize = 0x00178; // TX Configuration Word - RW
pub const RXCW: usize = 0x00180; // RX Configuration Word - RO
pub const TCTL_EXT: usize = 0x00404; // Extended TX Control - RW
pub const PBA: usize = 0x01000; // Packet Buffer Allocation Register
pub const PBS: usize = 0x01008; // Packet Buffer Size
pub const EEMNGCTL: usize = 0x01010; // MNG EEprom Control
pub const EEWR: usize = 0x0102C; // EEPROM Write Register - RW
pub const FLOP: usize = 0x0103C; // FLASH Opcode Register
pub const FCRTL: usize = 0x02160; // Flow Control Receive Threshold Low - RW
pub const FCRTH: usize = 0x02168; // Flow Control Receive Threshold High - RW
pub const KABGTXD: usize = 0x03004; // AFE Band Gap Transmit Ref Data
pub const CRCERRS: usize = 0x04000; // CRC Error Count - R/clr
pub const ALGNERRC: usize = 0x04004; // Alignment Error Count - R/clr
pub const SYMERRS: usize = 0x04008; // Symbol Error Count - R/clr
pub const RXERRC: usize = 0x0400C; // Receive Error Count - R/clr
pub const MPC: usize = 0x04010; // Missed Packet Count - R/clr
pub const SCC: usize = 0x04014; // Single Collision Count - R/clr
pub const ECOL: usize = 0x04018; // Excessive Collision Count - R/clr
pub const MCC: usize = 0x0401C; // Multiple Collision Count - R/clr
pub const LATECOL: usize = 0x04020; // Late Collision Count - R/clr
pub const COLC: usize = 0x04028; // Collision Count - R/clr
pub const DC: usize = 0x04030; // Defer Count - R/clr
pub const TNCRS: usize = 0x04034; // TX-No CRS - R/clr
pub const SEC: usize = 0x04038; // Sequence Error Count - R/clr
pub const CEXTERR: usize = 0x0403C; // Carrier Extension Error Count - R/clr
pub const RLEC: usize = 0x04040; // Receive Length Error Count - R/clr
pub const XONRXC: usize = 0x04048; // XON RX Count - R/clr
pub const XONTXC: usize = 0x0404C; // XON TX Count - R/clr
pub const XOFFRXC: usize = 0x04050; // XOFF RX Count - R/clr
pub const XOFFTXC: usize = 0x04054; // XOFF TX Count - R/clr
pub const FCRUC: usize = 0x04058; // Flow Control RX Unsupported Count- R/clr
pub const PRC64: usize = 0x0405C; // Packets RX (64 bytes) - R/clr
pub const PRC127: usize = 0x04060; // Packets RX (65-127 bytes) - R/clr
pub const PRC255: usize = 0x04064; // Packets RX (128-255 bytes) - R/clr
pub const PRC511: usize = 0x04068; // Packets RX (255-511 bytes) - R/clr
pub const PRC1023: usize = 0x0406C; // Packets RX (512-1023 bytes) - R/clr
pub const PRC1522: usize = 0x04070; // Packets RX (1024-1522 bytes) - R/clr
pub const GPRC: usize = 0x04074; // Good Packets RX Count - R/clr
pub const BPRC: usize = 0x04078; // Broadcast Packets RX Count - R/clr
pub const MPRC: usize = 0x0407C; // Multicast Packets RX Count - R/clr
pub const GPTC: usize = 0x04080; // Good Packets TX Count - R/clr
pub const GORCL: usize = 0x04088; // Good Octets RX Count Low - R/clr
pub const GORCH: usize = 0x0408C; // Good Octets RX Count High - R/clr
pub const GOTCL: usize = 0x04090; // Good Octets TX Count Low - R/clr
pub const GOTCH: usize = 0x04094; // Good Octets TX Count High - R/clr
pub const RNBC: usize = 0x040A0; // RX No Buffers Count - R/clr
pub const RUC: usize = 0x040A4; // RX Undersize Count - R/clr
pub const RFC: usize = 0x040A8; // RX Fragment Count - R/clr
pub const ROC: usize = 0x040AC; // RX Oversize Count - R/clr
pub const RJC: usize = 0x040B0; // RX Jabber Count - R/clr
pub const MGTPRC: usize = 0x040B4; // Management Packets RX Count - R/clr
pub const MGTPDC: usize = 0x040B8; // Management Packets Dropped Count - R/clr
pub const MGTPTC: usize = 0x040BC; // Management Packets TX Count - R/clr
pub const TORL: usize = 0x040C0; // Total Octets RX Low - R/clr
pub const TORH: usize = 0x040C4; // Total Octets RX High - R/clr
pub const TOTL: usize = 0x040C8; // Total Octets TX Low - R/clr
pub const TOTH: usize = 0x040CC; // Total Octets TX High - R/clr
pub const TPR: usize = 0x040D0; // Total Packets RX - R/clr
pub const TPT: usize = 0x040D4; // Total Packets TX - R/clr
pub const PTC64: usize = 0x040D8; // Packets TX (64 bytes) - R/clr
pub const PTC127: usize = 0x040DC; // Packets TX (65-127 bytes) - R/clr
pub const PTC255: usize = 0x040E0; // Packets TX (128-255 bytes) - R/clr
pub const PTC511: usize = 0x040E4; // Packets TX (256-511 bytes) - R/clr
pub const PTC1023: usize = 0x040E8; // Packets TX (512-1023 bytes) - R/clr
pub const PTC1522: usize = 0x040EC; // Packets TX (1024-1522 Bytes) - R/clr
pub const MPTC: usize = 0x040F0; // Multicast Packets TX Count - R/clr
pub const BPTC: usize = 0x040F4; // Broadcast Packets TX Count - R/clr
pub const TSCTC: usize = 0x040F8; // TCP Segmentation Context TX - R/clr
pub const TSCTFC: usize = 0x040FC; // TCP Segmentation Context TX Fail - R/clr
pub const IAC: usize = 0x04100; // Interrupt Assertion Count
pub const ICRXPTC: usize = 0x04104; // Interrupt Cause Rx Packet Timer Expire Count
pub const ICRXATC: usize = 0x04108; // Interrupt Cause Rx Absolute Timer Expire Count
pub const ICTXPTC: usize = 0x0410C; // Interrupt Cause Tx Packet Timer Expire Count
pub const ICTXATC: usize = 0x04110; // Interrupt Cause Tx Absolute Timer Expire Count
pub const ICTXQEC: usize = 0x04118; // Interrupt Cause Tx Queue Empty Count
pub const ICTXQMTC: usize = 0x0411C; // Interrupt Cause Tx Queue Minimum Threshold Count
pub const ICRXDMTC: usize = 0x04120; // Interrupt Cause Rx Descriptor Minimum Threshold Count
pub const ICRXOC: usize = 0x04124; // Interrupt Cause Receiver Overrun Count
pub const PCS_CFG0: usize = 0x04200; // PCS Configuration 0 - RW
pub const PCS_LCTL: usize = 0x04208; // PCS Link Control - RW
pub const PCS_LSTAT: usize = 0x0420C; // PCS Link Status - RO
pub const SW_FW_SYNC: usize = 0x05B5C; // Software-Firmware Synchronization - RW
pub const CRC_OFFSET: usize = 0x05F50; // CRC Offset Register
pub const HICR: usize = 0x08F00; // Host Interface Control
pub const TARC0: usize = 0x03840; // TX Arbitration Count (0)
pub const TARC1: usize = 0x03940; // TX Arbitration Count (1)
pub const VFTA: usize = 0x05600; //VLAN Filter Table Array - RW Array
pub const FFLT: usize = 0x05F00; // Flexible Filter Length Table - RW Array
pub const FFLT_DBG: usize = 0x05F04; // Debug Register
pub const RA: usize = 0x05400; // Receive Address - RW Array
pub const FCRTV_PCH: usize = 0x05F40; // PCH Flow Control Refresh Timer Value
pub const HOST_IF: usize = 0x08800; // Host Interface

// Status Register
pub const STATUS: usize = 0x00008; // Device Status register
pub const STATUS_FD: u32 = 1 << 0; // Full Duplex
pub const STATUS_LU: u32 = 1 << 1; // Link Up

pub const STATUS_FUNC_MASK: u32 = 0x0000000C; // PCI Function Mask
pub const STATUS_FUNC_SHIFT: u32 = 2;

pub const STATUS_FUNC_0: u32 = 0x00000000; // Function 0
pub const STATUS_FUNC_1: u32 = 0x00000004; // Function 1
pub const STATUS_TXOFF: u32 = 0x00000010; // transmission paused
pub const STATUS_TBIMODE: u32 = 0x00000020; // TBI mode
pub const STATUS_SPEED_MASK: u32 = 0x000000C0;
pub const STATUS_SPEED_10: u32 = 0x00000000; // Speed 10Mb/s
pub const STATUS_SPEED_100: u32 = 0x00000040; // Speed 100Mb/s
pub const STATUS_SPEED_1000: u32 = 0x00000080; // Speed 1000Mb/s
pub const STATUS_LAN_INIT_DONE: u32 = 0x00000200; // Lan Init Completion
pub const STATUS_PCI66: u32 = 0x00000800; // In 66MHz slot
pub const STATUS_PCIX_MODE: u32 = 0x00002000; // PCI-X mode
pub const STATUS_PCIX_SPEED: u32 = 0x0000C000; // PCI-X bus speed
pub const STATUS_DEV_RST_SET: u32 = 0x00100000;

// Constants used to interpret the masked PCI-X bus speed.
pub const STATUS_PCIX_SPEED_66: u32 = 0x00000000; // PCI-X bus speed  50-66 MHz
pub const STATUS_PCIX_SPEED_100: u32 = 0x00004000; // PCI-X bus speed  66-100 MHz
pub const STATUS_PCIX_SPEED_133: u32 = 0x00008000; // PCI-X bus speed 100-133 MHz

pub const E1000_82542_2_0_REV_ID: u32 = 2;
pub const E1000_82542_2_1_REV_ID: u32 = 3;
pub const E1000_REVISION_0: u32 = 0;
pub const E1000_REVISION_1: u32 = 1;
pub const E1000_REVISION_2: u32 = 2;
pub const E1000_REVISION_3: u32 = 3;

// Host Interface Control Register
pub const HICR_EN: u32 = 0x00000001; // Enable Bit - RO
pub const HICR_C: u32 = 0x00000002; // Driver sets this bit when done to put command in RAM

// Interrupt Mask Set/Read Register
pub const IMS: usize = 0x000D0;
pub const IMS_ENABLE_MASK: u32 = IMS_RXT0 | IMS_TXDW | IMS_RXDMT0 | IMS_RXSEQ | IMS_LSC;
pub const IMS_TXDW: u32 = 0x00000001; // Transmit Descriptor Written Back
pub const IMS_LSC: u32 = 0x00000004; // Link Status Change
pub const IMS_RXSEQ: u32 = 0x00000008; //  Receive Sequence Error
pub const IMS_RXDMT0: u32 = 0x00000010; // Receive Descriptor Minimum Threshold hit (ring 0)
pub const IMS_RX0: u32 = 0x00000040; // Rx overrun
pub const IMS_RXT0: u32 = 0x00000080; // Rx timer intr (ring 0)

// Transmit Registers
pub const TCTL: usize = 0x00400; // Transmit Control Register
pub const TIPG: usize = 0x00410; // Transmit IPG Register
pub const TDBAL: usize = 0x03800; // Transmit Descriptor Base Address Low
pub const TDBAH: usize = 0x03804; // Transmit Descriptor Base Address High
pub const TDLEN: usize = 0x03808; // Transmit Descriptor Length
pub const TDH: usize = 0x03810; // Transmit Descriptor Head
pub const TDT: usize = 0x03818; // Transmit Descriptor Tail
pub const TXDCTL: usize = 0x03828; // Transmit Descriptor Control

// Receive Registers
pub const RCTL: usize = 0x00100; // Receive Control Register
pub const RDBAL: usize = 0x02800; // Receive Descriptor Base Address Low
pub const RDBAH: usize = 0x02804; // Receive Descriptor Base Address High
pub const RDLEN: usize = 0x02808; // Receive Descriptor Base Length
pub const RDH: usize = 0x02810; // Receive Descriptor Head
pub const RDT: usize = 0x02818; // Receive Descriptor Tail
pub const RDTR: usize = 0x2820; // RX Delay Timer Register
pub const RADV: usize = 0x282C; // RX Interrupt Absolute Delay Timer
pub const MTA: usize = 0x05200; // Multicast Table Array
pub const RAL: usize = 0x05400; // Receive Address Low
pub const RAH: usize = 0x05404; // Receive Address High

// Receive Configuration Word
pub const RXCW_CW: u32 = 0x0000ffff; // RxConfigWord mask
pub const RXCW_NC: u32 = 0x04000000; // Receive config no carrier
pub const RXCW_IV: u32 = 0x08000000; // Receive config invalid
pub const RXCW_CC: u32 = 0x10000000; // Receive config change
pub const RXCW_C: u32 = 0x20000000; // Receive config
pub const RXCW_SYNCH: u32 = 0x40000000; // Receive config synch
pub const RXCW_ANC: u32 = 0x80000000; // Auto-neg complete

pub const CONNSW_ENRGSRC: u32 = 0x4;
pub const PCS_CFG_PCS_EN: u32 = 8;
pub const PCS_LCTL_FSV_1000: u32 = 4;
pub const PCS_LCTL_FDV_FULL: u32 = 8;
pub const PCS_LCTL_FSD: u32 = 0x10;
pub const PCS_LCTL_FORCE_FCTRL: u32 = 0x80;

pub const PCS_LSTS_LINK_OK: u32 = 0x01;
pub const PCS_LSTS_SPEED_100: u32 = 0x02;
pub const PCS_LSTS_SPEED_1000: u32 = 0x04;
pub const PCS_LSTS_DUPLEX_FULL: u32 = 0x08;
pub const PCS_LSTS_SYNK_OK: u32 = 0x10;

// Receive Address
pub const RAH_AV: u32 = 0x80000000; // Receive descriptor valid

pub const GCR: usize = 0x05B00; // 3GIO
pub const GCR_CMPL_TMOUT_MASK: u32 = 0x0000F000;
pub const GCR_CMPL_TMOUT_10_MS: u32 = 0x00001000;
pub const GCR_CMPL_TMOUT_RESEND: u32 = 0x00010000;
pub const GCR_CAP_VER2: u32 = 0x00040000;

pub const GCR_L1_ACT_WITHOUT_L0S_RX: u32 = 0x08000000;

pub const GCR_RXD_NO_SNOOP: u32 = 0x00000001;
pub const GCR_RXDSCW_NO_SNOOP: u32 = 0x00000002;
pub const GCR_RXDSCR_NO_SNOOP: u32 = 0x00000004;
pub const GCR_TXD_NO_SNOOP: u32 = 0x00000008;
pub const GCR_TXDSCW_NO_SNOOP: u32 = 0x00000010;
pub const GCR_TXDSCR_NO_SNOOP: u32 = 0x00000020;

pub const PCI_EX_NO_SNOOP_ALL: u32 = GCR_RXD_NO_SNOOP
    | GCR_RXDSCW_NO_SNOOP
    | GCR_RXDSCR_NO_SNOOP
    | GCR_TXD_NO_SNOOP
    | GCR_TXDSCW_NO_SNOOP
    | GCR_TXDSCR_NO_SNOOP;

pub const PCI_EX_82566_SNOOP_ALL: u32 = PCI_EX_NO_SNOOP_ALL;

// PCI-Ex Config Space
pub const PCI_EX_LINK_STATUS: u32 = 0x12;
pub const PCI_EX_LINK_WIDTH_MASK: u16 = 0x3F0;
pub const PCI_EX_LINK_WIDTH_SHIFT: u16 = 4;

pub const CTRL_FD: u32 = 0x00000001; // Full duplex.0=half; 1=full
pub const CTRL_LRST: u32 = 0x00000008; // Link reset. 0=normal,1=reset
pub const CTRL_ASDE: u32 = 0x00000020; // Auto-speed detect enable
pub const CTRL_SLU: u32 = 0x00000040; // Set link up (Force Link)
pub const CTRL_ILOS: u32 = 0x00000080; // Invert Loss-Of Signal
pub const CTRL_SPD_100: u32 = 0x00000100; // Force 100Mb
pub const CTRL_SPD_1000: u32 = 0x00000200; // Force 1Gb
pub const CTRL_SPD_SEL: u32 = 0x00000300; // Speed Select Mask
pub const CTRL_FRCSPD: u32 = 0x00000800; // Force Speed
pub const CTRL_FRCDPX: u32 = 0x00001000; // Force Duplex
pub const CTRL_RST: u32 = 1 << 26;
pub const CTRL_GIO_MASTER_DISABLE: u32 = 1 << 2;
pub const CTRL_I2C_ENA: u32 = 1 << 25;
pub const CTRL_PHY_RST: u32 = 1 << 31;
pub const CTRL_LANPHYPC_OVERRIDE: u32 = 0x00010000;
pub const CTRL_LANPHYPC_VALUE: u32 = 0x00020000;
pub const CTRL_RFCE: u32 = 0x08000000; // Receive Flow Control enable
pub const CTRL_TFCE: u32 = 0x10000000; // Transmit flow control enable

pub const CTRL_SWDPIN0: u32 = 0x00040000; // SWDPIN 0 value
pub const CTRL_SWDPIN1: u32 = 0x00080000; // SWDPIN 1 value
pub const CTRL_SWDPIN2: u32 = 0x00100000; // SWDPIN 2 value
pub const CTRL_SWDPIN3: u32 = 0x00200000; // SWDPIN 3 value
pub const CTRL_SWDPIO0: u32 = 0x00400000; // SWDPIN 0 Input or output
pub const CTRL_SWDPIO1: u32 = 0x00800000; // SWDPIN 1 input or output
pub const CTRL_SWDPIO2: u32 = 0x01000000; // SWDPIN 2 input or output
pub const CTRL_SWDPIO3: u32 = 0x02000000; // SWDPIN 3 input or output

pub const TCTL_CT: u32 = 0x0F << 4; // Collision Thresold

pub const TIPG_IPGT: u32 = 0x8;
pub const TIPG_IPGR1: u32 = 0x2 << 10;
pub const TIPG_IPGR2: u32 = 0xA << 20;

pub const TIPG_IPGT_MASK: u32 = 0x000003FF;
pub const TIPG_IPGR1_MASK: u32 = 0x000FFC00;
pub const TIPG_IPGR2_MASK: u32 = 0x3FF00000;

pub const DEFAULT_80003ES2LAN_TIPG_IPGT_10_100: u32 = 0x00000009;
pub const DEFAULT_80003ES2LAN_TIPG_IPGT_1000: u32 = 0x00000008;

pub const DEFAULT_80003ES2LAN_TCTL_EXT_GCEX: u32 = 0x00010000;

pub const RCTL_EN: u32 = 1 << 1; // Receive Control Register Enable
pub const RCTL_SBP: u32 = 1 << 2; // store bad packet
pub const RCTL_BAM: u32 = 1 << 15; // Broadcast Accept Mode
pub const RCTL_BSIZE: u32 = 11 << 16; // Receive Buffer Size (4096 Bytes)
pub const RCTL_BSEX: u32 = 1 << 25; // Buffer Size Extension
pub const RCTL_SECRC: u32 = 1 << 26; // Strip CRC from packet

// Transmit Configuration Word
pub const TXCW_FD: u32 = 0x00000020; // TXCW full duplex
pub const TXCW_HD: u32 = 0x00000040; // TXCW half duplex
pub const TXCW_PAUSE: u32 = 0x00000080; // TXCW sym pause request
pub const TXCW_ASM_DIR: u32 = 0x00000100; // TXCW astm pause direction
pub const TXCW_PAUSE_MASK: u32 = 0x00000180; // TXCW pause request mask
pub const TXCW_RF: u32 = 0x00003000; // TXCW remote fault
pub const TXCW_NP: u32 = 0x00008000; // TXCW next page
pub const TXCW_CW: u32 = 0x0000ffff; // TxConfigWord mask
pub const TXCW_TXC: u32 = 0x40000000; // Transmit Config control
pub const TXCW_ANE: u32 = 0x80000000; // Auto-neg enable

// Collision related configuration parameters
pub const COLLISION_THRESHOLD: u32 = 15;
pub const CT_SHIFT: u32 = 4;

// Collision distance is a 0-based value that applies to
// half-duplex-capable hardware only.
pub const COLLISION_DISTANCE: u32 = 63;
pub const COLLISION_DISTANCE_82542: u32 = 64;
pub const FDX_COLLISION_DISTANCE: u32 = COLLISION_DISTANCE;
pub const HDX_COLLISION_DISTANCE: u32 = COLLISION_DISTANCE;
pub const COLD_SHIFT: u32 = 12;

// FEXTNVM registers
pub const FEXTNVM7: usize = 0xe;
pub const _FEXTNVM7_SIDE_CLK_UNGATE: u32 = 0x04;
pub const FEXTNVM7_DISABLE_SMB_PERST: u32 = 0x00000020;
pub const _FEXTNVM9: usize = 0x5bb4;
pub const _FEXTNVM9_IOSFSB_CLKGATE_DIS: u32 = 0x0800;
pub const _FEXTNVM9_IOSFSB_CLKREQ_DIS: u32 = 0x1000;
pub const FEXTNVM11: usize = 0x05bbc;
pub const FEXTNVM11_DISABLE_MULR_FIX: u32 = 0x00002000;

pub const FEXTNVM_SW_CONFIG: u32 = 1;
pub const FEXTNVM_SW_CONFIG_ICH8M: u32 = 1 << 27; // Bit redefined for ICH8M :/

pub const _TXD_CMD_EOP: u8 = 1 << 0; // End of Packet
pub const TXD_CMD_IFCS: u8 = 1 << 1; // Insert FCS
pub const _TXD_CMD_TSE: u8 = 1 << 2; // TCP Segmentation Enable
pub const _TXD_CMD_RS: u8 = 1 << 3; // Report Status
pub const _TXD_CMD_RPS_RSV: u8 = 1 << 4; // Report Packet Sent
pub const _TXD_CMD_DEXT: u8 = 1 << 5; // Descriptor extension (0 = legacy)
pub const _TXD_CMD_VLE: u8 = 1 << 6; // VLAN Packet Enable
pub const _TXD_CMD_IDE: u8 = 1 << 7; // Interrupt Delay Enable

pub const PCICFG_DESC_RING_STATUS: usize = 0xe4;
pub const FLUSH_DESC_REQUIRED: u32 = 0x100;

// Extended Configuration Control and Size
pub const EXTCNF_CTRL: usize = 0x00F00;
pub const EXTCNF_SIZE: usize = 0x00F08; // Extended Configuration Size
pub const _EXTCNF_CTRL_PCIE_WRITE_ENABLE: u32 = 0x00000001;
pub const _EXTCNF_CTRL_PHY_WRITE_ENABLE: u32 = 0x00000002;
pub const _EXTCNF_CTRL_D_UD_ENABLE: u32 = 0x00000004;
pub const _EXTCNF_CTRL_D_UD_LATENCY: u32 = 0x00000008;
pub const _EXTCNF_CTRL_D_UD_OWNER: u32 = 0x00000010;
pub const EXTCNF_CTRL_MDIO_SW_OWNERSHIP: u32 = 0x00000020;
pub const _EXTCNF_CTRL_MDIO_HW_OWNERSHIP: u32 = 0x00000040;
pub const EXTCNF_CTRL_EXT_CNF_POINTER: u32 = 0x0FFF0000;
pub const _EXTCNF_SIZE_EXT_PHY_LENGTH: u32 = 0x000000FF;
pub const _EXTCNF_SIZE_EXT_DOCK_LENGTH: u32 = 0x0000FF00;
pub const EXTCNF_SIZE_EXT_PCIE_LENGTH: u32 = 0x00FF0000;
pub const EXTCNF_CTRL_LCD_WRITE_ENABLE: u32 = 0x00000001;
pub const EXTCNF_CTRL_SWFLAG: u32 = 0x00000020;
pub const EXTCNF_CTRL_GATE_PHY_CFG: u32 = 0x00000080;

pub const EXTCNF_CTRL_OEM_WRITE_ENABLE: u32 = 0x00000008;
pub const EXTCNF_SIZE_EXT_PCIE_LENGTH_MASK: u32 = 0x00FF0000;
pub const EXTCNF_SIZE_EXT_PCIE_LENGTH_SHIFT: u32 = 16;
pub const EXTCNF_CTRL_EXT_CNF_POINTER_MASK: u32 = 0x0FFF0000;
pub const EXTCNF_CTRL_EXT_CNF_POINTER_SHIFT: u32 = 16;

pub const DISABLE_SERDES_LOOPBACK: u32 = 0x0400;

// FW Semaphore
pub const FWSM: usize = 0x05B54;

pub const FWSM_MODE_MASK: u32 = 0x0000000E; // FW mode
pub const FWSM_MODE_SHIFT: u32 = 1;
pub const FWSM_ULP_CFG_DONE: u32 = 0x00000400; // Low power cfg done
pub const FWSM_FW_VALID: u32 = 0x00008000; // FW established a valid mode
pub const FWSM_RSPCIPHY: u32 = 0x00000040; // Reset PHY on PCI reset
pub const _FWSM_DISSW: u32 = 0x10000000; // FW disable SW Write Access
pub const _FWSM_SKUSEL_MASK: u32 = 0x60000000; // LAN SKU select
pub const _FWSM_SKUEL_SHIFT: u32 = 29;
pub const _FWSM_SKUSEL_EMB: u32 = 0x0; // Embedded SKU
pub const _FWSM_SKUSEL_CONS: u32 = 0x1; // Consumer SKU
pub const _FWSM_SKUSEL_PERF_100: u32 = 0x2; // Perf & Corp 10/100 SKU
pub const _FWSM_SKUSEL_PERF_GBE: u32 = 0x3; // Perf & Copr GbE SKU

pub const MNG_DHCP_COMMAND_TIMEOUT: u32 = 10; // Time in ms to process MNG command
pub const MNG_DHCP_COOKIE_OFFSET: u32 = 0x6F0; // Cookie offset
pub const MNG_DHCP_COOKIE_LENGTH: u32 = 0x10; // Cookie length
pub const MNG_IAMT_MODE: u32 = 0x3;
pub const MNG_ICH_IAMT_MODE: u32 = 0x2;
pub const IAMT_SIGNATURE: u32 = 0x544D4149; // Intel(R) Active Management Technology signature

pub const MNG_DHCP_COOKIE_STATUS_PARSING_SUPPORT: u8 = 0x1; // DHCP parsing enabled

// Management Control
pub const MANC: usize = 0x05820;

pub const _MANC_SMBUS_EN: u32 = 0x00000001; // SMBus Enabled - RO
pub const _MANC_ASF_EN: u32 = 0x00000002; // ASF Enabled - RO
pub const _MANC_R_ON_FORCE: u32 = 0x00000004; // Reset on Force TCO - RO
pub const _MANC_RMCP_EN: u32 = 0x00000100; // Enable RCMP 026Fh Filtering
pub const _MANC_0298_EN: u32 = 0x00000200; // Enable RCMP 0298h Filtering
pub const _MANC_IPV4_EN: u32 = 0x00000400; // Enable IPv4
pub const _MANC_IPV6_EN: u32 = 0x00000800; // Enable IPv6
pub const _MANC_SNAP_EN: u32 = 0x00001000; // Accept LLC/SNAP
pub const MANC_ARP_EN: u32 = 0x00002000; // Enable ARP Request Filtering
pub const _MANC_NEIGHBOR_EN: u32 = 0x00004000; // Enable Neighbor Discovery Filtering
pub const _MANC_ARP_RES_EN: u32 = 0x00008000; // Enable ARP response Filtering
pub const _MANC_TCO_RESET: u32 = 0x00010000; // TCO Reset Occurred
pub const _MANC_RCV_TCO_EN: u32 = 0x00020000; // Receive TCO Packets Enabled
pub const _MANC_REPORT_STATUS: u32 = 0x00040000; // Status Reporting Enabled
pub const _MANC_RCV_ALL: u32 = 0x00080000; // Receive All Enabled
pub const MANC_BLK_PHY_RST_ON_IDE: u32 = 0x00040000; // Block phy resets
pub const _MANC_EN_MAC_ADDR_FILTER: u32 = 0x00100000; // Enable MAC address filtering
pub const _MANC_EN_MNG2HOST: u32 = 0x00200000; // Enable MNG packets to host memory
pub const _MANC_EN_IP_ADDR_FILTER: u32 = 0x00400000; // Enable IP address filtering
pub const _MANC_EN_XSUM_FILTER: u32 = 0x00800000; // Enable checksum filtering
pub const _MANC_BR_EN: u32 = 0x01000000; // Enable broadcast filtering
pub const _MANC_SMB_REQ: u32 = 0x01000000; // SMBus Request
pub const _MANC_SMB_GNT: u32 = 0x02000000; // SMBus Grant
pub const _MANC_SMB_CLK_IN: u32 = 0x04000000; // SMBus Clock In
pub const _MANC_SMB_DATA_IN: u32 = 0x08000000; // SMBus Data In
pub const _MANC_SMB_DATA_OUT: u32 = 0x10000000; // SMBus Data Out
pub const _MANC_SMB_CLK_OUT: u32 = 0x20000000; // SMBus Clock Out

pub const _MANC_SMB_DATA_OUT_SHIFT: u32 = 28; // SMBus Data Out Shift
pub const _MANC_SMB_CLK_OUT_SHIFT: u32 = 29; // SMBus Clock Out Shift

// SW Semaphore Register
pub const SWSM: usize = 0x05B50;
pub const SWSM_SMBI: u32 = 0x00000001; // Driver Semaphore bit
pub const SWSM_SWESMBI: u32 = 0x00000002; // FW Semaphore bit
pub const _SWSM_WMNG: u32 = 0x00000004; // Wake MNG Clock
pub const _SWSM_DRV_LOAD: u32 = 0x00000008; // Driver Loaded Bit

// Extended Device Control
pub const CTRL_EXT: usize = 0x00018;
pub const _CTRL_EXT_GPI0_EN: u32 = 0x00000001; // Maps SDP4 to GPI0
pub const _CTRL_EXT_GPI1_EN: u32 = 0x00000002; // Maps SDP5 to GPI1
pub const _CTRL_EXT_PHYINT_EN: u32 = _CTRL_EXT_GPI1_EN;
pub const _CTRL_EXT_GPI2_EN: u32 = 0x00000004; // Maps SDP6 to GPI2
pub const CTRL_EXT_LPCD: u32 = 0x00000004; // LCD Power Cycle Done
pub const _CTRL_EXT_GPI3_EN: u32 = 0x00000008; // Maps SDP7 to GPI3
pub const CTRL_EXT_SDP4_DATA: u32 = 0x00000010; // Value of SW Defineable Pin 4
pub const _CTRL_EXT_SDP5_DATA: u32 = 0x00000020; // Value of SW Defineable Pin 5
pub const _CTRL_EXT_PHY_INT: u32 = _CTRL_EXT_SDP5_DATA;
pub const _CTRL_EXT_SDP6_DATA: u32 = 0x00000040; // Value of SW Defineable Pin 6
pub const _CTRL_EXT_SDP7_DATA: u32 = 0x00000080; // Value of SW Defineable Pin 7
pub const CTRL_EXT_SDP3_DATA: u32 = 0x00000080; // Value of SW Defineable Pin 3
pub const CTRL_EXT_SDP4_DIR: u32 = 0x00000100; // Direction of SDP4 0=in 1=out
pub const _CTRL_EXT_SDP5_DIR: u32 = 0x00000200; // Direction of SDP5 0=in 1=out
pub const _CTRL_EXT_SDP6_DIR: u32 = 0x00000400; // Direction of SDP6 0=in 1=out
pub const _CTRL_EXT_SDP7_DIR: u32 = 0x00000800; // Direction of SDP7 0=in 1=out
pub const _CTRL_EXT_ASDCHK: u32 = 0x00001000; // Initiate an ASD sequence
pub const CTRL_EXT_EE_RST: u32 = 0x00002000; // Reinitialize from EEPROM
pub const _CTRL_EXT_IPS: u32 = 0x00004000; // Invert Power State
pub const CTRL_EXT_SPD_BYPS: u32 = 0x00008000; // Speed Select Bypass
pub const CTRL_EXT_RO_DIS: u32 = 0x00020000; // Relaxed Ordering disable
pub const CTRL_EXT_LINK_MODE_MASK: u32 = 0x00C00000;
pub const _CTRL_EXT_LINK_MODE_GMII: u32 = 0x00000000;
pub const _CTRL_EXT_LINK_MODE_TBI: u32 = 0x00C00000;
pub const _CTRL_EXT_LINK_MODE_KMRN: u32 = 0x00000000;
pub const CTRL_EXT_LINK_MODE_PCIE_SERDES: u32 = 0x00C00000;
pub const CTRL_EXT_LINK_MODE_1000BASE_KX: u32 = 0x00400000;
pub const CTRL_EXT_LINK_MODE_SGMII: u32 = 0x00800000;
pub const _CTRL_EXT_WR_WMARK_MASK: u32 = 0x03000000;
pub const _CTRL_EXT_WR_WMARK_256: u32 = 0x00000000;
pub const _CTRL_EXT_WR_WMARK_320: u32 = 0x01000000;
pub const _CTRL_EXT_WR_WMARK_384: u32 = 0x02000000;
pub const _CTRL_EXT_WR_WMARK_448: u32 = 0x03000000;
pub const _CTRL_EXT_EXT_VLAN: u32 = 0x04000000;
pub const _CTRL_EXT_DRV_LOAD: u32 = 0x10000000; // Driver loaded bit for FW
pub const _CTRL_EXT_IAME: u32 = 0x08000000; // Interrupt acknowledge Auto-mask
pub const _CTRL_EXT_INT_TIMER_CLR: u32 = 0x20000000; // Clear Interrupt timers after IMS clear
pub const _CRTL_EXT_PB_PAREN: u32 = 0x01000000; // packet buffer parity error detection enabled
pub const _CTRL_EXT_DF_PAREN: u32 = 0x02000000; // descriptor FIFO parity error detection enable
pub const CTRL_EXT_FORCE_SMBUS: u32 = 0x00000800; // Force SMBus mode

pub const MDICNFG: usize = 0x00E04;
pub const MDICNFG_EXT_MDIO: u32 = 0x80000000; // MDI ext/int destination
pub const MDICNFG_COM_MDIO: u32 = 0x40000000; // MDI shared w/ lan 0
pub const MDICNFG_PHY_MASK: u32 = 0x03E00000;
pub const MDICNFG_PHY_SHIFT: u32 = 21;

// SFPI2C Command Register - RW
pub const I2CCMD: usize = 0x01028;
pub const I2CCMD_REG_ADDR_SHIFT: usize = 16;
pub const I2CCMD_PHY_ADDR_SHIFT: usize = 24;
pub const I2CCMD_OPCODE_READ: u32 = 0x08000000;
pub const I2CCMD_OPCODE_WRITE: u32 = 0x00000000;
pub const I2CCMD_READY: u32 = 0x20000000;
pub const I2CCMD_ERROR: u32 = 0x80000000;
pub const I2CCMD_PHY_TIMEOUT: u32 = 200;
pub const MAX_SGMII_PHY_REG_ADDR: u32 = 255;

// SFP modules ID memory locations
pub const SFF_IDENTIFIER_OFFSET: u32 = 0x00;
pub const SFF_IDENTIFIER_SFF: u8 = 0x02;
pub const SFF_IDENTIFIER_SFP: u8 = 0x03;
pub const SFF_ETH_FLAGS_OFFSET: u32 = 0x06;

// MDI Control
pub const MDIC: usize = 0x00020;
pub const _MDIC_DATA_MASK: u32 = 0x0000FFFF;
pub const _MDIC_REG_MASK: u32 = 0x001F0000;
pub const MDIC_REG_SHIFT: u32 = 16;
pub const _MDIC_PHY_MASK: u32 = 0x03E00000;
pub const MDIC_PHY_SHIFT: u32 = 21;
pub const MDIC_OP_WRITE: u32 = 0x04000000;
pub const MDIC_OP_READ: u32 = 0x08000000;
pub const MDIC_READY: u32 = 0x10000000;
pub const _MDIC_INT_EN: u32 = 0x20000000;
pub const MDIC_ERROR: u32 = 0x40000000;
pub const MDIC_DEST: u32 = 0x80000000;

// 1000BASE-T Status Register
pub const SR_1000T_IDLE_ERROR_CNT: u16 = 0x00FF; // Num idle errors since last read
pub const SR_1000T_ASYM_PAUSE_DIR: u16 = 0x0100; // LP asymmetric pause direction bit
pub const SR_1000T_LP_HD_CAPS: u16 = 0x0400; // LP is 1000T HD capable
pub const SR_1000T_LP_FD_CAPS: u16 = 0x0800; // LP is 1000T FD capable
pub const SR_1000T_REMOTE_RX_STATUS: u16 = 0x1000; // Remote receiver OK
pub const SR_1000T_LOCAL_RX_STATUS: u16 = 0x2000; // Local receiver OK
pub const SR_1000T_MS_CONFIG_RES: u16 = 0x4000; // 1=Local TX is Master, 0=Slave
pub const SR_1000T_MS_CONFIG_FAULT: u16 = 0x8000; // Master/Slave config fault
pub const SR_1000T_REMOTE_RX_STATUS_SHIFT: u16 = 12;
pub const SR_1000T_LOCAL_RX_STATUS_SHIFT: u16 = 13;
pub const SR_1000T_PHY_EXCESSIVE_IDLE_ERR_COUNT: u16 = 5;
pub const FFE_IDLE_ERR_COUNT_TIMEOUT_20: usize = 20;
pub const FFE_IDLE_ERR_COUNT_TIMEOUT_100: usize = 100;

// PHY 1000 MII Register/Bit Definitions
// PHY Registers defined by IEEE
pub const PHY_CTRL: u32 = 0x00; // Control Register
pub const PHY_STATUS: u32 = 0x01; // Status Register
pub const PHY_ID1: u32 = 0x02; // Phy Id Reg (word 1)
pub const PHY_ID2: u32 = 0x03; // Phy Id Reg (word 2)
pub const PHY_AUTONEG_ADV: u32 = 0x04; // Autoneg Advertisement
pub const PHY_LP_ABILITY: u32 = 0x05; // Link Partner Ability (Base Page)
pub const PHY_AUTONEG_EXP: u32 = 0x06; // Autoneg Expansion Reg
pub const PHY_NEXT_PAGE_TX: u32 = 0x07; // Next Page TX
pub const PHY_LP_NEXT_PAGE: u32 = 0x08; // Link Partner Next Page
pub const PHY_1000T_CTRL: u32 = 0x09; // 1000Base-T Control Reg
pub const PHY_1000T_STATUS: u32 = 0x0A; // 1000Base-T Status Reg
pub const PHY_EXT_STATUS: u32 = 0x0F; // Extended Status Reg

pub const PHY_CTRL_SPD_EN: u32 = 0x00000001;
pub const PHY_CTRL_D0A_LPLU: u32 = 0x00000002;
pub const PHY_CTRL_NOND0A_LPLU: u32 = 0x00000004;
pub const PHY_CTRL_NOND0A_GBE_DISABLE: u32 = 0x00000008;
pub const PHY_CTRL_GBE_DISABLE: u32 = 0x00000040;
pub const PHY_CTRL_B2B_EN: u32 = 0x00000080;
pub const PHY_CTRL_LOOPBACK: u16 = 0x00004000;

// PBA constants
pub const PBA_8K: u32 = 0x0008; // 8KB, default Rx allocation
pub const _PBA_10K: u32 = 0x000A;
pub const _PBA_12K: u32 = 0x000C; // 12KB, default Rx allocation
pub const _PBA_14K: u32 = 0x000E; // 14KB
pub const PBA_16K: u32 = 0x0010; // 16KB, default TX allocation
pub const _PBA_20K: u32 = 0x0014;
pub const _PBA_22K: u32 = 0x0016;
pub const _PBA_24K: u32 = 0x0018;
pub const _PBA_26K: u32 = 0x001A;
pub const _PBA_30K: u32 = 0x001E;
pub const _PBA_32K: u32 = 0x0020;
pub const _PBA_34K: u32 = 0x0022;
pub const _PBA_38K: u32 = 0x0026;
pub const _PBA_40K: u32 = 0x0028;
pub const _PBA_48K: u32 = 0x0030; // 48KB, default RX allocation

pub const PBS_16K: u32 = PBA_16K;

pub const SW_FLAG_TIMEOUT: usize = 100;

pub const MAX_PHY_REG_ADDRESS: u32 = 0x1F; // 5 bit address bus (0-0x1F)
pub const MAX_PHY_MULTI_PAGE_REG: u32 = 0xF; // Registers equal on all pages

// IGP01E1000 Specific Registers
pub const IGP01E1000_PHY_PORT_CONFIG: u32 = 0x10; // PHY Specific Port Config Register
pub const _IGP01E1000_PHY_PORT_STATUS: u32 = 0x11; // PHY Specific Status Register
pub const IGP01E1000_PHY_PORT_CTRL: u32 = 0x12; // PHY Specific Control Register
pub const IGP01E1000_PHY_LINK_HEALTH: u32 = 0x13; // PHY Link Health Register
pub const IGP01E1000_GMII_FIFO: u32 = 0x14; // GMII FIFO Register
pub const _IGP01E1000_PHY_CHANNEL_QUALITY: u32 = 0x15; // PHY Channel Quality Register
pub const IGP02E1000_PHY_POWER_MGMT: u32 = 0x19;
pub const IGP01E1000_PHY_PAGE_SELECT: u32 = 0x1F; // PHY Page Select Core Register

pub const IGP01E1000_PLHR_SS_DOWNGRADE: u16 = 0x8000;

// IGP01E1000 Specific Port Control Register - R/W
pub const IGP01E1000_PSCR_TP_LOOPBACK: u16 = 0x0010;
pub const IGP01E1000_PSCR_CORRECT_NC_SCMBLR: u16 = 0x0200;
pub const IGP01E1000_PSCR_TEN_CRS_SELECT: u16 = 0x0400;
pub const IGP01E1000_PSCR_FLIP_CHIP: u16 = 0x0800;
pub const IGP01E1000_PSCR_AUTO_MDIX: u16 = 0x1000;
pub const IGP01E1000_PSCR_FORCE_MDI_MDIX: u16 = 0x2000; // 0-MDI, 1-MDIX

// IGP01E1000 Specific Port Config Register - R/W
pub const IGP01E1000_PSCFR_AUTO_MDIX_PAR_DETECT: u16 = 0x0010;
pub const IGP01E1000_PSCFR_PRE_EN: u16 = 0x0020;
pub const IGP01E1000_PSCFR_SMART_SPEED: u16 = 0x0080;
pub const IGP01E1000_PSCFR_DISABLE_TPLOOPBACK: u16 = 0x0100;
pub const IGP01E1000_PSCFR_DISABLE_JABBER: u16 = 0x0400;
pub const IGP01E1000_PSCFR_DISABLE_TRANSMIT: u16 = 0x2000;

// IGP01E1000 GMII FIFO Register
pub const IGP01E1000_GMII_FLEX_SPD: u16 = 0x10; // Enable flexible speed on Link-Up
pub const IGP01E1000_GMII_SPD: u16 = 0x20; // Enable SPD

pub const IGP02E1000_PM_SPD: u16 = 0x0001; // Smart Power Down
pub const IGP02E1000_PM_D3_LPLU: u16 = 0x0004; // Enable LPLU in non-D0a modes
pub const IGP02E1000_PM_D0_LPLU: u16 = 0x0002; // Enable LPLU in D0a mode

pub const IGP01E1000_PHY_CHANNEL_NUM: usize = 4;
pub const IGP02E1000_PHY_CHANNEL_NUM: usize = 4;

pub const IGP01E1000_PHY_EDAC_MU_INDEX: u16 = 0xC000;
pub const IGP01E1000_PHY_EDAC_SIGN_EXT_9_BITS: u16 = 0x8000;

pub const IGP01E1000_PHY_AGC_PARAM_A: u32 = 0x1171;
pub const IGP01E1000_PHY_AGC_PARAM_B: u32 = 0x1271;
pub const IGP01E1000_PHY_AGC_PARAM_C: u32 = 0x1471;
pub const IGP01E1000_PHY_AGC_PARAM_D: u32 = 0x1871;

// IGP01E1000 AGC Registers - stores the cable length values
pub const IGP01E1000_PHY_AGC_A: u32 = 0x1172;
pub const IGP01E1000_PHY_AGC_B: u32 = 0x1272;
pub const IGP01E1000_PHY_AGC_C: u32 = 0x1472;
pub const IGP01E1000_PHY_AGC_D: u32 = 0x1872;

// IGP02E1000 AGC Registers for cable length values
pub const IGP02E1000_PHY_AGC_A: u32 = 0x11B1;
pub const IGP02E1000_PHY_AGC_B: u32 = 0x12B1;
pub const IGP02E1000_PHY_AGC_C: u32 = 0x14B1;
pub const IGP02E1000_PHY_AGC_D: u32 = 0x18B1;

// IGP01E1000 DSP Reset Register
pub const IGP01E1000_PHY_DSP_RESET: u32 = 0x1F33;
pub const IGP01E1000_PHY_DSP_SET: u32 = 0x1F71;
pub const IGP01E1000_PHY_DSP_FFE: u32 = 0x1F35;

pub const IGP01E1000_PHY_DSP_FFE_CM_CP: u16 = 0x0069;

pub const IGP01E1000_PHY_DSP_FFE_DEFAULT: u16 = 0x002A;

pub const IGP01E1000_IEEE_RESTART_AUTONEG: u16 = 0x3300;
pub const IGP01E1000_IEEE_FORCE_GIGA: u16 = 0x0140;

pub const IGP01E1000_AGC_LENGTH_TABLE_SIZE: u16 = 128;
pub const IGP02E1000_AGC_LENGTH_TABLE_SIZE: u16 = 113;

pub const IGP01E1000_AGC_LENGTH_SHIFT: u16 = 7; // Coarse - 13:11, Fine - 10:7
pub const IGP02E1000_AGC_LENGTH_SHIFT: u16 = 9; // Coarse - 15:13, Fine - 12:9

// IGP02E1000 AGC Register Length 9-bit mask
pub const IGP02E1000_AGC_LENGTH_MASK: u16 = 0x7F;

// The precision error of the cable length is +/- 10 meters
pub const IGP01E1000_AGC_RANGE: u16 = 10;
pub const IGP02E1000_AGC_RANGE: u16 = 15;

// IGP cable length table
pub const IGP_CABLE_LENGTH_TABLE: [u16; IGP01E1000_AGC_LENGTH_TABLE_SIZE as usize] = [
    5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 10, 10, 10, 10, 10, 10, 10, 20, 20, 20, 20,
    20, 25, 25, 25, 25, 25, 25, 25, 30, 30, 30, 30, 40, 40, 40, 40, 40, 40, 40, 40, 40, 50, 50, 50,
    50, 50, 50, 50, 60, 60, 60, 60, 60, 60, 60, 60, 60, 70, 70, 70, 70, 70, 70, 80, 80, 80, 80, 80,
    80, 90, 90, 90, 90, 90, 90, 90, 90, 90, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100, 100,
    100, 100, 100, 110, 110, 110, 110, 110, 110, 110, 110, 110, 110, 110, 110, 110, 110, 110, 110,
    110, 110, 120, 120, 120, 120, 120, 120, 120, 120, 120, 120,
];

pub const IGP_2_CABLE_LENGTH_TABLE: [u16; IGP02E1000_AGC_LENGTH_TABLE_SIZE as usize] = [
    0, 0, 0, 0, 0, 0, 0, 0, 3, 5, 8, 11, 13, 16, 18, 21, 0, 0, 0, 3, 6, 10, 13, 16, 19, 23, 26, 29,
    32, 35, 38, 41, 6, 10, 14, 18, 22, 26, 30, 33, 37, 41, 44, 48, 51, 54, 58, 61, 21, 26, 31, 35,
    40, 44, 49, 53, 57, 61, 65, 68, 72, 75, 79, 82, 40, 45, 51, 56, 61, 66, 70, 75, 79, 83, 87, 91,
    94, 98, 101, 104, 60, 66, 72, 77, 82, 87, 92, 96, 100, 104, 108, 111, 114, 117, 119, 121, 83,
    89, 95, 100, 105, 109, 113, 116, 119, 122, 124, 104, 109, 114, 118, 121, 124,
];

// BM/HV Specific Registers
pub const BM_PORT_CTRL_PAGE: u32 = 769;
pub const _BM_PCIE_PAGE: u16 = 770;
pub const BM_WUC_PAGE: u16 = 800;
pub const BM_WUC_ADDRESS_OPCODE: u32 = 0x11;
pub const BM_WUC_DATA_OPCODE: u32 = 0x12;
pub const BM_WUC_ENABLE_PAGE: u16 = BM_PORT_CTRL_PAGE as u16;
pub const BM_WUC_ENABLE_REG: u32 = 17;
pub const BM_WUC_ENABLE_BIT: u16 = 1 << 2;
pub const BM_WUC_HOST_WU_BIT: u16 = 1 << 4;

// BM PHY Copper Specific Status
pub const BM_CS_STATUS: u32 = 17;
pub const BM_CS_STATUS_ENERGY_DETECT: u16 = 0x0010; // Energy Detect Status
pub const BM_CS_STATUS_LINK_UP: u16 = 0x0400;
pub const BM_CS_STATUS_RESOLVED: u16 = 0x0800;
pub const BM_CS_STATUS_SPEED_MASK: u16 = 0xC000;
pub const BM_CS_STATUS_SPEED_1000: u16 = 0x8000;

pub const PHY_PAGE_SHIFT: u32 = 5;
pub const PHY_UPPER_SHIFT: u32 = 21;

// SW_W_SYNC definitions
pub const SWFW_EEP_SM: u16 = 0x0001;
pub const SWFW_PHY0_SM: u16 = 0x0002;
pub const SWFW_PHY1_SM: u16 = 0x0004;
pub const _SWFW_MAC_CSR_SM: u16 = 0x0008;
pub const SWFW_PHY2_SM: u16 = 0x0020;
pub const SWFW_PHY3_SM: u16 = 0x0040;

// Hanksville definitions
pub const HV_INTC_FC_PAGE_START: u16 = 768;

pub const HV_SCC_UPPER: u32 = phy_reg(778, 16); // Single Collision Count
pub const HV_SCC_LOWER: u32 = phy_reg(778, 17);
pub const HV_ECOL_UPPER: u32 = phy_reg(778, 18); // Excessive Collision Count
pub const HV_ECOL_LOWER: u32 = phy_reg(778, 19);
pub const HV_MCC_UPPER: u32 = phy_reg(778, 20); // Multiple Collision Count
pub const HV_MCC_LOWER: u32 = phy_reg(778, 21);
pub const HV_LATECOL_UPPER: u32 = phy_reg(778, 23); // Late Collision Count
pub const HV_LATECOL_LOWER: u32 = phy_reg(778, 24);
pub const HV_COLC_UPPER: u32 = phy_reg(778, 25); // Collision Count
pub const HV_COLC_LOWER: u32 = phy_reg(778, 26);
pub const HV_DC_UPPER: u32 = phy_reg(778, 27); // Defer Count
pub const HV_DC_LOWER: u32 = phy_reg(778, 28);
pub const HV_TNCRS_UPPER: u32 = phy_reg(778, 29); // Transmit with no CRS
pub const HV_TNCRS_LOWER: u32 = phy_reg(778, 30);

// 82577 Mobile Phy Status Register
pub const HV_M_STATUS: u32 = 26;
pub const HV_M_STATUS_AUTONEG_COMPLETE: u16 = 0x1000;
pub const HV_M_STATUS_SPEED_MASK: u16 = 0x0300;
pub const HV_M_STATUS_SPEED_1000: u16 = 0x0200;
pub const HV_M_STATUS_LINK_UP: u16 = 0x0040;

// OEM Bits Phy Register
pub const HV_OEM_BITS: u32 = phy_reg(768, 25);
pub const HV_OEM_BITS_LPLU: u16 = 0x0004; // Low Power Link Up
pub const HV_OEM_BITS_GBE_DIS: u16 = 0x0040; // Gigabit Disable
pub const HV_OEM_BITS_RESTART_AN: u16 = 0x0400; // Restart Auto-negotiation

pub const HV_MUX_DATA_CTRL: u32 = phy_reg(776, 16);
pub const HV_MUX_DATA_CTRL_GEN_TO_MAC: u16 = 0x0400;
pub const HV_MUX_DATA_CTRL_FORCE_SPEED: u16 = 0x0004;

// 1000BASE-T Control Register
pub const CR_1000T_ASYM_PAUSE: u16 = 0x0080; // Advertise asymmetric pause bit
pub const CR_1000T_HD_CAPS: u16 = 0x0100; // Advertise 1000T HD capability
pub const CR_1000T_FD_CAPS: u16 = 0x0200; // Advertise 1000T FD capability
pub const CR_1000T_REPEATER_DTE: u16 = 0x0400; // 1=Repeater/switch device port, 0=DTE device
pub const CR_1000T_MS_VALUE: u16 = 0x0800; // 1=Configure PHY as Master, 0=Configure PHY as Slave
pub const CR_1000T_MS_ENABLE: u16 = 0x1000; // 1=Master/Slave manual config value, 0=Automatic Master/Slave config
pub const CR_1000T_TEST_MODE_NORMAL: u16 = 0x0000; // Normal Operation
pub const CR_1000T_TEST_MODE_1: u16 = 0x2000; // Transmit Waveform test
pub const CR_1000T_TEST_MODE_2: u16 = 0x4000; // Master Transmit Jitter test
pub const CR_1000T_TEST_MODE_3: u16 = 0x6000; // Slave Transmit Jitter test
pub const CR_1000T_TEST_MODE_4: u16 = 0x8000; // Transmitter Distortion test

// I82578 Specific Registers
pub const I82578_PHY_ADDR_REG: u32 = 29;

// Bit definitions for valid PHY IDs.
// I = Integrated
// E = External
pub const M88_VENDOR: u32 = 0x0141;
pub const M88E1000_E_PHY_ID: u32 = 0x01410C50;
pub const M88E1000_I_PHY_ID: u32 = 0x01410C30;
pub const M88E1011_I_PHY_ID: u32 = 0x01410C20;
pub const IGP01E1000_I_PHY_ID: u32 = 0x02A80380;
pub const M88E1000_12_PHY_ID: u32 = M88E1000_E_PHY_ID;
pub const M88E1000_14_PHY_ID: u32 = M88E1000_E_PHY_ID;
pub const M88E1011_I_REV_4: u32 = 0x04;
pub const M88E1111_I_PHY_ID: u32 = 0x01410CC0;
pub const M88E1112_E_PHY_ID: u32 = 0x01410C90;
pub const I347AT4_E_PHY_ID: u32 = 0x01410DC0;
pub const L1LXT971A_PHY_ID: u32 = 0x001378E0;
pub const GG82563_E_PHY_ID: u32 = 0x01410CA0;
pub const BME1000_E_PHY_ID: u32 = 0x01410CB0;
pub const BME1000_E_PHY_ID_R2: u32 = 0x01410CB1;
pub const M88E1543_E_PHY_ID: u32 = 0x01410EA0;
pub const I82577_E_PHY_ID: u32 = 0x01540050;
pub const I82578_E_PHY_ID: u32 = 0x004DD040;
pub const I82579_E_PHY_ID: u32 = 0x01540090;
pub const I217_E_PHY_ID: u32 = 0x015400A0;
pub const I82580_I_PHY_ID: u32 = 0x015403A0;
pub const I350_I_PHY_ID: u32 = 0x015403B0;
pub const I210_I_PHY_ID: u32 = 0x01410C00;
pub const IGP04E1000_E_PHY_ID: u32 = 0x02A80391;
pub const M88E1141_E_PHY_ID: u32 = 0x01410CD0;
pub const M88E1512_E_PHY_ID: u32 = 0x01410DD0;

pub const M88E1543_PAGE_ADDR: u32 = 0x16;

pub const M88E1512_CFG_REG_1: u32 = 0x0010;
pub const M88E1512_CFG_REG_2: u32 = 0x0011;
pub const M88E1512_CFG_REG_3: u32 = 0x0007;
pub const M88E1512_MODE: u32 = 0x0014;

// M88E1000 Specific Registers
pub const M88E1000_PHY_SPEC_CTRL: u32 = 0x10; // PHY Specific Control Register
pub const M88E1000_PHY_SPEC_STATUS: u32 = 0x11; // PHY Specific Status Register
pub const M88E1000_INT_ENABLE: u32 = 0x12; // Interrupt Enable Register
pub const M88E1000_INT_STATUS: u32 = 0x13; // Interrupt Status Register
pub const M88E1000_EXT_PHY_SPEC_CTRL: u32 = 0x14; // Extended PHY Specific Control
pub const M88E1000_RX_ERR_CNTR: u32 = 0x15; // Receive Error Counter

// M88E1000 PHY Specific Control Register
pub const M88E1000_PSCR_JABBER_DISABLE: u16 = 0x0001; // 1=Jabber Function disabled
pub const M88E1000_PSCR_POLARITY_REVERSAL: u16 = 0x0002; // 1=Polarity Reversal enabled
pub const M88E1000_PSCR_SQE_TEST: u16 = 0x0004; // 1=SQE Test enabled
pub const M88E1000_PSCR_CLK125_DISABLE: u16 = 0x0010; // 1=CLK125 low, 0=CLK125 toggling

pub const M88E1000_PSCR_MDI_MANUAL_MODE: u16 = 0x0000; // MDI Crossover Mode bits 6:5, Manual MDI configuration
pub const M88E1000_PSCR_MDIX_MANUAL_MODE: u16 = 0x0020; // Manual MDIX configuration
pub const M88E1000_PSCR_AUTO_X_1000T: u16 = 0x0040; // 1000BASE-T: Auto crossover, 100BASE-TX/10BASE-T: MDI Mode
pub const M88E1000_PSCR_AUTO_X_MODE: u16 = 0x0060; // Auto crossover enabled all speeds.
pub const M88E1000_PSCR_10BT_EXT_DIST_ENABLE: u16 = 0x0080; // 1=Enable Extended 10BASE-T distance (Lower 10BASE-T RX Threshold), 0=Normal 10BASE-T RX Threshold
pub const M88E1000_PSCR_MII_5BIT_ENABLE: u16 = 0x0100; // 1=5-Bit interface in 100BASE-TX, 0=MII interface in 100BASE-TX
pub const M88E1000_PSCR_SCRAMBLER_DISABLE: u16 = 0x0200; // 1=Scrambler disable
pub const M88E1000_PSCR_FORCE_LINK_GOOD: u16 = 0x0400; // 1=Force link good
pub const M88E1000_PSCR_ASSERT_CRS_ON_TX: u16 = 0x0800; // 1=Assert CRS on Transmit

// M88E1000 PHY Specific Status Register
pub const M88E1000_PSSR_JABBER: u16 = 0x0001; // 1=Jabber
pub const M88E1000_PSSR_REV_POLARITY: u16 = 0x0002; // 1=Polarity reversed
pub const M88E1000_PSSR_DOWNSHIFT: u16 = 0x0020; // 1=Downshifted
pub const M88E1000_PSSR_MDIX: u16 = 0x0040; // 1=MDIX; 0=MDI
pub const M88E1000_PSSR_CABLE_LENGTH: u16 = 0x0380; // 0=<50M;1=50-80M;2=80-110M; 3=110-140M;4=>140M
pub const M88E1000_PSSR_LINK: u16 = 0x0400; // 1=Link up, 0=Link down
pub const M88E1000_PSSR_SPD_DPLX_RESOLVED: u16 = 0x0800; // 1=Speed & Duplex resolved
pub const M88E1000_PSSR_PAGE_RCVD: u16 = 0x1000; // 1=Page received
pub const M88E1000_PSSR_DPLX: u16 = 0x2000; // 1=Duplex 0=Half Duplex
pub const M88E1000_PSSR_SPEED: u16 = 0xC000; // Speed, bits 14:15
pub const M88E1000_PSSR_10MBS: u16 = 0x0000; // 00=10Mbs
pub const M88E1000_PSSR_100MBS: u16 = 0x4000; // 01=100Mbs
pub const M88E1000_PSSR_1000MBS: u16 = 0x8000; // 10=1000Mbs

pub const M88E1000_PSSR_REV_POLARITY_SHIFT: u16 = 1;
pub const M88E1000_PSSR_DOWNSHIFT_SHIFT: u16 = 5;
pub const M88E1000_PSSR_MDIX_SHIFT: u16 = 6;
pub const M88E1000_PSSR_CABLE_LENGTH_SHIFT: u16 = 7;

// M88E1141 specific
pub const M88E1000_EPSCR_TX_TIME_CTRL: u16 = 0x0002; // Add Delay
pub const M88E1000_EPSCR_RX_TIME_CTRL: u16 = 0x0080; // Add Delay

// Number of times we will attempt to autonegotiate before downshifting if we
// are the master
pub const M88E1000_EPSCR_MASTER_DOWNSHIFT_MASK: u16 = 0x0C00;
pub const M88E1000_EPSCR_MASTER_DOWNSHIFT_1X: u16 = 0x0000;
pub const M88E1000_EPSCR_MASTER_DOWNSHIFT_2X: u16 = 0x0400;
pub const M88E1000_EPSCR_MASTER_DOWNSHIFT_3X: u16 = 0x0800;
pub const M88E1000_EPSCR_MASTER_DOWNSHIFT_4X: u16 = 0x0C00;

// Number of times we will attempt to autonegotiate before downshifting if we
// are the slave
pub const M88E1000_EPSCR_SLAVE_DOWNSHIFT_MASK: u16 = 0x0300;
pub const M88E1000_EPSCR_SLAVE_DOWNSHIFT_DIS: u16 = 0x0000;
pub const M88E1000_EPSCR_SLAVE_DOWNSHIFT_1X: u16 = 0x0100;
pub const M88E1000_EPSCR_SLAVE_DOWNSHIFT_2X: u16 = 0x0200;
pub const M88E1000_EPSCR_SLAVE_DOWNSHIFT_3X: u16 = 0x0300;
pub const M88E1000_EPSCR_TX_CLK_2_5: u16 = 0x0060; // 2.5 MHz TX_CLK
pub const M88E1000_EPSCR_TX_CLK_25: u16 = 0x0070; // 25  MHz TX_CLK
pub const M88E1000_EPSCR_TX_CLK_0: u16 = 0x0000; // NO  TX_CLK

pub const M88E1000_PHY_EXT_CTRL: u32 = 0x1A; // PHY extend control register
pub const M88E1000_PHY_PAGE_SELECT: u32 = 0x1D; // Reg 29 for page number setting
pub const M88E1000_PHY_GEN_CONTROL: u32 = 0x1E; // Its meaning depends on reg 29
pub const M88E1000_PHY_VCO_REG_BIT8: u16 = 0x100; // Bits 8 & 11 are adjusted for
pub const M88E1000_PHY_VCO_REG_BIT11: u16 = 0x800; // improved BER performance

// M88EC018 Rev 2 specific DownShift settings
pub const M88EC018_EPSCR_DOWNSHIFT_COUNTER_MASK: u16 = 0x0E00;
pub const M88EC018_EPSCR_DOWNSHIFT_COUNTER_1X: u16 = 0x0000;
pub const M88EC018_EPSCR_DOWNSHIFT_COUNTER_2X: u16 = 0x0200;
pub const M88EC018_EPSCR_DOWNSHIFT_COUNTER_3X: u16 = 0x0400;
pub const M88EC018_EPSCR_DOWNSHIFT_COUNTER_4X: u16 = 0x0600;
pub const M88EC018_EPSCR_DOWNSHIFT_COUNTER_5X: u16 = 0x0800;
pub const M88EC018_EPSCR_DOWNSHIFT_COUNTER_6X: u16 = 0x0A00;
pub const M88EC018_EPSCR_DOWNSHIFT_COUNTER_7X: u16 = 0x0C00;
pub const M88EC018_EPSCR_DOWNSHIFT_COUNTER_8X: u16 = 0x0E00;

pub const IGP03E1000_E_PHY_ID: u32 = 0x02A80390;
pub const IFE_E_PHY_ID: u32 = 0x02A80330; // 10/100 PHY
pub const IFE_PLUS_E_PHY_ID: u32 = 0x02A80320;
pub const IFE_C_E_PHY_ID: u32 = 0x02A80310;

pub const IFE_PHY_MDIX_CONTROL: u32 = 0x1C; // MDI/MDI-X Control register

pub const IFE_PMC_AUTO_MDIX: u16 = 0x0080; // 1=enable MDI/MDI-X feature, default 0=disabled
pub const IFE_PMC_FORCE_MDIX: u16 = 0x0040; // 1=force MDIX-X, 0=force MDI

pub const MC_TBL_SIZE: usize = 128; // Multicast Filter Table (4096 bits)
pub const VLAN_FILTER_TBL_SIZE: usize = 128; // VLAN Filter Table (4096 bits)

pub const MC_TBL_SIZE_ICH8LAN: usize = 32;

pub const RTL8211_E_PHY_ID: u32 = 0x001CC912;

pub const GG82563_PAGE_SHIFT: u32 = 5;
pub const GG82563_MIN_ALT_REG: u32 = 30;

// GG82563 PHY Specific Status Register (Page 0, Register 16)
pub const GG82563_PSCR_DISABLE_JABBER: u16 = 0x0001; // 1=Disable Jabber
pub const GG82563_PSCR_POLARITY_REVERSAL_DISABLE: u16 = 0x0002; // 1=Polarity Reversal Disabled
pub const GG82563_PSCR_POWER_DOWN: u16 = 0x0004; // 1=Power Down
pub const GG82563_PSCR_COPPER_TRANSMITER_DISABLE: u16 = 0x0008; // 1=Transmitter Disabled
pub const GG82563_PSCR_CROSSOVER_MODE_MASK: u16 = 0x0060;
pub const GG82563_PSCR_CROSSOVER_MODE_MDI: u16 = 0x0000; // 00=Manual MDI configuration
pub const GG82563_PSCR_CROSSOVER_MODE_MDIX: u16 = 0x0020; // 01=Manual MDIX configuration
pub const GG82563_PSCR_CROSSOVER_MODE_AUTO: u16 = 0x0060; // 11=Automatic crossover
pub const GG82563_PSCR_ENALBE_EXTENDED_DISTANCE: u16 = 0x0080; // 1=Enable Extended Distance
pub const GG82563_PSCR_ENERGY_DETECT_MASK: u16 = 0x0300;
pub const GG82563_PSCR_ENERGY_DETECT_OFF: u16 = 0x0000; // 00,01=Off
pub const GG82563_PSCR_ENERGY_DETECT_RX: u16 = 0x0200; // 10=Sense on Rx only (Energy Detect)
pub const GG82563_PSCR_ENERGY_DETECT_RX_TM: u16 = 0x0300; // 11=Sense and Tx NLP
pub const GG82563_PSCR_FORCE_LINK_GOOD: u16 = 0x0400; // 1=Force Link Good
pub const GG82563_PSCR_DOWNSHIFT_ENABLE: u16 = 0x0800; // 1=Enable Downshift
pub const GG82563_PSCR_DOWNSHIFT_COUNTER_MASK: u16 = 0x7000;
pub const GG82563_PSCR_DOWNSHIFT_COUNTER_SHIFT: u16 = 12;

// GG82563 Specific Registers
pub const GG82563_PHY_SPEC_CTRL: u32 = gg82563_reg(0, 16); // PHY Specific Control
pub const GG82563_PHY_SPEC_STATUS: u32 = gg82563_reg(0, 17); // PHY Specific Status
pub const GG82563_PHY_INT_ENABLE: u32 = gg82563_reg(0, 18); // Interrupt Enable
pub const GG82563_PHY_SPEC_STATUS_2: u32 = gg82563_reg(0, 19); // PHY Specific Status 2
pub const GG82563_PHY_RX_ERR_CNTR: u32 = gg82563_reg(0, 21); // Receive Error Counter
pub const GG82563_PHY_PAGE_SELECT: u32 = gg82563_reg(0, 22); // Page Select
pub const GG82563_PHY_SPEC_CTRL_2: u32 = gg82563_reg(0, 26); // PHY Specific Control 2
pub const GG82563_PHY_PAGE_SELECT_ALT: u32 = gg82563_reg(0, 29); // Alternate Page Select
pub const GG82563_PHY_TEST_CLK_CTRL: u32 = gg82563_reg(0, 30); // Test Clock Control (use reg. 29 to select)

pub const GG82563_PHY_MAC_SPEC_CTRL: u32 = gg82563_reg(2, 21); // MAC Specific Control Register
pub const GG82563_PHY_MAC_SPEC_CTRL_2: u32 = gg82563_reg(2, 26); // MAC Specific Control 2

pub const GG82563_PHY_DSP_DISTANCE: u32 = gg82563_reg(5, 26); // DSP Distance

// PHY Specific Control Register 2 (Page 0, Register 26)
pub const GG82563_PSCR2_10BT_POLARITY_FORCE: u16 = 0x0002; // 1=Force Negative Polarity
pub const GG82563_PSCR2_1000MB_TEST_SELECT_MASK: u16 = 0x000C;
pub const GG82563_PSCR2_1000MB_TEST_SELECT_NORMAL: u16 = 0x0000; // 00,01=Normal Operation
pub const GG82563_PSCR2_1000MB_TEST_SELECT_112NS: u16 = 0x0008; // 10=Select 112ns Sequence
pub const GG82563_PSCR2_1000MB_TEST_SELECT_16NS: u16 = 0x000C; // 11=Select 16ns Sequence
pub const GG82563_PSCR2_REVERSE_AUTO_NEG: u16 = 0x2000; // 1=Reverse Auto-Negotiation
pub const GG82563_PSCR2_1000BT_DISABLE: u16 = 0x4000; // 1=Disable 1000BASE-T
pub const GG82563_PSCR2_TRANSMITER_TYPE_MASK: u16 = 0x8000;
pub const GG82563_PSCR2_TRANSMITTER_TYPE_CLASS_B: u16 = 0x0000; // 0=Class B
pub const GG82563_PSCR2_TRANSMITTER_TYPE_CLASS_A: u16 = 0x8000; // 1=Class A

// MAC Specific Control Register (Page 2, Register 21)
// Tx clock speed for Link Down and 1000BASE-T for the following speeds
pub const GG82563_MSCR_TX_CLK_MASK: u16 = 0x0007;
pub const GG82563_MSCR_TX_CLK_10MBPS_2_5MHZ: u16 = 0x0004;
pub const GG82563_MSCR_TX_CLK_100MBPS_25MHZ: u16 = 0x0005;
pub const GG82563_MSCR_TX_CLK_1000MBPS_2_5MHZ: u16 = 0x0006;
pub const GG82563_MSCR_TX_CLK_1000MBPS_25MHZ: u16 = 0x0007;

pub const GG82563_MSCR_ASSERT_CRS_ON_TX: u16 = 0x0010; // 1=Assert

// Page 193 - Port Control Registers
pub const GG82563_PHY_KMRN_MODE_CTRL: u32 = gg82563_reg(193, 16); // Kumeran Mode Control
pub const GG82563_PHY_PORT_RESET: u32 = gg82563_reg(193, 17); // Port Reset
pub const GG82563_PHY_REVISION_ID: u32 = gg82563_reg(193, 18); // Revision ID
pub const GG82563_PHY_DEVICE_ID: u32 = gg82563_reg(193, 19); // Device ID
pub const GG82563_PHY_PWR_MGMT_CTRL: u32 = gg82563_reg(193, 20); // Power Management Control
pub const GG82563_PHY_RATE_ADAPT_CTRL: u32 = gg82563_reg(193, 25); // Rate Adaptation Control

// Kumeran Mode Control Register (Page 193, Register 16)
pub const GG82563_KMCR_PHY_LEDS_EN: u16 = 0x0020; // 1=PHY LEDs, 0=Kumeran Inband LEDs
pub const GG82563_KMCR_FORCE_LINK_UP: u16 = 0x0040; // 1=Force Link Up
pub const GG82563_KMCR_SUPPRESS_SGMII_EPD_EXT: u16 = 0x0080;
pub const GG82563_KMCR_MDIO_BUS_SPEED_SELECT_MASK: u16 = 0x0400;
pub const GG82563_KMCR_MDIO_BUS_SPEED_SELECT: u16 = 0x0400; // 1=6.25MHz, 0=0.8MHz
pub const GG82563_KMCR_PASS_FALSE_CARRIER: u16 = 0x0800;

// Power Management Control Register (Page 193, Register 20)
pub const GG82563_PMCR_ENABLE_ELECTRICAL_IDLE: u16 = 0x0001; // 1=Enable SERDES Electrical Idle
pub const GG82563_PMCR_DISABLE_PORT: u16 = 0x0002; // 1=Disable Port
pub const GG82563_PMCR_DISABLE_SERDES: u16 = 0x0004; // 1=Disable SERDES
pub const GG82563_PMCR_REVERSE_AUTO_NEG: u16 = 0x0008; // 1=Enable Reverse Auto-Negotiation
pub const GG82563_PMCR_DISABLE_1000_NON_D0: u16 = 0x0010; // 1=Disable 1000Mbps Auto-Neg in non D0
pub const GG82563_PMCR_DISABLE_1000: u16 = 0x0020; // 1=Disable 1000Mbps Auto-Neg Always
pub const GG82563_PMCR_REVERSE_AUTO_NEG_D0A: u16 = 0x0040; // 1=Enable D0a Reverse Auto-Negotiation
pub const GG82563_PMCR_FORCE_POWER_STATE: u16 = 0x0080; // 1=Force Power State
pub const GG82563_PMCR_PROGRAMMED_POWER_STATE_MASK: u16 = 0x0300;
pub const GG82563_PMCR_PROGRAMMED_POWER_STATE_DR: u16 = 0x0000; // 00=Dr
pub const GG82563_PMCR_PROGRAMMED_POWER_STATE_D0U: u16 = 0x0100; // 01=D0u
pub const GG82563_PMCR_PROGRAMMED_POWER_STATE_D0A: u16 = 0x0200; // 10=D0a
pub const GG82563_PMCR_PROGRAMMED_POWER_STATE_D3: u16 = 0x0300; // 11=D3

// Page 194 - KMRN Registers
pub const GG82563_PHY_KMRN_FIFO_CTRL_STAT: u32 = gg82563_reg(194, 16); // FIFO's Control/Status
pub const GG82563_PHY_KMRN_CTRL: u32 = gg82563_reg(194, 17); // Control
pub const GG82563_PHY_INBAND_CTRL: u32 = gg82563_reg(194, 18); // Inband Control
pub const GG82563_PHY_KMRN_DIAGNOSTIC: u32 = gg82563_reg(194, 19); // Diagnostic
pub const GG82563_PHY_ACK_TIMEOUTS: u32 = gg82563_reg(194, 20); // Acknowledge Timeouts
pub const GG82563_PHY_ADV_ABILITY: u32 = gg82563_reg(194, 21); // Advertised Ability
pub const GG82563_PHY_LINK_PARTNER_ADV_ABILITY: u32 = gg82563_reg(194, 23); // Link Partner Advertised Ability
pub const GG82563_PHY_ADV_NEXT_PAGE: u32 = gg82563_reg(194, 24); // Advertised Next Page
pub const GG82563_PHY_LINK_PARTNER_ADV_NEXT_PAGE: u32 = gg82563_reg(194, 25); // Link Partner Advertised Next page
pub const GG82563_PHY_KMRN_MISC: u32 = gg82563_reg(194, 26); // Misc.

// In-Band Control Register (Page 194, Register 18)
pub const GG82563_ICR_DIS_PADDING: u16 = 0x0010; // Disable Padding Use

// DSP Distance Register (Page 5, Register 26)
pub const GG82563_DSPD_CABLE_LENGTH: u16 = 0x0007; // 0 = <50M; 1 = 50-80M; 2 = 80-110M; 3 = 110-140M; 4 = >140M

// BME1000 PHY Specific Control Register
pub const BME1000_PSCR_ENABLE_DOWNSHIFT: u16 = 0x0800; // 1 = enable downshift
pub const BM_PHY_PAGE_SELECT: u32 = 22; // Page Select for BM
pub const BM_REG_BIAS1: u32 = 29;
pub const BM_REG_BIAS2: u32 = 30;

pub const KMRNCTRLSTA_K1_CONFIG: u32 = 0x7;
pub const KMRNCTRLSTA_K1_ENABLE: u16 = 0x0002;

// Miscellaneous PHY bit definitions.
pub const PHY_PREAMBLE: u32 = 0xFFFFFFFF;
pub const PHY_SOF: u32 = 0x01;
pub const PHY_OP_READ: u32 = 0x02;
pub const PHY_OP_WRITE: u32 = 0x01;
pub const PHY_TURNAROUND: u32 = 0x02;
pub const PHY_PREAMBLE_SIZE: u32 = 32;
pub const MII_CR_SPEED_1000: u16 = 0x0040;
pub const MII_CR_SPEED_100: u16 = 0x2000;
pub const MII_CR_SPEED_10: u16 = 0x0000;
pub const PHY_ADDRESS: u32 = 0x01;
pub const PHY_AUTO_NEG_TIME: u32 = 45; // 4.5 Seconds
pub const PHY_FORCE_TIME: u32 = 20; // 2.0 Seconds
pub const PHY_REVISION_MASK: u32 = 0xFFFFFFF0;
pub const DEVICE_SPEED_MASK: u32 = 0x00000300; // Device Ctrl Reg Speed Mask
pub const REG4_SPEED_MASK: u16 = 0x01E0;
pub const REG9_SPEED_MASK: u16 = 0x0300;
pub const ADVERTISE_10_HALF: u32 = 0x0001;
pub const ADVERTISE_10_FULL: u32 = 0x0002;
pub const ADVERTISE_100_HALF: u32 = 0x0004;
pub const ADVERTISE_100_FULL: u32 = 0x0008;
pub const ADVERTISE_1000_HALF: u32 = 0x0010;
pub const ADVERTISE_1000_FULL: u32 = 0x0020;
pub const AUTONEG_ADVERTISE_SPEED_DEFAULT: u32 = 0x002F; // Everything but 1000-Half
pub const AUTONEG_ADVERTISE_10_100_ALL: u32 = 0x000F; // All 10/100 speeds
pub const AUTONEG_ADVERTISE_10_ALL: u32 = 0x0003; // 10Mbps Full & Half speeds

// Autoneg Advertisement Register
pub const NWAY_AR_SELECTOR_FIELD: u16 = 0x0001; // indicates IEEE 802.3 CSMA/CD
pub const NWAY_AR_10T_HD_CAPS: u16 = 0x0020; // 10T   Half Duplex Capable
pub const NWAY_AR_10T_FD_CAPS: u16 = 0x0040; // 10T   Full Duplex Capable
pub const NWAY_AR_100TX_HD_CAPS: u16 = 0x0080; // 100TX Half Duplex Capable
pub const NWAY_AR_100TX_FD_CAPS: u16 = 0x0100; // 100TX Full Duplex Capable
pub const NWAY_AR_100T4_CAPS: u16 = 0x0200; // 100T4 Capable
pub const NWAY_AR_PAUSE: u16 = 0x0400; // Pause operation desired
pub const NWAY_AR_ASM_DIR: u16 = 0x0800; // Asymmetric Pause Direction bit
pub const NWAY_AR_REMOTE_FAULT: u16 = 0x2000; // Remote Fault detected
pub const NWAY_AR_NEXT_PAGE: u16 = 0x8000; // Next Page ability supported

// Link Partner Ability Register (Base Page)
pub const NWAY_LPAR_SELECTOR_FIELD: u16 = 0x0000; // LP protocol selector field
pub const NWAY_LPAR_10T_HD_CAPS: u16 = 0x0020; // LP is 10T   Half Duplex Capable
pub const NWAY_LPAR_10T_FD_CAPS: u16 = 0x0040; // LP is 10T   Full Duplex Capable
pub const NWAY_LPAR_100TX_HD_CAPS: u16 = 0x0080; // LP is 100TX Half Duplex Capable
pub const NWAY_LPAR_100TX_FD_CAPS: u16 = 0x0100; // LP is 100TX Full Duplex Capable
pub const NWAY_LPAR_100T4_CAPS: u16 = 0x0200; // LP is 100T4 Capable
pub const NWAY_LPAR_PAUSE: u16 = 0x0400; // LP Pause operation desired
pub const NWAY_LPAR_ASM_DIR: u16 = 0x0800; // LP Asymmetric Pause Direction bit
pub const NWAY_LPAR_REMOTE_FAULT: u16 = 0x2000; // LP has detected Remote Fault
pub const NWAY_LPAR_ACKNOWLEDGE: u16 = 0x4000; // LP has rx'd link code word
pub const NWAY_LPAR_NEXT_PAGE: u16 = 0x8000; // Next Page ability supported

// Autoneg Expansion Register
pub const NWAY_ER_LP_NWAY_CAPS: u16 = 0x0001; // LP has Auto Neg Capability
pub const NWAY_ER_PAGE_RXD: u16 = 0x0002; // LP is 10T   Half Duplex Capable
pub const NWAY_ER_NEXT_PAGE_CAPS: u16 = 0x0004; // LP is 10T   Full Duplex Capable
pub const NWAY_ER_LP_NEXT_PAGE_CAPS: u16 = 0x0008; // LP is 100TX Half Duplex Capable
pub const NWAY_ER_PAR_DETECT_FAULT: u16 = 0x0010; // LP is 100TX Full Duplex Capable

// PHY Control Register
pub const MII_CR_COLL_TEST_ENABLE: u16 = 0x0080; // Collision test enable
pub const MII_CR_SPEED_SELECT_MSB: u16 = 0x0040; // bits 6,13: 10=1000, 01=100, 00=10
pub const MII_CR_FULL_DUPLEX: u16 = 0x0100; // FDX =1, half duplex =0
pub const MII_CR_RESTART_AUTO_NEG: u16 = 0x0200; // Restart auto negotiation
pub const MII_CR_ISOLATE: u16 = 0x0400; // Isolate PHY from MII
pub const MII_CR_POWER_DOWN: u16 = 0x0800; // Power down
pub const MII_CR_AUTO_NEG_EN: u16 = 0x1000; // Auto Neg Enable
pub const MII_CR_SPEED_SELECT_LSB: u16 = 0x2000; // bits 6,13: 10=1000, 01=100, 00=10
pub const MII_CR_LOOPBACK: u16 = 0x4000; // 0 = normal, 1 = loopback
pub const MII_CR_RESET: u16 = 0x8000; // 0 = normal, 1 = PHY reset

// PHY Status Register
pub const MII_SR_EXTENDED_CAPS: u16 = 0x0001; // Extended register capabilities
pub const MII_SR_JABBER_DETECT: u16 = 0x0002; // Jabber Detected
pub const MII_SR_LINK_STATUS: u16 = 0x0004; // Link Status 1 = link
pub const MII_SR_AUTONEG_CAPS: u16 = 0x0008; // Auto Neg Capable
pub const MII_SR_REMOTE_FAULT: u16 = 0x0010; // Remote Fault Detect
pub const MII_SR_AUTONEG_COMPLETE: u16 = 0x0020; // Auto Neg Complete
pub const MII_SR_PREAMBLE_SUPPRESS: u16 = 0x0040; // Preamble may be suppressed
pub const MII_SR_EXTENDED_STATUS: u16 = 0x0100; // Ext. status info in Reg 0x0F
pub const MII_SR_100T2_HD_CAPS: u16 = 0x0200; // 100T2 Half Duplex Capable
pub const MII_SR_100T2_FD_CAPS: u16 = 0x0400; // 100T2 Full Duplex Capable
pub const MII_SR_10T_HD_CAPS: u16 = 0x0800; // 10T   Half Duplex Capable
pub const MII_SR_10T_FD_CAPS: u16 = 0x1000; // 10T   Full Duplex Capable
pub const MII_SR_100X_HD_CAPS: u16 = 0x2000; // 100X  Half Duplex Capable
pub const MII_SR_100X_FD_CAPS: u16 = 0x4000; // 100X  Full Duplex Capable

pub const HV_KMRN_MODE_CTRL: u32 = phy_reg(769, 16);
pub const HV_KMRN_MDIO_SLOW: u32 = 0x0400;

// I82578 Downshift settings (Extended PHY Specific Control Register)
pub const I82578_EPSCR_DOWNSHIFT_ENABLE: u16 = 0x0020;
pub const I82578_EPSCR_DOWNSHIFT_COUNTER_MASK: u16 = 0x001C;

// EMI Registers
pub const I82579_EMI_ADDR: u32 = 0x10;
pub const I82579_EMI_DATA: u32 = 0x11;
pub const I82579_LPI_UPDATE_TIMER: u32 = 0x4805; // in 40ns units + 40 ns base value
pub const I82579_MSE_THRESHOLD: u16 = 0x084F; // Mean Square Error Threshold
pub const I82579_MSE_LINK_DOWN: u16 = 0x2411; // MSE count before dropping link

// PHY Low Power Idle Control
pub const I82579_LPI_CTRL: u32 = phy_reg(772, 20);
pub const I82579_LPI_CTRL_ENABLE_MASK: u16 = 0x6000;
pub const I82579_LPI_CTRL_FORCE_PLL_LOCK_COUNT: u16 = 0x80;

pub const LEDCTL: usize = 0x00E00;

pub const LEDCTL_LED0_MODE_MASK: u32 = 0x0000000F;
pub const LEDCTL_LED0_MODE_SHIFT: u32 = 0;
pub const LEDCTL_LED0_BLINK_RATE: u32 = 0x0000020;
pub const LEDCTL_LED0_IVRT: u32 = 0x00000040;
pub const LEDCTL_LED0_BLINK: u32 = 0x00000080;
pub const LEDCTL_LED1_MODE_MASK: u32 = 0x00000F00;
pub const LEDCTL_LED1_MODE_SHIFT: u32 = 8;
pub const LEDCTL_LED1_BLINK_RATE: u32 = 0x0002000;
pub const LEDCTL_LED1_IVRT: u32 = 0x00004000;
pub const LEDCTL_LED1_BLINK: u32 = 0x00008000;
pub const LEDCTL_LED2_MODE_MASK: u32 = 0x000F0000;
pub const LEDCTL_LED2_MODE_SHIFT: u32 = 16;
pub const LEDCTL_LED2_BLINK_RATE: u32 = 0x00200000;
pub const LEDCTL_LED2_IVRT: u32 = 0x00400000;
pub const LEDCTL_LED2_BLINK: u32 = 0x00800000;
pub const LEDCTL_LED3_MODE_MASK: u32 = 0x0F000000;
pub const LEDCTL_LED3_MODE_SHIFT: u32 = 24;
pub const LEDCTL_LED3_BLINK_RATE: u32 = 0x20000000;
pub const LEDCTL_LED3_IVRT: u32 = 0x40000000;
pub const LEDCTL_LED3_BLINK: u32 = 0x80000000;

pub const LEDCTL_MODE_LINK_10_1000: u32 = 0x0;
pub const LEDCTL_MODE_LINK_100_1000: u32 = 0x1;
pub const LEDCTL_MODE_LINK_UP: u32 = 0x2;
pub const LEDCTL_MODE_ACTIVITY: u32 = 0x3;
pub const LEDCTL_MODE_LINK_ACTIVITY: u32 = 0x4;
pub const LEDCTL_MODE_LINK_10: u32 = 0x5;
pub const LEDCTL_MODE_LINK_100: u32 = 0x6;
pub const LEDCTL_MODE_LINK_1000: u32 = 0x7;
pub const LEDCTL_MODE_PCIX_MODE: u32 = 0x8;
pub const LEDCTL_MODE_FULL_DUPLEX: u32 = 0x9;
pub const LEDCTL_MODE_COLLISION: u32 = 0xA;
pub const LEDCTL_MODE_BUS_SPEED: u32 = 0xB;
pub const LEDCTL_MODE_BUS_SIZE: u32 = 0xC;
pub const LEDCTL_MODE_PAUSED: u32 = 0xD;
pub const LEDCTL_MODE_LED_ON: u32 = 0xE;
pub const LEDCTL_MODE_LED_OFF: u32 = 0xF;

pub const IGP_ACTIVITY_LED_MASK: u32 = 0xFFFFF0FF;
pub const IGP_ACTIVITY_LED_ENABLE: u32 = 0x0300;
pub const IGP_LED3_MODE: u32 = 0x07000000;

pub const NVM_CFG_DONE_PORT_0: u32 = 0x040000; // MNG config cycle done
pub const NVM_CFG_DONE_PORT_1: u32 = 0x080000; // ...for second port
pub const NVM_CFG_DONE_PORT_2: u32 = 0x100000; // ...for third port
pub const NVM_CFG_DONE_PORT_3: u32 = 0x200000; // ...for fourth port

// EEPROM Commands - SPI
pub const EEPROM_MAX_RETRY_SPI: u16 = 5000; // Max wait of 5ms, for RDY signal
pub const EEPROM_READ_OPCODE_SPI: u16 = 0x03; // EEPROM read opcode
pub const EEPROM_WRITE_OPCODE_SPI: u16 = 0x02; // EEPROM write opcode
pub const EEPROM_A8_OPCODE_SPI: u16 = 0x08; // opcode bit-3 = address bit-8
pub const EEPROM_WREN_OPCODE_SPI: u16 = 0x06; // EEPROM set Write Enable latch
pub const EEPROM_WRDI_OPCODE_SPI: u16 = 0x04; // EEPROM reset Write Enable latch
pub const EEPROM_RDSR_OPCODE_SPI: u16 = 0x05; // EEPROM read Status register
pub const EEPROM_WRSR_OPCODE_SPI: u16 = 0x01; // EEPROM write Status register
pub const EEPROM_ERASE4K_OPCODE_SPI: u16 = 0x20; // EEPROM ERASE 4KB
pub const EEPROM_ERASE64K_OPCODE_SPI: u16 = 0xD8; // EEPROM ERASE 64KB
pub const EEPROM_ERASE256_OPCODE_SPI: u16 = 0xDB; // EEPROM ERASE 256B

// SPI EEPROM Status Register
pub const EEPROM_STATUS_RDY_SPI: u16 = 0x01;
pub const EEPROM_STATUS_WEN_SPI: u16 = 0x02;
pub const EEPROM_STATUS_BP0_SPI: u16 = 0x04;
pub const EEPROM_STATUS_BP1_SPI: u16 = 0x08;
pub const EEPROM_STATUS_WPEN_SPI: u16 = 0x80;

// EEPROM Commands - Microwire
pub const EEPROM_READ_OPCODE_MICROWIRE: u16 = 0x6; // EEPROM read opcode
pub const EEPROM_WRITE_OPCODE_MICROWIRE: u16 = 0x5; // EEPROM write opcode
pub const EEPROM_ERASE_OPCODE_MICROWIRE: u16 = 0x7; // EEPROM erase opcode
pub const EEPROM_EWEN_OPCODE_MICROWIRE: u16 = 0x13; // EEPROM erase/write enable
pub const EEPROM_EWDS_OPCODE_MICROWIRE: u16 = 0x10; // EEPROM erast/write disable

pub const EEPROM_SWDPIN0: u32 = 0x0001; // SWDPIN 0 EEPROM Value
pub const EEPROM_LED_LOGIC: u32 = 0x0020; // Led Logic Word
pub const EEPROM_RW_REG_DATA: u32 = 16; // Offset to data in EEPROM read/write registers
pub const EEPROM_RW_REG_DONE: u32 = 2; // Offset to READ/WRITE done bit
pub const EEPROM_RW_REG_START: u32 = 1; // First bit for telling part to start operation
pub const EEPROM_RW_ADDR_SHIFT: u32 = 2; // Shift to the address bits
pub const EEPROM_POLL_WRITE: u32 = 1; // Flag for polling for write complete
pub const EEPROM_POLL_READ: u32 = 0; // Flag for polling for read complete

// EEPROM Word Offsets
pub const EEPROM_MAC_ADDR_WORD0: u32 = 0x0000;
pub const EEPROM_MAC_ADDR_WORD1: u32 = 0x0001;
pub const EEPROM_MAC_ADDR_WORD2: u32 = 0x0002;
pub const EEPROM_COMPAT: u32 = 0x0003;
pub const EEPROM_ID_LED_SETTINGS: u32 = 0x0004;
pub const EEPROM_VERSION: u32 = 0x0005;
pub const EEPROM_SERDES_AMPLITUDE: u32 = 0x0006; // For SERDES output amplitude adjustment.
pub const EEPROM_PHY_CLASS_WORD: u32 = 0x0007;
pub const EEPROM_INIT_CONTROL1_REG: u32 = 0x000A;
pub const EEPROM_INIT_CONTROL2_REG: u32 = 0x000F;
pub const EEPROM_SWDEF_PINS_CTRL_PORT_1: u32 = 0x0010;
pub const EEPROM_INIT_CONTROL4_REG: u32 = 0x0013;
pub const EEPROM_INIT_CONTROL3_PORT_B: u32 = 0x0014;
pub const EEPROM_INIT_3GIO_3: u32 = 0x001A;
pub const EEPROM_LED_1_CFG: u32 = 0x001C;
pub const EEPROM_LED_0_2_CFG: u32 = 0x001F;
pub const EEPROM_SWDEF_PINS_CTRL_PORT_0: u32 = 0x0020;
pub const EEPROM_INIT_CONTROL3_PORT_A: u32 = 0x0024;
pub const EEPROM_CFG: u32 = 0x0012;
pub const EEPROM_FLASH_VERSION: u32 = 0x0032;
pub const EEPROM_CHECKSUM_REG: u32 = 0x003F;

// Mask bits for SERDES amplitude adjustment in Word 6 of the EEPROM
pub const EEPROM_SERDES_AMPLITUDE_MASK: u16 = 0x000F;

pub const EEPROM_CHECKSUM_REG_ICP_XXXX: u32 = EEPROM_CHECKSUM_REG;

pub const EEPROM_COMPAT_VALID_CSUM: u16 = 0x0001;
pub const EEPROM_FUTURE_INIT_WORD1: u32 = 0x0019;
pub const EEPROM_FUTURE_INIT_WORD1_VALID_CSUM: u16 = 0x0040;

pub const EEPROM_SUM: u16 = 0xBABA; // For checksumming, the sum of all words in the EEPROM should equal 0xBABA.

// EEPROM/Flash Control
pub const EECD_SK: u32 = 0x00000001; // EEPROM Clock
pub const EECD_CS: u32 = 0x00000002; // EEPROM Chip Select
pub const EECD_DI: u32 = 0x00000004; // EEPROM Data In
pub const EECD_DO: u32 = 0x00000008; // EEPROM Data Out
pub const EECD_FWE_MASK: u32 = 0x00000030;
pub const EECD_FWE_DIS: u32 = 0x00000010; // Disable FLASH writes
pub const EECD_FWE_EN: u32 = 0x00000020; // Enable FLASH writes
pub const EECD_FWE_SHIFT: u32 = 4;
pub const EECD_REQ: u32 = 0x00000040; // EEPROM Access Request
pub const EECD_GNT: u32 = 0x00000080; // EEPROM Access Grant
pub const EECD_PRES: u32 = 0x00000100; // EEPROM Present
pub const EECD_SIZE: u32 = 0x00000200; // EEPROM Size (0=64 word 1=256 word)
pub const EECD_ADDR_BITS: u32 = 0x00000400; // EEPROM Addressing bits based on type
pub const EECD_TYPE: u32 = 0x00002000;
pub const EECD_AUTO_RD: u32 = 0x00000200; // EEPROM Auto Read done
pub const EECD_SIZE_EX_MASK: u32 = 0x00007800;
pub const EECD_SIZE_EX_SHIFT: u32 = 11;
pub const EECD_FLUPD: u32 = 0x00080000;
pub const EECD_AUPDEN: u32 = 0x00100000;
pub const EECD_SHADV: u32 = 0x00200000; // Shadow RAM Data Valid
pub const EECD_SEC1VAL: u32 = 0x00400000; // Sector One Valid
pub const EECD_SEC1VAL_VALID_MASK: u32 = EECD_AUTO_RD | EECD_PRES;
pub const EECD_SECVAL_SHIFT: u32 = 22;
pub const STM_OPCODE: u32 = 0xDB00;
pub const HICR_FW_RESET: u32 = 0xC0;

pub const EEPROM_GRANT_ATTEMPTS: u32 = 1000; // EEPROM # attempts to gain grant

pub const EEPROM_WORD_SIZE_SHIFT: u32 = 6;
pub const EEPROM_WORD_SIZE_SHIFT_MAX: u32 = 14;

pub const EEPROM_RESERVED_WORD: u16 = 0xFFFF;
pub const EEPROM_PHY_CLASS_A: u16 = 0x8000;

// EEPROM Map defines (WORD OFFSETS)
pub const EEPROM_NODE_ADDRESS_BYTE_0: u32 = 0;
pub const EEPROM_PBA_BYTE_1: u32 = 8;

pub const INVM_SIZE: u16 = 64;

pub const INVM_UNINITIALIZED_STRUCTURE: u8 = 0x0;
pub const INVM_WORD_AUTOLOAD_STRUCTURE: u8 = 0x1;
pub const INVM_CSR_AUTOLOAD_STRUCTURE: u8 = 0x2;
pub const INVM_PHY_REGISTER_AUTOLOAD_STRUCTURE: u8 = 0x3;
pub const INVM_RSA_KEY_SHA256_STRUCTURE: u8 = 0x4;
pub const INVM_INVALIDATED_STRUCTURE: u8 = 0x5;

pub const INVM_RSA_KEY_SHA256_DATA_SIZE_IN_DWORDS: u16 = 8;
pub const INVM_CSR_AUTOLOAD_DATA_SIZE_IN_DWORDS: u16 = 1;

// NVM offset defaults for i211
pub const NVM_INIT_CTRL_2_DEFAULT_I211: u16 = 0x7243;
pub const NVM_INIT_CTRL_4_DEFAULT_I211: u16 = 0x00C1;
pub const NVM_LED_1_CFG_DEFAULT_I211: u16 = 0x0184;
pub const NVM_LED_0_2_CFG_DEFAULT_I211: u16 = 0x200C;
pub const NVM_RESERVED_WORD: u16 = 0xFFFF;

// Mask bits for fields in Word 0x24 of the NVM
pub const NVM_WORD24_COM_MDIO: u16 = 0x0008; // MDIO interface shared
pub const NVM_WORD24_EXT_MDIO: u16 = 0x0004; // MDIO accesses routed external

pub const E1000_NVM_K1_CONFIG: u32 = 0x1B; // NVM K1 Config Word
pub const E1000_NVM_K1_ENABLE: u16 = 0x1; // NVM Enable K1 bit

pub const ID_LED_RESERVED_0000: u16 = 0x0000;
pub const ID_LED_RESERVED_FFFF: u16 = 0xFFFF;
pub const ID_LED_RESERVED_82573: u16 = 0xF746;
pub const ID_LED_DEFAULT_82573: u16 = 0x1811;
pub const ID_LED_DEFAULT: u16 = (ID_LED_OFF1_ON2 << 12)
    | (ID_LED_OFF1_OFF2 << 8)
    | (ID_LED_DEF1_DEF2 << 4)
    | (ID_LED_DEF1_DEF2);
pub const ID_LED_DEFAULT_ICH8LAN: u16 = (ID_LED_DEF1_DEF2 << 12)
    | (ID_LED_DEF1_OFF2 << 8)
    | (ID_LED_DEF1_ON2 << 4)
    | (ID_LED_DEF1_DEF2);
pub const ID_LED_DEF1_DEF2: u16 = 0x1;
pub const ID_LED_DEF1_ON2: u16 = 0x2;
pub const ID_LED_DEF1_OFF2: u16 = 0x3;
pub const ID_LED_ON1_DEF2: u16 = 0x4;
pub const ID_LED_ON1_ON2: u16 = 0x5;
pub const ID_LED_ON1_OFF2: u16 = 0x6;
pub const ID_LED_OFF1_DEF2: u16 = 0x7;
pub const ID_LED_OFF1_ON2: u16 = 0x8;
pub const ID_LED_OFF1_OFF2: u16 = 0x9;

pub const ICH_CYCLE_READ: u16 = 0x0;
pub const ICH_CYCLE_RESERVED: u16 = 0x1;
pub const ICH_CYCLE_WRITE: u16 = 0x2;
pub const ICH_CYCLE_ERASE: u16 = 0x3;

pub const ICH_FLASH_GFPREG: usize = 0x0000;
pub const ICH_FLASH_HSFSTS: usize = 0x0004;
pub const ICH_FLASH_HSFCTL: usize = 0x0006;
pub const ICH_FLASH_FADDR: usize = 0x0008;
pub const ICH_FLASH_FDATA0: usize = 0x0010;
pub const ICH_FLASH_FRACC: usize = 0x0050;
pub const ICH_FLASH_FREG0: usize = 0x0054;
pub const ICH_FLASH_FREG1: usize = 0x0058;
pub const ICH_FLASH_FREG2: usize = 0x005C;
pub const ICH_FLASH_FREG3: usize = 0x0060;
pub const ICH_FLASH_FPR0: usize = 0x0074;
pub const ICH_FLASH_FPR1: usize = 0x0078;
pub const ICH_FLASH_SSFSTS: usize = 0x0090;
pub const ICH_FLASH_SSFCTL: usize = 0x0092;
pub const ICH_FLASH_PREOP: usize = 0x0094;
pub const ICH_FLASH_OPTYPE: usize = 0x0096;
pub const ICH_FLASH_OPMENU: usize = 0x0098;

pub const ICH_FLASH_COMMAND_TIMEOUT: u32 = 5000; // 5000 uSecs - adjusted
pub const ICH_FLASH_ERASE_TIMEOUT: u32 = 3000000; // Up to 3 seconds - worst case
pub const ICH_FLASH_CYCLE_REPEAT_COUNT: u32 = 10; // 10 cycles
pub const ICH_FLASH_SEG_SIZE_256: u32 = 256;
pub const ICH_FLASH_SEG_SIZE_4K: u32 = 4096;
pub const ICH_FLASH_SEG_SIZE_8K: u32 = 8192;
pub const ICH_FLASH_SEG_SIZE_64K: u32 = 65536;

pub const ICH_FLASH_REG_MAPSIZE: u32 = 0x00A0;
pub const ICH_FLASH_SECTOR_SIZE: u32 = 4096;
pub const ICH_GFPREG_BASE_MASK: u32 = 0x1FFF;
pub const ICH_FLASH_LINEAR_ADDR_MASK: u32 = 0x00FFFFFF;
pub const ICH_FLASH_SECT_ADDR_SHIFT: u32 = 12;

pub const SHADOW_RAM_WORDS: u16 = 2048;
pub const ICH_NVM_SIG_WORD: u32 = 0x13;
pub const ICH_NVM_SIG_MASK: u32 = 0xC000;
pub const ICH_NVM_VALID_SIG_MASK: u32 = 0xC0;
pub const ICH_NVM_SIG_VALUE: u32 = 0x80;

// IGP01E1000 Analog Register
pub const IGP01E1000_ANALOG_SPARE_FUSE_STATUS: u32 = 0x20D1;
pub const IGP01E1000_ANALOG_FUSE_STATUS: u32 = 0x20D0;
pub const IGP01E1000_ANALOG_FUSE_CONTROL: u32 = 0x20DC;
pub const IGP01E1000_ANALOG_FUSE_BYPASS: u32 = 0x20DE;

pub const IGP01E1000_ANALOG_FUSE_POLY_MASK: u16 = 0xF000;
pub const IGP01E1000_ANALOG_FUSE_FINE_MASK: u16 = 0x0F80;
pub const IGP01E1000_ANALOG_FUSE_COARSE_MASK: u16 = 0x0070;
pub const IGP01E1000_ANALOG_SPARE_FUSE_ENABLED: u16 = 0x0100;
pub const IGP01E1000_ANALOG_FUSE_ENABLE_SW_CONTROL: u16 = 0x0002;

pub const IGP01E1000_ANALOG_FUSE_COARSE_THRESH: u16 = 0x0040;
pub const IGP01E1000_ANALOG_FUSE_COARSE_10: u16 = 0x0010;
pub const IGP01E1000_ANALOG_FUSE_FINE_1: u16 = 0x0080;
pub const IGP01E1000_ANALOG_FUSE_FINE_10: u16 = 0x0500;

pub const KABGTXD_BGSQLBIAS: u32 = 0x00050000;

// Energy Efficient Ethernet "EEE" registers
pub const IPCNFG: usize = 0x0E38; // Internal PHY Configuration
pub const LTRC: usize = 0x01A0; // Latency Tolerance Reporting Control
pub const EEER: usize = 0x0E30; // Energy Efficient Ethernet "EEE"
pub const EEE_SU: usize = 0x0E34; // EEE Setup
pub const TLPIC: usize = 0x4148; // EEE Tx LPI Count - TLPIC
pub const RLPIC: usize = 0x414C; // EEE Rx LPI Count - RLPIC

// I350 EEE defines
pub const IPCNFG_EEE_1G_AN: u32 = 0x00000008; // IPCNFG EEE Ena 1G AN
pub const IPCNFG_EEE_100M_AN: u32 = 0x00000004; // IPCNFG EEE Ena 100M AN
pub const EEER_TX_LPI_EN: u32 = 0x00010000; // EEER Tx LPI Enable
pub const EEER_RX_LPI_EN: u32 = 0x00020000; // EEER Rx LPI Enable
pub const EEER_LPI_FC: u32 = 0x00040000; // EEER Ena on Flow Cntrl

pub const fn gg82563_reg(page: u32, reg: u32) -> u32 {
    (page << GG82563_PAGE_SHIFT) | (reg & MAX_PHY_REG_ADDRESS)
}

pub const fn phy_reg(page: u32, reg: u32) -> u32 {
    (page << PHY_PAGE_SHIFT) | (reg & MAX_PHY_REG_ADDRESS)
}

pub const NODE_ADDRESS_SIZE: usize = 6;

pub const MASTER_DISABLE_TIMEOUT: u32 = 800;

pub const MAX_TXD: usize = 512;
pub const MAX_RXD: usize = 256;

pub const H2ME: usize = SWSM; // Host to ME

pub const H2ME_ULP: u32 = 0x00000800; // ULP Indication Bit
pub const H2ME_ENFORCE_SETTINGS: u32 = 0x00001000; // Enforce Settings

// SMBus Control Phy Register
pub const CV_SMB_CTRL: u32 = phy_reg(769, 23);
pub const CV_SMB_CTRL_FORCE_SMBUS: u16 = 0x0001;

// PHY Power Management Control
pub const HV_PM_CTRL: u32 = phy_reg(770, 17);
pub const HV_PM_CTRL_K1_CLK_REQ: u16 = 0x200;
pub const HV_PM_CTRL_K1_ENABLE: u16 = 0x4000;

// I218 Ultra Low Power Configuration 1 Register
pub const I218_ULP_CONFIG1: u32 = phy_reg(779, 16);
pub const I218_ULP_CONFIG1_START: u16 = 0x0001; // Start auto ULP config
pub const I218_ULP_CONFIG1_IND: u16 = 0x0004; // Pwr up from ULP indication
pub const I218_ULP_CONFIG1_STICKY_ULP: u16 = 0x0010; // Set sticky ULP mode
pub const I218_ULP_CONFIG1_INBAND_EXIT: u16 = 0x0020; // Inband on ULP exit
pub const I218_ULP_CONFIG1_WOL_HOST: u16 = 0x0040; // WoL Host on ULP exit
pub const I218_ULP_CONFIG1_RESET_TO_SMBUS: u16 = 0x0100; // Reset to SMBus mode

// enable ULP even if when phy powered down via lanphypc
pub const I218_ULP_CONFIG1_EN_ULP_LANPHYPC: u16 = 0x0400;

// disable clear of sticky ULP on PERST
pub const I218_ULP_CONFIG1_DIS_CLR_STICKY_ON_PERST: u16 = 0x0800;
pub const I218_ULP_CONFIG1_DISABLE_SMB_PERST: u16 = 0x1000; // Disable on PERST#

// Inband Control
pub const I217_INBAND_CTRL: u32 = phy_reg(770, 18);
pub const I217_INBAND_CTRL_LINK_STAT_TX_TIMEOUT_MASK: u16 = 0x3F00;
pub const I217_INBAND_CTRL_LINK_STAT_TX_TIMEOUT_SHIFT: u16 = 8;

pub const FEXTNVM3_PHY_CFG_COUNTER_MASK: u32 = 0x0C000000;
pub const FEXTNVM3_PHY_CFG_COUNTER_50MSEC: u32 = 0x08000000;

pub const FEXTNVM4_BEACON_DURATION_MASK: u32 = 0x7;
pub const FEXTNVM4_BEACON_DURATION_8USEC: u32 = 0x7;
pub const FEXTNVM4_BEACON_DURATION_16USEC: u32 = 0x3;

pub const FEXTNVM6_REQ_PLL_CLK: u32 = 0x00000100;
pub const FEXTNVM6_ENABLE_K1_ENTRY_CONDITION: u32 = 0x00000200;

// Transmit Descriptor Control
pub const TXDCTL_PTHRESH: u32 = 0x000000FF; // TXDCTL Prefetch Threshold
pub const TXDCTL_HTHRESH: u32 = 0x0000FF00; // TXDCTL Host Threshold
pub const TXDCTL_WTHRESH: u32 = 0x00FF0000; // TXDCTL Writeback Threshold
pub const TXDCTL_GRAN: u32 = 0x01000000; // TXDCTL Granularity
pub const TXDCTL_LWTHRESH: u32 = 0xFE000000; // TXDCTL Low Threshold
pub const TXDCTL_FULL_TX_DESC_WB: u32 = 0x01010000; // GRAN=1, WTHRESH=1
pub const TXDCTL_COUNT_DESC: u32 = 0x00400000; // Enable the counting of desc. still to be processed.
pub const TXDCTL_QUEUE_ENABLE: u32 = 0x02000000;

pub fn txdctl(n: usize) -> usize {
    if n < 4 {
        0x03828 + n * 0x100
    } else {
        0x0E028 + n * 0x40
    }
}

// Transmit Control
pub const TCTL_RST: u32 = 0x00000001; // software reset
pub const TCTL_EN: u32 = 0x00000002; // enable tx
pub const TCTL_BCE: u32 = 0x00000004; // busy check enable
pub const TCTL_PSP: u32 = 0x00000008; // pad short packets
pub const TCTL_COLD: u32 = 0x003ff000; // collision distance
pub const TCTL_SWXOFF: u32 = 0x00400000; // SW Xoff transmission
pub const TCTL_PBE: u32 = 0x00800000; // Packet Burst Enable
pub const TCTL_RTLC: u32 = 0x01000000; // Re-transmit on late collision
pub const TCTL_NRTU: u32 = 0x02000000; // No Re-transmit on underrun
pub const TCTL_MULR: u32 = 0x10000000; // Multiple request support

// Extended Transmit Control
pub const TCTL_EXT_BST_MASK: u32 = 0x000003FF; // Backoff Slot Time
pub const TCTL_EXT_GCEX_MASK: u32 = 0x000FFC00; // Gigabit Carry Extend Padding

pub const CTRL_EXT_PHYPDEN: u32 = 0x00100000;

pub const VFTA_ENTRY_SHIFT: u16 = 0x5;
pub const VFTA_ENTRY_MASK: u16 = 0x7F;
pub const VFTA_ENTRY_BIT_SHIFT_MASK: u16 = 0x1F;

pub const KUMCTRLSTA_MASK: u32 = 0x0000FFFF;
pub const KUMCTRLSTA_OFFSET: u32 = 0x001F0000;
pub const KUMCTRLSTA_OFFSET_SHIFT: u32 = 16;
pub const KUMCTRLSTA_REN: u32 = 0x00200000;

pub const KUMCTRLSTA_OFFSET_FIFO_CTRL: u32 = 0x00000000;
pub const KUMCTRLSTA_OFFSET_CTRL: u32 = 0x00000001;
pub const KUMCTRLSTA_OFFSET_INB_CTRL: u32 = 0x00000002;
pub const KUMCTRLSTA_OFFSET_DIAG: u32 = 0x00000003;
pub const KUMCTRLSTA_OFFSET_TIMEOUTS: u32 = 0x00000004;
pub const KUMCTRLSTA_OFFSET_INB_PARAM: u32 = 0x00000009;
pub const KUMCTRLSTA_OFFSET_HD_CTRL: u32 = 0x00000010;
pub const KUMCTRLSTA_OFFSET_M2P_SERDES: u32 = 0x0000001E;
pub const KUMCTRLSTA_OFFSET_M2P_MODES: u32 = 0x0000001F;

// In-Band Control
pub const KUMCTRLSTA_INB_CTRL_LINK_STATUS_TX_TIMEOUT_DEFAULT: u16 = 0x00000500;
pub const KUMCTRLSTA_INB_CTRL_DIS_PADDING: u16 = 0x00000010;

// Half-Duplex Control
pub const KUMCTRLSTA_HD_CTRL_10_100_DEFAULT: u16 = 0x00000004;
pub const KUMCTRLSTA_HD_CTRL_1000_DEFAULT: u16 = 0x00000000;

// FIFO Control
pub const KUMCTRLSTA_FIFO_CTRL_RX_BYPASS: u16 = 0x00000008;
pub const KUMCTRLSTA_FIFO_CTRL_TX_BYPASS: u16 = 0x00000800;

pub const IGP3_KMRN_DIAG: u32 = phy_reg(770, 19); // KMRN Diagnostic register
pub const IGP3_KMRN_POWER_MNG_CTRL: u32 = phy_reg(770, 17); // KMRN Power Management Control Register

pub const IGP3_KMRN_DIAG_PCS_LOCK_LOSS: u16 = 0x0002; // RX PCS is not synced

// I217 definitions
pub const I2_DFT_CTRL: u32 = phy_reg(769, 20);
pub const I2_SMBUS_CTRL: u32 = phy_reg(769, 23);
pub const I2_MODE_CTRL: u32 = HV_KMRN_MODE_CTRL;
pub const I2_PCIE_POWER_CTRL: u32 = IGP3_KMRN_POWER_MNG_CTRL;

// Number of high/low register pairs in the RAR. The RAR (Receive Address
// Registers) holds the directed and multicast addresses that we monitor. We
// reserve one of these spots for our directed address, allowing us room for
// E1000_RAR_ENTRIES - 1 multicast addresses.
pub const RAR_ENTRIES: usize = 15;
pub const RAR_ENTRIES_ICH8LAN: usize = 7;
pub const RAR_ENTRIES_82575: usize = 16;
pub const RAR_ENTRIES_82576: usize = 24;
pub const RAR_ENTRIES_82580: usize = 24;
pub const RAR_ENTRIES_I350: usize = 32;

// Flow Control
pub const FCRTH_RTH: u32 = 0x0000FFF8; // Mask Bits[15:3] for RTH
pub const FCRTH_XFCE: u32 = 0x80000000; // External Flow Control Enable
pub const FCRTL_RTL: u32 = 0x0000FFF8; // Mask Bits[15:3] for RTL
pub const FCRTL_XONE: u32 = 0x80000000; // Enable XON frame transmission

// Flow Control Constants
pub const FLOW_CONTROL_ADDRESS_LOW: u32 = 0x00C28001;
pub const FLOW_CONTROL_ADDRESS_HIGH: u32 = 0x00000100;
pub const FLOW_CONTROL_TYPE: u32 = 0x8808;

// Flow Control Settings
pub const FC_NONE: u8 = 0;
pub const FC_RX_PAUSE: u8 = 1;
pub const FC_TX_PAUSE: u8 = 2;
pub const FC_FULL: u8 = 3;

// I82577 Specific Registers
pub const I82577_PHY_ADDR_REG: u32 = 16;
pub const I82577_PHY_CFG_REG: u32 = 22;
pub const I82577_PHY_CTRL_REG: u32 = 23;

// I82577 Config Register
pub const I82577_PHY_CFG_ENABLE_CRS_ON_TX: u16 = 1 << 15;
pub const I82577_PHY_CFG_ENABLE_DOWNSHIFT: u16 = (1 << 10) + (1 << 11);

// 82580 specific PHY registers
pub const I82580_ADDR_REG: u32 = 16;
pub const I82580_CFG_REG: u32 = 22;
pub const I82580_CFG_ASSERT_CRS_ON_TX: u16 = 1 << 15;
pub const I82580_CFG_ENABLE_DOWNSHIFT: u16 = 3 << 10; // auto downshift 100/10
pub const I82580_CTRL_REG: u32 = 23;
pub const I82580_CTRL_DOWNSHIFT_MASK: u16 = 7 << 10;

// Realtek 8169S/8110S gigE PHY registers

// RTL8211B(L)/RTL8211C(L)
pub const RGEPHY_CR: u32 = 0x10; // PHY Specific Control
pub const RGEPHY_CR_ASSERT_CRS: u16 = 0x0800;
pub const RGEPHY_CR_FORCE_LINK: u16 = 0x0400;
pub const RGEPHY_CR_MDI_MASK: u16 = 0x0060;
pub const RGEPHY_CR_MDIX_AUTO: u16 = 0x0040;
pub const RGEPHY_CR_MDIX_MANUAL: u16 = 0x0020;
pub const RGEPHY_CR_MDI_MANUAL: u16 = 0x0000;
pub const RGEPHY_CR_CLK125_DIS: u16 = 0x0010;
pub const RGEPHY_CR_ALDPS: u16 = 0x0004; // RTL8251 only
pub const RGEPHY_CR_JABBER_DIS: u16 = 0x0001;

// RTL8211B(L)/RTL8211C(L)
pub const RGEPHY_SR: u32 = 0x11; // PHY Specific Status
pub const RGEPHY_SR_SPEED_1000MBPS: u16 = 0x8000;
pub const RGEPHY_SR_SPEED_100MBPS: u16 = 0x4000;
pub const RGEPHY_SR_SPEED_10MBPS: u16 = 0x0000;
pub const RGEPHY_SR_SPEED_MASK: u16 = 0xc000;
pub const RGEPHY_SR_FDX: u16 = 0x2000; // full duplex
pub const RGEPHY_SR_PAGE_RECEIVED: u16 = 0x1000; // new page received
pub const RGEPHY_SR_SPD_DPLX_RESOLVED: u16 = 0x0800; // speed/duplex resolved
pub const RGEPHY_SR_LINK: u16 = 0x0400; // link up
pub const RGEPHY_SR_MDI_XOVER: u16 = 0x0040; // MDI crossover
pub const RGEPHY_SR_ALDPS: u16 = 0x0008; // RTL8211C(L) only
pub const RGEPHY_SR_JABBER: u16 = 0x0001; // Jabber

// pub const RGEPHY_SR_SPEED(X)              ((X) & RGEPHY_SR_SPEED_MASK)

// RTL8211F
pub const RGEPHY_F_SR: u32 = 0x1A; // PHY Specific Status
pub const RGEPHY_F_SR_SPEED_1000MBPS: u16 = 0x0020;
pub const RGEPHY_F_SR_SPEED_100MBPS: u16 = 0x0010;
pub const RGEPHY_F_SR_SPEED_10MBPS: u16 = 0x0000;
pub const RGEPHY_F_SR_SPEED_MASK: u16 = 0x0030;
pub const RGEPHY_F_SR_FDX: u16 = 0x0008;
pub const RGEPHY_F_SR_LINK: u16 = 0x0004;

// pub const RGEPHY_F_SR_SPEED(X)            ((X) & RGEPHY_F_SR_SPEED_MASK)

pub const RGEPHY_LC: u32 = 0x18; // PHY LED Control Register
pub const RGEPHY_LC_P2: u32 = 0x1A; // PHY LED Control Register, Page 2
pub const RGEPHY_LC_DISABLE: u16 = 0x8000; // disable leds

// Led pusle strething
pub const RGEPHY_LC_PULSE_1_3S: u16 = 0x7000;
pub const RGEPHY_LC_PULSE_670MS: u16 = 0x6000;
pub const RGEPHY_LC_PULSE_340MS: u16 = 0x5000;
pub const RGEPHY_LC_PULSE_170MS: u16 = 0x4000;
pub const RGEPHY_LC_PULSE_84MS: u16 = 0x3000;
pub const RGEPHY_LC_PULSE_42MS: u16 = 0x2000;
pub const RGEPHY_LC_PULSE_21MS: u16 = 0x1000;
pub const RGEPHY_LC_PULSE_0MS: u16 = 0x0000;
pub const RGEPHY_LC_LINK: u16 = 0x0008; // Link and speed indicated by combination of leds
pub const RGEPHY_LC_DUPLEX: u16 = 0x0004;
pub const RGEPHY_LC_RX: u16 = 0x0002;
pub const RGEPHY_LC_TX: u16 = 0x0001;

pub const RGEPHY_PS: u32 = 0x1F; // Page Select Register
pub const RGEPHY_PS_PAGE_0: u16 = 0x0000;
pub const RGEPHY_PS_PAGE_1: u16 = 0x0001;
pub const RGEPHY_PS_PAGE_2: u16 = 0x0002;
pub const RGEPHY_PS_PAGE_3: u16 = 0x0003;
pub const RGEPHY_PS_PAGE_4: u16 = 0x0004;

// RTL8211F
pub const RGEPHY_PS_PAGE_MII: u32 = 0x0d08;
pub const RGEPHY_MIICR1: u16 = 0x11;
pub const RGEPHY_MIICR1_TXDLY_EN: u16 = 0x0100;
pub const RGEPHY_MIICR2: u16 = 0x15;
pub const RGEPHY_MIICR2_RXDLY_EN: u16 = 0x0008;
