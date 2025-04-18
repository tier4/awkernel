// General Register Descriptions
pub(super) const IGC_CTRL: usize = 0x00000; // Device Control - RW
pub(super) const IGC_STATUS: usize = 0x00008; // Device Status - RO
pub(super) const IGC_EECD: usize = 0x00010; // EEPROM/Flash Control - RW

// NVM  Register Descriptions
pub(super) const IGC_EERD: usize = 0x12014; // EEprom mode read - RW
pub(super) const IGC_EEWR: usize = 0x12018; // EEprom mode write - RW
pub(super) const IGC_CTRL_EXT: usize = 0x00018; // Extended Device Control - RW
pub(super) const IGC_MDIC: usize = 0x00020; // MDI Control - RW
pub(super) const IGC_MDICNFG: usize = 0x00E04; // MDI Config - RW
pub(super) const IGC_FCAL: usize = 0x00028; // Flow Control Address Low - RW
pub(super) const IGC_FCAH: usize = 0x0002C; // Flow Control Address High -RW
pub(super) const IGC_I225_FLSWCTL: usize = 0x12048; // FLASH control register
pub(super) const IGC_I225_FLSWDATA: usize = 0x1204C; // FLASH data register
pub(super) const IGC_I225_FLSWCNT: usize = 0x12050; // FLASH Access Counter
pub(super) const IGC_I225_FLSECU: usize = 0x12114; // FLASH Security
pub(super) const IGC_FCT: usize = 0x00030; // Flow Control Type - RW
pub(super) const IGC_CONNSW: usize = 0x00034; // Copper/Fiber switch control - RW
pub(super) const IGC_VET: usize = 0x00038; // VLAN Ether Type - RW
pub(super) const IGC_ICR: usize = 0x01500; // Intr Cause Read - RC/W1C
pub(super) const IGC_ITR: usize = 0x000C4; // Interrupt Throttling Rate - RW
pub(super) const IGC_ICS: usize = 0x01504; // Intr Cause Set - WO
pub(super) const IGC_IMS: usize = 0x01508; // Intr Mask Set/Read - RW
pub(super) const IGC_IMC: usize = 0x0150C; // Intr Mask Clear - WO
pub(super) const IGC_IAM: usize = 0x01510; // Intr Ack Auto Mask- RW
pub(super) const IGC_RCTL: usize = 0x00100; // Rx Control - RW
pub(super) const IGC_FCTTV: usize = 0x00170; // Flow Control Transmit Timer Value
pub(super) const IGC_TXCW: usize = 0x00178; // Tx Configuration Word - RW
pub(super) const IGC_RXCW: usize = 0x00180; // Rx Configuration Word - RO
pub(super) const IGC_EICR: usize = 0x01580; // Ext. Interrupt Cause Read - R/clr
pub(super) const IGC_EITR: fn(usize) -> usize = |n| 0x01680 + (0x4 * n);
pub(super) const IGC_EICS: usize = 0x01520; // Ext. Interrupt Cause Set - W0
pub(super) const IGC_EIMS: usize = 0x01524; // Ext. Interrupt Mask Set/Read - RW
pub(super) const IGC_EIMC: usize = 0x01528; // Ext. Interrupt Mask Clear - WO
pub(super) const IGC_EIAC: usize = 0x0152C; // Ext. Interrupt Auto Clear - RW
pub(super) const IGC_EIAM: usize = 0x01530; // Ext. Interrupt Ack Auto Clear Mask
pub(super) const IGC_GPIE: usize = 0x01514; // General Purpose Interrupt Enable - RW
pub(super) const IGC_IVAR0: usize = 0x01700; // Interrupt Vector Allocation (array) - RW
pub(super) const IGC_IVAR_MISC: usize = 0x01740; // IVAR for "other" causes - RW
pub(super) const IGC_TCTL: usize = 0x00400; // Tx Control - RW
pub(super) const IGC_TCTL_EXT: usize = 0x00404; // Extended Tx Control - RW
pub(super) const IGC_TIPG: usize = 0x00410; // Tx Inter-packet gap -RW
pub(super) const IGC_AIT: usize = 0x00458; // Adaptive Interframe Spacing Throttle - RW
pub(super) const IGC_LEDCTL: usize = 0x00E00; // LED Control - RW
pub(super) const IGC_LEDMUX: usize = 0x08130; // LED MUX Control
pub(super) const IGC_EXTCNF_CTRL: usize = 0x00F00; // Extended Configuration Control
pub(super) const IGC_EXTCNF_SIZE: usize = 0x00F08; // Extended Configuration Size
pub(super) const IGC_PHY_CTRL: usize = 0x00F10; // PHY Control Register in CSR
pub(super) const IGC_PBA: usize = 0x01000; // Packet Buffer Allocation - RW
pub(super) const IGC_PBS: usize = 0x01008; // Packet Buffer Size
pub(super) const IGC_EEMNGCTL: usize = 0x01010; // MNG EEprom Control
pub(super) const IGC_EEMNGCTL_I225: usize = 0x01010; // i225 MNG EEprom Mode Control
pub(super) const IGC_EEARBC_I225: usize = 0x12024; // EEPROM Auto Read Bus Control
pub(super) const IGC_FLOP: usize = 0x0103C; // FLASH Opcode Register
pub(super) const IGC_WDSTP: usize = 0x01040; // Watchdog Setup - RW
pub(super) const IGC_SWDSTS: usize = 0x01044; // SW Device Status - RW
pub(super) const IGC_FRTIMER: usize = 0x01048; // Free Running Timer - RW
pub(super) const IGC_TCPTIMER: usize = 0x0104C; // TCP Timer - RW
pub(super) const IGC_ERT: usize = 0x02008; // Early Rx Threshold - RW
pub(super) const IGC_FCRTL: usize = 0x02160; // Flow Control Receive Threshold Low - RW
pub(super) const IGC_FCRTH: usize = 0x02168; // Flow Control Receive Threshold High - RW
pub(super) const IGC_PSRCTL: usize = 0x02170; // Packet Split Receive Control - RW
pub(super) const IGC_RDFH: usize = 0x02410; // Rx Data FIFO Head - RW
pub(super) const IGC_RDFT: usize = 0x02418; // Rx Data FIFO Tail - RW
pub(super) const IGC_RDFHS: usize = 0x02420; // Rx Data FIFO Head Saved - RW
pub(super) const IGC_RDFTS: usize = 0x02428; // Rx Data FIFO Tail Saved - RW
pub(super) const IGC_RDFPC: usize = 0x02430; // Rx Data FIFO Packet Count - RW
pub(super) const IGC_PBRTH: usize = 0x02458; // PB Rx Arbitration Threshold - RW
pub(super) const IGC_FCRTV: usize = 0x02460; // Flow Control Refresh Timer Value - RW

// Shadow Ram Write Register - RW
pub(super) const IGC_SRWR: usize = 0x12018;

pub(super) const IGC_MMDAC: u32 = 13; // MMD Access Control
pub(super) const IGC_MMDAAD: u32 = 14; // MMD Access Address/Data

// Convenience macros
//
// Example usage:
// IGC_RDBAL_REG(current_rx_queue)
pub(super) const IGC_RDBAL: fn(usize) -> usize = |n| {
    if n < 4 {
        0x02800 + (n * 0x100)
    } else {
        0x0C000 + (n * 0x40)
    }
};
pub(super) const IGC_RDBAH: fn(usize) -> usize = |n| {
    if n < 4 {
        0x02804 + (n * 0x100)
    } else {
        0x0C004 + (n * 0x40)
    }
};
pub(super) const IGC_RDLEN: fn(usize) -> usize = |n| {
    if n < 4 {
        0x02808 + (n * 0x100)
    } else {
        0x0C008 + (n * 0x40)
    }
};
pub(super) const IGC_SRRCTL: fn(usize) -> usize = |n| {
    if n < 4 {
        0x0280C + (n * 0x100)
    } else {
        0x0C00C + (n * 0x40)
    }
};
pub(super) const IGC_RDH: fn(usize) -> usize = |n| {
    if n < 4 {
        0x02810 + (n * 0x100)
    } else {
        0x0C010 + (n * 0x40)
    }
};
pub(super) const IGC_RDT: fn(usize) -> usize = |n| {
    if n < 4 {
        0x02818 + (n * 0x100)
    } else {
        0x0C018 + (n * 0x40)
    }
};
pub(super) const IGC_RXDCTL: fn(usize) -> usize = |n| {
    if n < 4 {
        0x02828 + (n * 0x100)
    } else {
        0x0C028 + (n * 0x40)
    }
};
pub(super) const IGC_RQDPC: fn(usize) -> usize = |n| {
    if n < 4 {
        0x02830 + (n * 0x100)
    } else {
        0x0C030 + (n * 0x40)
    }
};
pub(super) const IGC_TDBAL: fn(usize) -> usize = |n| {
    if n < 4 {
        0x03800 + (n * 0x100)
    } else {
        0x0E000 + (n * 0x40)
    }
};
pub(super) const IGC_TDBAH: fn(usize) -> usize = |n| {
    if n < 4 {
        0x03804 + (n * 0x100)
    } else {
        0x0E004 + (n * 0x40)
    }
};
pub(super) const IGC_TDLEN: fn(usize) -> usize = |n| {
    if n < 4 {
        0x03808 + (n * 0x100)
    } else {
        0x0E008 + (n * 0x40)
    }
};
pub(super) const IGC_TDH: fn(usize) -> usize = |n| {
    if n < 4 {
        0x03810 + (n * 0x100)
    } else {
        0x0E010 + (n * 0x40)
    }
};
pub(super) const IGC_TDT: fn(usize) -> usize = |n| {
    if n < 4 {
        0x03818 + (n * 0x100)
    } else {
        0x0E018 + (n * 0x40)
    }
};
pub(super) const IGC_TXDCTL: fn(usize) -> usize = |n| {
    if n < 4 {
        0x03828 + (n * 0x100)
    } else {
        0x0E028 + (n * 0x40)
    }
};
pub(super) const IGC_TARC: fn(usize) -> usize = |n| 0x03840 + (n * 0x100);
pub(super) const IGC_RSRPD: usize = 0x02C00; // Rx Small Packet Detect - RW
pub(super) const IGC_RAID: usize = 0x02C08; // Receive Ack Interrupt Delay - RW
pub(super) const IGC_KABGTXD: usize = 0x03004; // AFE Band Gap Transmit Ref Data
pub(super) const IGC_PSRTYPE: fn(usize) -> usize = |i| 0x05480 + (i * 4);
pub(super) const IGC_RAL: fn(usize) -> usize = |i| {
    if i <= 15 {
        0x05400 + (i * 8)
    } else {
        0x054E0 + ((i - 16) * 8)
    }
};
pub(super) const IGC_RAH: fn(usize) -> usize = |i| {
    if i <= 15 {
        0x05404 + (i * 8)
    } else {
        0x054E4 + ((i - 16) * 8)
    }
};

// Statistics Register Descriptions
pub(super) const IGC_CRCERRS: usize = 0x04000; // CRC Error Count - R/clr
pub(super) const IGC_ALGNERRC: usize = 0x04004; // Alignment Error Count - R/clr
pub(super) const IGC_MPC: usize = 0x04010; // Missed Packet Count - R/clr
pub(super) const IGC_SCC: usize = 0x04014; // Single Collision Count - R/clr
pub(super) const IGC_ECOL: usize = 0x04018; // Excessive Collision Count - R/clr
pub(super) const IGC_MCC: usize = 0x0401C; // Multiple Collision Count - R/clr
pub(super) const IGC_LATECOL: usize = 0x04020; // Late Collision Count - R/clr
pub(super) const IGC_COLC: usize = 0x04028; // Collision Count - R/clr
pub(super) const IGC_RERC: usize = 0x0402C; // Receive Error Count - R/clr
pub(super) const IGC_DC: usize = 0x04030; // Defer Count - R/clr
pub(super) const IGC_TNCRS: usize = 0x04034; // Tx-No CRS - R/clr
pub(super) const IGC_HTDPMC: usize = 0x0403C; // Host Transmit Discarded by MAC - R/clr
pub(super) const IGC_RLEC: usize = 0x04040; // Receive Length Error Count - R/clr
pub(super) const IGC_XONRXC: usize = 0x04048; // XON Rx Count - R/clr
pub(super) const IGC_XONTXC: usize = 0x0404C; // XON Tx Count - R/clr
pub(super) const IGC_XOFFRXC: usize = 0x04050; // XOFF Rx Count - R/clr
pub(super) const IGC_XOFFTXC: usize = 0x04054; // XOFF Tx Count - R/clr
pub(super) const IGC_FCRUC: usize = 0x04058; // Flow Control Rx Unsupported Count- R/clr
pub(super) const IGC_PRC64: usize = 0x0405C; // Packets Rx (64 bytes) - R/clr
pub(super) const IGC_PRC127: usize = 0x04060; // Packets Rx (65-127 bytes) - R/clr
pub(super) const IGC_PRC255: usize = 0x04064; // Packets Rx (128-255 bytes) - R/clr
pub(super) const IGC_PRC511: usize = 0x04068; // Packets Rx (255-511 bytes) - R/clr
pub(super) const IGC_PRC1023: usize = 0x0406C; // Packets Rx (512-1023 bytes) - R/clr
pub(super) const IGC_PRC1522: usize = 0x04070; // Packets Rx (1024-1522 bytes) - R/clr
pub(super) const IGC_GPRC: usize = 0x04074; // Good Packets Rx Count - R/clr
pub(super) const IGC_BPRC: usize = 0x04078; // Broadcast Packets Rx Count - R/clr
pub(super) const IGC_MPRC: usize = 0x0407C; // Multicast Packets Rx Count - R/clr
pub(super) const IGC_GPTC: usize = 0x04080; // Good Packets Tx Count - R/clr
pub(super) const IGC_GORCL: usize = 0x04088; // Good Octets Rx Count Low - R/clr
pub(super) const IGC_GORCH: usize = 0x0408C; // Good Octets Rx Count High - R/clr
pub(super) const IGC_GOTCL: usize = 0x04090; // Good Octets Tx Count Low - R/clr
pub(super) const IGC_GOTCH: usize = 0x04094; // Good Octets Tx Count High - R/clr
pub(super) const IGC_RNBC: usize = 0x040A0; // Rx No Buffers Count - R/clr
pub(super) const IGC_RUC: usize = 0x040A4; // Rx Undersize Count - R/clr
pub(super) const IGC_RFC: usize = 0x040A8; // Rx Fragment Count - R/clr
pub(super) const IGC_ROC: usize = 0x040AC; // Rx Oversize Count - R/clr
pub(super) const IGC_RJC: usize = 0x040B0; // Rx Jabber Count - R/clr
pub(super) const IGC_MGTPRC: usize = 0x040B4; // Management Packets Rx Count - R/clr
pub(super) const IGC_MGTPDC: usize = 0x040B8; // Management Packets Dropped Count - R/clr
pub(super) const IGC_MGTPTC: usize = 0x040BC; // Management Packets Tx Count - R/clr
pub(super) const IGC_TORL: usize = 0x040C0; // Total Octets Rx Low - R/clr
pub(super) const IGC_TORH: usize = 0x040C4; // Total Octets Rx High - R/clr
pub(super) const IGC_TOTL: usize = 0x040C8; // Total Octets Tx Low - R/clr
pub(super) const IGC_TOTH: usize = 0x040CC; // Total Octets Tx High - R/clr
pub(super) const IGC_TPR: usize = 0x040D0; // Total Packets Rx - R/clr
pub(super) const IGC_TPT: usize = 0x040D4; // Total Packets Tx - R/clr
pub(super) const IGC_PTC64: usize = 0x040D8; // Packets Tx (64 bytes) - R/clr
pub(super) const IGC_PTC127: usize = 0x040DC; // Packets Tx (65-127 bytes) - R/clr
pub(super) const IGC_PTC255: usize = 0x040E0; // Packets Tx (128-255 bytes) - R/clr
pub(super) const IGC_PTC511: usize = 0x040E4; // Packets Tx (256-511 bytes) - R/clr
pub(super) const IGC_PTC1023: usize = 0x040E8; // Packets Tx (512-1023 bytes) - R/clr
pub(super) const IGC_PTC1522: usize = 0x040EC; // Packets Tx (1024-1522 Bytes) - R/clr
pub(super) const IGC_MPTC: usize = 0x040F0; // Multicast Packets Tx Count - R/clr
pub(super) const IGC_BPTC: usize = 0x040F4; // Broadcast Packets Tx Count - R/clr
pub(super) const IGC_TSCTC: usize = 0x040F8; // TCP Segmentation Context Tx - R/clr
pub(super) const IGC_IAC: usize = 0x04100; // Interrupt Assertion Count
pub(super) const IGC_RXDMTC: usize = 0x04120; // Rx Descriptor Minimum Threshold Count

pub(super) const IGC_VFGPRC: usize = 0x00F10;
pub(super) const IGC_VFGORC: usize = 0x00F18;
pub(super) const IGC_VFMPRC: usize = 0x00F3C;
pub(super) const IGC_VFGPTC: usize = 0x00F14;
pub(super) const IGC_VFGOTC: usize = 0x00F34;
pub(super) const IGC_VFGOTLBC: usize = 0x00F50;
pub(super) const IGC_VFGPTLBC: usize = 0x00F44;
pub(super) const IGC_VFGORLBC: usize = 0x00F48;
pub(super) const IGC_VFGPRLBC: usize = 0x00F40;
pub(super) const IGC_HGORCL: usize = 0x04128; // Host Good Octets Received Count Low
pub(super) const IGC_HGORCH: usize = 0x0412C; // Host Good Octets Received Count High
pub(super) const IGC_HGOTCL: usize = 0x04130; // Host Good Octets Transmit Count Low
pub(super) const IGC_HGOTCH: usize = 0x04134; // Host Good Octets Transmit Count High
pub(super) const IGC_LENERRS: usize = 0x04138; // Length Errors Count
pub(super) const IGC_PCS_ANADV: usize = 0x04218; // AN advertisement - RW
pub(super) const IGC_PCS_LPAB: usize = 0x0421C; // Link Partner Ability - RW
pub(super) const IGC_RXCSUM: usize = 0x05000; // Rx Checksum Control - RW
pub(super) const IGC_RLPML: usize = 0x05004; // Rx Long Packet Max Length
pub(super) const IGC_RFCTL: usize = 0x05008; // Receive Filter Control
pub(super) const IGC_MTA: usize = 0x05200; // Multicast Table Array - RW Array
pub(super) const IGC_RA: usize = 0x05400; // Receive Address - RW Array
pub(super) const IGC_VFTA: usize = 0x05600; // VLAN Filter Table Array - RW Array
pub(super) const IGC_WUC: usize = 0x05800; // Wakeup Control - RW
pub(super) const IGC_WUFC: usize = 0x05808; // Wakeup Filter Control - RW
pub(super) const IGC_WUS: usize = 0x05810; // Wakeup Status - RO

// Management registers
pub(super) const IGC_MANC: usize = 0x05820; // Management Control - RW

// Semaphore registers
pub(super) const IGC_SW_FW_SYNC: usize = 0x05B5C; // SW-FW Synchronization - RW

// Function Active and Power State to MNG
pub(super) const IGC_FACTPS: usize = 0x05B30;
pub(super) const IGC_SWSM: usize = 0x05B50; // SW Semaphore
pub(super) const IGC_FWSM: usize = 0x05B54; // FW Semaphore
