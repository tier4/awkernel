pub const DEFAULT_TXD: usize = 256;
pub const DEFAULT_RXD: usize = 256;

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
pub const IXGBE_EITR_ITR_INT_MASK: usize = 0x00000FF8;
pub const IXGBE_EITR_LLI_MOD: usize = 0x00008000;
pub const IXGBE_EITR_CNT_WDIS: usize = 0x80000000;
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
pub const IXGBE_VFTA: fn(u32) -> u32 = |i| 0x0A000 + (i * 4);
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

pub const IXGBE_PFDTXGSWC_VT_LBEN: usize = 0x1; // Local L2 VT switch enable

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
pub const IXGBE_FWSM_TS_ENABLED: usize = 0x1;
pub const IXGBE_FWSM_FW_MODE_PT: usize = 0x4;

// ARC Subsystem registers
pub const IXGBE_HICR: usize = 0x15F00;
pub const IXGBE_FWSTS: usize = 0x15F0C;
pub const IXGBE_HSMC0R: usize = 0x15F04;
pub const IXGBE_HSMC1R: usize = 0x15F08;
pub const IXGBE_SWSR: usize = 0x15F10;
pub const IXGBE_HFDR: usize = 0x15FE8;
pub const IXGBE_FLEX_MNG: usize = 0x15800; /* 0x15800 - 0x15EFC */

pub const IXGBE_HICR_EN: usize = 0x01; /* Enable bit - RO */
// Driver sets this bit when done to put command in RAM
pub const IXGBE_HICR_C: usize = 0x02;
pub const IXGBE_HICR_SV: usize = 0x04; /* Status Validity */
pub const IXGBE_HICR_FW_RESET_ENABLE: usize = 0x40;
pub const IXGBE_HICR_FW_RESET: usize = 0x80;

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
pub const IXGBE_FACTPS_MNGCG: usize = 0x20000000; // Manageability Clock Gated
pub const IXGBE_FACTPS_LFS: usize = 0x40000000; // LAN Function Select

// MHADD Bit Masks
pub const IXGBE_MHADD_MFS_MASK: usize = 0xFFFF0000;
pub const IXGBE_MHADD_MFS_SHIFT: usize = 16;

// Extended Device Control
pub const IXGBE_CTRL_EXT_PFRSTD: usize = 0x00004000; // Physical Function Reset Done
pub const IXGBE_CTRL_EXT_NS_DIS: usize = 0x00010000; // No Snoop disable
pub const IXGBE_CTRL_EXT_RO_DIS: usize = 0x00020000; // Relaxed Ordering disable
pub const IXGBE_CTRL_EXT_DRV_LOAD: usize = 0x10000000; // Driver loaded bit for FW

// Direct Cache Access (DCA) definitions
pub const IXGBE_DCA_CTRL_DCA_ENABLE: usize = 0x00000000; // DCA Enable
pub const IXGBE_DCA_CTRL_DCA_DISABLE: usize = 0x00000001; // DCA Disable

pub const IXGBE_DCA_CTRL_DCA_MODE_CB1: usize = 0x00; // DCA Mode CB1
pub const IXGBE_DCA_CTRL_DCA_MODE_CB2: usize = 0x02; // DCA Mode CB2

pub const IXGBE_DCA_RXCTRL_CPUID_MASK: usize = 0x0000001F; // Rx CPUID Mask
pub const IXGBE_DCA_RXCTRL_CPUID_MASK_82599: usize = 0xFF000000; // Rx CPUID Mask
pub const IXGBE_DCA_RXCTRL_CPUID_SHIFT_82599: usize = 24; // Rx CPUID Shift
pub const IXGBE_DCA_RXCTRL_DESC_DCA_EN: usize = 1 << 5; // Rx Desc enable
pub const IXGBE_DCA_RXCTRL_HEAD_DCA_EN: usize = 1 << 6; // Rx Desc header enable
pub const IXGBE_DCA_RXCTRL_DATA_DCA_EN: usize = 1 << 7; // Rx Desc payload enable
pub const IXGBE_DCA_RXCTRL_DESC_RRO_EN: usize = 1 << 9; // Rx read Desc Relax Order
pub const IXGBE_DCA_RXCTRL_DATA_WRO_EN: usize = 1 << 13; // Rx write data Relax Order
pub const IXGBE_DCA_RXCTRL_HEAD_WRO_EN: usize = 1 << 15; // Rx write header RO

pub const IXGBE_DCA_TXCTRL_CPUID_MASK: usize = 0x0000001F; // Tx CPUID Mask
pub const IXGBE_DCA_TXCTRL_CPUID_MASK_82599: usize = 0xFF000000; // Tx CPUID Mask
pub const IXGBE_DCA_TXCTRL_CPUID_SHIFT_82599: usize = 24; // Tx CPUID Shift
pub const IXGBE_DCA_TXCTRL_DESC_DCA_EN: usize = 1 << 5; // DCA Tx Desc enable
pub const IXGBE_DCA_TXCTRL_DESC_RRO_EN: usize = 1 << 9; // Tx read Desc Relax Order
pub const IXGBE_DCA_TXCTRL_DESC_WRO_EN: usize = 1 << 11; // Tx Desc writeback RO bit
pub const IXGBE_DCA_TXCTRL_DATA_RRO_EN: usize = 1 << 13; // Tx read data Relax Order

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
pub const IXGBE_MII_10GBASE_T_ADVERTISE: u32 = 0x1000; // full duplex, bit:12
pub const IXGBE_MII_1GBASE_T_ADVERTISE_XNP_TX: u32 = 0x4000; // full duplex, bit:14
pub const IXGBE_MII_1GBASE_T_ADVERTISE: u32 = 0x8000; // full duplex, bit:15
pub const IXGBE_MII_2_5GBASE_T_ADVERTISE: u32 = 0x0400;
pub const IXGBE_MII_5GBASE_T_ADVERTISE: u32 = 0x0800;
pub const IXGBE_MII_100BASE_T_ADVERTISE: u32 = 0x0100; // full duplex, bit:8
pub const IXGBE_MII_100BASE_T_ADVERTISE_HALF: u32 = 0x0080; // half duplex, bit:7
pub const IXGBE_MII_RESTART: u32 = 0x200;
pub const IXGBE_MII_AUTONEG_COMPLETE: u32 = 0x20;
pub const IXGBE_MII_AUTONEG_LINK_UP: u32 = 0x04;
pub const IXGBE_MII_AUTONEG_REG: u32 = 0x0;

pub const IXGBE_PHY_REVISION_MASK: u32 = 0xFFFFFFF0;
pub const IXGBE_MAX_PHY_ADDR: u32 = 32;

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
pub const IXGBE_IVAR_TCP_TIMER_INDEX: u32 = 96; // 0 based index
pub const IXGBE_IVAR_OTHER_CAUSES_INDEX: u32 = 97; // 0 based index
pub fn ixgbe_msix_vector(i: u32) -> u32 {
    0 + i
}
pub const IXGBE_IVAR_ALLOC_VAL: u32 = 0x80; // Interrupt Allocation valid

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
pub const IXGBE_EEPROM_WORD_SIZE_SHIFT: u32 = 6;
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

pub const IXGBE_SAN_MAC_ADDR_PTR: u32 = 0x28;
pub const IXGBE_DEVICE_CAPS: u32 = 0x2C;
pub const IXGBE_82599_SERIAL_NUMBER_MAC_ADDR: u32 = 0x11;
pub const IXGBE_X550_SERIAL_NUMBER_MAC_ADDR: u32 = 0x04;

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

//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
//
pub const IXGBE_FLAGS_DOUBLE_RESET_REQUIRED: u8 = 0x01;
