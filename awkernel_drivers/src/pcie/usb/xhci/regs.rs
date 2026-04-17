/// Capability Register offsets — relative to BAR[0]. xHCI spec §5.3.
pub mod cap {
    pub const CAPLENGTH: usize = 0x00; // u8  — byte length of this register set
    pub const HCIVERSION: usize = 0x02; // u16 — BCD-encoded xHCI version
    pub const HCSPARAMS1: usize = 0x04; // u32 — MaxSlots[7:0], MaxIntrs[18:8], MaxPorts[31:24]
    pub const HCSPARAMS2: usize = 0x08; // u32 — IST, ERST_Max, scratchpad counts
    pub const HCSPARAMS3: usize = 0x0C; // u32 — U1/U2 exit latencies
    pub const HCCPARAMS1: usize = 0x10; // u32 — AC64, CSZ, xECP pointer, …
    pub const DBOFF: usize = 0x14; // u32 — Doorbell Array offset from BAR[0]
    pub const RTSOFF: usize = 0x18; // u32 — Runtime Registers offset from BAR[0]
    pub const HCCPARAMS2: usize = 0x1C; // u32
}

/// Operational Register offsets — relative to `op_base` (= BAR[0] + CAPLENGTH). xHCI spec §5.4.
pub mod op {
    pub const USBCMD: usize = 0x00;
    pub const USBSTS: usize = 0x04;
    pub const PAGESIZE: usize = 0x08;
    pub const DNCTRL: usize = 0x14;
    pub const CRCR_LO: usize = 0x18; // Command Ring Control Register (low 32 bits)
    pub const CRCR_HI: usize = 0x1C;
    pub const DCBAAP_LO: usize = 0x30; // Device Context Base Address Array Pointer (low 32 bits)
    pub const DCBAAP_HI: usize = 0x34;
    pub const CONFIG: usize = 0x38; // MaxSlotsEn[7:0]

    // USBCMD bits
    pub const CMD_RUN_STOP: u32 = 1 << 0;
    pub const CMD_HCRST: u32 = 1 << 1; // Host Controller Reset
    pub const CMD_INTE: u32 = 1 << 2; // Interrupter Enable
    pub const CMD_HSEE: u32 = 1 << 3; // Host System Error Enable

    // USBSTS bits
    pub const STS_HCH: u32 = 1 << 0; // HCHalted — set when Run/Stop = 0 and controller has stopped
    pub const STS_HSE: u32 = 1 << 2; // Host System Error
    pub const STS_EINT: u32 = 1 << 3; // Event Interrupt
    pub const STS_PCD: u32 = 1 << 4; // Port Change Detect
    pub const STS_CNR: u32 = 1 << 11; // Controller Not Ready (set during reset)

    // CRCR bits (written to low word; high bits are ring base address)
    pub const CRCR_RCS: u32 = 1 << 0; // Ring Cycle State
    pub const CRCR_CS: u32 = 1 << 1; // Command Stop
    pub const CRCR_CA: u32 = 1 << 2; // Command Abort
}

/// Interrupter Register Set offsets — relative to `ir0_base` (= rt_base + BASE). xHCI spec §5.5.2.
pub mod ir {
    /// Offset of Interrupter Register Set 0 from the Runtime Register base.
    pub const BASE: usize = 0x20;
    pub const IMAN: usize = 0x00; // Interrupter Management — IP[0], IE[1]
    pub const IMOD: usize = 0x04; // Interrupter Moderation
    pub const ERSTSZ: usize = 0x08; // Event Ring Segment Table Size
    pub const ERSTBA_LO: usize = 0x10; // Event Ring Segment Table Base Address (low)
    pub const ERSTBA_HI: usize = 0x14;
    pub const ERDP_LO: usize = 0x18; // Event Ring Dequeue Pointer (low)
    pub const ERDP_HI: usize = 0x1C;

    pub const IMAN_IP: u32 = 1 << 0; // Interrupt Pending (write-1-to-clear)
    pub const IMAN_IE: u32 = 1 << 1; // Interrupt Enable
    pub const ERDP_EHB: u32 = 1 << 3; // Event Handler Busy (write-1-to-clear)
}

/// TRB type codes placed in ctrl[15:10]. xHCI spec §6.4.6 Table 139.
pub mod trb_type {
    pub const NORMAL: u32 = 1;
    pub const SETUP_STAGE: u32 = 2;
    pub const DATA_STAGE: u32 = 3;
    pub const STATUS_STAGE: u32 = 4;
    pub const LINK: u32 = 6;
    pub const NOOP: u32 = 8;
    pub const ENABLE_SLOT: u32 = 9;
    pub const DISABLE_SLOT: u32 = 10;
    pub const ADDRESS_DEVICE: u32 = 11;
    pub const CONFIGURE_EP: u32 = 12;
    pub const EVALUATE_CONTEXT: u32 = 13;
    pub const RESET_EP: u32 = 14;
    pub const STOP_EP: u32 = 15;
    pub const NOOP_CMD: u32 = 23;
    pub const TRANSFER_EVENT: u32 = 32;
    pub const CMD_COMPLETION: u32 = 33;
    pub const PORT_STATUS_CHANGE: u32 = 34;
}

/// Port Status and Control Register offsets — relative to op_base. xHCI spec §5.4.8.
/// Port n (1-based) is at BASE + (n-1) * STRIDE.
pub mod port {
    pub const BASE: usize = 0x400;
    pub const STRIDE: usize = 0x10;

    pub const CCS: u32 = 1 << 0;  // Current Connect Status (RO)
    pub const PED: u32 = 1 << 1;  // Port Enabled/Disabled (RW1C — write 1 to disable)
    pub const PR: u32 = 1 << 4;   // Port Reset (RWS)
    pub const PP: u32 = 1 << 9;   // Port Power (RWS)
    pub const CSC: u32 = 1 << 17; // Connect Status Change (RW1CS)
    pub const PEC: u32 = 1 << 18; // Port Enabled/Disabled Change (RW1CS)
    pub const WRC: u32 = 1 << 19; // Warm Port Reset Change (RW1CS)
    pub const OCC: u32 = 1 << 20; // Over-current Change (RW1CS)
    pub const PRC: u32 = 1 << 21; // Port Reset Change (RW1CS)
    pub const PLC: u32 = 1 << 22; // Port Link State Change (RW1CS)
    pub const CEC: u32 = 1 << 23; // Port Config Error Change (RW1CS)

    /// All RW1CS change bits.
    pub const CHANGE_BITS: u32 = CSC | PEC | WRC | OCC | PRC | PLC | CEC;
}

/// Bit position of the TRB type field within the ctrl word.
pub const TRB_TYPE_SHIFT: u32 = 10;

/// Cycle Bit — bit 0 of TRB ctrl field.
pub const TRB_CYCLE: u32 = 1 << 0;

/// Toggle Cycle — bit 1 of Link TRB ctrl field. Flips Ring Cycle State when traversed.
pub const TRB_LINK_TC: u32 = 1 << 1;
