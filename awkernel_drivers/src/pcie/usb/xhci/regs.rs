/// Capability Register offsets — relative to BAR[0]. xHCI spec §5.3.
pub mod cap {
    pub const CAPLENGTH: usize = 0x00; // u8  — byte length of this register set
    pub const HCIVERSION: usize = 0x02; // u16 — BCD-encoded xHCI version
    pub const HCSPARAMS1: usize = 0x04; // u32 — MaxSlots[7:0], MaxIntrs[18:8], MaxPorts[31:24]
    pub const HCSPARAMS2: usize = 0x08; // u32 — IST, ERST_Max, scratchpad counts
    pub const HCCPARAMS1: usize = 0x10; // u32 — AC64, CSZ, xECP pointer, …
    pub const DBOFF: usize = 0x14; // u32 — Doorbell Array offset from BAR[0]
    pub const RTSOFF: usize = 0x18; // u32 — Runtime Registers offset from BAR[0]

    /// HCCPARAMS1.CSZ: 0 = 32-byte contexts, 1 = 64-byte contexts.
    pub const HCC_CSZ: u32 = 1 << 2;
}

/// Operational Register offsets — relative to `op_base` (= BAR[0] + CAPLENGTH). xHCI spec §5.4.
pub mod op {
    pub const USBCMD: usize = 0x00;
    pub const USBSTS: usize = 0x04;
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
    pub const STS_CNR: u32 = 1 << 11; // Controller Not Ready (set during reset)

    // CRCR bits (written to low word; high bits are ring base address)
    pub const CRCR_RCS: u32 = 1 << 0; // Ring Cycle State
}

/// Interrupter Register Set offsets — relative to `ir0_base` (= rt_base + BASE). xHCI spec §5.5.2.
pub mod ir {
    /// Offset of Interrupter Register Set 0 from the Runtime Register base.
    pub const BASE: usize = 0x20;
    pub const IMAN: usize = 0x00; // Interrupter Management — IP[0], IE[1]
    pub const ERSTSZ: usize = 0x08; // Event Ring Segment Table Size
    pub const ERSTBA_LO: usize = 0x10; // Event Ring Segment Table Base Address (low)
    pub const ERSTBA_HI: usize = 0x14;
    pub const ERDP_LO: usize = 0x18; // Event Ring Dequeue Pointer (low)
    pub const ERDP_HI: usize = 0x1C;

    pub const IMAN_IE: u32 = 1 << 1; // Interrupt Enable
    pub const ERDP_EHB: u32 = 1 << 3; // Event Handler Busy (write-1-to-clear)
}

/// Bit position of the TRB type field within the ctrl word.
const TRB_TYPE_SHIFT: u32 = 10;

/// Mask of the TRB type field (ctrl[15:10]).
pub const TRB_TYPE_MASK: u32 = 0x3f << TRB_TYPE_SHIFT;

/// TRB type codes, already shifted into ctrl[15:10]. xHCI spec §6.4.6 Table 139.
pub mod trb_type {
    use super::TRB_TYPE_SHIFT;

    pub const NORMAL: u32 = 1 << TRB_TYPE_SHIFT;
    pub const SETUP_STAGE: u32 = 2 << TRB_TYPE_SHIFT;
    pub const DATA_STAGE: u32 = 3 << TRB_TYPE_SHIFT;
    pub const STATUS_STAGE: u32 = 4 << TRB_TYPE_SHIFT;
    pub const LINK: u32 = 6 << TRB_TYPE_SHIFT;
    pub const ENABLE_SLOT: u32 = 9 << TRB_TYPE_SHIFT;
    pub const ADDRESS_DEVICE: u32 = 11 << TRB_TYPE_SHIFT;
    pub const CONFIGURE_EP: u32 = 12 << TRB_TYPE_SHIFT;
    pub const RESET_EP: u32 = 14 << TRB_TYPE_SHIFT;
    pub const STOP_EP: u32 = 15 << TRB_TYPE_SHIFT;
    pub const SET_TR_DEQUEUE_POINTER: u32 = 16 << TRB_TYPE_SHIFT;
    pub const NOOP_CMD: u32 = 23 << TRB_TYPE_SHIFT;
    pub const TRANSFER_EVENT: u32 = 32 << TRB_TYPE_SHIFT;
    pub const CMD_COMPLETION: u32 = 33 << TRB_TYPE_SHIFT;
}

/// TRB ctrl-word flag bits. xHCI spec §6.4.
pub mod trb_flag {
    /// Cycle Bit — bit 0 of every TRB.
    pub const CYCLE: u32 = 1 << 0;
    /// Link TRB: Toggle Cycle — flips the Ring Cycle State when traversed.
    pub const LINK_TC: u32 = 1 << 1;
    /// Interrupt On Completion.
    pub const IOC: u32 = 1 << 5;
    /// Setup Stage TRB: Immediate Data (setup packet is inside the TRB).
    pub const IDT: u32 = 1 << 6;
    /// Data/Status Stage TRB: direction IN.
    pub const DIR_IN: u32 = 1 << 16;
    /// Setup Stage TRB: Transfer Type = No Data Stage.
    pub const TRT_NO_DATA: u32 = 0 << 16;
    /// Setup Stage TRB: Transfer Type = OUT Data Stage.
    pub const TRT_OUT: u32 = 2 << 16;
    /// Setup Stage TRB: Transfer Type = IN Data Stage.
    pub const TRT_IN: u32 = 3 << 16;
}

/// Completion codes reported in event TRBs (status[31:24]). xHCI spec §6.4.5.
pub mod completion {
    pub const SUCCESS: u8 = 1;
    pub const STALL_ERROR: u8 = 6;
    pub const SHORT_PACKET: u8 = 13;
    pub const CONTEXT_STATE_ERROR: u8 = 19;
}

/// Port Status and Control Register offsets — relative to op_base. xHCI spec §5.4.8.
/// Port n (1-based) is at BASE + (n-1) * STRIDE.
pub mod port {
    pub const BASE: usize = 0x400;
    pub const STRIDE: usize = 0x10;

    pub const CCS: u32 = 1 << 0; // Current Connect Status (RO)
    pub const PED: u32 = 1 << 1; // Port Enabled/Disabled (RW1C — write 1 to disable)
    pub const PR: u32 = 1 << 4; // Port Reset (RWS)
    pub const PP: u32 = 1 << 9; // Port Power (RWS)
    pub const SPEED_MASK: u32 = 0xf << 10; // Port Speed (RO) — PORTSC[13:10]
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
