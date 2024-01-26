//! Interrupt remapping of Vt-d.

const PRESENT: u32 = 1;
const FPD: u32 = 1 << 1; // Fault Processing Disable, 0: enable, 1: disable
const DM: u32 = 1 << 2; // Destination Mode, 0: Physical, 1: Logical
const RH: u32 = 1 << 3; // Redirection Hint, 0: directed to the processor listed in the Destination ID field, 1: directed to 1 of N processors specified in the Destination ID field
const TM: u32 = 1 << 4; // Trigger Mode, 0: Edge, 1: Level

const DLM_FIXED: u32 = 0b000 << 5; // Fixed, the destination ID is a fixed value
const DLM_LOWEST: u32 = 0b001 << 5; // Lowest Priority
const DLM_SMI: u32 = 0b010 << 5; // System Management Interrupt (SMI)
const DLM_NMI: u32 = 0b100 << 5; // Non-Maskable Interrupt (NMI)
const DLM_INIT: u32 = 0b101 << 5; // INIT
const DLM_EXT_INIT: u32 = 0b111 << 5;

const IM: u32 = 1 << 15; // IRTE Mode, 0: interrupt requests processed through this IRTE are remapped, 1: interrupt requests processed through this IRTE are remapped

const V_SHIFT: u32 = 16; // Vector shift

/// Source Validation Type
/// 0b00: No source validation
/// 0b01: Source validation by SID and SQ
/// 0b10: Verify the most significant 8-bits of the requester-id
/// 0b11: Reserved
const SVT_SHIFT: u32 = 2;

#[repr(C, packed)]
struct IRTEntry {
    flags: u32,
    dest: u32,
    sid: u16,
    svt_sq: u16,
    reserved: u32,
}

impl IRTEntry {
    const fn new() -> Self {
        IRTEntry {
            flags: 0,
            dest: 0,
            sid: 0,
            svt_sq: 0,
            reserved: 0,
        }
    }

    fn enable(&mut self, irq: u8, level_trigger: bool, lowest_priority: bool) {
        let mut flags = PRESENT;
    }
}
