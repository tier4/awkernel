use awkernel_lib::{addr::Addr, dma_pool::DMAPool};

use super::regs::{TRB_CYCLE, TRB_LINK_TC, TRB_TYPE_SHIFT, trb_type};

/// Number of TRBs in the Command Ring. The last entry is the Link TRB.
/// 256 × 16 bytes = 4096 bytes = 1 page, so DMAPool<CmdRingMem>::new(n, 1) works.
pub const CMD_RING_SIZE: usize = 256;

/// Number of TRBs in the primary Event Ring segment.
/// 256 × 16 bytes = 4096 bytes = 1 page.
pub const EVT_RING_SIZE: usize = 256;

/// Transfer Request Block — 16 bytes. xHCI spec §4.11.1.
///
/// Layout (little-endian):
///   [63:0]  param   — address, data, or command-specific parameter
///   [95:64] status  — length, completion code, …
///   [127:96] ctrl   — cycle bit[0], TRB-specific flags, TRB type[15:10]
#[repr(C)]
#[derive(Default, Copy, Clone)]
pub struct Trb {
    pub param: u64,
    pub status: u32,
    pub ctrl: u32,
}

/// Flat array of TRBs backing the Command Ring (1 page).
pub type CmdRingMem = [Trb; CMD_RING_SIZE];

/// Flat array of TRBs backing the primary Event Ring segment (1 page).
pub type EvtRingMem = [Trb; EVT_RING_SIZE];

/// Event Ring Segment Table entry — 16 bytes. xHCI spec §6.5.
///
/// The ERST consists of one or more of these entries.  We use a single-entry
/// table pointing at the sole event ring segment.
#[repr(C)]
#[derive(Default, Copy, Clone)]
pub struct ErstEntry {
    /// Physical base address of the ring segment (must be 64-byte aligned).
    pub ring_segment_base: u64,
    /// bits[15:0] = segment size (number of TRBs), bits[63:16] must be zero.
    pub size_rsvd: u64,
}

/// A one-entry ERST.  DMAPool allocates 1 page; only 16 bytes are used.
pub type ErstMem = [ErstEntry; 1];

// ---------------------------------------------------------------------------
// Command Ring
// ---------------------------------------------------------------------------

pub struct CommandRing {
    pub mem: DMAPool<CmdRingMem>,
    /// Software enqueue index (0 … CMD_RING_SIZE-2; skips the Link TRB slot).
    pub enqueue_idx: usize,
    /// Current Producer Cycle State — toggled when the Link TRB is traversed.
    pub cycle_bit: u32,
}

impl CommandRing {
    pub fn new(numa_id: usize) -> Option<Self> {
        let mem = DMAPool::<CmdRingMem>::new(numa_id, 1)?;
        Some(Self {
            mem,
            enqueue_idx: 0,
            cycle_bit: 1,
        })
    }

    /// Zero all TRBs and install the Link TRB at the last slot.
    pub fn init(&mut self) {
        // Compute physical base before taking the mutable borrow on mem.
        let phy_base = self.phys_base();

        let trbs = self.mem.as_mut();
        for trb in trbs.iter_mut() {
            *trb = Trb::default();
        }

        let link = &mut trbs[CMD_RING_SIZE - 1];
        link.param = phy_base;
        // TC=1 toggles cycle state when the controller wraps; initial cycle = 1.
        link.ctrl = (trb_type::LINK << TRB_TYPE_SHIFT) | TRB_LINK_TC | TRB_CYCLE;
    }

    /// Physical base address of the ring (written to CRCR during init).
    pub fn phys_base(&self) -> u64 {
        self.mem.get_phy_addr().as_usize() as u64
    }
}

// ---------------------------------------------------------------------------
// Event Ring
// ---------------------------------------------------------------------------

pub struct EventRing {
    /// DMA memory for the ring segment (the actual TRBs).
    pub seg_mem: DMAPool<EvtRingMem>,
    /// DMA memory for the Event Ring Segment Table.
    pub erst_mem: DMAPool<ErstMem>,
    /// Software dequeue index into `seg_mem`.
    pub dequeue_idx: usize,
    /// Current Consumer Cycle State.
    pub cycle_bit: u32,
}

impl EventRing {
    pub fn new(numa_id: usize) -> Option<Self> {
        let seg_mem = DMAPool::<EvtRingMem>::new(numa_id, 1)?;
        let erst_mem = DMAPool::<ErstMem>::new(numa_id, 1)?;
        Some(Self {
            seg_mem,
            erst_mem,
            dequeue_idx: 0,
            cycle_bit: 1,
        })
    }

    /// Zero the segment and populate the ERST entry.
    pub fn init(&mut self) {
        for trb in self.seg_mem.as_mut().iter_mut() {
            *trb = Trb::default();
        }
        let seg_base = self.seg_phys();
        let erst = self.erst_mem.as_mut();
        erst[0].ring_segment_base = seg_base;
        erst[0].size_rsvd = EVT_RING_SIZE as u64;
    }

    /// Physical address of the ERST (written to ERSTBA during init).
    pub fn erst_phys(&self) -> u64 {
        self.erst_mem.get_phy_addr().as_usize() as u64
    }

    /// Physical base of the event ring segment (written to ERDP during init).
    pub fn seg_phys(&self) -> u64 {
        self.seg_mem.get_phy_addr().as_usize() as u64
    }
}

// ---------------------------------------------------------------------------
// Device Context Base Address Array (DCBAA)
// ---------------------------------------------------------------------------

/// Slot 0 = scratchpad-buffer-array pointer (or 0); slots 1–255 = Device Context pointers.
/// 256 × 8 bytes = 2048 bytes — fits in one DMA page.
pub const DCBAA_SIZE: usize = 256;
pub type DcbaaMem = [u64; DCBAA_SIZE];

pub struct Dcbaa {
    pub mem: DMAPool<DcbaaMem>,
}

impl Dcbaa {
    pub fn new(numa_id: usize) -> Option<Self> {
        let mem = DMAPool::<DcbaaMem>::new(numa_id, 1)?;
        Some(Self { mem })
    }

    pub fn init(&mut self) {
        for slot in self.mem.as_mut().iter_mut() {
            *slot = 0;
        }
    }

    /// Physical base address (written to DCBAAP during init).
    pub fn phys_base(&self) -> u64 {
        self.mem.get_phy_addr().as_usize() as u64
    }
}
