//! xHCI rings shared with the host controller through DMA.
//!
//! Every TRB/ERST/DCBAA access goes through `read_volatile`/`write_volatile`:
//! the controller reads and writes this memory behind the compiler's back, so a
//! plain load could be hoisted out of a polling loop and a plain store could be
//! sunk past the doorbell write.  Ordering against MMIO is enforced with
//! `fence(Release)` before a doorbell ([`publish`]) and `fence(Acquire)` after an
//! event is consumed ([`EventRing::dequeue`]).
//!
//! WCET contract (all methods): no heap allocation after `new`, no blocking,
//! no panic, O(1) work per call (the `new` constructors write `RING_SIZE`
//! entries once at init).

use core::{
    ptr::{read_volatile, write_volatile},
    sync::atomic::{fence, Ordering},
};

use awkernel_lib::{addr::Addr, dma_pool::DMAPool};

use super::{
    regs::{trb_flag, trb_type, TRB_TYPE_MASK},
    XhciErr,
};

/// Number of TRBs per ring segment. 256 × 16 bytes = 4096 bytes = 1 page.
pub const RING_SIZE: usize = 256;

/// Index of the Link TRB in a producer ring.
const LINK_IDX: usize = RING_SIZE - 1;

/// Size of one TRB in bytes (xHCI spec §4.11.1).
const TRB_BYTES: u64 = 16;

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

impl Trb {
    /// TRB type, still shifted into ctrl[15:10] (compare with `regs::trb_type`).
    pub fn trb_type(&self) -> u32 {
        self.ctrl & TRB_TYPE_MASK
    }

    /// Completion code of an event TRB (status[31:24]).
    pub fn completion_code(&self) -> u8 {
        let [_, _, _, code] = self.status.to_le_bytes();
        code
    }

    /// Slot ID of a Command Completion event (ctrl[31:24]).
    pub fn slot_id(&self) -> u8 {
        let [_, _, _, slot] = self.ctrl.to_le_bytes();
        slot
    }
}

type RingMem = [Trb; RING_SIZE];

/// Make all preceding volatile DMA writes visible before the caller's next MMIO
/// write (doorbell).
#[inline]
pub fn publish() {
    fence(Ordering::Release);
}

fn phys_of<T>(pool: &DMAPool<T>) -> Result<u64, XhciErr> {
    u64::try_from(pool.get_phy_addr().as_usize()).map_err(|_| XhciErr::Overflow)
}

// ---------------------------------------------------------------------------
// Producer ring (Command Ring and Transfer Rings)
// ---------------------------------------------------------------------------

/// A single-segment producer ring terminated by a Link TRB (xHCI spec §4.9.2).
///
/// Used for the Command Ring and for every Transfer Ring.  The driver submits at
/// most a handful of TRBs and waits for their completion before submitting more,
/// so the producer can never lap the controller's dequeue pointer.
pub struct ProducerRing {
    mem: DMAPool<RingMem>,
    /// Software enqueue index (0 … LINK_IDX-1; never points at the Link TRB).
    enqueue_idx: usize,
    /// Current Producer Cycle State — toggled when the Link TRB is traversed.
    cycle_bit: u32,
}

pub type CommandRing = ProducerRing;
pub type TransferRing = ProducerRing;

impl ProducerRing {
    /// Allocate a zeroed ring with its Link TRB pointing back to the start.
    pub fn new(numa_id: usize) -> Result<Self, XhciErr> {
        let mut mem = DMAPool::<RingMem>::new(numa_id, 1).ok_or(XhciErr::DmaAlloc)?;
        let base = phys_of(&mem)?;

        for slot in mem.as_mut().iter_mut() {
            // SAFETY: `slot` is a valid, aligned &mut Trb inside the DMA page.
            unsafe { write_volatile(slot, Trb::default()) };
        }
        let link = mem.as_mut().get_mut(LINK_IDX).ok_or(XhciErr::Overflow)?;
        let link_trb = Trb {
            param: base,
            status: 0,
            // TC=1 toggles cycle state when the controller wraps; initial cycle = 1.
            ctrl: trb_type::LINK | trb_flag::LINK_TC | trb_flag::CYCLE,
        };
        // SAFETY: `link` is a valid, aligned &mut Trb inside the DMA page.
        unsafe { write_volatile(link, link_trb) };

        Ok(Self {
            mem,
            enqueue_idx: 0,
            cycle_bit: trb_flag::CYCLE,
        })
    }

    /// Write `trb` at the enqueue position, stamping the Producer Cycle State.
    /// Wraps through the Link TRB when the last data slot is used.
    ///
    /// The caller must call [`publish`] and then ring the doorbell.
    pub fn enqueue(&mut self, mut trb: Trb) -> Result<(), XhciErr> {
        let idx = self.enqueue_idx;
        let pcs = self.cycle_bit;
        trb.ctrl = (trb.ctrl & !trb_flag::CYCLE) | pcs;

        let slot = self.mem.as_mut().get_mut(idx).ok_or(XhciErr::RingFull)?;
        // SAFETY: `slot` is a valid, aligned &mut Trb inside the DMA page.
        unsafe { write_volatile(slot, trb) };

        let next = idx.checked_add(1).ok_or(XhciErr::Overflow)?;
        if next == LINK_IDX {
            // Hand the Link TRB to the controller with the current cycle so it
            // follows the link and toggles its own cycle state (TC=1).
            let link = self
                .mem
                .as_mut()
                .get_mut(LINK_IDX)
                .ok_or(XhciErr::Overflow)?;
            // SAFETY: `link` is a valid, aligned &mut Trb inside the DMA page.
            unsafe {
                let ctrl = read_volatile(&link.ctrl);
                write_volatile(&mut link.ctrl, (ctrl & !trb_flag::CYCLE) | pcs);
            }
            self.enqueue_idx = 0;
            self.cycle_bit ^= trb_flag::CYCLE;
        } else {
            self.enqueue_idx = next;
        }
        Ok(())
    }

    /// Physical base address of the ring (CRCR / EP Context TR Dequeue Pointer).
    pub fn phys_base(&self) -> Result<u64, XhciErr> {
        phys_of(&self.mem)
    }

    /// Physical address of the enqueue position with the DCS bit (bit 0) set to
    /// the current cycle — the value for SET_TR_DEQUEUE_POINTER.
    pub fn enqueue_pointer(&self) -> Result<u64, XhciErr> {
        let offset = u64::try_from(self.enqueue_idx)
            .ok()
            .and_then(|i| i.checked_mul(TRB_BYTES))
            .ok_or(XhciErr::Overflow)?;
        let addr = self
            .phys_base()?
            .checked_add(offset)
            .ok_or(XhciErr::Overflow)?;
        Ok(addr | u64::from(self.cycle_bit))
    }
}

// ---------------------------------------------------------------------------
// Event Ring
// ---------------------------------------------------------------------------

/// Event Ring Segment Table entry — 16 bytes. xHCI spec §6.5.
#[repr(C)]
#[derive(Default, Copy, Clone)]
struct ErstEntry {
    /// Physical base address of the ring segment (must be 64-byte aligned).
    ring_segment_base: u64,
    /// bits[15:0] = segment size (number of TRBs), bits[63:16] must be zero.
    size_rsvd: u64,
}

/// Single-segment consumer ring plus its one-entry segment table.
pub struct EventRing {
    seg_mem: DMAPool<RingMem>,
    erst_mem: DMAPool<ErstEntry>,
    /// Software dequeue index into `seg_mem`.
    dequeue_idx: usize,
    /// Current Consumer Cycle State.
    cycle_bit: u32,
}

impl EventRing {
    pub fn new(numa_id: usize) -> Result<Self, XhciErr> {
        let mut seg_mem = DMAPool::<RingMem>::new(numa_id, 1).ok_or(XhciErr::DmaAlloc)?;
        let mut erst_mem = DMAPool::<ErstEntry>::new(numa_id, 1).ok_or(XhciErr::DmaAlloc)?;

        for slot in seg_mem.as_mut().iter_mut() {
            // SAFETY: `slot` is a valid, aligned &mut Trb inside the DMA page.
            unsafe { write_volatile(slot, Trb::default()) };
        }
        let entry = ErstEntry {
            ring_segment_base: phys_of(&seg_mem)?,
            size_rsvd: u64::try_from(RING_SIZE).map_err(|_| XhciErr::Overflow)?,
        };
        // SAFETY: `erst_mem` owns one page, large enough for one ErstEntry.
        unsafe { write_volatile(erst_mem.as_mut(), entry) };

        Ok(Self {
            seg_mem,
            erst_mem,
            dequeue_idx: 0,
            cycle_bit: trb_flag::CYCLE,
        })
    }

    /// Return the next event TRB if its cycle bit matches the Consumer Cycle State.
    /// Advances the dequeue index and toggles the cycle state on wrap-around.
    pub fn dequeue(&mut self) -> Result<Option<Trb>, XhciErr> {
        let idx = self.dequeue_idx;
        let slot = self.seg_mem.as_ref().get(idx).ok_or(XhciErr::Overflow)?;
        // SAFETY: `slot` is a valid, aligned &Trb inside the DMA page.
        let trb = unsafe { read_volatile(slot) };

        if trb.ctrl & trb_flag::CYCLE != self.cycle_bit {
            return Ok(None); // no event ready
        }
        // Everything the controller wrote before this event (e.g. a descriptor
        // in a data buffer) must be read after the cycle bit check.
        fence(Ordering::Acquire);

        let next = idx.checked_add(1).ok_or(XhciErr::Overflow)?;
        if next >= RING_SIZE {
            self.dequeue_idx = 0;
            self.cycle_bit ^= trb_flag::CYCLE;
        } else {
            self.dequeue_idx = next;
        }
        Ok(Some(trb))
    }

    /// Physical address of the current dequeue position (ERDP).
    pub fn dequeue_phys(&self) -> Result<u64, XhciErr> {
        let offset = u64::try_from(self.dequeue_idx)
            .ok()
            .and_then(|i| i.checked_mul(TRB_BYTES))
            .ok_or(XhciErr::Overflow)?;
        self.seg_phys()?
            .checked_add(offset)
            .ok_or(XhciErr::Overflow)
    }

    /// Physical address of the ERST (ERSTBA).
    pub fn erst_phys(&self) -> Result<u64, XhciErr> {
        phys_of(&self.erst_mem)
    }

    /// Physical base of the event ring segment.
    pub fn seg_phys(&self) -> Result<u64, XhciErr> {
        phys_of(&self.seg_mem)
    }
}

// ---------------------------------------------------------------------------
// Device Context Base Address Array (DCBAA)
// ---------------------------------------------------------------------------

/// Slot 0 = scratchpad-buffer-array pointer (or 0); slots 1–255 = Device Context pointers.
/// 256 × 8 bytes = 2048 bytes — fits in one DMA page.
const DCBAA_SIZE: usize = 256;

pub struct Dcbaa {
    mem: DMAPool<[u64; DCBAA_SIZE]>,
}

impl Dcbaa {
    pub fn new(numa_id: usize) -> Result<Self, XhciErr> {
        let mut mem = DMAPool::<[u64; DCBAA_SIZE]>::new(numa_id, 1).ok_or(XhciErr::DmaAlloc)?;
        for entry in mem.as_mut().iter_mut() {
            // SAFETY: `entry` is a valid, aligned &mut u64 inside the DMA page.
            unsafe { write_volatile(entry, 0) };
        }
        Ok(Self { mem })
    }

    /// Store `phys` in DCBAA[`index`] (0 = scratchpad array, 1..=255 = slot ID).
    pub fn set(&mut self, index: u8, phys: u64) -> Result<(), XhciErr> {
        let entry = self
            .mem
            .as_mut()
            .get_mut(usize::from(index))
            .ok_or(XhciErr::Overflow)?;
        // SAFETY: `entry` is a valid, aligned &mut u64 inside the DMA page.
        unsafe { write_volatile(entry, phys) };
        Ok(())
    }

    /// Physical base address (DCBAAP).
    pub fn phys_base(&self) -> Result<u64, XhciErr> {
        phys_of(&self.mem)
    }
}
