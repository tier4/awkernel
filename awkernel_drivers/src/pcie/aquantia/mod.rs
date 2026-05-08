//! Aquantia Atlantic 2 (AQC113 series) Ethernet controller driver.
//!
//! Supported devices: AQC113CS (0x04C0), AQC113 (0x04D0–0x04D3), AQC107 (0xD107–0xD109).
//!
//! Register layout references:
//! - Linux kernel `drivers/net/ethernet/aquantia/atlantic/hw_atl/hw_atl_llh_internal.h`
//! - Linux kernel `drivers/net/ethernet/aquantia/atlantic/hw_atl2/hw_atl2_llh_internal.h`

use crate::pcie::{pcie_id::AQUANTIA_VENDOR_ID, PCIeDevice, PCIeDeviceErr, PCIeInfo};
use alloc::{borrow::Cow, boxed::Box, collections::BTreeMap, format, sync::Arc, vec::Vec};
use awkernel_async_lib_verified::ringq::RingQ;
use awkernel_lib::{
    addr::Addr,
    dma_pool::DMAPool,
    interrupt::IRQ,
    net::{
        multicast::MulticastAddrs,
        net_device::{
            EtherFrameBuf, EtherFrameRef, LinkStatus, NetCapabilities, NetDevError, NetDevice,
            NetFlags,
        },
    },
    paging::PAGESIZE,
    sync::{
        mutex::{MCSNode, Mutex},
        rwlock::RwLock,
    },
};

mod atlantic_regs;

use atlantic_regs::*;

// ── Device list ──────────────────────────────────────────────────────────────

const DEVICE_NAME: &str = "Aquantia AQC Atlantic Ethernet Controller";
const DEVICE_SHORT_NAME: &str = "atl";

/// Supported (vendor_id, device_id) pairs.
pub const AQUANTIA_DEVICES: &[(u16, u16)] = &[
    // Atlantic 2 (hw_atl2) — AQC113 family
    (AQUANTIA_VENDOR_ID, 0x04C0), // AQC113CS
    (AQUANTIA_VENDOR_ID, 0x04D0), // AQC113
    (AQUANTIA_VENDOR_ID, 0x04D1), // AQC113
    (AQUANTIA_VENDOR_ID, 0x04D2), // AQC113
    (AQUANTIA_VENDOR_ID, 0x04D3), // AQC113
    (AQUANTIA_VENDOR_ID, 0x04D4), // AQC113
    (AQUANTIA_VENDOR_ID, 0x0005), // AQC100
    // Atlantic 1 (hw_atl_b0) — AQC107/AQC108 family
    (AQUANTIA_VENDOR_ID, 0x0001), // AQC100
    (AQUANTIA_VENDOR_ID, 0xD100), // AQC100 (OEM)
    (AQUANTIA_VENDOR_ID, 0xD107), // AQC107 (10GbE)
    (AQUANTIA_VENDOR_ID, 0xD108), // AQC108 (5GbE)
    (AQUANTIA_VENDOR_ID, 0xD109), // AQC109 (2.5GbE)
    (AQUANTIA_VENDOR_ID, 0x87B1), // AQC107 (OEM/rebranded)
];

// ── Constants ────────────────────────────────────────────────────────────────

/// Number of TX / RX descriptors per ring (must be a power of 2, ≥ 32).
const NUM_RING_DESC: usize = 256;
/// Maximum size of each DMA packet buffer (bytes).
const PKT_BUF_SIZE: usize = 2048;
/// Software RX queue depth (packets buffered before the network stack drains them).
const SW_RX_QUEUE_SIZE: usize = 64;
/// Number of milliseconds between periodic tick calls (link check, TX reclaim).
const TICK_MSEC: u64 = 200;
/// Firmware ready poll maximum iterations (each ~1 ms apart in delay::wait_millisec).
const FIRMWARE_POLL_ITERS: u32 = 5000;

// ── DMA ring types ───────────────────────────────────────────────────────────

/// Raw 16-byte descriptor slot shared by both the TX and RX rings.
type DescRing = [[u64; 2]; NUM_RING_DESC];
/// Contiguous packet buffer backing an entire ring.
type PktBuf = [[u8; PKT_BUF_SIZE]; NUM_RING_DESC];

// Both rings use exactly one page: 256 × 16 = 4096 bytes.
const _: () = assert!(
    core::mem::size_of::<DescRing>() == PAGESIZE,
    "DescRing must fit in one page"
);
// Packet buffers: 256 × 2048 = 524 288 bytes = 128 pages — fine for DMAPool.
const _: () = assert!(core::mem::size_of::<PktBuf>() % PAGESIZE == 0);

// ── Interrupt tracking ───────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum IrqRole {
    /// Combined RX + TX for queue n.
    Queue(usize),
    /// Link-status change interrupt.
    #[allow(dead_code)]
    LinkStatus,
}

#[derive(Debug)]
enum PcieInt {
    None,
    Msi(#[allow(dead_code)] IRQ),
    MsiX(#[allow(dead_code)] IRQ),
}

// ── Driver error type ─────────────────────────────────────────────────────────

#[derive(Debug, Clone, Copy)]
pub enum AtlDriverErr {
    NoBar0,
    ReadFailure,
    DmaAlloc,
    InitInterrupt,
    FirmwareTimeout,
}

impl core::fmt::Display for AtlDriverErr {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl core::error::Error for AtlDriverErr {}

impl From<AtlDriverErr> for PCIeDeviceErr {
    fn from(e: AtlDriverErr) -> Self {
        log::error!("atl: {e}");
        PCIeDeviceErr::InitFailure
    }
}

// ── Register helpers ─────────────────────────────────────────────────────────

fn read_reg(info: &PCIeInfo, offset: usize) -> Result<u32, AtlDriverErr> {
    let bar0 = info.get_bar(0).ok_or(AtlDriverErr::NoBar0)?;
    bar0.read32(offset).ok_or(AtlDriverErr::ReadFailure)
}

fn write_reg(info: &PCIeInfo, offset: usize, value: u32) -> Result<(), AtlDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(AtlDriverErr::NoBar0)?;
    bar0.write32(offset, value);
    Ok(())
}

// ── TX queue ─────────────────────────────────────────────────────────────────

struct Tx {
    /// Next descriptor slot to fill (software tail, driver advances after each send).
    sw_tail: usize,
    /// Oldest in-flight descriptor (updated by reading the hardware head register).
    sw_head: usize,
    /// DMA-mapped descriptor ring.
    desc_ring: DMAPool<DescRing>,
    /// DMA-mapped packet buffers backing the ring.
    pkt_buf: DMAPool<PktBuf>,
}

impl Tx {
    fn ring_len() -> usize {
        NUM_RING_DESC
    }

    /// True when the ring is full (one slot kept empty as sentinel).
    fn is_full(&self) -> bool {
        (self.sw_tail + 1) % Self::ring_len() == self.sw_head
    }

    /// Number of free TX descriptor slots.
    fn free_slots(&self) -> usize {
        let len = Self::ring_len();
        (self.sw_head + len - self.sw_tail - 1) % len
    }

    /// Post a packet: copy payload to the DMA buffer and fill the descriptor.
    /// The caller is responsible for writing the updated tail to hardware afterwards.
    fn post_packet(&mut self, data: &[u8]) -> bool {
        if self.is_full() || data.len() > PKT_BUF_SIZE {
            return false;
        }

        let i = self.sw_tail;
        let buf_phys = self.pkt_buf.get_phy_addr().as_usize() + i * PKT_BUF_SIZE;

        // Copy into DMA buffer.
        let dst = &mut self.pkt_buf.as_mut()[i];
        dst[..data.len()].copy_from_slice(data);

        // Fill descriptor: [0] = physical buffer address,
        //                  [1] = ctl (low 32) | pay_len (high 32, 0 for non-TSO)
        let ctl: u32 = (data.len() as u32 & 0xFFFF)
            | TX_DESC_TYPE_DATA
            | TX_DESC_EOP
            | TX_DESC_FCS
            | TX_DESC_WB;
        self.desc_ring.as_mut()[i] = [buf_phys as u64, ctl as u64];

        self.sw_tail = (self.sw_tail + 1) % Self::ring_len();
        true
    }

    /// Reclaim descriptors by reading the hardware head pointer.
    fn reclaim(&mut self, info: &PCIeInfo, ring_idx: usize) {
        if let Ok(hw_head) = read_reg(info, tx_ring_head(ring_idx)) {
            self.sw_head = hw_head as usize % Self::ring_len();
        }
    }
}

// ── RX queue ─────────────────────────────────────────────────────────────────

struct Rx {
    /// Index of the next descriptor to inspect for a completed packet.
    hw_head: usize,
    /// Index of the last descriptor we handed to hardware (written to the tail register).
    sw_tail: usize,
    /// DMA-mapped descriptor ring.
    desc_ring: DMAPool<DescRing>,
    /// DMA-mapped packet buffers backing the ring.
    pkt_buf: DMAPool<PktBuf>,
    /// Software queue holding received frames waiting to be consumed.
    recv_queue: RingQ<EtherFrameBuf>,
    /// Number of packets dropped due to full software queue.
    dropped: u64,
}

impl Rx {
    fn ring_len() -> usize {
        NUM_RING_DESC
    }

    /// Refill descriptor slot `i` by writing a fresh buffer address.
    fn refill_desc(&mut self, i: usize) {
        let buf_phys = self.pkt_buf.get_phy_addr().as_usize() + i * PKT_BUF_SIZE;
        // Submit format: [0] = buf_addr, [1] = 0 (no header split).
        self.desc_ring.as_mut()[i] = [buf_phys as u64, 0];
    }

    /// Scan for completed descriptors, drain them into the software queue, and
    /// recycle slots back to hardware.  Returns the number of frames received.
    fn drain(&mut self, info: &PCIeInfo, ring_idx: usize) -> usize {
        let mut count = 0;

        loop {
            if self.recv_queue.is_full() {
                break;
            }

            let i = self.hw_head;
            // Write-back layout: raw[1] = status(16) | pkt_len(16) | next(16) | vlan(16)
            // Use volatile read so the compiler never caches the descriptor value.
            let raw1 =
                unsafe { core::ptr::read_volatile(&self.desc_ring.as_ref()[i][1] as *const u64) };

            let status = (raw1 & 0xFFFF) as u16;
            if status & RX_WB_DD == 0 {
                break; // hardware hasn't written this descriptor yet
            }

            let pkt_len_raw = ((raw1 >> 16) & 0xFFFF) as usize;
            // Strip 4-byte Ethernet FCS that the hardware appends to pkt_len.
            let pkt_len = pkt_len_raw.saturating_sub(4);

            if pkt_len > 0 && pkt_len <= PKT_BUF_SIZE {
                let src = &self.pkt_buf.as_ref()[i];
                let data = src[..pkt_len].to_vec();
                let vlan = None; // TODO: parse VLAN from RX WB if needed
                if self
                    .recv_queue
                    .push(EtherFrameBuf { data, vlan })
                    .is_err()
                {
                    self.dropped += 1;
                } else {
                    count += 1;
                }
            }

            // Recycle the descriptor slot.
            self.refill_desc(i);

            self.hw_head = (self.hw_head + 1) % Self::ring_len();
            self.sw_tail = (self.sw_tail + 1) % Self::ring_len();
        }

        if count > 0 {
            // Inform hardware of new tail (more descriptors available).
            let _ = write_reg(info, rx_ring_tail(ring_idx), self.sw_tail as u32);
        }

        count
    }
}

// ── Per-queue container ───────────────────────────────────────────────────────

struct Queue {
    tx: Mutex<Tx>,
    rx: Mutex<Rx>,
    /// Hardware ring index (= software queue index for us, always 0).
    #[allow(dead_code)]
    idx: usize,
}

// ── Inner device state ────────────────────────────────────────────────────────

struct AtlInner {
    info: PCIeInfo,
    mac_addr: [u8; 6],
    flags: NetFlags,
    capabilities: NetCapabilities,
    pcie_int: PcieInt,
    irq_to_role: BTreeMap<u16, IrqRole>,
    is_poll_mode: bool,
    link_up: bool,
    link_mbps: u64,
    multicast_addrs: MulticastAddrs,
    que: Vec<Queue>,
}

impl AtlInner {
    /// Read the MAC address that firmware loaded into the L2 unicast filter registers.
    fn read_mac_addr(info: &PCIeInfo) -> Result<[u8; 6], AtlDriverErr> {
        let lo = read_reg(info, mac_filter_addrl(0))?;
        let hi = read_reg(info, mac_filter_addrh(0))?;
        Ok([
            ((hi >> 8) & 0xFF) as u8,
            (hi & 0xFF) as u8,
            ((lo >> 24) & 0xFF) as u8,
            ((lo >> 16) & 0xFF) as u8,
            ((lo >> 8) & 0xFF) as u8,
            (lo & 0xFF) as u8,
        ])
    }

    /// Wait until firmware signals it has completed boot.
    fn wait_firmware(info: &PCIeInfo) -> Result<(), AtlDriverErr> {
        for _ in 0..FIRMWARE_POLL_ITERS {
            let status = read_reg(info, MPI_BOOT_COMPLETE).unwrap_or(0);
            let code = read_reg(info, MPI_BOOT_CODE).unwrap_or(0);
            if code != 0 || (status & 0x10 != 0) {
                return Ok(());
            }
            awkernel_lib::delay::wait_millisec(1);
        }
        Err(AtlDriverErr::FirmwareTimeout)
    }

    /// Allocate DMA descriptor ring + packet buffer for one queue.
    fn alloc_queue(info: &PCIeInfo, idx: usize) -> Result<Queue, AtlDriverErr> {
        let ring_pages = core::mem::size_of::<DescRing>() / PAGESIZE;
        let buf_pages = core::mem::size_of::<PktBuf>() / PAGESIZE;
        let numa = info.get_segment_group() as usize;

        let tx_desc = DMAPool::<DescRing>::new(numa, ring_pages).ok_or(AtlDriverErr::DmaAlloc)?;
        let tx_buf = DMAPool::<PktBuf>::new(numa, buf_pages).ok_or(AtlDriverErr::DmaAlloc)?;

        let rx_desc = DMAPool::<DescRing>::new(numa, ring_pages).ok_or(AtlDriverErr::DmaAlloc)?;
        let rx_buf = DMAPool::<PktBuf>::new(numa, buf_pages).ok_or(AtlDriverErr::DmaAlloc)?;

        Ok(Queue {
            tx: Mutex::new(Tx {
                sw_tail: 0,
                sw_head: 0,
                desc_ring: tx_desc,
                pkt_buf: tx_buf,
            }),
            rx: Mutex::new(Rx {
                hw_head: 0,
                sw_tail: NUM_RING_DESC - 1,
                desc_ring: rx_desc,
                pkt_buf: rx_buf,
                recv_queue: RingQ::new(SW_RX_QUEUE_SIZE),
                dropped: 0,
            }),
            idx,
        })
    }

    /// Full device initialization sequence (called from `up()`).
    fn init(&mut self) -> Result<(), AtlDriverErr> {
        // 1. Disable TX and RX while reconfiguring.
        write_reg(&self.info, TPB_TX_BUF_ENABLE, 0)?;
        write_reg(&self.info, RPB_RX_BUF_ENABLE, 0)?;
        // Disable ring 0 explicitly.
        write_reg(&self.info, TDM_RING_DISABLE, 1)?;
        write_reg(&self.info, RDM_RING_DISABLE, 1)?;

        // 2. Configure TX ring 0.
        {
            let que = &self.que[0];
            let mut node = MCSNode::new();
            let mut tx = que.tx.lock(&mut node);

            tx.sw_tail = 0;
            tx.sw_head = 0;

            // Zero the descriptor ring so there are no stale descriptors.
            for slot in tx.desc_ring.as_mut().iter_mut() {
                *slot = [0u64; 2];
            }

            let phys = tx.desc_ring.get_phy_addr().as_usize() as u64;
            write_reg(&self.info, tx_ring_base_addrl(0), phys as u32)?;
            write_reg(&self.info, tx_ring_base_addrh(0), (phys >> 32) as u32)?;
            write_reg(&self.info, tx_ring_len(0), (NUM_RING_DESC - 1) as u32)?;
            write_reg(&self.info, tx_ring_head(0), 0)?;
            write_reg(&self.info, tx_ring_tail(0), 0)?;
        }
        // Enable TX ring 0.
        write_reg(&self.info, TDM_RING_ENABLE, 1)?;

        // 3. Configure RX ring 0 — pre-fill all descriptors with buffer addresses.
        {
            let que = &self.que[0];
            let mut node = MCSNode::new();
            let mut rx = que.rx.lock(&mut node);

            rx.hw_head = 0;
            rx.sw_tail = NUM_RING_DESC - 1;

            let buf_base = rx.pkt_buf.get_phy_addr().as_usize();
            for (i, slot) in rx.desc_ring.as_mut().iter_mut().enumerate() {
                *slot = [(buf_base + i * PKT_BUF_SIZE) as u64, 0u64];
            }

            let phys = rx.desc_ring.get_phy_addr().as_usize() as u64;
            write_reg(&self.info, rx_ring_base_addrl(0), phys as u32)?;
            write_reg(&self.info, rx_ring_base_addrh(0), (phys >> 32) as u32)?;
            write_reg(&self.info, rx_ring_len(0), (NUM_RING_DESC - 1) as u32)?;
            // Tell hardware where the last valid descriptor is.
            write_reg(&self.info, rx_ring_tail(0), rx.sw_tail as u32)?;
        }
        // Enable RX ring 0.
        write_reg(&self.info, RDM_RING_ENABLE, 1)?;

        // 4. Configure MAC unicast filter with our address.
        let mac = self.mac_addr;
        let lo: u32 = ((mac[2] as u32) << 24)
            | ((mac[3] as u32) << 16)
            | ((mac[4] as u32) << 8)
            | (mac[5] as u32);
        let hi: u32 = ((mac[0] as u32) << 8) | (mac[1] as u32);
        write_reg(&self.info, mac_filter_addrl(0), lo)?;
        write_reg(&self.info, mac_filter_addrh(0), hi)?;
        // Enable filter 0 and broadcast.
        write_reg(&self.info, MAC_FILTER_ENABLE, 1)?;
        write_reg(&self.info, MAC_BCAST_ENABLE, 1)?;

        // 5. Re-enable TX and RX packet buffers.
        write_reg(&self.info, TPB_TX_BUF_ENABLE, 1)?;
        write_reg(&self.info, RPB_RX_BUF_ENABLE, 1)?;

        self.flags |= NetFlags::RUNNING;

        // 6. Set up interrupts (MSI) or fall through to poll mode.
        self.init_interrupts()?;

        // 7. Read initial link status.
        self.update_link_status();

        Ok(())
    }

    /// Try MSI-X → MSI → poll mode.
    fn init_interrupts(&mut self) -> Result<(), AtlDriverErr> {
        self.info.disable_legacy_interrupt();

        let seg = self.info.get_segment_group() as usize;
        let bdf = self.info.get_bdf();
        let irq_name = format!("{DEVICE_SHORT_NAME}-{bdf}");
        let cpu = awkernel_lib::cpu::raw_cpu_id() as u32;

        // ── Try MSI-X first (AQC113 natively supports MSI-X) ─────────────────
        if let Some(msi) = self.info.get_msi_mut() {
            msi.disable();
        }
        if let Some(msix) = self.info.get_msix_mut() {
            msix.disable();
            match msix.register_handler(
                irq_name.clone().into(),
                Box::new(|irq| awkernel_lib::net::net_interrupt(irq)),
                seg,
                cpu,
                0, // vector 0 = queue 0
            ) {
                Ok(mut irq) => {
                    irq.enable();
                    self.info.get_msix_mut().unwrap().enable();
                    let irq_num = irq.get_irq();
                    self.irq_to_role.insert(irq_num, IrqRole::Queue(0));
                    self.pcie_int = PcieInt::MsiX(irq);
                    self.is_poll_mode = false;
                    let _ = write_reg(
                        &self.info,
                        ATL2_ITR_MASK_SET,
                        ITR_RX0 | ITR_TX0 | ITR_LSC,
                    );
                    return Ok(());
                }
                Err(_) => {
                    log::error!("atl {bdf}: MSI-X allocation failed, trying MSI");
                }
            }
        }

        // ── Fall back to plain MSI ────────────────────────────────────────────
        if let Some(msi) = self.info.get_msi_mut() {
            msi.disable();
            match msi.register_handler(
                irq_name.into(),
                Box::new(|irq| awkernel_lib::net::net_interrupt(irq)),
                seg,
                cpu,
            ) {
                Ok(mut irq) => {
                    irq.enable();
                    self.info.get_msi_mut().unwrap().enable();
                    let irq_num = irq.get_irq();
                    self.irq_to_role.insert(irq_num, IrqRole::Queue(0));
                    self.pcie_int = PcieInt::Msi(irq);
                    self.is_poll_mode = false;
                    let _ = write_reg(
                        &self.info,
                        ATL2_ITR_MASK_SET,
                        ITR_RX0 | ITR_TX0 | ITR_LSC,
                    );
                    return Ok(());
                }
                Err(_) => {
                    log::warn!("atl {bdf}: MSI allocation failed, using poll mode");
                }
            }
        }

        // ── Fall back to poll mode ────────────────────────────────────────────
        self.is_poll_mode = true;
        Ok(())
    }

    /// Stop TX/RX and disable interrupts.
    fn stop(&mut self) {
        match &self.pcie_int {
            PcieInt::Msi(_) | PcieInt::MsiX(_) => {
                let _ = write_reg(&self.info, ATL2_ITR_MASK_CLR, !0u32);
            }
            PcieInt::None => {}
        }
        let _ = write_reg(&self.info, TPB_TX_BUF_ENABLE, 0);
        let _ = write_reg(&self.info, RPB_RX_BUF_ENABLE, 0);
        self.flags.remove(NetFlags::RUNNING);
    }

    /// Update cached link status from the PHY status register.
    fn update_link_status(&mut self) {
        if let Ok(phy) = read_reg(&self.info, PHY_STATUS) {
            let old = self.link_up;
            if phy & PHY_STATUS_10G != 0 {
                self.link_up = true;
                self.link_mbps = 10_000;
            } else if phy & PHY_STATUS_5G != 0 {
                self.link_up = true;
                self.link_mbps = 5_000;
            } else if phy & PHY_STATUS_2_5G != 0 {
                self.link_up = true;
                self.link_mbps = 2_500;
            } else if phy & PHY_STATUS_1G != 0 {
                self.link_up = true;
                self.link_mbps = 1_000;
            } else if phy & PHY_STATUS_100M != 0 {
                self.link_up = true;
                self.link_mbps = 100;
            } else {
                self.link_up = false;
                self.link_mbps = 0;
            }
            if old != self.link_up {
                if self.link_up {
                    log::info!(
                        "atl {}: link up, {} Mbps",
                        self.info.get_bdf(),
                        self.link_mbps
                    );
                } else {
                    log::info!("atl {}: link down", self.info.get_bdf());
                }
            }
        }
    }

    /// Handle an interrupt: drain RX queue and update link status.
    fn handle_interrupt(&self, irq: u16) {
        // Read and acknowledge interrupt status.
        if let Ok(status) = read_reg(&self.info, ATL2_ITR_STATUS) {
            if status & (ITR_RX0 | ITR_TX0) != 0 {
                self.rx_drain(0);
            }
            // Re-arm the interrupt.
            let _ = write_reg(&self.info, ATL2_ITR_MASK_SET, status);
        }

        // If this is the link IRQ, schedule a link-status update.
        if let Some(IrqRole::LinkStatus) = self.irq_to_role.get(&irq) {
            // Cannot call update_link_status here (needs &mut self); the tick will handle it.
        }
    }

    /// Drain received packets from RX queue `q` into the software ring.
    fn rx_drain(&self, q: usize) {
        let que = &self.que[q];
        let mut node = MCSNode::new();
        let mut rx = que.rx.lock(&mut node);
        rx.drain(&self.info, q);
    }
}

// ── Public driver struct ──────────────────────────────────────────────────────

/// Aquantia Atlantic Ethernet controller driver.
pub struct Atlantic {
    inner: RwLock<AtlInner>,
}

// ── Public entry points ───────────────────────────────────────────────────────

pub fn match_device(vendor: u16, id: u16) -> bool {
    AQUANTIA_DEVICES.contains(&(vendor, id))
}

pub fn attach(mut info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    if let Err(e) = info.map_bar() {
        log::warn!("atl: failed to map BAR: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }
    info.read_capability();
    info.enable_bus_master();

    let atl = Atlantic::new(info)?;
    let result = Arc::new(atl);
    awkernel_lib::net::add_interface(result.clone(), None);
    Ok(result)
}

impl Atlantic {
    fn new(info: PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        // Wait for firmware to signal readiness.
        if let Err(e) = AtlInner::wait_firmware(&info) {
            log::warn!("atl {}: firmware not ready ({e}), continuing anyway", info.get_bdf());
        }

        let mac_addr = AtlInner::read_mac_addr(&info).unwrap_or([0u8; 6]);
        log::info!(
            "atl {}: MAC {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
            info.get_bdf(),
            mac_addr[0],
            mac_addr[1],
            mac_addr[2],
            mac_addr[3],
            mac_addr[4],
            mac_addr[5],
        );

        let que0 = AtlInner::alloc_queue(&info, 0)?;

        let inner = AtlInner {
            info,
            mac_addr,
            flags: NetFlags::BROADCAST | NetFlags::SIMPLEX | NetFlags::MULTICAST,
            capabilities: NetCapabilities::VLAN_MTU,
            pcie_int: PcieInt::None,
            irq_to_role: BTreeMap::new(),
            is_poll_mode: true,
            link_up: false,
            link_mbps: 0,
            multicast_addrs: MulticastAddrs::new(),
            que: alloc::vec![que0],
        };

        Ok(Self {
            inner: RwLock::new(inner),
        })
    }
}

// ── PCIeDevice ────────────────────────────────────────────────────────────────

impl PCIeDevice for Atlantic {
    fn device_name(&self) -> Cow<'static, str> {
        let bdf = self.inner.read().info.get_bdf();
        format!("{bdf}: {DEVICE_NAME}").into()
    }

    fn config_space(&self) -> Option<crate::pcie::config_space::ConfigSpace> {
        let inner = self.inner.read();
        Some(inner.info.config_space.clone())
    }
}

// ── NetDevice ─────────────────────────────────────────────────────────────────

impl NetDevice for Atlantic {
    fn num_queues(&self) -> usize {
        1
    }

    fn flags(&self) -> NetFlags {
        self.inner.read().flags
    }

    fn capabilities(&self) -> NetCapabilities {
        self.inner.read().capabilities
    }

    fn device_short_name(&self) -> Cow<'static, str> {
        let bdf = self.inner.read().info.get_bdf();
        format!("{DEVICE_SHORT_NAME}-{bdf}").into()
    }

    fn link_status(&self) -> LinkStatus {
        let inner = self.inner.read();
        if inner.link_up {
            LinkStatus::UpFullDuplex
        } else {
            LinkStatus::Down
        }
    }

    fn link_speed(&self) -> u64 {
        self.inner.read().link_mbps
    }

    fn mac_address(&self) -> [u8; 6] {
        self.inner.read().mac_addr
    }

    fn can_send(&self) -> bool {
        let inner = self.inner.read();
        inner.flags.contains(NetFlags::RUNNING) && inner.link_up
    }

    // ── UP / DOWN ─────────────────────────────────────────────────────────────

    fn up(&self) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();
        if inner.flags.contains(NetFlags::UP) {
            return Err(NetDevError::AlreadyUp);
        }
        inner.init().map_err(|e| {
            log::error!("atl: init failed: {e}");
            NetDevError::DeviceError
        })?;
        inner.flags.insert(NetFlags::UP);
        Ok(())
    }

    fn down(&self) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();
        if !inner.flags.contains(NetFlags::UP) {
            return Err(NetDevError::AlreadyDown);
        }
        inner.stop();
        inner.flags.remove(NetFlags::UP);
        Ok(())
    }

    // ── TX ────────────────────────────────────────────────────────────────────

    fn send(&self, data: EtherFrameRef, que_id: usize) -> Result<(), NetDevError> {
        let inner = self.inner.read();

        if !inner.flags.contains(NetFlags::RUNNING) || !inner.link_up {
            return Err(NetDevError::DeviceError);
        }

        let que = &inner.que[que_id];
        let mut node = MCSNode::new();
        let mut tx = que.tx.lock(&mut node);

        // Reclaim completed descriptors to make room.
        if tx.free_slots() == 0 {
            tx.reclaim(&inner.info, que_id);
        }

        if !tx.post_packet(data.data) {
            return Err(NetDevError::DeviceError);
        }

        // Notify hardware of the new tail.
        write_reg(&inner.info, tx_ring_tail(que_id), tx.sw_tail as u32)
            .map_err(|_| NetDevError::DeviceError)
    }

    // ── RX ────────────────────────────────────────────────────────────────────

    fn recv(&self, que_id: usize) -> Result<Option<EtherFrameBuf>, NetDevError> {
        let inner = self.inner.read();

        // First try the software queue.
        {
            let que = &inner.que[que_id];
            let mut node = MCSNode::new();
            let mut rx = que.rx.lock(&mut node);
            if let Some(frame) = rx.recv_queue.pop() {
                return Ok(Some(frame));
            }
        }

        // Drain hardware ring into software queue.
        inner.rx_drain(que_id);

        let que = &inner.que[que_id];
        let mut node = MCSNode::new();
        let mut rx = que.rx.lock(&mut node);
        Ok(rx.recv_queue.pop())
    }

    // ── Interrupts ────────────────────────────────────────────────────────────

    fn interrupt(&self, irq: u16) -> Result<(), NetDevError> {
        let inner = self.inner.read();
        inner.handle_interrupt(irq);
        Ok(())
    }

    fn irqs(&self) -> Vec<u16> {
        let inner = self.inner.read();
        inner.irq_to_role.keys().copied().collect()
    }

    fn rx_irq_to_que_id(&self, _irq: u16) -> Option<usize> {
        Some(0)
    }

    // ── Polling ───────────────────────────────────────────────────────────────

    fn poll_mode(&self) -> bool {
        self.inner.read().is_poll_mode
    }

    fn poll(&self) -> bool {
        let inner = self.inner.read();
        if !inner.flags.contains(NetFlags::RUNNING) {
            return false;
        }
        // Check if the hardware head has advanced (= new data arrived).
        if let Ok(hw_head) = read_reg(&inner.info, rx_ring_head(0)) {
            let que = &inner.que[0];
            let mut node = MCSNode::new();
            let rx = que.rx.lock(&mut node);
            (hw_head as usize % Rx::ring_len()) != rx.hw_head
        } else {
            false
        }
    }

    fn poll_in_service(&self) -> Result<(), NetDevError> {
        let inner = self.inner.read();
        inner.rx_drain(0);
        Ok(())
    }

    // ── Periodic tick ─────────────────────────────────────────────────────────

    fn tick_msec(&self) -> Option<u64> {
        Some(TICK_MSEC)
    }

    fn tick(&self) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();
        inner.update_link_status();
        Ok(())
    }

    // ── Multicast ─────────────────────────────────────────────────────────────

    fn add_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();
        inner.multicast_addrs.add_addr(*addr);
        // Enable promiscuous multicast so all multicast frames pass.
        // A proper hash-filter implementation can replace this later.
        if inner.flags.contains(NetFlags::UP) {
            let _ = write_reg(&inner.info, RPB_RX_BUF_ENABLE, 1);
        }
        Ok(())
    }

    fn remove_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();
        inner.multicast_addrs.remove_addr(addr);
        Ok(())
    }
}
