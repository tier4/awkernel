use crate::pcie::{
    capability::virtio::VirtioCap,
    pcie_id,
    virtio::config::{
        virtio_common_config::VirtioCommonConfig, virtio_net_config::VirtioNetConfig,
        virtio_notify_config::VirtioNotifyConfig,
    },
    virtio::VirtioDriverErr,
    PCIeDevice, PCIeDeviceErr, PCIeInfo,
};
use alloc::{
    borrow::Cow,
    boxed::Box,
    collections::{BTreeMap, LinkedList},
    format,
    sync::Arc,
    vec::Vec,
};
use awkernel_async_lib_verified::ringq::RingQ;
use awkernel_lib::{
    addr::Addr,
    barrier::{membar_consumer, membar_producer, membar_sync},
    dma_pool::DMAPool,
    interrupt::IRQ,
    net::net_device::{
        EtherFrameBuf, EtherFrameRef, LinkStatus, NetCapabilities, NetDevError, NetDevice, NetFlags,
    },
    paging::PAGESIZE,
    sync::{
        mutex::{MCSNode, Mutex},
        rwlock::RwLock,
    },
};

const DEVICE_SHORT_NAME: &str = "virtio-net";

const RECV_QUEUE_SIZE: usize = 32; // To Be Determined

const VIRTIO_NET_ID: u16 = 0x1041;

// device-specific feature bits
const VIRTIO_NET_F_MAC: u64 = 1 << 5;
const VIRTIO_NET_F_MRG_RXBUF: u64 = 1 << 15;
const VIRTIO_NET_F_STATUS: u64 = 1 << 16;
const VIRTIO_NET_F_CTRL_VQ: u64 = 1 << 17;
const VIRTIO_NET_F_SPEED_DUPLEX: u64 = 1 << 63;

// Reserved Feature Bits
const VIRTIO_F_NOTIFY_ON_EMPTY: u64 = 1 << 24;
const VIRTIO_F_EVENT_IDX: u64 = 1 << 29;
const VIRTIO_F_VERSION_1: u64 = 1 << 32;
const VIRTIO_F_ACCESS_PLATFORM: u64 = 1 << 33;

// device status bits
const VIRTIO_CONFIG_DEVICE_STATUS_RESET: u8 = 0;
const VIRTIO_CONFIG_DEVICE_STATUS_ACK: u8 = 1;
const VIRTIO_CONFIG_DEVICE_STATUS_DRIVER: u8 = 2;
const VIRTIO_CONFIG_DEVICE_STATUS_DRIVER_OK: u8 = 4;
const VIRTIO_CONFIG_DEVICE_STATUS_FEATURES_OK: u8 = 8;
const _VIRTIO_CONFIG_DEVICE_STATUS_DEVICE_NEEDS_RESET: u8 = 64;
const VIRTIO_CONFIG_DEVICE_STATUS_FAILED: u8 = 128;

// Virtio Structure PCI Capabilities cfg_type
const VIRTIO_PCI_CAP_COMMON_CFG: u8 = 1; // Common configuration
const VIRTIO_PCI_CAP_NOTIFY_CFG: u8 = 2; // Notifications
const _VIRTIO_PCI_CAP_ISR_CFG: u8 = 3; // ISR Status
const VIRTIO_PCI_CAP_DEVICE_CFG: u8 = 4; // Device specific configuration
const _VIRTIO_PCI_CAP_PCI_CFG: u8 = 5; // PCI configuration access
const _VIRTIO_PCI_CAP_SHARED_MEMORY_CFG: u8 = 8; // Shared memory region
const _VIRTIO_PCI_CAP_VENDOR_CFG: u8 = 9; // Vendor-specific data

const VIRTIO_NET_S_LINK_UP: u16 = 1;

const MAX_VQ_SIZE: usize = 256; // TODO: to be considered

const VIRTQ_DESC_F_NEXT: u16 = 1; // This marks a buffer as continuing via the next field.
const VIRTQ_DESC_F_WRITE: u16 = 2; // This marks a buffer as write-only (otherwise read-only).

// The device uses this in used->flags to advise the driver: don’t kick me when you add a buffer.
// It’s unreliable, so it’s simply an optimization.
const VIRTQ_USED_F_NO_NOTIFY: u16 = 1;

// The driver uses this in avail->flags to advise the device: don’t interrupt me when you consume a buffer.
// It’s unreliable, so it’s simply an optimization.
const VRING_AVAIL_F_NO_INTERRUPT: u16 = 1;

const MCLSHIFT: u32 = 11;
const MCLBYTES: u32 = 1 << MCLSHIFT;
type RxTxBuffer = [[u8; MCLBYTES as usize]; MAX_VQ_SIZE];

pub enum IRQType {
    Config,
    Control,
    Queue(usize),
}

// TODO: support MSI and legacy interrupts
enum PCIeInt {
    None,
    MsiX(Vec<(IRQ, IRQType)>),
}

#[derive(Copy, Clone)]
struct VirtqueueEnrty {
    index: u16, // index in VirtqDesc array
    next: i16,  // next enq slot
}

// Virtio ring descriptors: 16 bytes.
// These can chain together via "next".
#[repr(C, packed)]
#[derive(Default, Copy, Clone)]
struct VirtqDesc {
    addr: u64,  // Address (guest-physical).
    len: u32,   // Length.
    flags: u16, // The flags as indicated above.
    next: u16,  // Next field if flags & NEXT.
}

#[repr(C, packed)]
struct VirtqAvail {
    flags: u16,
    idx: u16,
    ring: [u16; MAX_VQ_SIZE],
    used_event: u16, // Only if VIRTIO_F_EVENT_IDX
}

impl Default for VirtqAvail {
    fn default() -> Self {
        VirtqAvail {
            flags: 0,
            idx: 0,
            ring: [0; MAX_VQ_SIZE],
            used_event: 0,
        }
    }
}

// u32 is used here for ids for padding reasons.
#[repr(C, packed)]
#[derive(Default, Copy, Clone)]
struct VirtqUsedElem {
    id: u32, // Index of start of used descriptor chain.
    len: u32, // The number of bytes written into the device writable portion of
             // the buffer described by the descriptor chain.
}

#[repr(C, packed)]
struct VirtqUsed {
    flags: u16,
    idx: u16,
    ring: [VirtqUsedElem; MAX_VQ_SIZE],
    avail_event: u16, // Only if VIRTIO_F_EVENT_IDX
}

impl Default for VirtqUsed {
    fn default() -> Self {
        VirtqUsed {
            flags: 0,
            idx: 0,
            ring: [VirtqUsedElem::default(); MAX_VQ_SIZE],
            avail_event: 0,
        }
    }
}

// This is the memory layout on DMA
#[repr(C, packed)]
struct VirtqDMA {
    desc: [VirtqDesc; MAX_VQ_SIZE], // 4096 bytes
    avail: VirtqAvail,              // 518 bytes
    _pad: [u8; 3578],               // 4096 - 518 = 3578 bytes
    used: VirtqUsed,                // 2054 bytes
    _pad2: [u8; 2042],              // 4096 - 2054 = 2042 bytes
} // 4096 * 3 = 12288 bytes in total

impl Default for VirtqDMA {
    fn default() -> Self {
        VirtqDMA {
            desc: [VirtqDesc::default(); MAX_VQ_SIZE],
            avail: VirtqAvail::default(),
            _pad: [0; 3578],
            used: VirtqUsed::default(),
            _pad2: [0; 2042],
        }
    }
}

struct Virtq {
    vq_dma: DMAPool<VirtqDMA>,
    vq_freelist: LinkedList<usize>,
    vq_entries: [VirtqueueEnrty; MAX_VQ_SIZE],
    vq_num: usize,
    vq_mask: usize,
    vq_avail_idx: u16,
    vq_used_idx: u16,
    vq_index: u16,
    vq_intr_vec: u16,

    is_event_idx: bool,
    data_buf: DMAPool<RxTxBuffer>,
    rx_buffer: RingQ<EtherFrameBuf>,
    tx_hdrs: DMAPool<[VirtioNetHdr; MAX_VQ_SIZE]>,
}

impl Virtq {
    fn init(&mut self) {
        assert!(self.vq_num > 0);

        self.vq_freelist = LinkedList::new();
        for i in (0..self.vq_num).rev() {
            self.vq_freelist.push_front(i);
            self.vq_entries[i].index = i as u16;
        }

        self.vq_avail_idx = 0;
        self.vq_used_idx = 0;
    }

    fn vq_alloc_entry(&mut self) -> Option<usize> {
        self.vq_freelist.pop_front()
    }

    fn vq_free_entry(&mut self, slot: usize) {
        self.vq_freelist.push_front(slot);
    }

    /// enqueue_prep: allocate a slot number
    fn virtio_enqueue_prep(&mut self) -> Option<usize> {
        let slot = self.vq_alloc_entry()?;
        self.vq_entries[slot].next = -1; // next slot is not allocated yet
        Some(slot)
    }

    /// enqueue_reserve: allocate remaining slots and build the descriptor chain.
    /// Calls virtio_enqueue_abort() on failure.
    fn virtio_enqueue_reserve(&mut self, slot: usize, nsegs: usize) -> Result<(), VirtioDriverErr> {
        debug_assert!(self.vq_entries[slot].next == -1);
        debug_assert!((1..=MAX_VQ_SIZE).contains(&nsegs));

        self.vq_entries[slot].next = self.vq_entries[slot].index as i16;

        let mut s = slot;
        for _ in 0..nsegs - 1 {
            let next_slot = if let Some(slot) = self.vq_alloc_entry() {
                slot
            } else {
                self.vq_dma.as_mut().desc[s].flags = 0;
                self.virtio_enqueue_abort(slot);
                return Err(VirtioDriverErr::NoSlot);
            };

            self.vq_dma.as_mut().desc[s].flags = VIRTQ_DESC_F_NEXT;
            self.vq_dma.as_mut().desc[s].next = next_slot as u16;
            s = next_slot;
        }

        self.vq_dma.as_mut().desc[s].flags = 0;

        Ok(())
    }

    /// enqueue: enqueue a single dmamap.
    fn virtio_enqueue(&mut self, slot: usize, phy_addr: usize, len: usize, write: bool) {
        let next_slot = self.vq_entries[slot].next;
        debug_assert!(next_slot >= 0);

        let desc = &mut self.vq_dma.as_mut().desc[next_slot as usize];

        desc.addr = phy_addr as u64;
        desc.len = len as u32;
        if !write {
            desc.flags |= VIRTQ_DESC_F_WRITE;
        }
        let next_slot = desc.next;

        self.vq_entries[slot].next = next_slot as i16;
    }

    fn virtio_enqueue_p(&mut self, slot: usize, phy_addr: usize, len: usize, write: bool) {
        let next_slot = self.vq_entries[slot].next;
        debug_assert!(next_slot >= 0);

        let desc = &mut self.vq_dma.as_mut().desc[next_slot as usize];
        desc.addr = phy_addr as u64;
        desc.len = len as u32;
        if !write {
            desc.flags |= VIRTQ_DESC_F_WRITE;
        }

        self.vq_entries[slot].next = desc.next as i16;
    }

    /// enqueue_commit: add it to the available ring.
    fn virtio_enqueue_commit(&mut self, slot: usize) {
        let avail = &mut self.vq_dma.as_mut().avail;

        avail.ring[self.vq_avail_idx as usize & self.vq_mask] = slot as u16;
        self.vq_avail_idx += 1;
    }

    /// dequeue: dequeue a request from uring.
    fn virtio_dequeue(&mut self) -> Option<(usize, u32)> {
        if self.vq_used_idx == self.vq_dma.as_ref().used.idx {
            return None;
        }

        let used_idx = self.vq_used_idx & self.vq_mask as u16;
        self.vq_used_idx += 1;

        membar_consumer();

        let used_ring = &self.vq_dma.as_ref().used.ring[used_idx as usize];
        Some((used_ring.id as usize, used_ring.len))
    }

    /// dequeue_commit: complete dequeue; the slot is recycled for future use.
    /// if you forget to call this the slot will be leaked.
    fn virtio_dequeue_commit(&mut self, slot: usize) -> u16 {
        let mut freed = 1;
        let mut s = slot;

        while self.vq_dma.as_ref().desc[s].flags & VIRTQ_DESC_F_NEXT != 0 {
            self.vq_free_entry(s);
            s = self.vq_dma.as_ref().desc[s].next as usize;
            freed += 1;
        }
        self.vq_free_entry(s);

        freed
    }

    /// Increase the event index in order to delay interrupts.
    /// Returns false on success; returns true if the used ring has already advanced
    /// too far, and the caller must process the queue again (otherwise, no
    /// more interrupts will happen).
    fn virtio_postpone_intr(&mut self, nslots: u16) -> bool {
        let idx = self.vq_used_idx + nslots;

        // set the new event index: avail_ring->used_event = idx
        self.vq_dma.as_mut().avail.used_event = idx;
        membar_sync();

        // number of slots in the used ring available to be supplied to the avail ring.
        let nused = self.vq_dma.as_ref().used.idx - self.vq_used_idx;
        debug_assert!(nused < self.vq_num as u16);

        nslots < nused
    }

    /// Postpone interrupt until 3/4 of the available descriptors have been consumed.
    fn virtio_postpone_intr_smart(&mut self) -> bool {
        let nslots = (self.vq_dma.as_ref().avail.idx - self.vq_used_idx) * 3 / 4;
        self.virtio_postpone_intr(nslots)
    }

    /// Postpone interrupt until all of the available descriptors have been consumed.
    fn virtio_postpone_intr_far(&mut self) -> bool {
        let nslots = self.vq_dma.as_ref().avail.idx - self.vq_used_idx;
        self.virtio_postpone_intr(nslots)
    }

    /// enqueue_abort: rollback.
    fn virtio_enqueue_abort(&mut self, slot: usize) {
        if self.vq_entries[slot].next < 0 {
            self.vq_free_entry(slot);
            return;
        }

        let mut s = slot;
        while self.vq_dma.as_mut().desc[s].flags & VIRTQ_DESC_F_NEXT != 0 {
            self.vq_free_entry(s);
            s = self.vq_dma.as_mut().desc[s].next as usize;
        }

        self.vq_free_entry(s);
    }

    /// Stop vq interrupt.  No guarantee.
    fn virtio_stop_vq_intr(&mut self) {
        if self.is_event_idx {
            // No way to disable the interrupt completely with RingEventIdx.
            // Instead advance used_event by half the possible value.
            // This won't happen soon and is far enough in the past to not trigger a spurious interrupt.
            self.vq_dma.as_mut().avail.used_event = self.vq_used_idx + 0x8000;
        } else {
            self.vq_dma.as_mut().avail.flags |= VRING_AVAIL_F_NO_INTERRUPT;
        }
    }

    /// Start vq interrupt.  No guarantee.
    fn virtio_start_vq_intr(&mut self) -> bool {
        // If event index feature is negotiated,
        // enabling interrupts is done through setting the latest consumed index in the used_event field
        if self.is_event_idx {
            self.vq_dma.as_mut().avail.used_event = self.vq_used_idx;
        } else {
            self.vq_dma.as_mut().avail.flags &= !VRING_AVAIL_F_NO_INTERRUPT;
        }

        membar_sync();

        self.vq_used_idx != self.vq_dma.as_ref().used.idx
    }

    fn publish_avail_idx(&mut self) {
        membar_producer();
        self.vq_dma.as_mut().avail.idx = self.vq_avail_idx;
    }

    /// add mbufs for all the empty receive slots
    fn vio_populate_rx_mbufs(&mut self) -> bool {
        let mut should_notify = false;
        for _ in 0..self.vq_num {
            let slot = if let Some(slot) = self.virtio_enqueue_prep() {
                slot
            } else {
                break;
            };

            // NOTE: assume nsegs in rx dmamap is 1
            if self.virtio_enqueue_reserve(slot, 1).is_err() {
                break;
            }

            let data_phy_addr = self.data_buf.get_phy_addr().as_usize() + slot * MCLBYTES as usize;
            self.virtio_enqueue(slot, data_phy_addr, MCLBYTES as usize, false);
            self.virtio_enqueue_commit(slot);
            should_notify = true;
        }

        should_notify
    }

    /// dequeue received packets
    fn vio_rxeof(&mut self) -> u16 {
        let mut freed = 0;

        while let Some((slot, len)) = self.virtio_dequeue() {
            let buf = self.data_buf.as_mut();
            let data = buf[slot];

            let header_len = core::mem::size_of::<VirtioNetHdr>();
            let header = &data[0..header_len];
            let header = unsafe { &*(header.as_ptr() as *const VirtioNetHdr) };

            if header.num_buffers > 1 {
                log::error!(
                    "virtio-net: num_buffers > 1. Receipt of large packets is not supported"
                );
                break;
            }

            let data = data[header_len..len as usize].to_vec();

            self.rx_buffer
                .push(EtherFrameBuf { data, vlan: None })
                .unwrap();

            freed += self.virtio_dequeue_commit(slot);
        }

        freed
    }

    fn vio_rx_intr(&mut self) -> bool {
        let freed = self.vio_rxeof();
        if freed > 0 {
            self.vio_populate_rx_mbufs()
        } else {
            false
        }
    }

    fn vio_tx_dequeue(&mut self) -> u16 {
        let mut freed = 0;
        while let Some((slot, _len)) = self.virtio_dequeue() {
            freed += self.virtio_dequeue_commit(slot);
        }

        freed
    }

    fn vio_txeof(&mut self) {
        let freed = self.vio_tx_dequeue();
        if freed > 0 {
            self.virtio_stop_vq_intr();
        }
    }

    fn vio_tx_intr(&mut self) {
        self.vio_txeof();
    }

    fn vio_encap(&mut self, slot: usize, frame: &EtherFrameRef) -> (usize, usize) {
        let len = frame.data.len();
        let buf = self.data_buf.as_mut()[slot].as_mut_ptr();
        unsafe {
            core::ptr::copy_nonoverlapping(frame.data.as_ptr(), buf, len);
        }

        let data_phy_addr = self.data_buf.get_phy_addr().as_usize() + slot * MCLBYTES as usize;
        (data_phy_addr, len)
    }

    fn vio_start(&mut self, frame: &EtherFrameRef) {
        self.vio_tx_dequeue();

        let slot = if let Some(slot) = self.virtio_enqueue_prep() {
            slot
        } else {
            log::error!("virtio-net: virtio_enqueue_prep failed");
            return;
        };

        // NOTE: assume nsegs in tx dmamap is 1. +1 is for the header
        if self.virtio_enqueue_reserve(slot, 1 + 1).is_err() {
            log::error!("virtio-net: virtio_enqueue_reserve failed");
            return;
        }

        let header_len = core::mem::size_of::<VirtioNetHdr>();
        let header_phy_addr = self.tx_hdrs.get_phy_addr().as_usize() + slot * header_len;
        self.virtio_enqueue_p(slot, header_phy_addr, header_len, true);

        let (data_phy_addr, data_len) = self.vio_encap(slot, frame);
        self.virtio_enqueue(slot, data_phy_addr, data_len, true);

        self.virtio_enqueue_commit(slot);

        let should_dequeue = if self.is_event_idx {
            self.virtio_postpone_intr_smart()
        } else {
            self.virtio_start_vq_intr()
        };

        if should_dequeue {
            self.vio_tx_dequeue();
        }
    }

    fn vio_ctrleof(&mut self) {
        while let Some((slot, _)) = self.virtio_dequeue() {
            self.virtio_dequeue_commit(slot);
            if !self.virtio_start_vq_intr() {
                break;
            }
        }
    }
}

/// Packet header structure
#[repr(C, packed)]
#[derive(Default, Copy, Clone)]
struct VirtioNetHdr {
    flags: u8,
    gso_type: u8,
    hdr_len: u16,
    gso_size: u16,
    csum_start: u16,
    csum_offset: u16,
    num_buffers: u16, // only present if VIRTIO_NET_F_MRG_RXBUF is negotiated
}

const _VIRTIO_NET_HDR_F_NEEDS_CSUM: u8 = 1;
const _VIRTIO_NET_HDR_F_DATA_VALID: u8 = 2;
const _VIRTIO_NET_HDR_GSO_NONE: u8 = 0;
const _VIRTIO_NET_HDR_GSO_TCPV4: u8 = 1;
const _VIRTIO_NET_HDR_GSO_UDP: u8 = 3;
const _VIRTIO_NET_HDR_GSO_TCPV6: u8 = 4;
const _VIRTIO_NET_HDR_GSO_ECN: u8 = 0x80;

pub fn match_device(vendor: u16, id: u16) -> bool {
    vendor == pcie_id::VIRTIO_VENDOR_ID && id == VIRTIO_NET_ID
}

pub fn attach(mut info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    // Non-transitional devices SHOULD have a PCI Revision ID of 1 or higher.
    if info.get_revision_id() == 0 {
        return Err(PCIeDeviceErr::RevisionIDMismatch);
    }

    // Map the memory regions of MMIO.
    if let Err(e) = info.map_bar() {
        log::warn!("Failed to map the memory regions of MMIO: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }

    // Read capabilities of PCIe.
    info.read_capability();

    let virtio_net = VirtioNet::new(info)?;

    let result = Arc::new(virtio_net);

    awkernel_lib::net::add_interface(result.clone(), None);

    Ok(result)
}

struct Queue {
    rx: Mutex<Virtq>,
    tx: Mutex<Virtq>,
}

struct VirtioNetInner {
    info: PCIeInfo,
    mac_addr: [u8; 6],
    common_cfg: VirtioCommonConfig,
    net_cfg: VirtioNetConfig,
    notify_cfg: VirtioNotifyConfig,
    notify_off_multiplier: u32,
    driver_features: u64,
    active_features: u64,
    flags: NetFlags,
    capabilities: NetCapabilities,
    virtqueues: Vec<Queue>,
    ctrl_vq: Option<Mutex<Virtq>>,
    irq_to_type: BTreeMap<u16, IRQType>,
    pcie_int: PCIeInt,
}

impl VirtioNetInner {
    pub fn new(info: PCIeInfo) -> Self {
        Self {
            info,
            mac_addr: [0; 6],
            common_cfg: VirtioCommonConfig::default(),
            net_cfg: VirtioNetConfig::default(),
            notify_cfg: VirtioNotifyConfig::default(),
            notify_off_multiplier: 0,
            driver_features: 0,
            active_features: 0,
            flags: NetFlags::empty(),
            capabilities: NetCapabilities::empty(),
            virtqueues: Vec::new(),
            ctrl_vq: None,
            irq_to_type: BTreeMap::new(),
            pcie_int: PCIeInt::None,
        }
    }

    fn virtio_pci_find_capability(&self, cfg_type: u8) -> Result<VirtioCap, VirtioDriverErr> {
        for cap in &self.info.virtio_caps {
            if cap.get_cfg_type() == cfg_type {
                return Ok(cap.clone());
            }
        }
        Err(VirtioDriverErr::NoCap)
    }

    fn virtio_pci_attach_10(&mut self) -> Result<(), VirtioDriverErr> {
        let common_cfg_cap = self.virtio_pci_find_capability(VIRTIO_PCI_CAP_COMMON_CFG)?;
        let net_cfg_cap = self.virtio_pci_find_capability(VIRTIO_PCI_CAP_DEVICE_CFG)?;
        let notify_cap = self.virtio_pci_find_capability(VIRTIO_PCI_CAP_NOTIFY_CFG)?;

        self.notify_off_multiplier = notify_cap.get_notify_off_multiplier();

        self.common_cfg.init(&self.info, common_cfg_cap)?;
        self.net_cfg.init(&self.info, net_cfg_cap)?;
        self.notify_cfg.init(&self.info, notify_cap)?;

        Ok(())
    }

    fn virtio_pci_attach(&mut self) -> Result<(), VirtioDriverErr> {
        // TODO: setup MSIX

        self.virtio_pci_attach_10()?;

        self.common_cfg
            .virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_RESET)?;
        self.common_cfg
            .virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_ACK)?;
        self.common_cfg
            .virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_DRIVER)?;

        Ok(())
    }

    fn vio_attach(&mut self) -> Result<(), VirtioDriverErr> {
        self.driver_features = 0;
        self.driver_features |= VIRTIO_F_EVENT_IDX;
        self.driver_features |= VIRTIO_NET_F_MAC;
        self.driver_features |= VIRTIO_NET_F_MRG_RXBUF;
        self.driver_features |= VIRTIO_NET_F_STATUS;
        self.driver_features |= VIRTIO_NET_F_CTRL_VQ;
        self.driver_features |= VIRTIO_NET_F_SPEED_DUPLEX;

        self.virtio_pci_negotiate_features()?;

        if self.virtio_has_feature(VIRTIO_NET_F_MAC) {
            self.mac_addr = self.net_cfg.virtio_get_mac_addr()?;
        } else {
            todo!()
        }

        self.capabilities = NetCapabilities::empty();
        self.flags = NetFlags::BROADCAST | NetFlags::SIMPLEX | NetFlags::MULTICAST;

        let num_queues = 1; // TODO: support multiple queues
        for i in 0..num_queues {
            let mut rx = self.virtio_alloc_vq(2 * i)?;
            rx.virtio_start_vq_intr();
            rx.vq_intr_vec = i + 2;

            let mut tx = self.virtio_alloc_vq(2 * i + 1)?;
            if self.virtio_has_feature(VIRTIO_F_EVENT_IDX) {
                tx.virtio_postpone_intr_far();
            } else {
                tx.virtio_stop_vq_intr();
            }
            tx.vq_intr_vec = i + 2;

            self.virtqueues.push(Queue {
                rx: Mutex::new(rx),
                tx: Mutex::new(tx),
            });
        }

        if self.virtio_has_feature(VIRTIO_NET_F_CTRL_VQ) {
            let vq_index = 2; // NOTE: when VIRTIO_NET_F_CTRL_VQ is negotiated, vq_index changes.
            let mut vq = self.virtio_alloc_vq(vq_index)?;
            vq.vq_intr_vec = 1;
            vq.virtio_start_vq_intr();

            self.ctrl_vq = Some(Mutex::new(vq));
        }

        {
            let mut irqs = Vec::new();

            let irq = self.virtio_pci_msix_establish(0, IRQType::Config)?;
            irqs.push((irq, IRQType::Config));

            let irq = self.virtio_pci_msix_establish(1, IRQType::Control)?;
            irqs.push((irq, IRQType::Control));

            for i in 0..num_queues {
                let irq = self.virtio_pci_msix_establish(i + 2, IRQType::Queue(i as usize))?;
                irqs.push((irq, IRQType::Queue(i as usize)));
            }

            self.pcie_int = PCIeInt::MsiX(irqs);
        }

        self.virtio_attach_finish()?;

        Ok(())
    }

    fn virtio_pci_negotiate_features(&mut self) -> Result<(), VirtioDriverErr> {
        self.active_features = 0;

        // TODO: VIRTIO_F_RING_INDIRECT_DESC related setup

        self.virtio_pci_negotiate_features_10()?;

        Ok(())
    }

    fn virtio_pci_negotiate_features_10(&mut self) -> Result<(), VirtioDriverErr> {
        self.driver_features |= VIRTIO_F_VERSION_1;

        // Without this SEV doesn't work with a KVM/qemu hypervisor on amd64
        self.driver_features |= VIRTIO_F_ACCESS_PLATFORM;

        // notify on empty is 0.9 only
        self.driver_features &= !VIRTIO_F_NOTIFY_ON_EMPTY;

        let device_features = self.common_cfg.virtio_get_device_features()?;

        let negotiated_features = device_features & self.driver_features;

        self.common_cfg
            .virtio_set_driver_features(negotiated_features);

        self.common_cfg
            .virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_FEATURES_OK)?;

        let device_status = self.common_cfg.virtio_get_device_status()?;
        if device_status & VIRTIO_CONFIG_DEVICE_STATUS_FEATURES_OK == 0 {
            self.common_cfg
                .virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_FAILED)?;
            return Err(VirtioDriverErr::InitFailure);
        }

        self.active_features = negotiated_features;

        if negotiated_features & VIRTIO_F_VERSION_1 == 0
            || negotiated_features & VIRTIO_NET_F_MRG_RXBUF == 0
        {
            self.common_cfg
                .virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_FAILED)?;
            return Err(VirtioDriverErr::InitFailure);
        }

        Ok(())
    }

    fn virtio_pci_setup_queue(&mut self, vq_idx: u16, addr: u64) -> Result<(), VirtioDriverErr> {
        self.common_cfg.virtio_set_queue_select(vq_idx)?;

        if addr == 0 {
            self.common_cfg.virtio_set_queue_enable(0)?;
            self.common_cfg.virtio_set_queue_desc(0)?;
            self.common_cfg.virtio_set_queue_avail(0)?;
            self.common_cfg.virtio_set_queue_used(0)?;
        } else {
            let avail_offset = 4096; // TODO: offset of _avail in VirtqDMA
            let used_offset = 8192; // TODO: offset of _used in VirtqDMA
            self.common_cfg.virtio_set_queue_desc(addr)?;
            self.common_cfg
                .virtio_set_queue_avail(addr + avail_offset)?;
            self.common_cfg.virtio_set_queue_used(addr + used_offset)?;
            self.common_cfg.virtio_set_queue_enable(1)?;
        }

        Ok(())
    }

    fn virtio_pci_read_queue_size(&mut self, idx: u16) -> Result<u16, VirtioDriverErr> {
        self.common_cfg.virtio_set_queue_select(idx)?;
        self.common_cfg.virtio_get_queue_size()
    }

    fn virtio_pci_set_msix_config_vector(&mut self, vector: u16) -> Result<(), VirtioDriverErr> {
        self.common_cfg.virtio_set_config_msix_vector(vector)
    }

    fn virtio_pci_set_msix_queue_vector(
        &mut self,
        idx: u16,
        vector: u16,
    ) -> Result<(), VirtioDriverErr> {
        self.common_cfg.virtio_set_queue_select(idx)?;
        self.common_cfg.virtio_set_queue_msix_vector(vector)
    }

    fn virtio_pci_kick(&mut self, idx: u16) -> Result<(), VirtioDriverErr> {
        let queue_notify_off = self.common_cfg.virtio_get_queue_notify_off()? as usize;
        let notify_off_multiplier = self.notify_off_multiplier as usize;
        let offset = queue_notify_off * notify_off_multiplier;
        self.notify_cfg.virtio_set_notify(offset, idx)
    }

    fn virtio_pci_msix_establish(
        &mut self,
        idx: u16,
        irq_type: IRQType,
    ) -> Result<IRQ, VirtioDriverErr> {
        let segment_number = self.info.segment_group as usize;
        let bfd = self.info.get_bfd();
        let msix = self
            .info
            .get_msix_mut()
            .ok_or(VirtioDriverErr::InitFailure)?;
        let irq_name = format!("{DEVICE_SHORT_NAME}-{bfd}-{idx}");
        let mut irq_new = msix
            .register_handler(
                irq_name.into(),
                Box::new(move |irq| {
                    awkernel_lib::net::net_interrupt(irq);
                }),
                segment_number,
                awkernel_lib::cpu::raw_cpu_id() as u32,
                idx as usize,
            )
            .or(Err(VirtioDriverErr::InitFailure))?;
        irq_new.enable();

        self.irq_to_type.insert(irq_new.get_irq(), irq_type);

        let msix = self.info.get_msix_mut().unwrap();
        msix.enable();

        Ok(irq_new)
    }

    fn virtio_pci_setup_intrs(&mut self) -> Result<(), VirtioDriverErr> {
        for i in 0..self.virtqueues.len() {
            let (idx, vector) = {
                let mut node = MCSNode::new();
                let rx = self.virtqueues[i].rx.lock(&mut node);
                (rx.vq_index, rx.vq_intr_vec)
            };
            self.virtio_pci_set_msix_queue_vector(idx, vector)?;

            let (idx, vector) = {
                let mut node = MCSNode::new();
                let tx = self.virtqueues[i].tx.lock(&mut node);
                (tx.vq_index, tx.vq_intr_vec)
            };
            self.virtio_pci_set_msix_queue_vector(idx, vector)?;
        }

        self.virtio_pci_set_msix_config_vector(0)
    }

    fn virtio_pci_attach_finish(&mut self) -> Result<(), VirtioDriverErr> {
        // NOTE: msix is already assigned by vio_attach()
        Ok(())
    }

    fn virtio_has_feature(&self, feature: u64) -> bool {
        self.active_features & feature != 0
    }

    fn virtio_attach_finish(&mut self) -> Result<(), VirtioDriverErr> {
        self.virtio_pci_attach_finish()?;
        self.virtio_pci_setup_intrs()?;

        for i in 0..self.virtqueues.len() {
            let (idx, phy_addr) = {
                let mut node = MCSNode::new();
                let rx = self.virtqueues[i].rx.lock(&mut node);
                (rx.vq_index, rx.vq_dma.get_phy_addr().as_usize() as u64)
            };
            self.virtio_pci_setup_queue(idx, phy_addr)?;

            let (idx, phy_addr) = {
                let mut node = MCSNode::new();
                let tx = self.virtqueues[i].tx.lock(&mut node);
                (tx.vq_index, tx.vq_dma.get_phy_addr().as_usize() as u64)
            };
            self.virtio_pci_setup_queue(idx, phy_addr)?;
        }

        self.common_cfg
            .virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_DRIVER_OK)?;

        Ok(())
    }

    /// To reset the device to a known state, do following:
    ///  virtio_reset();              // this will stop the device activity
    ///  <dequeue finished requests>; // virtio_dequeue() still can be called
    ///  <revoke pending requests in the vqs if any>;
    ///  virtio_reinit_start();       // dequeue prohibited
    ///  <some other initialization>;
    ///  virtio_reinit_end();         // device activated; enqueue allowed
    /// Once attached, features are assumed to not change again.
    fn virtio_reset(&mut self) -> Result<(), VirtioDriverErr> {
        self.common_cfg
            .virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_RESET)?;
        self.active_features = 0;
        Ok(())
    }

    fn virtio_reinit_start(&mut self) -> Result<(), VirtioDriverErr> {
        self.common_cfg
            .virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_ACK)?;
        self.common_cfg
            .virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_DRIVER)?;
        self.virtio_pci_negotiate_features()?;
        self.virtio_pci_setup_intrs()?;

        for i in 0..self.virtqueues.len() {
            let (vq_index, phy_addr) = {
                let mut node = MCSNode::new();
                let mut rx = self.virtqueues[i].rx.lock(&mut node);
                rx.init();
                (rx.vq_index, rx.vq_dma.get_phy_addr().as_usize() as u64)
            };
            self.virtio_pci_setup_queue(vq_index, phy_addr)?;

            let (vq_index, phy_addr) = {
                let mut node = MCSNode::new();
                let mut tx = self.virtqueues[i].tx.lock(&mut node);
                tx.init();
                (tx.vq_index, tx.vq_dma.get_phy_addr().as_usize() as u64)
            };
            self.virtio_pci_setup_queue(vq_index, phy_addr)?;
        }

        Ok(())
    }

    fn virtio_reinit_end(&mut self) -> Result<(), VirtioDriverErr> {
        self.common_cfg
            .virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_DRIVER_OK)?;

        Ok(())
    }

    /// Allocate a vq.
    fn virtio_alloc_vq(&mut self, index: u16) -> Result<Virtq, VirtioDriverErr> {
        let vq_size = self.virtio_pci_read_queue_size(index)? as usize;
        if vq_size == 0 {
            return Err(VirtioDriverErr::NoVirtqueue);
        }
        if (vq_size - 1) & vq_size != 0 {
            return Err(VirtioDriverErr::InvalidQueueSize);
        }
        if vq_size > MAX_VQ_SIZE {
            return Err(VirtioDriverErr::InvalidQueueSize);
        }

        // DMAPool for virtqueues
        let allocsize = core::mem::size_of::<VirtqDMA>();
        let pages = allocsize.div_ceil(PAGESIZE);
        let mut vq_dma: DMAPool<VirtqDMA> =
            DMAPool::new(0, pages).ok_or(VirtioDriverErr::DMAPool)?;
        *vq_dma.as_mut() = VirtqDMA::default();

        // DMAPool for sent/received data
        let allocsize = MCLBYTES as usize * MAX_VQ_SIZE;
        let pages = allocsize.div_ceil(PAGESIZE);
        let mut data_buf: DMAPool<RxTxBuffer> =
            DMAPool::new(0, pages).ok_or(VirtioDriverErr::DMAPool)?;
        for i in 0..MAX_VQ_SIZE {
            for j in 0..MCLBYTES as usize {
                data_buf.as_mut()[i][j] = 0u8;
            }
        }

        // DMAPool for tx headers
        let allocsize = core::mem::size_of::<VirtioNetHdr>() * MAX_VQ_SIZE;
        let pages = allocsize.div_ceil(PAGESIZE);
        let mut tx_hdrs: DMAPool<[VirtioNetHdr; MAX_VQ_SIZE]> =
            DMAPool::new(0, pages).ok_or(VirtioDriverErr::DMAPool)?;
        *tx_hdrs.as_mut() = [VirtioNetHdr::default(); MAX_VQ_SIZE];

        let mut vq = Virtq {
            vq_dma,
            vq_entries: [VirtqueueEnrty { index: 0, next: -1 }; MAX_VQ_SIZE],
            vq_freelist: LinkedList::new(),
            vq_num: vq_size,
            vq_mask: vq_size - 1,
            vq_avail_idx: 0,
            vq_used_idx: 0,
            vq_index: index,
            vq_intr_vec: 0,
            is_event_idx: self.virtio_has_feature(VIRTIO_F_EVENT_IDX),
            data_buf,
            rx_buffer: RingQ::new(RECV_QUEUE_SIZE),
            tx_hdrs,
        };

        vq.init();

        Ok(vq)
    }

    fn virtio_notify(&mut self, vq_idx: u16) -> Result<(), VirtioDriverErr> {
        let should_kick = {
            let queue_idx = (vq_idx / 2) as usize;
            let mut node = MCSNode::new();
            let vq = if vq_idx % 2 == 0 {
                &mut self.virtqueues[queue_idx].rx.lock(&mut node)
            } else {
                &mut self.virtqueues[queue_idx].tx.lock(&mut node)
            };

            if self.virtio_has_feature(VIRTIO_F_EVENT_IDX) {
                let old_idx = vq.vq_dma.as_ref().avail.idx;
                let new_idx = vq.vq_avail_idx;
                vq.publish_avail_idx();
                membar_sync();
                let event_idx = vq.vq_dma.as_ref().used.avail_event + 1;
                (new_idx - event_idx) < (new_idx - old_idx)
            } else {
                vq.publish_avail_idx();
                membar_sync();
                vq.vq_dma.as_ref().used.flags & VIRTQ_USED_F_NO_NOTIFY == 0
            }
        };

        if should_kick {
            self.virtio_pci_kick(vq_idx)?;
        }

        Ok(())
    }

    fn vio_iff(&mut self) {
        self.flags.insert(NetFlags::MULTICAST);
        self.flags.insert(NetFlags::PROMISC);
    }

    fn vio_init(&mut self) -> Result<(), VirtioDriverErr> {
        self.vio_stop()?;

        let mut should_notify = Vec::new();
        for queue in self.virtqueues.iter_mut() {
            let mut node = MCSNode::new();
            let mut rx = queue.rx.lock(&mut node);
            should_notify.push(rx.vio_populate_rx_mbufs());
        }

        for (queue_idx, should_notify) in should_notify.iter().enumerate() {
            if *should_notify {
                self.virtio_notify((queue_idx * 2) as u16)?;
            }
        }

        self.vio_iff();
        self.flags.insert(NetFlags::RUNNING);

        Ok(())
    }

    fn vio_stop(&mut self) -> Result<(), VirtioDriverErr> {
        self.flags.remove(NetFlags::RUNNING);
        self.virtio_reset()?;

        for queue in self.virtqueues.iter_mut() {
            let mut node = MCSNode::new();
            let mut rx = queue.rx.lock(&mut node);
            rx.vio_rxeof();
        }

        self.virtio_reinit_start()?;

        for queue in self.virtqueues.iter_mut() {
            {
                let mut node = MCSNode::new();
                let mut rx = queue.rx.lock(&mut node);
                rx.virtio_start_vq_intr();
            }
            {
                let mut node = MCSNode::new();
                let mut tx = queue.tx.lock(&mut node);
                tx.virtio_stop_vq_intr();
            }
        }

        if let Some(ctrl_vq) = &self.ctrl_vq {
            let mut node = MCSNode::new();
            let mut ctrl_vq = ctrl_vq.lock(&mut node);
            ctrl_vq.virtio_start_vq_intr();
        }

        self.virtio_reinit_end()?;

        Ok(())
    }
}

pub struct VirtioNet {
    inner: RwLock<VirtioNetInner>,
}

impl VirtioNet {
    pub fn new(info: PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        let mut inner = VirtioNetInner::new(info);

        inner.virtio_pci_attach()?;
        inner.vio_attach()?;

        Ok(Self {
            inner: RwLock::new(inner),
        })
    }
}

impl PCIeDevice for VirtioNet {
    fn device_name(&self) -> Cow<'static, str> {
        "Virtio-net".into()
    }
}

impl NetDevice for VirtioNet {
    fn num_queues(&self) -> usize {
        let inner = self.inner.read();
        inner.virtqueues.len()
    }

    fn flags(&self) -> NetFlags {
        let inner = self.inner.read();
        inner.flags
    }

    fn device_short_name(&self) -> Cow<'static, str> {
        "virtio-net".into()
    }

    fn capabilities(&self) -> NetCapabilities {
        let inner = self.inner.read();
        inner.capabilities
    }

    fn link_status(&self) -> LinkStatus {
        let inner = self.inner.read();
        if inner.virtio_has_feature(VIRTIO_NET_F_STATUS) {
            let status = inner.net_cfg.virtio_get_status().unwrap_or(0);
            if status & VIRTIO_NET_S_LINK_UP == 0 {
                return LinkStatus::Down;
            }
        }

        match inner.net_cfg.virtio_get_duplex() {
            Ok(0x00) => LinkStatus::UpHalfDuplex,
            _ => LinkStatus::UpFullDuplex,
        }
    }

    fn link_speed(&self) -> u64 {
        let inner = self.inner.read();
        inner.net_cfg.virtio_get_speed().unwrap_or(0) as u64
    }

    fn mac_address(&self) -> [u8; 6] {
        let inner = self.inner.read();
        inner.mac_addr
    }

    fn recv(&self, que_id: usize) -> Result<Option<EtherFrameBuf>, NetDevError> {
        let inner = self.inner.read();

        let mut node = MCSNode::new();
        let mut rx = inner.virtqueues[que_id].rx.lock(&mut node);

        if let Some(data) = rx.rx_buffer.pop() {
            return Ok(Some(data));
        }

        rx.vio_rxeof();

        if let Some(data) = rx.rx_buffer.pop() {
            Ok(Some(data))
        } else {
            Ok(None)
        }
    }

    fn can_send(&self) -> bool {
        let inner = self.inner.read();
        if !inner.flags.contains(NetFlags::UP) {
            return false;
        }

        if self.link_status() == LinkStatus::Down {
            return false;
        }

        true
    }

    fn send(&self, data: EtherFrameRef, que_id: usize) -> Result<(), NetDevError> {
        {
            let inner = self.inner.read();
            let mut node = MCSNode::new();
            let mut tx = inner.virtqueues[que_id].tx.lock(&mut node);
            tx.vio_start(&data);
        }

        let tx_vq_index = (que_id * 2 + 1) as u16;
        let mut inner = self.inner.write();
        inner
            .virtio_notify(tx_vq_index)
            .or(Err(NetDevError::DeviceError))?;

        Ok(())
    }

    fn up(&self) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();
        if inner.flags.contains(NetFlags::UP) {
            return Err(NetDevError::AlreadyUp);
        }

        if let Err(err_init) = inner.vio_init() {
            if let Err(err_stop) = inner.vio_stop() {
                log::error!("virtio-net: stop failed: {err_stop:?}");
            }
            log::error!("virtio-net: init failed: {err_init:?}");
            Err(NetDevError::DeviceError)
        } else {
            inner.flags.insert(NetFlags::UP);
            Ok(())
        }
    }

    fn down(&self) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();

        if inner.flags.contains(NetFlags::UP) {
            if let Err(e) = inner.vio_stop() {
                log::error!("virtio-net: stop failed: {e:?}");
                Err(NetDevError::DeviceError)
            } else {
                inner.flags.remove(NetFlags::UP);
                Ok(())
            }
        } else {
            Err(NetDevError::AlreadyDown)
        }
    }

    fn interrupt(&self, irq: u16) -> Result<(), NetDevError> {
        let inner = self.inner.read();

        let irq_type = if let Some(irq_type) = inner.irq_to_type.get(&irq) {
            irq_type
        } else {
            return Ok(());
        };

        match irq_type {
            IRQType::Config => Ok(()),
            IRQType::Control => {
                drop(inner);
                let mut inner = self.inner.write();

                if let Some(ctrl_vq) = &mut inner.ctrl_vq {
                    let mut node = MCSNode::new();
                    let mut ctrl_vq = ctrl_vq.lock(&mut node);
                    if ctrl_vq.vq_used_idx != ctrl_vq.vq_dma.as_ref().used.idx {
                        ctrl_vq.vio_ctrleof();
                    }
                }

                Ok(())
            }
            IRQType::Queue(idx) => {
                let should_notify = {
                    let mut node = MCSNode::new();
                    let mut rx = inner.virtqueues[*idx].rx.lock(&mut node);
                    if rx.vq_used_idx != rx.vq_dma.as_ref().used.idx {
                        rx.vio_rx_intr()
                    } else {
                        false
                    }
                };

                {
                    let mut node = MCSNode::new();
                    let mut tx = inner.virtqueues[*idx].tx.lock(&mut node);
                    if tx.vq_used_idx != tx.vq_dma.as_ref().used.idx {
                        tx.vio_tx_intr();
                    }
                }

                if should_notify {
                    let rx_vq_index = (*idx * 2) as u16;
                    drop(inner);
                    let mut inner = self.inner.write();
                    inner
                        .virtio_notify(rx_vq_index)
                        .or(Err(NetDevError::DeviceError))?;
                }

                Ok(())
            }
        }
    }

    fn irqs(&self) -> Vec<u16> {
        let inner = self.inner.read();

        let mut result = Vec::new();
        if let PCIeInt::MsiX(vec) = &inner.pcie_int {
            for (irq, _) in vec {
                result.push(irq.get_irq());
            }
        }

        result
    }

    fn rx_irq_to_que_id(&self, irq: u16) -> Option<usize> {
        let inner = self.inner.read();

        if let Some(IRQType::Queue(idx)) = inner.irq_to_type.get(&irq) {
            assert!(*idx == 0); // TODO: support multiple queues
            return Some(*idx);
        }

        None
    }

    fn add_multicast_addr(&self, _addr: &[u8; 6]) -> Result<(), NetDevError> {
        todo!()
    }

    fn remove_multicast_addr(&self, _addr: &[u8; 6]) -> Result<(), NetDevError> {
        todo!()
    }

    fn poll_in_service(&self) -> Result<(), NetDevError> {
        todo!()
    }

    fn poll_mode(&self) -> bool {
        // TODO: Implement this
        false
    }

    fn poll(&self) -> bool {
        todo!()
    }

    fn tick(&self) -> Result<(), NetDevError> {
        todo!()
    }

    fn tick_msec(&self) -> Option<u64> {
        // TODO: Implement this
        None
    }
}
