use crate::pcie::{
    capability::virtio::VirtioCap,
    pcie_id,
    virtio::config::{
        virtio_common_config::VirtioCommonConfig, virtio_net_config::VirtioNetConfig,
        virtio_notify_cap::VirtioNotifyCap,
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
use awkernel_lib::{
    addr::Addr,
    dma_pool::DMAPool,
    net::net_device::{
        EtherFrameBuf, EtherFrameRef, LinkStatus, NetCapabilities, NetDevError, NetDevice, NetFlags,
    },
    paging::PAGESIZE,
    sync::rwlock::RwLock,
};

const DEVICE_SHORT_NAME: &str = "virtio-net";

const VIRTIO_NET_ID: u16 = 0x1041;

// device-specific feature bits
const VIRTIO_NET_F_MAC: u64 = 1 << 5;
const VIRTIO_NET_F_STATUS: u64 = 1 << 16;

// Reserved Feature Bits
const VIRTIO_F_NOTIFY_ON_EMPTY: u64 = 1 << 24;
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

const VIRTQ_DESC_F_WRITE: u16 = 2;

pub enum IRQType {
    Config,
    Queue(usize),
}

// Virtio ring descriptors: 16 bytes.
// These can chain together via "next".
#[repr(C, packed)]
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

// u32 is used here for ids for padding reasons.
#[repr(C, packed)]
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

// This is the memory layout on DMA
#[repr(C, packed)]
struct VirtqDMA {
    desc: [VirtqDesc; MAX_VQ_SIZE], // 4096 bytes
    avail: VirtqAvail,              // 518 bytes
    _pad: [u8; 3578],               // 4096 - 518 = 3578 bytes
    used: VirtqUsed,                // 2054 bytes
    _pad2: [u8; 2042],              // 4096 - 2054 = 2042 bytes
} // 4096 * 3 = 12288 bytes in total

struct Virtq {
    vq_dma: DMAPool<VirtqDMA>,
    vq_entries: Vec<VirtqEntry>,
    vq_freelist: LinkedList<VirtqEntry>,
    vq_mask: u16,
    vq_avail_idx: u16,
    vq_used_idx: u16,
    vq_queued: u16,
    vq_index: u16,
    vq_intr_vec: u16,
    // TODO: add more fields
}

#[derive(Copy, Clone)]
struct VirtqEntry {
    qe_index: usize, // index in vq_desc array
    // The following are used only in the `head' entry
    qe_next: i16, // next enq slot
                  // qe_indirect: i16,        // 1 if using indirect
                  // qe_vr_index: i16,        // index in sc_reqs array
}

impl Virtq {
    pub fn new(dma: DMAPool<VirtqDMA>) -> Self {
        let vq_size = MAX_VQ_SIZE;

        // virtio_enqueue_trim needs monotonely raising entries,
        // therefore initialize in reverse order
        let mut entries = Vec::with_capacity(vq_size);
        let mut freelist = LinkedList::new();
        for i in (0..vq_size).rev() {
            freelist.push_front(VirtqEntry {
                qe_index: i,
                qe_next: 0,
            });
            entries.push(VirtqEntry {
                qe_index: i,
                qe_next: -1,
            });
        }

        Self {
            vq_dma: dma,
            vq_entries: entries,
            vq_freelist: freelist,
            vq_mask: (vq_size - 1) as u16,
            vq_avail_idx: 0,
            vq_used_idx: 0,
            vq_queued: 0,
            vq_index: 0,
            vq_intr_vec: 0,
        }
    }

    fn vq_alloc_entry(&mut self) -> Option<VirtqEntry> {
        self.vq_freelist.pop_front()
    }

    fn vq_free_entry(&mut self, entry: VirtqEntry) {
        self.vq_freelist.push_front(entry);
    }

    /// enqueue_prep: allocate a slot number
    fn virtio_enqueue_prep(&mut self) -> Option<usize> {
        let mut qe = self.vq_alloc_entry().unwrap();

        // next slot is not allocated yet
        qe.qe_next = -1;
        Some(qe.qe_index)
    }

    fn publish_avail_idx(&mut self) {
        self.vq_dma.as_mut().avail.idx = self.vq_avail_idx;
        self.vq_queued = 1;
    }

    /// dequeue: dequeue a request from uring;
    /// bus_dmamap_sync for uring must already have been done,
    /// usually by virtio_check_vq() in the interrupt handler.
    /// This means that polling virtio_dequeue() repeatedly until it returns 0 does not work.
    fn virtio_dequeue(&mut self) -> Result<usize, VirtioDriverErr> {
        if self.vq_used_idx == self.vq_dma.as_mut().used.idx {
            return Err(VirtioDriverErr::NoData);
        }

        self.vq_used_idx += 1;
        let used_idx = self.vq_used_idx & self.vq_mask;

        let slot = self.vq_dma.as_ref().used.ring[used_idx as usize].id;
        Ok(slot as usize)
    }

    /// dequeue_commit: complete dequeue; the slot is recycled for future use.
    /// if you forget to call this the slot will be leaked.
    /// Don't call this if you use statically allocated slots and virtio_enqueue_trim().
    /// returns the number of freed slots.
    fn virtio_dequeue_commit(&mut self, slot: usize) -> Result<u16, VirtioDriverErr> {
        let mut freed_num = 0;

        // TODO: chain for descriptors

        self.vq_free_entry(self.vq_entries[slot]);
        freed_num += 1;

        Ok(freed_num)
    }
}

/// Packet header structure
#[repr(C, packed)]
struct _VirtioNetHdr {
    flags: u8,
    gso_type: u8,
    hdr_len: u16,
    gso_size: u16,
    csum_start: u16,
    csum_offset: u16,
    num_buffers: u16, // only present if VIRTIO_NET_F_MRG_RXBUF is negotiated
}

const MCLSHIFT: u32 = 11;
const MCLBYTES: u32 = 1 << MCLSHIFT;
type TxBuffer = [[u8; MCLBYTES as usize]; MAX_VQ_SIZE];

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

struct VirtioNetInner {
    info: PCIeInfo,
    mac_addr: [u8; 6],
    common_cfg: VirtioCommonConfig,
    notify_cap: VirtioNotifyCap,
    net_cfg: VirtioNetConfig,
    driver_features: u64,
    active_features: u64,
    flags: NetFlags,
    capabilities: NetCapabilities,
    tx_vq: Option<Virtq>,
    tx_dma: Option<DMAPool<TxBuffer>>,
    irq_to_type: BTreeMap<u16, IRQType>,
}

impl VirtioNetInner {
    pub fn new(info: PCIeInfo) -> Self {
        Self {
            info,
            mac_addr: [0; 6],
            common_cfg: VirtioCommonConfig::default(),
            notify_cap: VirtioNotifyCap::default(),
            net_cfg: VirtioNetConfig::default(),
            driver_features: 0,
            active_features: 0,
            flags: NetFlags::empty(),
            capabilities: NetCapabilities::empty(),
            tx_vq: None,
            tx_dma: None,
            irq_to_type: BTreeMap::new(),
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

        self.common_cfg.init(&self.info, common_cfg_cap)?;
        self.net_cfg.init(&self.info, net_cfg_cap)?;
        self.notify_cap.init(&self.info, notify_cap)?;

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
        self.driver_features |= VIRTIO_NET_F_MAC;
        self.driver_features |= VIRTIO_NET_F_STATUS;
        // TODO: setup more features

        self.virtio_pci_negotiate_features()?;

        // TODO: VIRTIO_NET_F_MQ related setup
        // TODO: setup virtio queues

        if self.virtio_has_feature(VIRTIO_NET_F_MAC) {
            self.mac_addr = self.net_cfg.virtio_get_mac_addr()?;
        } else {
            todo!()
        }

        // TODO: VIRTIO_NET_F_MRG_RXBUF related setup

        self.capabilities = NetCapabilities::empty();
        self.flags = NetFlags::BROADCAST | NetFlags::SIMPLEX | NetFlags::MULTICAST;

        // TODO: VIRTIO_NET_F_CSUM related setup
        // TODO: VIRTIO_NET_F_HOST_TSO4 related setup
        // TODO: VIRTIO_NET_F_HOST_TSO6 related setup
        // TODO: VIRTIO_NET_F_CTRL_GUEST_OFFLOADS related setup
        // TODO: VIRTIO_NET_F_MRG_RXBUF related setup
        // TODO: VIRTIO_NET_F_GUEST_TSO related setup
        // TODO: VIRTIO_F_RING_INDIRECT_DESC related setup

        // TODO: setup virtio queues
        // defrag for longer mbuf chains
        let tx_max_segments = 16;
        self.tx_vq = Some(self.virtio_alloc_vq(0, tx_max_segments + 1)?);

        // TODO: setup control queue
        // TODO: setup interrupt

        self.vio_alloc_mem()?;

        self.virtio_attach_finish()?;

        // TODO: VIRTIO_NET_F_MQ related setup
        // TODO: setup virtio queues

        Ok(())
    }

    fn virtio_pci_negotiate_features(&mut self) -> Result<(), VirtioDriverErr> {
        self.active_features = 0;

        // TODO: VIRTIO_F_RING_INDIRECT_DESC related setup
        // TODO: VIRTIO_F_RING_EVENT_IDX related setup

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

        // TODO: VIRTIO_F_RING_INDIRECT_DESC related setup

        if negotiated_features & VIRTIO_F_VERSION_1 == 0 {
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
        let offset = self.common_cfg.virtio_get_queue_notify_off()? as usize
            * self.notify_cap.virtio_get_notify_off_multiplier()? as usize;

        self.notify_cap.virtio_set_notify(offset, idx)
    }

    fn virtio_check_vq(&mut self, _idx: u16) -> Result<(), VirtioDriverErr> {
        let tx = self.tx_vq.as_mut().unwrap();
        if tx.vq_used_idx != tx.vq_dma.as_ref().used.idx {
            self.vio_tx_intr()?;
        }

        Ok(())
    }

    fn virtio_pci_msix_establish(
        &mut self,
        idx: u16,
        irq_type: IRQType,
    ) -> Result<(), VirtioDriverErr> {
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
        msix.enable();
        Ok(())
    }

    fn virtio_pci_setup_intrs(&mut self) -> Result<(), VirtioDriverErr> {
        let vector = self.tx_vq.as_ref().unwrap().vq_intr_vec;
        self.virtio_pci_set_msix_queue_vector(1, vector)?; // tx

        self.virtio_pci_set_msix_config_vector(0) // config
    }

    fn virtio_pci_setup_msix(&mut self) -> Result<(), VirtioDriverErr> {
        self.virtio_pci_msix_establish(0, IRQType::Config)?;

        self.virtio_pci_msix_establish(1, IRQType::Queue(0))?; // tx
        self.tx_vq.as_mut().unwrap().vq_intr_vec = 1;

        Ok(())
    }

    fn virtio_pci_attach_finish(&mut self) -> Result<(), VirtioDriverErr> {
        // TODO: we currently support only PER_VQ MSIX
        self.virtio_pci_setup_msix()
    }

    fn virtio_has_feature(&self, feature: u64) -> bool {
        self.active_features & feature != 0
    }

    fn virtio_attach_finish(&mut self) -> Result<(), VirtioDriverErr> {
        self.virtio_pci_attach_finish()?;
        self.virtio_pci_setup_intrs()?;

        let tx_dma_addr = self.tx_dma.as_mut().unwrap().get_phy_addr().as_usize() as u64;
        self.virtio_pci_setup_queue(0, tx_dma_addr)?;

        // TODO: setup rx queue

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

        // TODO: setup interrupts

        self.virtio_pci_negotiate_features()?;

        // TODO: setup virtio queues

        Ok(())
    }

    fn virtio_reinit_end(&mut self) -> Result<(), VirtioDriverErr> {
        self.common_cfg
            .virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_DRIVER_OK)?;

        Ok(())
    }

    /// Allocate a vq.
    /// maxnsegs denotes how much space should be allocated for indirect descriptors.
    /// maxnsegs == 1 can be used to disable use indirect descriptors for this queue.
    fn virtio_alloc_vq(&mut self, index: u16, _maxnsegs: u16) -> Result<Virtq, VirtioDriverErr> {
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

        // alloc and map the memory
        let allocsize = core::mem::size_of::<VirtqDMA>();
        log::info!("virtio-net: allocsize: {allocsize}, PAGESIZE: {PAGESIZE}");
        let dma = DMAPool::new(0, allocsize / PAGESIZE).ok_or(VirtioDriverErr::DMAPool)?;

        // remember addresses and offsets for later use
        let mut vq = Virtq::new(dma);
        vq.vq_index = index;

        // TODO: continue Virtq initialization

        Ok(vq)
    }

    /// enqueue_reserve: allocate remaining slots and build the descriptor chain.
    /// Calls virtio_enqueue_abort() on failure.
    fn virtio_enqueue_reserve(&mut self, slot: usize) -> Result<(), VirtioDriverErr> {
        let tx = self.tx_vq.as_mut().unwrap();

        log::info!(
            "virtio-net: enqueue reserve: vq_entries size: {}",
            tx.vq_entries.len()
        );

        assert!(tx.vq_entries[slot].qe_next == -1);

        tx.vq_entries[slot].qe_next = tx.vq_entries[slot].qe_index as i16;
        tx.vq_dma.as_mut().desc[slot].flags = 0;

        // TODO: chain for descriptors

        Ok(())
    }

    /// enqueue: enqueue a single dmamap.
    fn virtio_enqueue(&mut self, slot: usize, write: bool) -> Result<(), VirtioDriverErr> {
        let tx = self.tx_vq.as_mut().unwrap();

        let vq_entry = tx.vq_entries[slot];
        let s = vq_entry.qe_next;
        assert!(s >= 0);

        let s = s as usize;

        tx.vq_dma.as_mut().desc[s].addr = (self.tx_dma.as_mut().unwrap().get_phy_addr().as_usize()
            + s * MCLBYTES as usize) as u64;
        tx.vq_dma.as_mut().desc[s].len = MCLBYTES;
        if !write {
            tx.vq_dma.as_mut().desc[s].flags |= VIRTQ_DESC_F_WRITE;
        }
        tx.vq_entries[s].qe_next = tx.vq_dma.as_ref().desc[s].next as i16;

        // TODO: chain for descriptors

        Ok(())
    }

    /// enqueue_commit: add it to the available ring.
    fn virtio_enqueue_commit(&mut self, slot: usize) -> Result<(), VirtioDriverErr> {
        let tx = self.tx_vq.as_mut().unwrap();
        let vq_index = tx.vq_index;

        tx.vq_avail_idx += 1;
        tx.vq_dma.as_mut().avail.ring[(tx.vq_avail_idx & tx.vq_mask) as usize] = slot as u16;

        tx.publish_avail_idx();
        self.virtio_pci_kick(vq_index)?;

        Ok(())
    }

    fn vio_txeof(&mut self) -> Result<(), VirtioDriverErr> {
        log::info!("virtio-net: tx eof");
        self.vio_tx_dequeue()?;
        log::info!("virtio-net: tx eof done");
        Ok(())
    }

    fn vio_tx_intr(&mut self) -> Result<(), VirtioDriverErr> {
        log::info!("virtio-net: tx interrupt");
        self.vio_txeof()?;
        // self.vio_start()?;
        Ok(())
    }

    fn vio_alloc_mem(&mut self) -> Result<(), VirtioDriverErr> {
        let allocsize = MCLBYTES as usize * MAX_VQ_SIZE;
        let dma = DMAPool::new(0, allocsize / PAGESIZE).ok_or(VirtioDriverErr::DMAPool)?;
        self.tx_dma = Some(dma);

        Ok(())
    }

    fn vio_tx_dequeue(&mut self) -> Result<(), VirtioDriverErr> {
        let tx_vq = self.tx_vq.as_mut().unwrap();
        while let Ok(slot) = tx_vq.virtio_dequeue() {
            let _freed = tx_vq.virtio_dequeue_commit(slot)?;
        }

        Ok(())
    }

    fn vio_encap(&mut self, slot: usize, frame: &EtherFrameRef) -> Result<(), VirtioDriverErr> {
        let len = frame.data.len();
        let tx_dma = self.tx_dma.as_mut().unwrap();
        let dst = &mut tx_dma.as_mut()[slot];
        unsafe {
            core::ptr::copy_nonoverlapping(frame.data.as_ptr(), dst.as_mut_ptr(), len);
        }

        Ok(())
    }

    fn vio_start(&mut self, frames: &[EtherFrameRef]) -> Result<(), VirtioDriverErr> {
        self.vio_tx_dequeue()?;

        for frame in frames {
            let slot = self.tx_vq.as_mut().unwrap().virtio_enqueue_prep().unwrap();
            self.vio_encap(slot, frame)?;
            self.virtio_enqueue_reserve(slot)?;
            self.virtio_enqueue(slot, true)?;
            self.virtio_enqueue_commit(slot)?;
        }

        Ok(())
    }

    fn vio_iff(&mut self) -> Result<(), VirtioDriverErr> {
        self.flags.insert(NetFlags::MULTICAST);
        self.flags.insert(NetFlags::PROMISC);

        Ok(())
    }

    fn vio_init(&mut self) -> Result<(), VirtioDriverErr> {
        self.vio_stop()?;
        self.vio_iff()?;
        self.flags.insert(NetFlags::RUNNING);

        Ok(())
    }

    fn vio_stop(&mut self) -> Result<(), VirtioDriverErr> {
        self.flags.remove(NetFlags::RUNNING);

        // TODO: stop timers

        self.virtio_reset()?;

        // TODO: drain tx/rx queues

        self.virtio_reinit_start()?;

        // TODO: interrupt tx/rx queues

        self.virtio_reinit_end()?;

        // TODO: VIRTIO_NET_F_MQ related setup
        // TODO: VIRTIO_NET_F_CTRL_VQ related setup

        Ok(())
    }

    fn intr(&mut self, irq: u16) -> Result<(), VirtioDriverErr> {
        let irq_type = if let Some(irq_type) = self.irq_to_type.get(&irq) {
            irq_type
        } else {
            return Ok(());
        };

        match irq_type {
            IRQType::Config => Ok(()),
            IRQType::Queue(idx) => self.virtio_check_vq(*idx as u16),
        }
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
        1
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

        LinkStatus::UpFullDuplex
    }

    fn link_speed(&self) -> u64 {
        // TODO: Implement this
        10
    }

    fn mac_address(&self) -> [u8; 6] {
        let inner = self.inner.read();
        inner.mac_addr
    }

    fn recv(&self, _que_id: usize) -> Result<Option<EtherFrameBuf>, NetDevError> {
        todo!()
    }

    fn can_send(&self) -> bool {
        log::info!("virtio-net: can_send");

        let inner = self.inner.read();
        if !inner.flags.contains(NetFlags::UP) {
            log::info!("virtio-net: not up");
            return false;
        }

        if self.link_status() == LinkStatus::Down {
            log::info!("virtio-net: link down");
            return false;
        }

        log::info!("virtio-net: can_send: true");
        true
    }

    fn send(&self, data: EtherFrameRef, que_id: usize) -> Result<(), NetDevError> {
        assert!(que_id == 0);

        let frames = [data];
        let mut inner = self.inner.write();
        inner.vio_start(&frames).or(Err(NetDevError::DeviceError))?;

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
        let mut inner = self.inner.write();
        inner.intr(irq).or(Err(NetDevError::DeviceError))
    }

    fn irqs(&self) -> Vec<u16> {
        let inner = self.inner.read();

        let mut result = Vec::new();
        for irq in inner.irq_to_type.keys() {
            if *irq != 0 {
                result.push(*irq);
            }
        }

        result
    }

    fn rx_irq_to_que_id(&self, _irq: u16) -> Option<usize> {
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
