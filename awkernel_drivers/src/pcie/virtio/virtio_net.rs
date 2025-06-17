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
    dma_pool::DMAPool,
    interrupt::IRQ,
    net::net_device::{
        EtherFrameBuf, EtherFrameRef, LinkStatus, NetCapabilities, NetDevError, NetDevice, NetFlags,
    },
    paging::PAGESIZE,
    sync::rwlock::RwLock,
};

const DEVICE_SHORT_NAME: &str = "virtio-net";

const RECV_QUEUE_SIZE: usize = 32; // To Be Determined

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
    Control,
    Queue(usize),
}

// TODO: support MSI and legacy interrupts
enum PCIeInt {
    None,
    MsiX(Vec<(IRQ, IRQType)>),
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

const VRING_AVAIL_F_NO_INTERRUPT: u16 = 1;

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
    vq_freelist: LinkedList<usize>,
    vq_num: usize,
    vq_mask: usize,
    vq_avail_idx: u16,
    vq_used_idx: u16,
    vq_index: u16,
    vq_intr_vec: u16,

    data_buf: DMAPool<RxTxBuffer>,
    rx_buffer: RingQ<EtherFrameBuf>,
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
    fn init(&mut self) {
        assert!(self.vq_num > 0);

        // virtio_enqueue_trim needs monotonely raising entries, therefore initialize in reverse order
        self.vq_freelist = LinkedList::new();
        for i in (0..self.vq_num).rev() {
            self.vq_freelist.push_front(i);
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
    fn virtio_enqueue_prep(&mut self) -> Result<usize, VirtioDriverErr> {
        let slot = self.vq_alloc_entry().ok_or(VirtioDriverErr::NoSlot)?;

        // next slot is not allocated yet
        self.vq_entries[slot].qe_next = -1;
        Ok(slot)
    }

    /// enqueue_reserve: allocate remaining slots and build the descriptor chain.
    /// Calls virtio_enqueue_abort() on failure.
    fn virtio_enqueue_reserve(&mut self, slot: usize) -> Result<(), VirtioDriverErr> {
        assert!(self.vq_entries[slot].qe_next == -1);

        self.vq_entries[slot].qe_next = self.vq_entries[slot].qe_index as i16;
        self.vq_dma.as_mut().desc[slot].flags = 0;

        Ok(())
    }

    /// enqueue: enqueue a single dmamap.
    fn virtio_enqueue(
        &mut self,
        slot: usize,
        len: usize,
        write: bool,
    ) -> Result<(), VirtioDriverErr> {
        let s = self.vq_entries[slot].qe_next;
        assert!(s >= 0);

        let s = s as usize;

        let addr = (self.data_buf.get_phy_addr().as_usize() + s * MCLBYTES as usize) as u64;
        self.vq_dma.as_mut().desc[s].addr = u64::to_le(addr);
        self.vq_dma.as_mut().desc[s].len = u32::to_le(len as u32);
        if !write {
            self.vq_dma.as_mut().desc[s].flags |= u16::to_le(VIRTQ_DESC_F_WRITE);
        }
        self.vq_dma.as_mut().desc[s].next = 0;
        self.vq_entries[s].qe_next = self.vq_dma.as_ref().desc[s].next as i16;

        Ok(())
    }

    /// enqueue_commit: add it to the available ring.
    fn virtio_enqueue_commit(&mut self, slot: usize) -> Result<(), VirtioDriverErr> {
        self.vq_avail_idx += 1;
        self.vq_dma.as_mut().avail.ring[self.vq_avail_idx as usize & self.vq_mask] = slot as u16;
        self.vq_dma.as_mut().avail.idx = self.vq_avail_idx;

        Ok(())
    }

    /// dequeue: dequeue a request from uring;
    /// bus_dmamap_sync for uring must already have been done,
    /// usually by virtio_check_vq() in the interrupt handler.
    /// This means that polling virtio_dequeue() repeatedly until it returns 0 does not work.
    fn virtio_dequeue(&mut self) -> Result<(usize, u32), VirtioDriverErr> {
        if self.vq_used_idx == self.vq_dma.as_ref().used.idx {
            return Err(VirtioDriverErr::NoData);
        }

        let used_idx = self.vq_used_idx & self.vq_mask as u16;
        self.vq_used_idx += 1;

        let used_ring = &self.vq_dma.as_ref().used.ring[used_idx as usize];
        Ok((used_ring.id as usize, used_ring.len))
    }

    /// dequeue_commit: complete dequeue; the slot is recycled for future use.
    /// if you forget to call this the slot will be leaked.
    /// Don't call this if you use statically allocated slots and virtio_enqueue_trim().
    /// returns the number of freed slots.
    fn virtio_dequeue_commit(&mut self, slot: usize) -> Result<u16, VirtioDriverErr> {
        let mut freed_num = 0;

        // TODO: chain for descriptors

        self.vq_free_entry(slot);
        freed_num += 1;

        Ok(freed_num)
    }

    fn virtio_stop_vq_intr(&mut self) {
        let dma = self.vq_dma.as_mut();
        dma.avail.flags |= VRING_AVAIL_F_NO_INTERRUPT;
    }

    fn virtio_start_vq_intr(&mut self) -> bool {
        let dma = self.vq_dma.as_mut();
        dma.avail.flags &= !VRING_AVAIL_F_NO_INTERRUPT;

        self.vq_used_idx != self.vq_dma.as_ref().used.idx
    }
}

/// Packet header structure
#[repr(C, packed)]
struct VirtioNetHdr {
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
type RxTxBuffer = [[u8; MCLBYTES as usize]; MAX_VQ_SIZE];

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
    net_cfg: VirtioNetConfig,
    notify_cfg: VirtioNotifyConfig,
    notify_off_multiplier: u32,
    driver_features: u64,
    active_features: u64,
    flags: NetFlags,
    capabilities: NetCapabilities,
    tx_vq: Option<Virtq>,
    rx_vq: Option<Virtq>,
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
            tx_vq: None,
            rx_vq: None,
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

        let rx_max_segments = 2;
        let tx_max_segments = 16;
        self.rx_vq = Some(self.virtio_alloc_vq(0, rx_max_segments)?);
        self.tx_vq = Some(self.virtio_alloc_vq(1, tx_max_segments + 1)?);

        self.rx_vq.as_mut().unwrap().virtio_start_vq_intr();
        self.tx_vq.as_mut().unwrap().virtio_stop_vq_intr();

        {
            let mut irqs = Vec::new();

            let irq = self.virtio_pci_msix_establish(0, IRQType::Config)?;
            irqs.push((irq, IRQType::Config));

            let irq = self.virtio_pci_msix_establish(1, IRQType::Control)?;
            irqs.push((irq, IRQType::Control));

            // TODO: support multiple queues
            let intr_vector = 2;
            self.rx_vq.as_mut().unwrap().vq_intr_vec = intr_vector;
            self.tx_vq.as_mut().unwrap().vq_intr_vec = intr_vector;
            let irq = self.virtio_pci_msix_establish(intr_vector, IRQType::Queue(0))?;
            irqs.push((irq, IRQType::Queue(0)));

            self.pcie_int = PCIeInt::MsiX(irqs);
        }

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
        let queue_notify_off = self.common_cfg.virtio_get_queue_notify_off()?;
        let notify_off_multiplier = self.notify_off_multiplier;
        let offset = queue_notify_off as usize * notify_off_multiplier as usize;
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
        let vector = self.rx_vq.as_ref().unwrap().vq_intr_vec;
        self.virtio_pci_set_msix_queue_vector(0, vector)?;

        let vector = self.tx_vq.as_ref().unwrap().vq_intr_vec;
        self.virtio_pci_set_msix_queue_vector(1, vector)?;

        self.virtio_pci_set_msix_config_vector(0)
    }

    fn virtio_pci_attach_finish(&mut self) -> Result<(), VirtioDriverErr> {
        // NOTE: we currently support virtio-net specific MSIX
        Ok(())
    }

    fn virtio_has_feature(&self, feature: u64) -> bool {
        self.active_features & feature != 0
    }

    fn virtio_attach_finish(&mut self) -> Result<(), VirtioDriverErr> {
        self.virtio_pci_attach_finish()?;
        self.virtio_pci_setup_intrs()?;

        let rx = self.rx_vq.as_ref().unwrap();
        self.virtio_pci_setup_queue(0, rx.vq_dma.get_phy_addr().as_usize() as u64)?;

        let tx = self.tx_vq.as_ref().unwrap();
        self.virtio_pci_setup_queue(1, tx.vq_dma.get_phy_addr().as_usize() as u64)?;

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

        self.rx_vq.as_mut().unwrap().init();
        self.virtio_pci_setup_queue(
            self.rx_vq.as_ref().unwrap().vq_index,
            self.rx_vq
                .as_ref()
                .unwrap()
                .vq_dma
                .get_phy_addr()
                .as_usize() as u64,
        )?;
        self.tx_vq.as_mut().unwrap().init();
        self.virtio_pci_setup_queue(
            self.tx_vq.as_ref().unwrap().vq_index,
            self.tx_vq
                .as_ref()
                .unwrap()
                .vq_dma
                .get_phy_addr()
                .as_usize() as u64,
        )?;

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
        let vq_dma = DMAPool::new(0, allocsize / PAGESIZE).ok_or(VirtioDriverErr::DMAPool)?;

        let mut vq_entries = Vec::with_capacity(vq_size);
        for i in 0..vq_size {
            vq_entries.push(VirtqEntry {
                qe_index: i,
                qe_next: -1,
            });
        }

        let allocsize = MCLBYTES as usize * MAX_VQ_SIZE;
        let data_buf = DMAPool::new(0, allocsize / PAGESIZE).ok_or(VirtioDriverErr::DMAPool)?;

        let mut vq = Virtq {
            vq_dma,
            vq_entries,
            vq_freelist: LinkedList::new(),
            vq_num: vq_size,
            vq_mask: vq_size - 1,
            vq_avail_idx: 0,
            vq_used_idx: 0,
            vq_index: index,
            vq_intr_vec: 0,
            data_buf,
            rx_buffer: RingQ::new(RECV_QUEUE_SIZE),
        };

        vq.init();

        Ok(vq)
    }

    /// add mbufs for all the empty receive slots
    fn vio_populate_rx_mbufs(&mut self) -> Result<(), VirtioDriverErr> {
        for _ in 0..self.rx_vq.as_ref().unwrap().vq_num {
            let rx = self.rx_vq.as_mut().unwrap();

            let slot = if let Ok(slot) = rx.virtio_enqueue_prep() {
                slot
            } else {
                break;
            };

            rx.virtio_enqueue_reserve(slot)?;
            rx.virtio_enqueue(slot, MCLBYTES as usize, false)?;
            rx.virtio_enqueue_commit(slot)?;

            self.virtio_pci_kick(self.rx_vq.as_ref().unwrap().vq_index)?;
        }

        Ok(())
    }

    /// dequeue received packets
    fn vio_rxeof(&mut self) -> Result<u16, VirtioDriverErr> {
        let mut freed = 0;
        let rx = self.rx_vq.as_mut().unwrap();
        while let Ok((slot, len)) = rx.virtio_dequeue() {
            let buf = rx.data_buf.as_mut();
            let data = buf[slot];
            let data = data[0..len as usize][12..].to_vec();
            rx.rx_buffer
                .push(EtherFrameBuf { data, vlan: None })
                .unwrap();

            freed += rx.virtio_dequeue_commit(slot)?;
        }

        Ok(freed)
    }

    fn vio_txeof(&mut self) -> Result<(), VirtioDriverErr> {
        let freed = self.vio_tx_dequeue()?;
        if freed > 0 {
            let tx = self.tx_vq.as_mut().unwrap();
            tx.virtio_stop_vq_intr();
        }
        Ok(())
    }

    fn vio_rx_intr(&mut self) -> Result<(), VirtioDriverErr> {
        let freed = self.vio_rxeof()?;
        if freed > 0 {
            self.vio_populate_rx_mbufs()?;
        }

        Ok(())
    }

    fn vio_tx_intr(&mut self) -> Result<(), VirtioDriverErr> {
        self.vio_txeof()?;
        // self.vio_start()?;
        Ok(())
    }

    fn vio_tx_dequeue(&mut self) -> Result<u16, VirtioDriverErr> {
        let mut freed = 0;
        let tx = self.tx_vq.as_mut().unwrap();
        while let Ok((slot, _len)) = tx.virtio_dequeue() {
            freed += tx.virtio_dequeue_commit(slot)?;
        }

        Ok(freed)
    }

    fn vio_encap(&mut self, slot: usize, frame: &EtherFrameRef) -> Result<usize, VirtioDriverErr> {
        let len = frame.data.len();
        let buf = self.tx_vq.as_mut().unwrap().data_buf.as_mut();
        let dst = &mut buf[slot].as_mut_ptr();
        let header_len = core::mem::size_of::<VirtioNetHdr>();
        unsafe {
            core::ptr::copy_nonoverlapping(frame.data.as_ptr(), dst.add(header_len), len);
        }

        Ok(header_len + len)
    }

    fn vio_start(&mut self, frames: &[EtherFrameRef]) -> Result<(), VirtioDriverErr> {
        self.vio_tx_dequeue()?;

        for frame in frames {
            let slot = self.tx_vq.as_mut().unwrap().virtio_enqueue_prep()?;
            let len = self.vio_encap(slot, frame)?;
            self.tx_vq.as_mut().unwrap().virtio_enqueue_reserve(slot)?;
            self.tx_vq
                .as_mut()
                .unwrap()
                .virtio_enqueue(slot, len, true)?;
            self.tx_vq.as_mut().unwrap().virtio_enqueue_commit(slot)?;

            self.virtio_pci_kick(self.tx_vq.as_ref().unwrap().vq_index)?;
        }

        if self.tx_vq.as_mut().unwrap().virtio_start_vq_intr() {
            self.vio_tx_dequeue()?;
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
        self.vio_populate_rx_mbufs()?;
        self.vio_iff()?;
        self.flags.insert(NetFlags::RUNNING);

        Ok(())
    }

    fn vio_stop(&mut self) -> Result<(), VirtioDriverErr> {
        self.flags.remove(NetFlags::RUNNING);
        self.virtio_reset()?;
        self.vio_rxeof()?;
        self.virtio_reinit_start()?;
        self.rx_vq.as_mut().unwrap().virtio_start_vq_intr();
        self.tx_vq.as_mut().unwrap().virtio_stop_vq_intr();
        self.virtio_reinit_end()
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
        let mut inner = self.inner.write();

        let rx = inner.rx_vq.as_mut().unwrap();
        if let Some(data) = rx.rx_buffer.pop() {
            return Ok(Some(data));
        }

        inner.vio_rxeof().or(Err(NetDevError::DeviceError))?;

        let rx = inner.rx_vq.as_mut().unwrap();
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

    fn send(&self, data: EtherFrameRef, _que_id: usize) -> Result<(), NetDevError> {
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

        let irq_type = if let Some(irq_type) = inner.irq_to_type.get(&irq) {
            irq_type
        } else {
            return Ok(());
        };

        // TODO: handle each interrupt
        match irq_type {
            IRQType::Config => Ok(()),
            IRQType::Control => Ok(()),
            IRQType::Queue(0) => {
                let rx = inner.rx_vq.as_mut().unwrap();
                if rx.vq_used_idx != rx.vq_dma.as_ref().used.idx {
                    inner.vio_rx_intr().or(Err(NetDevError::DeviceError))?;
                }

                let tx = inner.tx_vq.as_mut().unwrap();
                if tx.vq_used_idx != tx.vq_dma.as_ref().used.idx {
                    inner.vio_tx_intr().or(Err(NetDevError::DeviceError))?;
                }

                Ok(())
            }
            _ => unreachable!(),
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
