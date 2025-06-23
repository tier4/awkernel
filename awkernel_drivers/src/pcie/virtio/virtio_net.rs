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

const VIRTIO_NET_ID: u16 = 0x1041;

// device-specific feature bits
const VIRTIO_NET_F_MAC: u64 = 1 << 5;
const VIRTIO_NET_F_STATUS: u64 = 1 << 16;
const VIRTIO_NET_F_SPEED_DUPLEX: u64 = 1 << 63;

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

#[allow(dead_code)]
struct Virtq {
    vq_dma: DMAPool<VirtqDMA>,
    vq_freelist: LinkedList<usize>,
    vq_num: usize,
    vq_mask: usize,
    vq_avail_idx: u16,
    vq_used_idx: u16,
    vq_index: u16,
    vq_intr_vec: u16,

    data_buf: DMAPool<RxTxBuffer>,
}

impl Virtq {
    fn init(&mut self) {
        assert!(self.vq_num > 0);

        self.vq_freelist = LinkedList::new();
        for i in (0..self.vq_num).rev() {
            self.vq_freelist.push_front(i);
        }

        self.vq_avail_idx = 0;
        self.vq_used_idx = 0;
    }

    #[allow(dead_code)]
    fn vq_alloc_entry(&mut self) -> Option<usize> {
        self.vq_freelist.pop_front()
    }

    #[allow(dead_code)]
    fn vq_free_entry(&mut self, slot: usize) {
        self.vq_freelist.push_front(slot);
    }

    /// enqueue_prep: allocate a slot number
    #[allow(dead_code)]
    fn virtio_enqueue_prep(&mut self) -> Option<usize> {
        self.vq_alloc_entry()
    }

    /// enqueue_reserve: allocate remaining slots and build the descriptor chain.
    #[allow(dead_code)]
    fn virtio_enqueue_reserve(&mut self, slot: usize) {
        self.vq_dma.as_mut().desc[slot].flags = 0;
    }

    /// enqueue: enqueue a single dmamap.
    #[allow(dead_code)]
    fn virtio_enqueue(&mut self, slot: usize, len: usize, write: bool) {
        let desc = &mut self.vq_dma.as_mut().desc[slot];

        desc.addr = (self.data_buf.get_phy_addr().as_usize() + slot * MCLBYTES as usize) as u64;
        desc.len = len as u32;
        if !write {
            desc.flags |= VIRTQ_DESC_F_WRITE;
        }
        desc.next = 0;
    }

    /// enqueue_commit: add it to the available ring.
    #[allow(dead_code)]
    fn virtio_enqueue_commit(&mut self, slot: usize) {
        let avail = &mut self.vq_dma.as_mut().avail;

        avail.ring[self.vq_avail_idx as usize & self.vq_mask] = slot as u16;
        self.vq_avail_idx += 1;
        avail.idx = self.vq_avail_idx;
    }

    /// dequeue: dequeue a request from uring.
    #[allow(dead_code)]
    fn virtio_dequeue(&mut self) -> Option<(usize, u32)> {
        if self.vq_used_idx == self.vq_dma.as_ref().used.idx {
            return None;
        }

        let used_idx = self.vq_used_idx & self.vq_mask as u16;
        self.vq_used_idx += 1;

        let used_ring = &self.vq_dma.as_ref().used.ring[used_idx as usize];
        Some((used_ring.id as usize, used_ring.len))
    }

    /// dequeue_commit: complete dequeue; the slot is recycled for future use.
    /// if you forget to call this the slot will be leaked.
    #[allow(dead_code)]
    fn virtio_dequeue_commit(&mut self, slot: usize) {
        self.vq_free_entry(slot);
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
        self.driver_features |= VIRTIO_NET_F_SPEED_DUPLEX;

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
        // TODO: setup control queue

        {
            let mut irqs = Vec::new();

            let irq = self.virtio_pci_msix_establish(0, IRQType::Config)?;
            irqs.push((irq, IRQType::Config));

            let irq = self.virtio_pci_msix_establish(1, IRQType::Control)?;
            irqs.push((irq, IRQType::Control));

            // TODO: support multiple queues
            let intr_vector = 2;
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

    fn _virtio_pci_setup_queue(&mut self, vq_idx: u16, addr: u64) -> Result<(), VirtioDriverErr> {
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

    fn _virtio_pci_set_msix_config_vector(&mut self, vector: u16) -> Result<(), VirtioDriverErr> {
        self.common_cfg.virtio_set_config_msix_vector(vector)
    }

    fn _virtio_pci_set_msix_queue_vector(
        &mut self,
        idx: u16,
        vector: u16,
    ) -> Result<(), VirtioDriverErr> {
        self.common_cfg.virtio_set_queue_select(idx)?;
        self.common_cfg.virtio_set_queue_msix_vector(vector)
    }

    fn _virtio_pci_kick(&mut self, idx: u16) -> Result<(), VirtioDriverErr> {
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

    fn virtio_has_feature(&self, feature: u64) -> bool {
        self.active_features & feature != 0
    }

    fn virtio_attach_finish(&mut self) -> Result<(), VirtioDriverErr> {
        // TODO: setup msix
        // TODO: setup virt queues

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
    #[allow(dead_code)]
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

        // alloc and map the memory
        let allocsize = core::mem::size_of::<VirtqDMA>();
        let vq_dma = DMAPool::new(0, allocsize / PAGESIZE).ok_or(VirtioDriverErr::DMAPool)?;

        //
        let allocsize = MCLBYTES as usize * MAX_VQ_SIZE;
        let data_buf = DMAPool::new(0, allocsize / PAGESIZE).ok_or(VirtioDriverErr::DMAPool)?;

        let mut vq = Virtq {
            vq_dma,
            vq_freelist: LinkedList::new(),
            vq_num: vq_size,
            vq_mask: vq_size - 1,
            vq_avail_idx: 0,
            vq_used_idx: 0,
            vq_index: index,
            vq_intr_vec: 0,
            data_buf,
        };

        vq.init();

        Ok(vq)
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
        todo!()
    }

    fn flags(&self) -> NetFlags {
        todo!()
    }

    fn device_short_name(&self) -> Cow<'static, str> {
        "virtio-net".into()
    }

    fn capabilities(&self) -> NetCapabilities {
        NetCapabilities::empty()
    }

    fn link_status(&self) -> LinkStatus {
        let inner = self.inner.read();
        if inner.virtio_has_feature(VIRTIO_NET_F_STATUS) {
            let status = inner.net_cfg.virtio_get_status().unwrap_or(0);
            if status & VIRTIO_NET_S_LINK_UP == 0 {
                return LinkStatus::Down;
            }
        }

        let duplex = inner.net_cfg.virtio_get_duplex();
        match duplex {
            Ok(0x00) => LinkStatus::UpHalfDuplex,
            Ok(0x01) => LinkStatus::UpFullDuplex,
            Ok(0xff) => {
                log::warn!("virtio-net: duplex is unknown");
                LinkStatus::Unknown
            }
            _ => {
                log::warn!("virtio-net: cannot get duplex");
                LinkStatus::Down
            }
        }
    }

    fn link_speed(&self) -> u64 {
        let inner = self.inner.read();
        let speed = inner.net_cfg.virtio_get_speed();

        match speed {
            Ok(0xffffffff) => {
                log::warn!("virtio-net: speed is unknown");
                0
            }
            Ok(speed) => speed as u64,
            _ => {
                log::warn!("virtio-net: cannot get speed");
                0
            }
        }
    }

    fn mac_address(&self) -> [u8; 6] {
        let inner = self.inner.read();
        inner.mac_addr
    }

    fn recv(&self, _que_id: usize) -> Result<Option<EtherFrameBuf>, NetDevError> {
        todo!()
    }

    fn can_send(&self) -> bool {
        false
    }

    fn send(&self, _data: EtherFrameRef, _que_id: usize) -> Result<(), NetDevError> {
        todo!()
    }

    fn up(&self) -> Result<(), NetDevError> {
        // TODO: Implement this
        Ok(())
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

        // TODO: handle each interrupt
        match irq_type {
            IRQType::Config => Ok(()),
            IRQType::Control => Ok(()),
            IRQType::Queue(0) => Ok(()),
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
