use crate::pcie::{
    capability::virtio::VirtioCap,
    pcie_id,
    virtio::config::{
        virtio_common_config::VirtioCommonConfig, virtio_net_config::VirtioNetConfig,
    },
    PCIeDevice, PCIeDeviceErr, PCIeInfo,
};
use alloc::{borrow::Cow, sync::Arc, vec::Vec};
use awkernel_lib::net::net_device::{
    EtherFrameBuf, EtherFrameRef, LinkStatus, NetCapabilities, NetDevError, NetDevice, NetFlags,
};
use awkernel_lib::sync::rwlock::RwLock;
use crate::pcie::virtio::VirtioDriverErr;

const VIRTIO_NET_ID: u16 = 0x1041;

// device-specific feature bits
const VIRTIO_NET_F_CSUM: u64 = 1 << 0;
const VIRTIO_NET_F_CTRL_GUEST_OFFLOADS: u64 = 1 << 2;
const VIRTIO_NET_F_MAC: u64 = 1 << 5;
const VIRTIO_NET_F_GUEST_TSO4: u64 = 1 << 7;
const VIRTIO_NET_F_GUEST_TSO6: u64 = 1 << 8;
const VIRTIO_NET_F_HOST_TSO4: u64 = 1 << 11;
const VIRTIO_NET_F_HOST_TSO6: u64 = 1 << 12;
const VIRTIO_NET_F_STATUS: u64 = 1 << 16;
const VIRTIO_NET_F_CTRL_VQ: u64 = 1 << 17;
const VIRTIO_NET_F_MQ: u64 = 1 << 22;

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
const _VIRTIO_PCI_CAP_NOTIFY_CFG: u8 = 2; // Notifications
const _VIRTIO_PCI_CAP_ISR_CFG: u8 = 3; // ISR Status
const VIRTIO_PCI_CAP_DEVICE_CFG: u8 = 4; // Device specific configuration
const _VIRTIO_PCI_CAP_PCI_CFG: u8 = 5; // PCI configuration access
const _VIRTIO_PCI_CAP_SHARED_MEMORY_CFG: u8 = 8; // Shared memory region
const _VIRTIO_PCI_CAP_VENDOR_CFG: u8 = 9; // Vendor-specific data

const VIRTIO_NET_S_LINK_UP: u16 = 1;

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
    driver_features: u64,
    active_features: u64,

    nqueues: usize,
    nvqs: usize,

    flags: NetFlags,
    capabilities: NetCapabilities,
}

impl VirtioNetInner {
    pub fn new(info: PCIeInfo) -> Self {
        Self {
            info,
            mac_addr: [0; 6],
            common_cfg: VirtioCommonConfig::new(),
            net_cfg: VirtioNetConfig::new(),
            driver_features: 0,
            active_features: 0,

            nqueues: 0,
            nvqs: 0,

            flags: NetFlags::empty(),
            capabilities: NetCapabilities::empty(),
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

        self.common_cfg.init(&self.info, common_cfg_cap)?;
        self.net_cfg.init(&self.info, net_cfg_cap)?;

        Ok(())
    }

    fn virtio_pci_attach(&mut self) -> Result<(), VirtioDriverErr> {
        // TODO: init MSIX

        self.virtio_pci_attach_10()?;

        self.common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_RESET)?;
        self.common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_ACK)?;
        self.common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_DRIVER)?;

        Ok(())
    }

    fn vio_attach(&mut self) -> Result<(), VirtioDriverErr> {
        self.driver_features = 0;
        self.driver_features |= VIRTIO_NET_F_MAC;
        self.driver_features |= VIRTIO_NET_F_STATUS;
        // self.driver_features |= VIRTIO_NET_F_CTRL_VQ;
        // self.driver_features |= VIRTIO_NET_F_CTRL_RX;
        // self.driver_features |= VIRTIO_NET_F_MRG_RXBUF;
        // self.driver_features |= VIRTIO_NET_F_CSUM;
        // self.driver_features |= VIRTIO_F_RING_EVENT_IDX;
        // self.driver_features |= VIRTIO_NET_F_GUEST_CSUM;
        // self.driver_features |= VIRTIO_NET_F_MQ;
        // self.driver_features |= VIRTIO_NET_F_HOST_TSO4;
        // self.driver_features |= VIRTIO_NET_F_HOST_TSO6;
        // self.driver_features |= VIRTIO_NET_F_CTRL_GUEST_OFFLOADS;
        // self.driver_features |= VIRTIO_NET_F_GUEST_TSO4;
        // self.driver_features |= VIRTIO_NET_F_GUEST_TSO6;

        self.virtio_pci_negotiate_features()?;
        
        if self.virtio_has_feature(VIRTIO_NET_F_MQ) {
            todo!()
        } else {
            self.nqueues = 1;
            self.nvqs = 2;
            if self.virtio_has_feature(VIRTIO_NET_F_CTRL_VQ) {
                self.nvqs += 1;
            }
        }

        // TODO: malloc

        if self.virtio_has_feature(VIRTIO_NET_F_MAC) {
            self.mac_addr = self.net_cfg.virtio_get_mac_addr()?;
        } else {
            todo!()
        }

        self.capabilities = NetCapabilities::empty();
        self.flags = NetFlags::BROADCAST | NetFlags::SIMPLEX | NetFlags::MULTICAST;

        if self.virtio_has_feature(VIRTIO_NET_F_CSUM) {
            todo!()
        }

        if self.virtio_has_feature(VIRTIO_NET_F_HOST_TSO4) {
            todo!()
        }

        if self.virtio_has_feature(VIRTIO_NET_F_HOST_TSO6) {
            todo!()
        }

        if self.virtio_has_feature(VIRTIO_NET_F_CTRL_GUEST_OFFLOADS) && (
            self.virtio_has_feature(VIRTIO_NET_F_GUEST_TSO4) || self.virtio_has_feature(VIRTIO_NET_F_GUEST_TSO6)) {
            todo!()
        }
        
        // TODO: if.if_hardmtu
        // TODO: tx_max_segments
        // TODO: sc_tx_slots_per_req
        // TODO: initialize virtqueues

        if self.virtio_has_feature(VIRTIO_NET_F_CTRL_VQ) {
            todo!()
        }

        // TODO: sc_intrmap

        // TODO: vio_alloc_mem

        self.virtio_attach_finish()?;
        

        // TODO

        Ok(())
    }

    fn virtio_pci_negotiate_features(&mut self) -> Result<(), VirtioDriverErr> {
        self.active_features = 0;

        // TODO

        self.virtio_pci_negotiate_features_10()?;

        Ok(())
    }

    fn virtio_pci_negotiate_features_10(&mut self) -> Result<(), VirtioDriverErr> {
        self.driver_features |= VIRTIO_F_VERSION_1;
        self.driver_features |= VIRTIO_F_ACCESS_PLATFORM; // Without this SEV doesn't work with a KVM/qemu hypervisor on amd64
        self.driver_features &= !VIRTIO_F_NOTIFY_ON_EMPTY; // notify on empty is 0.9 only

        let device_features = self.common_cfg.virtio_get_device_features()?;

        let negotiated_features = device_features & self.driver_features;

        self.common_cfg.virtio_set_driver_features(negotiated_features);

        self.common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_FEATURES_OK)?;

        let device_status = self.common_cfg.virtio_get_device_status()?;
        if device_status & VIRTIO_CONFIG_DEVICE_STATUS_FEATURES_OK == 0 {
            self.common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_FAILED)?;
            return Err(VirtioDriverErr::InitFailure);
        }

        self.active_features = negotiated_features;

        if negotiated_features & VIRTIO_F_VERSION_1 == 0 {
            self.common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_FAILED)?;
            return Err(VirtioDriverErr::InitFailure);
        }

        Ok(())
    }

    fn virtio_has_feature(&self, feature: u64) -> bool {
        self.active_features & feature != 0
    }

    fn virtio_attach_finish(&mut self) -> Result<(), VirtioDriverErr> {
        // TODO: self.virtio_pci_attach_finish
        // TODO: self.virtio_pci_setup_intrs
        // TODO: virtio_setup_queue

        self.common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_DRIVER_OK)?;

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

        Ok(Self { inner: RwLock::new(inner) })
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
            log::info!("status: {}", status);
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
        todo!()
    }

    fn send(&self, _data: EtherFrameRef, _que_id: usize) -> Result<(), NetDevError> {
        todo!()
    }

    fn up(&self) -> Result<(), NetDevError> {
        // TODO: Implement this
        Ok(())
    }

    fn down(&self) -> Result<(), NetDevError> {
        todo!()
    }

    fn interrupt(&self, _irq: u16) -> Result<(), NetDevError> {
        todo!()
    }

    fn irqs(&self) -> Vec<u16> {
        // TODO: Implement this
        Vec::new()
    }

    fn rx_irq_to_que_id(&self, _irq: u16) -> Option<usize> {
        todo!()
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
