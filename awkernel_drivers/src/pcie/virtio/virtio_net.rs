use crate::pcie::{
    capability::virtio::VirtioCap,
    pcie_id,
    virtio::config::{
        virtio_common_config::VirtioCommonConfig, virtio_net_config::VirtioNetConfig,
    },
    virtio::VirtioDriverErr,
    PCIeDevice, PCIeDeviceErr, PCIeInfo,
};
use alloc::{borrow::Cow, sync::Arc, vec::Vec};
use awkernel_lib::{
    net::net_device::{
        EtherFrameBuf, EtherFrameRef, LinkStatus, NetCapabilities, NetDevError, NetDevice, NetFlags,
    },
    sync::rwlock::RwLock,
};

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
const _VIRTIO_PCI_CAP_NOTIFY_CFG: u8 = 2; // Notifications
const _VIRTIO_PCI_CAP_ISR_CFG: u8 = 3; // ISR Status
const VIRTIO_PCI_CAP_DEVICE_CFG: u8 = 4; // Device specific configuration
const _VIRTIO_PCI_CAP_PCI_CFG: u8 = 5; // PCI configuration access
const _VIRTIO_PCI_CAP_SHARED_MEMORY_CFG: u8 = 8; // Shared memory region
const _VIRTIO_PCI_CAP_VENDOR_CFG: u8 = 9; // Vendor-specific data

const VIRTIO_NET_S_LINK_UP: u16 = 1;

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
    driver_features: u64,
    active_features: u64,
    flags: NetFlags,
    capabilities: NetCapabilities,
}

impl VirtioNetInner {
    pub fn new(info: PCIeInfo) -> Self {
        Self {
            info,
            mac_addr: [0; 6],
            common_cfg: VirtioCommonConfig::default(),
            net_cfg: VirtioNetConfig::default(),
            driver_features: 0,
            active_features: 0,
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
        // TODO: setup control queue
        // TODO: setup interrupt

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

    fn _virtio_pci_read_queue_size(&mut self, idx: u16) -> Result<u16, VirtioDriverErr> {
        self.common_cfg.virtio_set_queue_select(idx)?;
        self.common_cfg.virtio_get_queue_size()
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
