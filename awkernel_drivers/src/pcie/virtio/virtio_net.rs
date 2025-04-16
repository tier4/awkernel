use crate::pcie::{
    capability::virtio::VirtioCap, pcie_id,
    virtio::virtio_configuration::VirtioCommonConfiguration, PCIeDevice, PCIeDeviceErr, PCIeInfo,
};
use alloc::{borrow::Cow, sync::Arc};

const VIRTIO_NET_ID: u16 = 0x1041;

// device-independent feature bits
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
const _VIRTIO_PCI_CAP_DEVICE_CFG: u8 = 4; // Device specific configuration
const _VIRTIO_PCI_CAP_PCI_CFG: u8 = 5; // PCI configuration access
const _VIRTIO_PCI_CAP_SHARED_MEMORY_CFG: u8 = 8; // Shared memory region
const _VIRTIO_PCI_CAP_VENDOR_CFG: u8 = 9; // Vendor-specific data

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

    Ok(result)
}

#[derive(Debug, Clone, Copy)]
pub enum VirtioDriverErr {
    NoBar,
    ReadFailure,
}

pub struct VirtioNet {
    _info: PCIeInfo,
}

impl VirtioNet {
    pub fn new(info: PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        let common_cfg_cap = Self::virtio_pci_find_capability(&info, VIRTIO_PCI_CAP_COMMON_CFG);
        if common_cfg_cap.is_none() {
            return Err(PCIeDeviceErr::InitFailure);
        }

        let mut common_cfg = VirtioCommonConfiguration::new(&info, common_cfg_cap.unwrap());

        // 1. Reset the device.
        common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_RESET);

        // 2. Set the ACKNOWLEDGE status bit: the guest OS has noticed the device.
        common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_ACK);

        // 3. Set the DRIVER status bit: the guest OS knows how to drive the device.
        common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_DRIVER);

        // 4. Read device feature bits,
        // and write the subset of feature bits understood by the OS and driver to the device.
        common_cfg.virtio_set_driver_features(VIRTIO_F_VERSION_1);
        common_cfg.virtio_set_driver_features(VIRTIO_F_ACCESS_PLATFORM);

        let device_features = common_cfg.virtio_get_device_features();
        let driver_features = common_cfg.virtio_get_driver_features();

        let negotiated_features = device_features & driver_features;
        common_cfg.virtio_set_driver_features(negotiated_features);

        // 5. Set the FEATURES_OK status bit. The driver MUST NOT accept new feature bits after this step.
        common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_FEATURES_OK);

        // 6. Re-read device status to ensure the FEATURES_OK bit is still set:
        // otherwise, the device does not support our subset of features and the device is unusable.
        let device_status = common_cfg.virtio_get_device_status();
        if device_status & VIRTIO_CONFIG_DEVICE_STATUS_FEATURES_OK == 0 {
            common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_FAILED);
            return Err(PCIeDeviceErr::InitFailure);
        }

        // 7. TODO: Perform device-specific setup.
        log::info!("TODO: VirtIO-net device-specific setup");

        // 8. Set the DRIVER_OK status bit. At this point the device is “live”.
        common_cfg.virtio_set_device_status(VIRTIO_CONFIG_DEVICE_STATUS_DRIVER_OK);

        Ok(Self { _info: info })
    }

    fn virtio_pci_find_capability(info: &PCIeInfo, cfg_type: u8) -> Option<VirtioCap> {
        for cap in &info.virtio_caps {
            if cap.get_cfg_type() == cfg_type {
                return Some(cap.clone());
            }
        }
        None
    }
}

impl PCIeDevice for VirtioNet {
    fn device_name(&self) -> Cow<'static, str> {
        "Virtio-net".into()
    }
}
