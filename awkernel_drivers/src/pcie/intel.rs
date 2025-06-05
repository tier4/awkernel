use alloc::sync::Arc;

use super::{PCIeDevice, PCIeDeviceErr, PCIeInfo};

#[cfg(feature = "igb")]
pub mod igb; // Intel GbE

#[cfg(feature = "igc")]
#[allow(dead_code)] // TODO: remove this
pub mod igc; // Intel 2.5GbE

#[cfg(feature = "ixgbe")]
pub mod ixgbe; // Intel 10GbE

pub mod e1000e_example;

pub(super) fn attach(info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    #[cfg(feature = "igb")]
    if igb::match_device(info.vendor, info.id) {
        return igb::attach(info);
    }

    #[cfg(feature = "igc")]
    if igc::match_device(info.vendor, info.id) {
        return igc::attach(info);
    }

    #[cfg(feature = "ixgbe")]
    if ixgbe::match_device(info.vendor, info.id) {
        return ixgbe::attach(info);
    }

    // Example of the driver for Intel E1000e.
    if e1000e_example::match_device(info.vendor, info.id) {
        return e1000e_example::attach(info);
    }

    Ok(info.unknown_device())
}
