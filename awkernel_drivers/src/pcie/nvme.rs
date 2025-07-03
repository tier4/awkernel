use alloc::sync::Arc;

use super::{PCIeDevice, PCIeDeviceErr, PCIeInfo};

pub(super) fn attach(info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    Ok(info.unknown_device())
}
