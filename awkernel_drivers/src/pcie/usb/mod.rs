use alloc::sync::Arc;

use super::{PCIeDevice, PCIeDeviceErr, PCIeInfo};

#[cfg(feature = "xhci")]
pub mod xhci;

/// Detect and attach a USB host controller from a SerialBusController PCIe device.
///
/// Reads sub-class and programming interface from config space to identify the
/// controller type, since PCIeClass::SerialBusController does not carry that detail.
pub(super) fn attach(info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    use super::registers::CLASS_CODE_REVISION_ID;

    let cls = info.config_space.read_u32(CLASS_CODE_REVISION_ID);
    let sub_class = ((cls >> 16) & 0xff) as u8;
    let prog_if = ((cls >> 8) & 0xff) as u8;

    #[cfg(feature = "xhci")]
    if sub_class == 0x03 && prog_if == 0x30 {
        return xhci::attach(info);
    }

    log::debug!(
        "usb: unhandled SerialBusController sub={:#04x} prog_if={:#04x}",
        sub_class,
        prog_if,
    );
    Ok(info.unknown_device())
}
