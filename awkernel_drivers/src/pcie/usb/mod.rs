//! USB host controller drivers.

// Hardening gates for this driver tree (see the rust-hardening policy):
// panics, silent overflow, lossy casts and swallowed results are compile errors.
#![deny(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::unreachable,
    clippy::todo,
    clippy::unimplemented,
    clippy::indexing_slicing,
    clippy::string_slice,
    clippy::unwrap_in_result,
    clippy::arithmetic_side_effects,
    clippy::let_underscore_must_use,
    clippy::as_conversions,
    clippy::cast_possible_truncation,
    clippy::cast_possible_wrap,
    clippy::cast_sign_loss,
    clippy::allow_attributes_without_reason,
    unsafe_op_in_unsafe_fn
)]

use alloc::sync::Arc;

use super::{registers::CLASS_CODE_REVISION_ID, PCIeDevice, PCIeDeviceErr, PCIeInfo};

pub mod xhci;

/// PCI sub-class of a USB controller (class 0x0C, Serial Bus Controller).
const SUBCLASS_USB: u8 = 0x03;
/// PCI programming interface of an xHCI controller.
const PROG_IF_XHCI: u8 = 0x30;

/// True if `info` is an xHCI USB host controller.
///
/// `PCIeClass::SerialBusController` does not carry the sub-class and
/// programming interface, so they are read from config space.
pub(super) fn is_xhci(info: &PCIeInfo) -> bool {
    // CLASS_CODE_REVISION_ID: class[31:24] sub-class[23:16] prog-if[15:8] revision[7:0].
    let [_, prog_if, sub_class, _] = info
        .config_space
        .read_u32(CLASS_CODE_REVISION_ID)
        .to_le_bytes();
    sub_class == SUBCLASS_USB && prog_if == PROG_IF_XHCI
}

/// Attach the xHCI controller `info` (the caller checked [`is_xhci`]).
pub(super) fn attach(info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    xhci::attach(info)
}
