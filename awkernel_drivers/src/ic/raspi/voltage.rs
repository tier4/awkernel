//! Raspberry Pi firmware property-mailbox voltage operations.

use super::mbox::{msg, Error, TagId};

const INVALID_VOLTAGE: u32 = 0x8000_0000;

/// Voltage IDs, as enumerated by the mailbox property interface.
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VoltageId {
    Core = 0x0000_0001,
    SdramC = 0x0000_0002,
    SdramP = 0x0000_0003,
    SdramI = 0x0000_0004,
}

/// Gets the absolute voltage for `id`, in microvolts.
fn get_voltage(id: VoltageId, tag: TagId) -> Result<u32, Error> {
    match msg::get_by_id(tag, id as u32)? {
        INVALID_VOLTAGE => Err(Error::DoesNotExist),
        voltage_uv => Ok(voltage_uv),
    }
}

/// Gets the absolute voltage for `id`, in microvolts.
pub fn get_voltage_uv(id: VoltageId) -> Result<u32, Error> {
    get_voltage(id, TagId::GetVoltage)
}

/// Gets the maximum supported absolute voltage for `id`, in microvolts.
pub fn get_max_voltage_uv(id: VoltageId) -> Result<u32, Error> {
    get_voltage(id, TagId::GetMaxVoltage)
}

/// Gets the minimum supported absolute voltage for `id`, in microvolts.
pub fn get_min_voltage_uv(id: VoltageId) -> Result<u32, Error> {
    get_voltage(id, TagId::GetMinVoltage)
}

/// Sets a voltage request and returns the firmware-reported absolute voltage in microvolts.
///
/// # Note
///
/// The request value follows the firmware encoding: values through 16 are 25 mV steps relative
/// to typical voltage, values 17 through 499999 are relative microvolts, and values at least
/// 500000 are absolute microvolts.
pub fn set_voltage(id: VoltageId, requested_value: u32) -> Result<u32, Error> {
    match msg::set_by_id(TagId::SetVoltage, id as u32, requested_value)? {
        INVALID_VOLTAGE => Err(Error::DoesNotExist),
        voltage_uv => Ok(voltage_uv),
    }
}
