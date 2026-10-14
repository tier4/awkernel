//! Raspberry Pi firmware property-mailbox temperature operations.

use super::mbox::{msg, Error, TagId};

const SOC_TEMPERATURE_ID: u32 = 0;

/// Gets the SoC temperature in thousandths of a degree Celsius.
pub fn get_temperature_millicelsius() -> Result<u32, Error> {
    msg::get_by_id(TagId::GetTemperature, SOC_TEMPERATURE_ID)
}

/// Gets the maximum safe SoC temperature in thousandths of a degree Celsius.
pub fn get_max_temperature_millicelsius() -> Result<u32, Error> {
    msg::get_by_id(TagId::GetMaxTemperature, SOC_TEMPERATURE_ID)
}
