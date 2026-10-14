use super::mbox::{msg, Error, TagId};

const POWER_STATE_MASK: u32 = 0x0000_0001;
const DEVICE_DOES_NOT_EXIST_MASK: u32 = 0x0000_0002;

/// Device IDs, as enumerated by the mailbox property interface.
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DeviceId {
    SDCard = 0x0000_0000,
    Uart0 = 0x0000_0001,
    Uart1 = 0x0000_0002,
    UsbHcd = 0x0000_0003,
    I2C0 = 0x0000_0004,
    I2C1 = 0x0000_0005,
    I2C2 = 0x0000_0006,
    Spi = 0x0000_0007,
    Ccp2Tx = 0x0000_0008,
}

/// Returns the enable state of `device_id`.
pub fn get_power_state(device_id: DeviceId) -> Result<bool, Error> {
    let state: u32 = msg::get_by_id(TagId::GetPowerState, device_id as u32)?;
    if state & DEVICE_DOES_NOT_EXIST_MASK != 0 {
        return Err(Error::DoesNotExist);
    }
    Ok(state & POWER_STATE_MASK != 0)
}

/// Returns the timing information of `device_id`.
pub fn get_timing(device_id: DeviceId) -> Result<u32, Error> {
    let micros: u32 = msg::get_by_id(TagId::GetTiming, device_id as u32)?;
    if micros == 0 {
        return Err(Error::DoesNotExist);
    }
    Ok(micros)
}

pub fn set_power_state(device_id: DeviceId, state: bool, wait: bool) -> Result<bool, Error> {
    let req_state = (wait as u32) << 1 | state as u32;
    let ret_state: u32 = msg::set_by_id(TagId::SetPowerState, device_id as u32, req_state)?;

    if ret_state & DEVICE_DOES_NOT_EXIST_MASK != 0 {
        return Err(Error::DoesNotExist);
    }
    Ok(ret_state & POWER_STATE_MASK != 0)
}
