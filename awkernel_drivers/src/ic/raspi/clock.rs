use super::mbox::{msg, Error, TagId};

const TURBO_ID: u32 = 0;
const CLOCK_STATE_ON_MASK: u32 = 0x0000_0001;
const CLOCK_STATE_NOT_EXISTS_MASK: u32 = 0x0000_0002;

/// Clock IDs, as enumerated by the mailbox property interface.
#[repr(u32)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClockId {
    Emmc = 0x0000_0001,
    Uart = 0x0000_0002,
    Arm = 0x0000_0003,
    Core = 0x0000_0004,
    V3d = 0x0000_0005,
    H264 = 0x0000_0006,
    Isp = 0x0000_0007,
    Sdram = 0x0000_0008,
    Pixel = 0x0000_0009,
    Pwm = 0x0000_000a,
    Hevc = 0x0000_000b,
    Emmc2 = 0x0000_000c,
    M2mc = 0x0000_000d,
    PixelBvb = 0x0000_000e,
}

/// Shared implementation for the "get {,max,min,measured} clock rate" tags, which
/// all share the same request (clock id) / response (clock id, rate) shape.
#[inline]
fn get_rate(tag: TagId, clock_id: ClockId) -> Result<u32, Error> {
    match msg::get_by_id(tag, clock_id as u32)? {
        0 => Err(Error::DoesNotExist),
        rate => Ok(rate),
    }
}

/// Returns the last requested/enabled rate (in Hz) of `clock_id`, even if the
/// clock is not currently running.
pub fn get_clock_rate_hz(clock_id: ClockId) -> Result<u32, Error> {
    get_rate(TagId::GetClockRate, clock_id)
}

/// Returns the true/actual rate (in Hz) of `clock_id`, respecting clamping,
/// throttling, and clock divider limitations (unlike [`get_clock_rate_hz`]).
pub fn get_clock_rate_measured_hz(clock_id: ClockId) -> Result<u32, Error> {
    get_rate(TagId::GetClockRateMeasured, clock_id)
}

/// Returns the maximum supported rate (in Hz) of `clock_id`.
pub fn get_max_clock_rate_hz(clock_id: ClockId) -> Result<u32, Error> {
    get_rate(TagId::GetMaxClockRate, clock_id)
}

/// Returns the minimum supported rate (in Hz) of `clock_id`.
pub fn get_min_clock_rate_hz(clock_id: ClockId) -> Result<u32, Error> {
    get_rate(TagId::GetMinClockRate, clock_id)
}

/// Returns the enable state of `clock_id`.
pub fn get_clock_state(clock_id: ClockId) -> Result<bool, Error> {
    let state: u32 = msg::get_by_id(TagId::GetClockState, clock_id as u32)?;
    if state == CLOCK_STATE_NOT_EXISTS_MASK {
        return Err(Error::DoesNotExist);
    }
    Ok(state & CLOCK_STATE_ON_MASK != 0)
}

/// Turns `clock_id` on or off.
pub fn set_clock_state(clock_id: ClockId, on: bool) -> Result<bool, Error> {
    let state: u32 = msg::set_by_id(TagId::SetClockState, clock_id as u32, on as u32)?;
    if state & CLOCK_STATE_NOT_EXISTS_MASK != 0 {
        return Err(Error::DoesNotExist);
    }
    Ok(state & CLOCK_STATE_ON_MASK != 0)
}

/// Requests the firmware to set `clock_id` to `hz`.
///
/// Returns the actual rate (in Hz) accepted by the firmware.
///
/// # Note
///
/// The firmware may clamp the requested rate to a supported value, so callers
/// must use the returned rate rather than assuming `hz` was applied as-is.
///
/// When `skip_turbo` is `false` (the default firmware behavior), raising a clock
/// above its default rate may also raise other turbo settings (voltage, SDRAM,
/// and GPU frequencies). Set `skip_turbo` to `true` to suppress that side effect.
pub fn set_clock_rate_hz(clock_id: ClockId, hz: u32, skip_turbo: bool) -> Result<u32, Error> {
    let skip_turbo = skip_turbo as u32;
    let rate_hz: u32 = msg::set_by_id(TagId::SetClockRate, clock_id as u32, (hz, skip_turbo))?;
    match rate_hz {
        0 => Err(Error::DoesNotExist),
        _ => Ok(rate_hz),
    }
}

/// Returns whether turbo mode is currently enabled.
pub fn get_turbo() -> Result<bool, Error> {
    let turbo: u32 = msg::get_by_id(TagId::GetTurbo, TURBO_ID)?;
    Ok(turbo != 0)
}

/// Enables or disables turbo mode. Returns the new turbo level echoed by the firmware.
///
/// # Note
///
/// Enabling sets the GPU clocks to maximum; disabling sets them to minimum.
pub fn set_turbo(enable: bool) -> Result<bool, Error> {
    let level: u32 = msg::set_by_id(TagId::SetTurbo, TURBO_ID, enable as u32)?;
    Ok(level != 0)
}
