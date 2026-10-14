//! DVFS for Raspberry Pi, backed by the firmware mailbox ARM clock.
//!
//! The ARM clock is shared by all cores, so per-CPU frequency control is not supported.

use crate::ic::raspi::{
    clock::{self, ClockId},
    mbox::Error as MboxError,
};
use awkernel_lib::{
    dvfs::{Dvfs, Error, Result},
    impl_dvfs,
};

pub struct RaspiDvfs;

fn map_err(e: MboxError) -> Error {
    match e {
        MboxError::DoesNotExist => Error::NotSupported,
        MboxError::InvalidAddress | MboxError::BufferTooLarge => Error::InvalidArgument,
        _ => Error::InternalError,
    }
}

impl Dvfs for RaspiDvfs {
    fn set_cpu_freq(_freq: u64) -> Result<()> {
        Err(Error::NotSupported)
    }
    /// Sets the ARM clock, which is shared by all cores. The effect is global.
    unsafe fn set_global_freq(freq: u64) -> Result<()> {
        let hz = u32::try_from(freq).map_err(|_| Error::InvalidArgument)?;
        clock::set_clock_rate_hz(ClockId::Arm, hz, true)
            .map(|_| ())
            .map_err(map_err)
    }

    fn get_max_cpu_freq() -> Result<u64> {
        clock::get_max_clock_rate_hz(ClockId::Arm)
            .map(u64::from)
            .map_err(map_err)
    }

    fn get_min_cpu_freq() -> Result<u64> {
        clock::get_min_clock_rate_hz(ClockId::Arm)
            .map(u64::from)
            .map_err(map_err)
    }

    fn get_curr_cpu_freq() -> Result<u64> {
        clock::get_clock_rate_hz(ClockId::Arm)
            .map(u64::from)
            .map_err(map_err)
    }
}

// Override default implementation of DVFS functions with the RaspiDvfs implementation.
impl_dvfs!(RaspiDvfs);
