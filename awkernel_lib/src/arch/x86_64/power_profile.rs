//! Energy and power measurement for Intel CPUs, using RAPL (Running Average Power Limit).
//!
//! The RAPL energy counters accumulate the energy consumed by a domain:
//! - [`Domain::Package`]: the whole processor package (`MSR_PKG_ENERGY_STATUS`).
//! - [`Domain::Cores`]: all the cores of the package (`MSR_PP0_ENERGY_STATUS`).
//!   RAPL does not report the energy of individual cores.
//!
//! The counters are 32 bits wide and wrap around at [`Domain::energy_range_uj`].

use crate::delay::{uptime_nano, wait_millisec};

use super::msr::{pkg_energy_status, pp0_energy_status, rapl_power_unit};

/// Sampling period of [`Domain::power_uw`] in milliseconds.
pub const POWER_SAMPLE_PERIOD_MS: u64 = 100;

/// Error type for power profiling operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The CPU does not implement the required RAPL MSRs.
    NotSupported,
    /// No time elapsed between two samples.
    InternalError,
}

pub type Result<T> = core::result::Result<T, Error>;

/// A RAPL power domain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Domain {
    /// The whole processor package.
    Package,
    /// All the cores of the package (PP0).
    Cores,
}

impl Domain {
    fn read_raw(self) -> Option<u32> {
        match self {
            Domain::Package => pkg_energy_status::try_read(),
            Domain::Cores => pp0_energy_status::try_read(),
        }
    }

    /// Read the energy counter of this domain in microjoules.
    /// The counter wraps around at [`Domain::energy_range_uj`].
    pub fn energy_uj(self) -> Result<u64> {
        let unit = rapl_power_unit::try_read().ok_or(Error::NotSupported)?;
        let raw = self.read_raw().ok_or(Error::NotSupported)?;
        Ok(unit.energy_to_uj(raw))
    }

    /// Value in microjoules at which the energy counter of this domain wraps around.
    pub fn energy_range_uj(self) -> Result<u64> {
        rapl_power_unit::try_read()
            .map(|unit| unit.max_energy_range_uj())
            .ok_or(Error::NotSupported)
    }

    /// Energy in microjoules consumed between two readings of [`Domain::energy_uj`],
    /// handling one wrap-around of the counter.
    pub fn energy_delta_uj(self, start_uj: u64, end_uj: u64) -> Result<u64> {
        if end_uj >= start_uj {
            Ok(end_uj - start_uj)
        } else {
            Ok(self.energy_range_uj()? - start_uj + end_uj)
        }
    }

    /// Average power in microwatts between two readings of [`Domain::energy_uj`]
    /// taken `elapsed_ns` nanoseconds apart. Use it to sample power without blocking.
    pub fn average_power_uw(self, start_uj: u64, end_uj: u64, elapsed_ns: u128) -> Result<u64> {
        if elapsed_ns == 0 {
            return Err(Error::InternalError);
        }
        let energy_uj = self.energy_delta_uj(start_uj, end_uj)?;
        Ok((energy_uj as u128 * 1_000_000_000 / elapsed_ns) as u64)
    }

    /// Average power of this domain in microwatts, sampled over [`POWER_SAMPLE_PERIOD_MS`].
    /// Blocks the current CPU during the sampling period.
    pub fn power_uw(self) -> Result<u64> {
        let start_ns = uptime_nano();
        let start_uj = self.energy_uj()?;
        wait_millisec(POWER_SAMPLE_PERIOD_MS);
        let end_uj = self.energy_uj()?;
        let end_ns = uptime_nano();

        self.average_power_uw(start_uj, end_uj, end_ns.saturating_sub(start_ns))
    }
}
