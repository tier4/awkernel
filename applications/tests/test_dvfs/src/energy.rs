//! Measure the energy and power of the package and of the cores with Intel RAPL.
//!
//! It runs on the same CPU as the DVFS task, so the power changes with the DVFS frequency.

use awkernel_lib::{arch::x86_64::power_profile::Domain, time::Instant};
use core::time::Duration;

pub const APP_NAME: &str = "test DVFS energy";

/// Sampling period. Shorter than the DVFS semi-period, so every frequency gets several samples.
const SAMPLE_PERIOD: Duration = Duration::from_millis(1000);

const DOMAINS: [(Domain, &str); 2] = [(Domain::Package, "package"), (Domain::Cores, "cores")];

/// Total energy and last reading of a domain.
struct Meter {
    domain: Domain,
    name: &'static str,
    last_uj: u64,
    total_uj: u64,
}

impl Meter {
    fn new(domain: Domain, name: &'static str) -> Option<Self> {
        match domain.energy_uj() {
            Ok(last_uj) => Some(Self {
                domain,
                name,
                last_uj,
                total_uj: 0,
            }),
            Err(e) => {
                log::warn!("[energy] {name}: RAPL not available: {e:?}");
                None
            }
        }
    }

    /// Read the counter and log the energy and the average power since the last reading.
    fn sample(&mut self, elapsed: Duration) {
        let result = self.domain.energy_uj().and_then(|now_uj| {
            let delta_uj = self.domain.energy_delta_uj(self.last_uj, now_uj)?;
            let power_uw =
                self.domain
                    .average_power_uw(self.last_uj, now_uj, elapsed.as_nanos())?;
            self.last_uj = now_uj;
            self.total_uj += delta_uj;
            Ok((delta_uj, power_uw))
        });

        match result {
            Ok((delta_uj, power_uw)) => log::info!(
                "[energy] {}: power = {}.{:03} W, energy = {} uJ, total = {} uJ",
                self.name,
                power_uw / 1_000_000,
                power_uw % 1_000_000 / 1_000,
                delta_uj,
                self.total_uj,
            ),
            Err(e) => log::warn!("[energy] {}: failed to sample: {e:?}", self.name),
        }
    }
}

pub async fn measure_energy() {
    let mut meters = DOMAINS.map(|(domain, name)| Meter::new(domain, name));
    if meters.iter().all(Option::is_none) {
        return;
    }

    let mut last = Instant::now();
    let mut next = last + SAMPLE_PERIOD;
    loop {
        awkernel_async_lib::sleep_until(next).await;
        next += SAMPLE_PERIOD;

        // Use the measured time, because the DVFS task may delay this one.
        let now = Instant::now();
        let elapsed = now - last;
        last = now;

        for meter in meters.iter_mut().flatten() {
            meter.sample(elapsed);
        }
    }
}
