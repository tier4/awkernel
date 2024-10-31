use crate::dvfs::Dvfs;

use super::RV64;

impl Dvfs for RV64 {
    /// Set the frequency of the current CPU.
    fn set_freq(&self, _freq: u64) {
        // TODO: Implement this.
    }

    /// Get the frequency of the current CPU.
    fn get_freq(&self) -> u64 {
        // TODO: Implement this.
        0
    }
}
