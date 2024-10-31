use crate::dvfs::Dvfs;

use super::X86;

impl Dvfs for X86 {
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
