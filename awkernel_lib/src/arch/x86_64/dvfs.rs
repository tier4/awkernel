use crate::dvfs::Dvfs;

use super::X86;

impl Dvfs for X86 {
    /// Fix the frequency of the current CPU.
    fn fix_freq(_freq: u64) {
        // TODO: Implement this.
    }

    /// Get the maximum frequency of the current CPU.
    fn get_max_freq() -> u64 {
        // TODO: Implement this.
        0
    }

    /// Get the frequency of the current CPU.
    fn get_curr_freq() -> u64 {
        // TODO: Implement this.
        0
    }
}
