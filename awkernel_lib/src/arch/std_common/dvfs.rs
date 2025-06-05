use crate::dvfs::Dvfs;

use super::StdCommon;

impl Dvfs for StdCommon {
    /// Fix the frequency of the current CPU.
    fn fix_freq(_freq: u64) {
        // no operation
    }

    /// Get the maximum frequency of the current CPU.
    fn get_max_freq() -> u64 {
        // no operation1
        1
    }

    /// Get the current frequency of the current CPU.
    fn get_curr_freq() -> u64 {
        // no operation
        1
    }
}
