#[allow(unused_variables)]
pub trait Dvfs {
    /// Fix the frequency of the current CPU.
    ///
    /// If current driver does not support this operation,
    /// it will return `false`.
    fn fix_freq(freq: u64) -> bool {
        false
    }

    /// Get the maximum frequency of the current CPU.
    ///
    /// If current driver does not support this operation,
    /// it will return `None`.
    fn get_max_freq() -> Option<u64> {
        None
    }

    /// Get the frequency of the current CPU.
    ///
    /// If current driver does not support this operation,
    /// it will return `None`.
    fn get_curr_freq() -> Option<u64> {
        None
    }

    /// Select the Minimum Performance.
    /// (range from 0, lowest performant, through 100, highest performance)
    ///
    /// If current driver does not support this operation,
    /// it will return `false`.
    fn set_min_performance(min: u8) -> bool {
        false
    }

    /// Get the Minimum Performance.
    /// (range from 0, lowest performant, through 100, highest performance)
    ///
    /// If current driver does not support this operation,
    /// it will return `None`.
    fn get_min_performance() -> Option<u8> {
        None
    }

    /// Set the Maximum Performance.
    /// (range from 0, lowest performant, through 100, highest performance)
    ///
    /// If current driver does not support this operation,
    /// it will return `false`.
    fn set_max_performance(max: u8) -> bool {
        false
    }

    /// Get the Maximum Performance.
    /// (range from 0, lowest performant, through 100, highest performance)
    ///
    /// If current driver does not support this operation,
    /// it will return `None`.
    fn get_max_performance() -> Option<u8> {
        None
    }
}

/// Fix the frequency of the current CPU.
#[inline(always)]
pub fn fix_freq(freq: u64) {
    crate::arch::ArchImpl::fix_freq(freq);
}

/// Get the maximum frequency of the current CPU.
#[inline(always)]
pub fn get_max_freq() -> Option<u64> {
    crate::arch::ArchImpl::get_max_freq()
}

/// Get the frequency of the current CPU.
#[inline(always)]
pub fn get_curr_freq() -> Option<u64> {
    crate::arch::ArchImpl::get_curr_freq()
}
