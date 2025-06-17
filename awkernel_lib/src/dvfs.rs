#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DesiredPerformance {
    Desired(u8),
    Auto,
}

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
    /// (range from 0, lowest performance, through 100, highest performance)
    ///
    /// If current driver does not support this operation,
    /// it will return `false`.
    fn set_min_performance(min: u8) -> bool {
        false
    }

    /// Get the Minimum Performance.
    /// (range from 0, lowest performance, through 100, highest performance)
    ///
    /// If current driver does not support this operation,
    /// it will return `None`.
    fn get_min_performance() -> Option<u8> {
        None
    }

    /// Set the Maximum Performance.
    /// (range from 0, lowest performance, through 100, highest performance)
    ///
    /// If current driver does not support this operation,
    /// it will return `false`.
    fn set_max_performance(max: u8) -> bool {
        false
    }

    /// Get the Maximum Performance.
    /// (range from 0, lowest performance, through 100, highest performance)
    ///
    /// If current driver does not support this operation,
    /// it will return `None`.
    fn get_max_performance() -> Option<u8> {
        None
    }

    /// Select the Minimum and Maximum Performance.
    /// (range from 0, lowest performance, through 100, highest performance)
    ///
    /// If current driver does not support this operation,
    /// it will return `false`.
    fn set_min_max_performance(min: u8) -> bool {
        false
    }

    /// Set the Energy Efficiency Preference.
    /// (range from 0, highest performance, through 100, highest energy efficient)
    ///
    /// If current driver does not support this operation,
    /// it will return `false`.
    fn set_energy_efficiency(val: u8) -> bool {
        false
    }

    /// Set the Desired Performance.
    /// (range from 0, lowest performance, through 100, highest performance)
    ///
    /// If current driver does not support this operation,
    /// it will return `false`.
    fn set_desired_performance(val: DesiredPerformance) -> bool {
        false
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

/// Set Maximum Performance.
/// (range from 0, lowest performance, through 100, highest performance)
///
/// If the driver does not support `set_max_performance()`, `false` will be returned.
#[inline(always)]
pub fn set_max_performance(max: u8) -> bool {
    crate::arch::ArchImpl::set_max_performance(max)
}

/// Set Minimum Performance.
/// (range from 0, lowest performance, through 100, highest performance)
///
/// If the driver does not support `set_min_performance()`, `false` will be returned.
#[inline(always)]
pub fn set_min_performance(min: u8) -> bool {
    crate::arch::ArchImpl::set_min_performance(min)
}

/// Set the Energy Efficiency Preference.
/// (range from 0, highest performance, through 100, highest energy efficient)
///
/// If the driver does not support `set_energy_efficiency()`, `false` will be returned.
#[inline(always)]
pub fn set_energy_efficiency(val: u8) -> bool {
    crate::arch::ArchImpl::set_energy_efficiency(val)
}

/// Set the Desired Performance.
/// (range from 0, lowest performance, through 100, highest performance)
///
/// If the driver does not support `set_desired_performance()`, `false` will be returned.
#[inline(always)]
pub fn set_desired_performance(val: DesiredPerformance) -> bool {
    crate::arch::ArchImpl::set_desired_performance(val)
}

/// Set Minimum and Maximum Performance.
/// (range from 0, lowest performance, through 100, highest performance)
///
/// If the driver does not support `set_min_max_performance()`, `false` will be returned.
#[inline(always)]
pub fn set_min_max_performance(percent: u8) -> bool {
    crate::arch::ArchImpl::set_min_max_performance(percent)
}
