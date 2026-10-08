/// Error type for DVFS operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    NotImplemented,
    NotSupported,
    InvalidArgument,
    InternalError,
    Other,
}

impl Error {
    /// Returns a string slice describing the error.
    pub const fn description(&self) -> &'static str {
        match self {
            Error::NotImplemented => "Not implemented",
            Error::NotSupported => "Not supported",
            Error::InvalidArgument => "Invalid argument",
            Error::InternalError => "Internal error",
            Error::Other => "Other error",
        }
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.description())
    }
}

impl core::error::Error for Error {}

pub type Result<T> = core::result::Result<T, Error>;

#[allow(unused_variables)]
pub trait Dvfs {
    /// Fix the frequency of the current CPU in Hz.
    #[inline(always)]
    fn set_cpu_freq(freq: u64) -> Result<()> {
        Err(Error::NotImplemented)
    }

    /// Set the frequency of all CPUs in the system.
    ///
    /// # Safety
    ///
    /// This function may have unintended side effects. Use with caution.
    #[inline(always)]
    unsafe fn set_global_freq(freq: u64) -> Result<()> {
        Err(Error::NotImplemented)
    }

    /// Get the maximum frequency of the current CPU in Hz.
    #[inline(always)]
    fn get_max_cpu_freq() -> Result<u64> {
        Err(Error::NotImplemented)
    }

    /// Get the minimum frequency of the current CPU in Hz.
    #[inline(always)]
    fn get_min_cpu_freq() -> Result<u64> {
        Err(Error::NotImplemented)
    }

    /// Get the frequency of the current CPU in Hz.
    #[inline(always)]
    fn get_curr_cpu_freq() -> Result<u64> {
        Err(Error::NotImplemented)
    }
}

/// Set the frequency of the current CPU in Hz and returns the actual frequency set in Hz.
#[inline(always)]
pub fn set_cpu_freq(freq: u64) -> Result<()> {
    crate::arch::ArchImpl::set_cpu_freq(freq)
}

/// Set the frequency of all CPUs in the system in Hz and returns the actual frequency set in Hz.
///
/// # Safety
///
/// This function may have unintended side effects. Use with caution.
#[inline(always)]
pub unsafe fn set_global_freq(freq: u64) -> Result<()> {
    crate::arch::ArchImpl::set_global_freq(freq)
}

/// Get the maximum frequency of the current CPU in Hz.
#[inline(always)]
pub fn get_max_cpu_freq() -> Result<u64> {
    crate::arch::ArchImpl::get_max_cpu_freq()
}

/// Get the frequency of the current CPU in Hz.
#[inline(always)]
pub fn get_curr_cpu_freq() -> Result<u64> {
    crate::arch::ArchImpl::get_curr_cpu_freq()
}
