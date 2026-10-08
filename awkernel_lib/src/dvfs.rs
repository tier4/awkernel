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

unsafe extern "Rust" {
    unsafe fn __awkernel_set_cpu_freq(freq: u64) -> Result<()>;
    unsafe fn __awkernel_set_global_freq(freq: u64) -> Result<()>;
    unsafe fn __awkernel_get_max_cpu_freq() -> Result<u64>;
    unsafe fn __awkernel_get_min_cpu_freq() -> Result<u64>;
    unsafe fn __awkernel_get_curr_cpu_freq() -> Result<u64>;
}

/// Set the frequency of the current CPU in Hz and returns the actual frequency set in Hz.
#[inline(always)]
pub fn set_cpu_freq(freq: u64) -> Result<()> {
    unsafe { __awkernel_set_cpu_freq(freq) }
}

/// Set the frequency of all CPUs in the system in Hz and returns the actual frequency set in Hz.
///
/// # Safety
///
/// This function may have unintended side effects. Use with caution.
#[inline(always)]
pub unsafe fn set_global_freq(freq: u64) -> Result<()> {
    unsafe { __awkernel_set_global_freq(freq) }
}

/// Get the maximum frequency of the current CPU in Hz.
#[inline(always)]
pub fn get_max_cpu_freq() -> Result<u64> {
    unsafe { __awkernel_get_max_cpu_freq() }
}

/// Get the minimum frequency of the current CPU in Hz.
#[inline(always)]
pub fn get_min_cpu_freq() -> Result<u64> {
    unsafe { __awkernel_get_min_cpu_freq() }
}

/// Get the frequency of the current CPU in Hz.
#[inline(always)]
pub fn get_curr_cpu_freq() -> Result<u64> {
    unsafe { __awkernel_get_curr_cpu_freq() }
}

#[linkage = "weak"]
#[export_name = "__awkernel_set_cpu_freq"]
extern "Rust" fn default_set_cpu_freq(freq: u64) -> Result<()> {
    crate::arch::ArchImpl::set_cpu_freq(freq)
}

#[linkage = "weak"]
#[export_name = "__awkernel_set_global_freq"]
unsafe extern "Rust" fn default_set_global_freq(freq: u64) -> Result<()> {
    crate::arch::ArchImpl::set_global_freq(freq)
}

#[linkage = "weak"]
#[export_name = "__awkernel_get_max_cpu_freq"]
extern "Rust" fn default_get_max_cpu_freq() -> Result<u64> {
    crate::arch::ArchImpl::get_max_cpu_freq()
}

#[linkage = "weak"]
#[export_name = "__awkernel_get_min_cpu_freq"]
extern "Rust" fn default_get_min_cpu_freq() -> Result<u64> {
    crate::arch::ArchImpl::get_min_cpu_freq()
}

#[linkage = "weak"]
#[export_name = "__awkernel_get_curr_cpu_freq"]
extern "Rust" fn default_get_curr_cpu_freq() -> Result<u64> {
    crate::arch::ArchImpl::get_curr_cpu_freq()
}

/// Overrides the weak default DVFS functions with the [`Dvfs`] implementation of `$ty`.
///
/// `$ty` must implement [`Dvfs`]. Invoke it once, in a crate linked into the final binary.
#[macro_export]
macro_rules! impl_dvfs {
    ($ty:ty) => {
        #[export_name = "__awkernel_set_cpu_freq"]
        extern "Rust" fn __awkernel_bsp_set_cpu_freq(freq: u64) -> $crate::dvfs::Result<()> {
            <$ty as $crate::dvfs::Dvfs>::set_cpu_freq(freq)
        }

        #[export_name = "__awkernel_set_global_freq"]
        unsafe extern "Rust" fn __awkernel_bsp_set_global_freq(
            freq: u64,
        ) -> $crate::dvfs::Result<()> {
            unsafe { <$ty as $crate::dvfs::Dvfs>::set_global_freq(freq) }
        }

        #[export_name = "__awkernel_get_max_cpu_freq"]
        extern "Rust" fn __awkernel_bsp_get_max_cpu_freq() -> $crate::dvfs::Result<u64> {
            <$ty as $crate::dvfs::Dvfs>::get_max_cpu_freq()
        }

        #[export_name = "__awkernel_get_min_cpu_freq"]
        extern "Rust" fn __awkernel_bsp_get_min_cpu_freq() -> $crate::dvfs::Result<u64> {
            <$ty as $crate::dvfs::Dvfs>::get_min_cpu_freq()
        }

        #[export_name = "__awkernel_get_curr_cpu_freq"]
        extern "Rust" fn __awkernel_bsp_get_curr_cpu_freq() -> $crate::dvfs::Result<u64> {
            <$ty as $crate::dvfs::Dvfs>::get_curr_cpu_freq()
        }
    };
}
