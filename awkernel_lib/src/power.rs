//! /// Error type for power operations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    NotImplemented,
    NotSupported,
    InternalError,
    Other,
}

impl Error {
    /// Returns a string slice describing the error.
    pub const fn description(&self) -> &'static str {
        match self {
            Error::NotImplemented => "Not implemented",
            Error::NotSupported => "Not supported",
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

pub trait Power {
    /// Reboot the board.
    fn reboot() -> Result<!> {
        Err(Error::NotImplemented)
    }

    /// Shut the board down.
    fn shutdown() -> Result<!> {
        Err(Error::NotImplemented)
    }
}

extern "Rust" {
    fn __awkernel_reboot() -> Result<!>;
    fn __awkernel_shutdown() -> Result<!>;
}

/// Reboot the board.
pub fn reboot() -> Result<!> {
    unsafe { __awkernel_reboot() }
}

/// Shut the board down.
pub fn shutdown() -> Result<!> {
    unsafe { __awkernel_shutdown() }
}

#[linkage = "weak"]
#[export_name = "__awkernel_reboot"]
extern "Rust" fn default_reboot() -> Result<!> {
    crate::arch::ArchImpl::reboot()
}

#[linkage = "weak"]
#[export_name = "__awkernel_shutdown"]
extern "Rust" fn default_shutdown() -> Result<!> {
    crate::arch::ArchImpl::shutdown()
}

/// Overrides the weak default power functions with the [`Power`] implementation of `$ty`.
///
/// `$ty` must implement [`Power`]. Invoke it once, in a crate linked into the final binary.
#[macro_export]
macro_rules! impl_power {
    ($ty:ty) => {
        #[export_name = "__awkernel_reboot"]
        extern "Rust" fn __awkernel_bsp_reboot() -> $crate::power::Result<!> {
            <$ty as $crate::power::Power>::reboot()
        }

        #[export_name = "__awkernel_shutdown"]
        extern "Rust" fn __awkernel_bsp_shutdown() -> $crate::power::Result<!> {
            <$ty as $crate::power::Power>::shutdown()
        }
    };
}
