pub type Result<T> = core::result::Result<T, DeviceTreeError>;

#[derive(Debug)]
pub enum DeviceTreeError {
    AllocatorInitFailed,
    InvalidMagicNumber,
    NotEnoughLength,
    InvalidToken,
    ParsingFailed,
    MemoryAccessFailed,
    InvalidSemantics,
    NotFound,
}

impl core::fmt::Display for DeviceTreeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl core::error::Error for DeviceTreeError {}
