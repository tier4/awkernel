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
