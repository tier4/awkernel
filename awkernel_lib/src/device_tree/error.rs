pub type Result<T> = core::result::Result<T, DeviceTreeError>;

#[derive(Debug)]
pub enum DeviceTreeError {
    InvalidMagicNumber,
    NotEnoughLength,
    InvalidToken,
    ParsingFailed,
    MemoryAccessFailed,
    InvalidSemantics,
}
