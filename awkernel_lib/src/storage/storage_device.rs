use alloc::{borrow::Cow, vec::Vec};

#[derive(Debug, Clone, Copy)]
pub enum StorageDeviceType {
    NVMe,
    SATA,
    USB,
    VirtIO,
    Memory,
}

#[derive(Debug)]
pub enum StorageDevError {
    IoError,
    InvalidCommand,
    DeviceNotReady,
    InvalidBlock,
    BufferTooSmall,
    NotSupported,
}

impl core::fmt::Display for StorageDevError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{self:?}")
    }
}

impl core::error::Error for StorageDevError {}

pub trait StorageDevice: Send + Sync {
    fn device_id(&self) -> u64;

    fn device_name(&self) -> Cow<'static, str>;

    fn device_short_name(&self) -> Cow<'static, str>;

    fn device_type(&self) -> StorageDeviceType;

    fn irqs(&self) -> Vec<u16>;

    fn interrupt(&self, irq: u16) -> Result<(), StorageDevError>;

    fn block_size(&self) -> usize;

    fn num_blocks(&self) -> u64;

    fn read_blocks(&self, buf: &mut [u8], transfer_id: u16) -> Result<(), StorageDevError>;

    fn write_blocks(&self, buf: &[u8], transfer_id: u16) -> Result<(), StorageDevError>;

    fn flush(&self, _transfer_id: u16) -> Result<(), StorageDevError> {
        Ok(())
    }

    fn get_namespace_id(&self) -> Option<u32> {
        None
    }
}
