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
}
