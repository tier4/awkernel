use crate::pcie::{capability::virtio::VirtioCap, virtio::VirtioDriverErr, BaseAddress, PCIeInfo};

// struct virtio_blk_config {
//     le64 capacity;    // offset 0x00  — number of 512-byte sectors
//     le32 size_max;    // offset 0x08  — max segment size
//     le32 seg_max;     // offset 0x0C  — max number of segments
//     struct { le16 cylinders; u8 heads; u8 sectors; } geometry;  // 0x10
//     le32 blk_size;    // offset 0x14  — preferred I/O block size
//     ...
// };

const VIRTIO_BLK_CONFIG_CAPACITY: usize = 0x00;
const VIRTIO_BLK_CONFIG_BLK_SIZE: usize = 0x14;

pub struct VirtioBlkConfig {
    bar: BaseAddress,
    offset: usize,
}

impl Default for VirtioBlkConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl VirtioBlkConfig {
    pub fn new() -> Self {
        Self {
            bar: BaseAddress::None,
            offset: 0,
        }
    }

    pub fn init(&mut self, info: &PCIeInfo, cap: VirtioCap) -> Result<(), VirtioDriverErr> {
        self.bar = info
            .get_bar(cap.get_bar() as usize)
            .ok_or(VirtioDriverErr::NoBar)?;
        self.offset = cap.get_offset() as usize;
        Ok(())
    }

    /// Read the device capacity in 512-byte sectors.
    pub fn capacity(&self) -> Result<u64, VirtioDriverErr> {
        let lo = self
            .bar
            .read32(self.offset + VIRTIO_BLK_CONFIG_CAPACITY)
            .ok_or(VirtioDriverErr::ReadFailure)? as u64;
        let hi = self
            .bar
            .read32(self.offset + VIRTIO_BLK_CONFIG_CAPACITY + 4)
            .ok_or(VirtioDriverErr::ReadFailure)? as u64;
        Ok((hi << 32) | lo)
    }

    /// Read the preferred block size reported by the device.
    /// Falls back to 512 if the device does not expose it.
    pub fn blk_size(&self) -> u32 {
        self.bar
            .read32(self.offset + VIRTIO_BLK_CONFIG_BLK_SIZE)
            .unwrap_or(512)
    }
}
