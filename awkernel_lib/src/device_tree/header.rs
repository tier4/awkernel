use crate::device_tree::error::{DeviceTreeError, Result};
use crate::device_tree::utils::read_aligned_be_u32;

#[derive(Debug)]
pub(super) struct DeviceTreeHeader {
    pub magic: u32,
    pub total_size: u32,
    pub off_dt_struct: u32,
    pub off_dt_strings: u32,
    pub off_mem_reserved: u32,
    pub version: u32,
    pub last_comp_version: u32,
    pub boot_cpu_id: u32,
    pub size_dt_strings: u32,
    pub size_dt_struct: u32,
}

impl DeviceTreeHeader {
    pub(super) fn from_bytes(data: &[u8]) -> Result<DeviceTreeHeader> {
        if data.len() < 10 {
            Err(DeviceTreeError::NotEnoughLength)
        } else {
            Ok(Self {
                magic: read_aligned_be_u32(data, 0)?,
                total_size: read_aligned_be_u32(data, 1)?,
                off_dt_struct: read_aligned_be_u32(data, 2)?,
                off_dt_strings: read_aligned_be_u32(data, 3)?,
                off_mem_reserved: read_aligned_be_u32(data, 4)?,
                version: read_aligned_be_u32(data, 5)?,
                last_comp_version: read_aligned_be_u32(data, 6)?,
                boot_cpu_id: read_aligned_be_u32(data, 7)?,
                size_dt_strings: read_aligned_be_u32(data, 8)?,
                size_dt_struct: read_aligned_be_u32(data, 9)?,
            })
        }
    }
}
