pub const NVME_CAP: usize = 0x0000; /* Controller Capabilities */
pub const NVME_CAP_MPSMAX: fn(u64) -> u32 = |r| 12 + (((r >> 52) & 0xf) as u32); /* shift */
pub const NVME_CAP_MPSMIN: fn(u64) -> u32 = |r| 12 + (((r >> 48) & 0xf) as u32); /* shift */
pub const NVME_CAP_DSTRD: fn(u64) -> u32 = |r| 1 << (2 + ((r >> 32) & 0xf)); /* bytes */
pub const NVME_CAP_TO: fn(u64) -> u32 = |r| 500 * ((r >> 24) & 0xff) as u32; /* ms */

pub const NVME_VS: usize = 0x0008; /* Version */
