use awkernel_lib::dma_pool::DMAPool;

pub const NVME_CAP: usize = 0x0000; /* Controller Capabilities */
pub const NVME_CAP_MPSMAX: fn(u64) -> u32 = |r| 12 + (((r >> 52) & 0xf) as u32); /* shift */
pub const NVME_CAP_MPSMIN: fn(u64) -> u32 = |r| 12 + (((r >> 48) & 0xf) as u32); /* shift */
pub const NVME_CAP_DSTRD: fn(u64) -> u32 = |r| 1 << (2 + ((r >> 32) & 0xf)); /* bytes */
pub const NVME_CAP_TO: fn(u64) -> u32 = |r| 500 * ((r >> 24) & 0xff) as u32; /* ms */

pub const NVME_VS: usize = 0x0008; /* Version */

pub const NVME_CC: usize = 0x0014; /* Controller Configuration */
pub const NVME_CC_EN: u32 = 1 << 0;

pub const NVME_CSTS: usize = 0x001c; /* Controller Status */
pub const NVME_CSTS_CFS: u32 = 1 << 1;
pub const NVME_CSTS_RDY: u32 = 1 << 0;

pub const NVME_ADMIN_Q: u16 = 0;
/* Submission Queue Tail Doorbell */
pub const NVME_SQTDBL: fn(u16, u32) -> u32 = |q, s| 0x1000 + (2 * (q as u32)) * s;
/* Completion Queue Head Doorbell */
pub const NVME_CQHDBL: fn(u16, u32) -> u32 = |q, s| 0x1000 + (2 * (q as u32) + 1) * s;

pub const NVME_CQE_PHASE: u16 = 1 << 0;

#[repr(C)]
#[derive(Clone, Copy)]
pub union Entry {
    pub prp: [u64; 2],
    pub sgl: Sge,
}
impl Default for Entry {
    fn default() -> Self {
        Self { prp: [0, 0] }
    }
}

impl core::fmt::Debug for Entry {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        unsafe {
            let Entry { prp } = self;
            write!(f, "PRP: [{:#x}, {:#x}]", prp[0], prp[1])
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Sge {
    pub _id: u8,
    pub _reserved: [u8; 15],
}

#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct SubQueueEntry {
    pub opcode: u8,
    pub flags: u8,
    pub cid: u16,
    pub nsid: u32,
    pub _reserved: [u8; 8],
    pub mptr: u64,
    pub entry: Entry,
    pub cdw10: u32,
    pub cdw11: u32,
    pub cdw12: u32,
    pub cdw13: u32,
    pub cdw14: u32,
    pub cdw15: u32,
}

pub struct SubQueue {
    pub _sub_ring: DMAPool<SubRing>,
    pub _sqtdbl: usize,
    pub _tail: u32,
}
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct ComQueueEntry {
    pub cdw0: u32,
    pub _reserved: u32,
    pub sqhd: u16,
    pub sqid: u16,
    pub cid: u16,
    pub flags: u16,
}

pub struct ComQueue {
    pub _com_ring: DMAPool<ComRing>,
    pub _cqhdbl: usize,
    pub _head: u32,
    pub _phase: u16,
}

pub const QUEUE_SIZE: usize = 128;
pub type SubRing = [SubQueueEntry; QUEUE_SIZE];
pub type ComRing = [ComQueueEntry; QUEUE_SIZE];
