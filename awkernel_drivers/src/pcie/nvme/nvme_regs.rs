use awkernel_lib::dma_pool::DMAPool;

pub const NVME_CAP: usize = 0x0000; /* Controller Capabilities */
pub const NVME_CAP_MPSMAX: fn(u64) -> u32 = |r| 12 + (((r >> 52) & 0xf) as u32); /* shift */
pub const NVME_CAP_MPSMIN: fn(u64) -> u32 = |r| 12 + (((r >> 48) & 0xf) as u32); /* shift */
pub const NVME_CAP_DSTRD: fn(u64) -> u32 = |r| 1 << (2 + ((r >> 32) & 0xf)); /* bytes */
pub const NVME_CAP_TO: fn(u64) -> u32 = |r| 500 * ((r >> 24) & 0xff) as u32; /* ms */

pub const NVME_VS: usize = 0x0008; /* Version */

#[allow(dead_code)]
pub const NVME_INTMS: usize = 0x000c; /* Interrupt Mask Set */
pub const NVME_INTMC: usize = 0x0010; /* Interrupt Mask Clear */

pub const NVME_CC: usize = 0x0014; /* Controller Configuration */
pub const NVME_CC_IOCQES: fn(u32) -> u32 = |_v| (((_v) & 0xf) << 20);
pub const NVME_CC_IOCQES_MASK: u32 = 0xf << 20;
pub const NVME_CC_IOSQES: fn(u32) -> u32 = |_v| (((_v) & 0xf) << 16);
pub const NVME_CC_IOSQES_MASK: u32 = 0xf << 16;
pub const NVME_CC_SHN: fn(u32) -> u32 = |_v| (((_v) & 0x3) << 14);
pub const NVME_CC_SHN_MASK: u32 = 0x3 << 14;
pub const NVME_CC_SHN_NONE: u32 = 0;
pub const NVME_CC_AMS: fn(u32) -> u32 = |_v| (((_v) & 0x7) << 11);
pub const NVME_CC_AMS_MASK: u32 = 0x7 << 11;
pub const NVME_CC_AMS_RR: u32 = 0; /* round-robin */
pub const NVME_CC_MPS: fn(u32) -> u32 = |_v| ((((_v) - 12) & 0xf) << 7);
pub const NVME_CC_MPS_MASK: u32 = 0xf << 7;
pub const NVME_CC_CSS: fn(u32) -> u32 = |_v| (((_v) & 0x7) << 4);
pub const NVME_CC_CSS_MASK: u32 = 0x7 << 4;
pub const NVME_CC_CSS_NVM: u32 = 0;
pub const NVME_CC_EN: u32 = 1 << 0;

pub const NVME_CSTS: usize = 0x001c; /* Controller Status */
pub const NVME_CSTS_CFS: u32 = 1 << 1;
pub const NVME_CSTS_RDY: u32 = 1 << 0;

pub const NVME_AQA: usize = 0x0024; /* Admin Queue Attributes */
/* Admin Completion Queue Size */
pub const NVME_AQA_ACQS: fn(u32) -> u32 = |_v| (((_v) - 1) << 16);
/* Admin Submission Queue Size */
pub const NVME_AQA_ASQS: fn(u32) -> u32 = |_v| (_v) - 1;
pub const NVME_ASQ: usize = 0x0028; /* Admin Submission Queue Base Address */
pub const NVME_ACQ: usize = 0x0030; /* Admin Completion Queue Base Address */

pub const NVME_ADMIN_Q: u16 = 0;
/* Submission Queue Tail Doorbell */
pub const NVME_SQTDBL: fn(u16, u32) -> u32 = |q, s| 0x1000 + (2 * (q as u32)) * s;
/* Completion Queue Head Doorbell */
pub const NVME_CQHDBL: fn(u16, u32) -> u32 = |q, s| 0x1000 + (2 * (q as u32) + 1) * s;

pub const NVME_CQE_PHASE: u16 = 1 << 0;
#[allow(dead_code)]
pub const NVME_CQE_SC_SUCCESS: u16 = 0x00 << 1;

pub const NVM_SQE_Q_PC: u8 = 1 << 0; /* Physically Contiguous */
pub const NVM_SQE_CQ_IEN: u8 = 1 << 1; /* Interrupts Enabled */

pub const NVM_ADMIN_ADD_IOSQ: u8 = 0x01; /* Create I/O Submission Queue */
pub const NVM_ADMIN_ADD_IOCQ: u8 = 0x05; /* Create I/O Completion Queue */
pub const NVM_ADMIN_IDENTIFY: u8 = 0x06; /* Identify */

pub const NVME_TIMO_QOP: u32 = 5000; /* 5 seconds */

/* Power State Descriptor Data */
#[repr(C, packed)]
#[derive(Debug, Clone, Copy)]
pub struct IdentifyPsd {
    pub mp: u16, /* Max Power */
    pub flags: u16,
    pub enlat: u16, /* Entry Latency */

    pub exlat: u32, /* Exit Latency */

    pub rrt: u8, /* Relative Read Throughput */
    pub rrl: u8, /* Relative Read Latency */
    pub rwt: u8, /* Relative Write Throughput */
    pub rwl: u8, /* Relative Write Latency */

    pub reserved: [u8; 16],
}

#[repr(C, packed)]
#[derive(Debug, Clone, Copy)]
pub struct NamespaceFormat {
    pub ms: u16,   /* Metadata Size */
    pub lbads: u8, /* LBA Data Size */
    pub rp: u8,    /* Relative Performance */
}

#[repr(C, packed)]
#[derive(Debug, Clone, Copy)]
pub struct IdentifyNamespace {
    pub nsze: u64,  /* Namespace Size */
    pub ncap: u64,  /* Namespace Capacity */
    pub nuse: u64,  /* Namespace Utilization */
    pub nsfeat: u8, /* Namespace Features */
    pub nlbaf: u8,  /* Number of LBA Formats */
    pub flbas: u8,  /* Formatted LBA Size */
    pub mc: u8,     /* Metadata Capabilities */
    pub dpc: u8,    /* End-to-end Data Protection Capabilities */
    pub dps: u8,    /* End-to-end Data Protection Type Settings */
    pub _reserved1: [u8; 74],
    pub nguid: [u8; 16],
    pub eui64: [u8; 8],              /* BIG-endian */
    pub lbaf: [NamespaceFormat; 16], /* LBA Format Support */
    pub _reserved2: [u8; 192],
    pub vs: [u8; 3712], /* Vendor Specific */
}

pub const NVME_ID_NS_NSFEAT_THIN_PROV: u8 = 1 << 0;

#[repr(C, packed)]
#[derive(Debug, Clone, Copy)]
pub struct IdentifyController {
    /* Controller Capabilities and Features */
    pub vid: u16,      /* PCI Vendor ID */
    pub ssvid: u16,    /* PCI Subsystem Vendor ID */
    pub sn: [u8; 20],  /* Serial Number */
    pub mn: [u8; 40],  /* Model Number */
    pub fr: [u8; 8],   /* Firmware Revision */
    pub rab: u8,       /* Recommended Arbitration Burst */
    pub ieee: [u8; 3], /* IEEE OUI Identifier */
    pub cmic: u8,      /* Controller Multi-Path I/O and Namespace Sharing Capabilities */
    pub mdts: u8,      /* Maximum Data Transfer Size */
    pub cntlid: u16,   /* Controller ID */
    pub _reserved1: [u8; 16],
    pub ctratt: u32,
    pub _reserved9: [u8; 156],
    pub oacs: u16, /* Optional Admin Command Support */
    pub acl: u8,   /* Abort Command Limit */
    pub aerl: u8,  /* Asynchronous Event Request Limit */
    pub frmw: u8,  /* Firmware Updates */
    pub lpa: u8,   /* Log Page Attributes */
    pub elpe: u8,  /* Error Log Page Entries */
    pub npss: u8,  /* Number of Power States Supported */
    pub avscc: u8, /* Admin Vendor Specific Command Config */
    pub apsta: u8, /* Autonomous Power State Transition Attributes */
    pub _reserved2: [u8; 62],
    pub sanicap: u32,
    pub _reserved10: [u8; 180],
    pub sqes: u8, /* Submission Queue Entry Size */
    pub cqes: u8, /* Completion Queue Entry Size */
    pub _reserved3: [u8; 2],
    pub nn: u32,    /* Number of Namespaces */
    pub oncs: u16,  /* Optional NVM Command Support */
    pub fuses: u16, /* Fused Operation Support */
    pub fna: u8,    /* Format NVM Attributes */
    pub vwc: u8,    /* Volatile Write Cache */
    pub awun: u16,  /* Atomic Write Unit Normal */
    pub awupf: u16, /* Atomic Write Unit Power Fail */
    pub nvscc: u8,  /* NVM Vendor Specific Command Config */
    pub _reserved4: u8,
    pub acwu: u16, /* Atomic Compare & Write Unit */
    pub _reserved5: [u8; 2],
    pub sgls: u32, /* SGL Support */
    pub _reserved6: [u8; 164],
    pub _reserved7: [u8; 1344],
    pub psd: [IdentifyPsd; 32], /* Power State Descriptors */
    pub vs: [u8; 1024],         /* Vendor Specific */
}

#[repr(C, packed)]
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
            let prp = self.prp;
            write!(f, "PRP: [{:#x}, {:#x}]", prp[0], prp[1])
        }
    }
}

/* Formatted LBA Size helpers */
#[allow(dead_code)]
pub fn nvme_id_ns_flbas(flbas: u8) -> u8 {
    flbas & 0x0f
}

#[allow(dead_code)]
pub const NVME_ID_NS_FLBAS_MD: u8 = 0x10;

// I/O Command Opcodes (from OpenBSD's nvmereg.h)
pub const NVM_CMD_FLUSH: u8 = 0x00;
pub const NVM_CMD_WRITE: u8 = 0x01;
pub const NVM_CMD_READ: u8 = 0x02;

#[repr(C, packed)]
#[derive(Debug, Clone, Copy)]
pub struct Sge {
    pub _id: u8,
    pub _reserved: [u8; 15],
}

#[repr(C, packed)]
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

#[repr(C, packed)]
#[derive(Debug, Clone, Copy, Default)]
pub struct SubQueueEntryQ {
    pub opcode: u8,
    pub flags: u8,
    pub cid: u16,
    pub _reserved1: [u8; 20],
    pub prp1: u64,
    pub _reserved2: [u8; 8],
    pub qid: u16,
    pub qsize: u16,
    pub qflags: u8,
    pub _reserved3: u8,
    pub cqid: u16,
    pub _reserved4: [u8; 16],
}

pub struct SubQueue {
    pub sub_ring: DMAPool<SubRing>,
    pub _sqtdbl: usize,
    pub _tail: u32,
}

#[repr(C, packed)]
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
    pub com_ring: DMAPool<ComRing>,
    pub _cqhdbl: usize,
    pub _head: u32,
    pub _phase: u16,
}

pub const QUEUE_SIZE: usize = 128;
// Based on OpenBSD's struct nvme_sqe_io (nvmereg.h)
#[repr(C)]
#[derive(Debug, Clone, Copy, Default)]
pub struct SubQueueEntryIo {
    pub opcode: u8,
    pub flags: u8,
    pub cid: u16,
    pub nsid: u32,
    pub _reserved: [u8; 8],
    pub mptr: u64,
    pub entry: Entry, // PRP entries
    pub slba: u64,    // Starting LBA
    pub nlb: u16,     // Number of Logical Blocks
    pub ioflags: u16,
    pub dsm: u8, // Dataset Management
    pub _reserved2: [u8; 3],
    pub eilbrt: u32, // Expected Initial Logical Block Reference Tag
    pub elbat: u16,  // Expected Logical Block Application Tag
    pub elbatm: u16, // Expected Logical Block Application Tag Mask
}

pub type SubRing = [SubQueueEntry; QUEUE_SIZE];
pub type ComRing = [ComQueueEntry; QUEUE_SIZE];
