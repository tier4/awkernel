use super::{PCIeDevice, PCIeDeviceErr, PCIeInfo};
use alloc::{format, sync::Arc};
use awkernel_lib::{
    barrier::{bus_space_barrier, BUS_SPACE_BARRIER_READ, BUS_SPACE_BARRIER_WRITE},
    delay::wait_microsec,
    dma_pool::DMAPool,
    paging::PAGESIZE,
    sync::{mutex::Mutex, rwlock::RwLock},
};

mod nvme_regs;
use nvme_regs::*;

const DEVICE_NAME: &str = "NVMe Controller";
const _DEVICE_SHORT_NAME: &str = "nvme";

pub const PAGE_SHIFT: u32 = PAGESIZE.trailing_zeros(); // 2^12 = 4096
pub const MAXPHYS: usize = 64 * 1024; /* max raw I/O transfer size */
// TODO - to be considered.

struct Queue {
    _subq: Mutex<SubQueue>,
    _comq: Mutex<ComQueue>,
    _id: u16,
    _entries: u32,
}

pub(super) fn attach(
    mut info: PCIeInfo,
) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    // Initialize PCIeInfo

    // Map the memory regions of MMIO.
    if let Err(e) = info.map_bar() {
        log::warn!("NVMe: Failed to map the memory regions of MMIO: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }

    // Read capabilities of PCIe.
    info.read_capability();

    let nvme = Nvme::new(info)?;

    Ok(Arc::new(nvme))
}
struct NvmeInner {
    info: PCIeInfo,
    dstrd: u32,
    rdy_to: u32,
    _mps: usize,
    _mdts: usize,
    _max_prpl: usize,
}
impl NvmeInner {
    fn new(info: PCIeInfo) -> Result<Self, NvmeDriverErr> {
        let reg = read_reg(&info, NVME_VS)?;
        if reg == 0xffffffff {
            log::error!("NVMe: Invalid register mapping");
            return Err(NvmeDriverErr::InitFailure);
        }

        let cap =
            read_reg(&info, NVME_CAP)? as u64 | ((read_reg(&info, NVME_CAP + 4)? as u64) << 32);
        let dstrd = NVME_CAP_DSTRD(cap);

        // Check page size compatibility
        let mpsmin = NVME_CAP_MPSMIN(cap);
        let mpsmax = NVME_CAP_MPSMAX(cap);

        if mpsmin > PAGE_SHIFT {
            log::error!(
                "NVMe: minimum page size {} is greater than CPU page size {}",
                1 << mpsmin,
                1 << PAGE_SHIFT
            );
            return Err(NvmeDriverErr::IncompatiblePageSize);
        }

        let mps = if mpsmax < PAGE_SHIFT {
            1 << mpsmax
        } else {
            1 << PAGE_SHIFT
        };

        let rdy_to = NVME_CAP_TO(cap);
        let mdts = MAXPHYS;
        let max_prpl = mdts / mps;

        Ok(Self {
            info,
            dstrd,
            rdy_to,
            _mps: mps,
            _mdts: mdts,
            _max_prpl: max_prpl,
        })
    }

    fn disable(&self) -> Result<(), NvmeDriverErr> {
        let mut cc = read_reg(&self.info, NVME_CC)?;

        if cc & NVME_CC_EN != 0 {
            let csts = read_reg(&self.info, NVME_CSTS)?;
            if csts & NVME_CSTS_CFS == 0 {
                self.ready(NVME_CSTS_RDY)?;
            }
        }

        cc &= !NVME_CC_EN;

        write_reg(&self.info, NVME_CC, cc)?;
        bus_space_barrier(BUS_SPACE_BARRIER_READ | BUS_SPACE_BARRIER_WRITE);

        self.ready(0)
    }

    fn ready(&self, rdy: u32) -> Result<(), NvmeDriverErr> {
        let mut i: u32 = 0;

        while (read_reg(&self.info, NVME_CSTS)? & NVME_CSTS_RDY) != rdy {
            if i > self.rdy_to {
                return Err(NvmeDriverErr::NotReady);
            }
            i += 1;

            wait_microsec(1000);
            bus_space_barrier(BUS_SPACE_BARRIER_READ);
        }

        Ok(())
    }

    fn allocate_queue(&self, id: u16) -> Result<Queue, NvmeDriverErr> {
        let subq_size = core::mem::size_of::<SubRing>();
        let sub_ring_pages = subq_size.div_ceil(PAGESIZE);
        let sub_ring = DMAPool::new(self.info.segment_group as usize, sub_ring_pages)
            .ok_or(NvmeDriverErr::DMAPool)?;
        let sqtdbl = NVME_SQTDBL(id, self.dstrd);

        let subq = SubQueue {
            _sub_ring: sub_ring,
            _sqtdbl: sqtdbl as usize,
            _tail: 0,
        };

        let comq_size = core::mem::size_of::<ComRing>();
        let com_ring_pages = comq_size.div_ceil(PAGESIZE);
        let com_ring = DMAPool::new(self.info.segment_group as usize, com_ring_pages)
            .ok_or(NvmeDriverErr::DMAPool)?;
        let cqhdbl = NVME_CQHDBL(id, self.dstrd);

        let comq = ComQueue {
            _com_ring: com_ring,
            _cqhdbl: cqhdbl as usize,
            _head: 0,
            _phase: NVME_CQE_PHASE,
        };

        let que = Queue {
            _subq: Mutex::new(subq),
            _comq: Mutex::new(comq),
            _id: id,
            _entries: SUB_QUEUE_SIZE as u32,
        };

        Ok(que)
    }
}

struct Nvme {
    inner: RwLock<NvmeInner>,
}
impl Nvme {
    fn new(info: PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        let inner = NvmeInner::new(info)?;

        inner.disable()?;

        let _admin_q = inner.allocate_queue(NVME_ADMIN_Q)?;

        let nvme = Self {
            inner: RwLock::new(inner),
        };

        Ok(nvme)
    }
}

impl PCIeDevice for Nvme {
    fn device_name(&self) -> alloc::borrow::Cow<'static, str> {
        let inner = self.inner.read();
        let bfd = inner.info.get_bfd();
        let name = format!("{bfd}:{DEVICE_NAME}");
        name.into()
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NvmeDriverErr {
    InitFailure,
    NoBar0,
    ReadFailure,
    DMAPool,
    NotReady,
    NotImplemented,
    NoAdminQueue,
    CommandTimeout,
    CommandFailed,
    NoCcb,
    IncompatiblePageSize,
}

impl From<NvmeDriverErr> for PCIeDeviceErr {
    fn from(value: NvmeDriverErr) -> Self {
        log::error!("nvme: {value:?}");
        match value {
            NvmeDriverErr::InitFailure => PCIeDeviceErr::InitFailure,
            NvmeDriverErr::NoBar0 => PCIeDeviceErr::InitFailure,
            NvmeDriverErr::ReadFailure => PCIeDeviceErr::ReadFailure,
            NvmeDriverErr::NotReady => PCIeDeviceErr::InitFailure,
            NvmeDriverErr::DMAPool => PCIeDeviceErr::InitFailure,
            NvmeDriverErr::NotImplemented => PCIeDeviceErr::NotImplemented,
            NvmeDriverErr::NoAdminQueue => PCIeDeviceErr::InitFailure,
            NvmeDriverErr::CommandTimeout => PCIeDeviceErr::InitFailure,
            NvmeDriverErr::CommandFailed => PCIeDeviceErr::InitFailure,
            NvmeDriverErr::NoCcb => PCIeDeviceErr::InitFailure,
            NvmeDriverErr::IncompatiblePageSize => PCIeDeviceErr::InitFailure,
        }
    }
}

#[inline(always)]
pub fn write_reg(info: &PCIeInfo, offset: usize, value: u32) -> Result<(), NvmeDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(NvmeDriverErr::NoBar0)?;
    bar0.write32(offset, value);
    Ok(())
}

#[inline(always)]
pub fn write_reg_array(
    info: &PCIeInfo,
    offset: usize,
    index: usize,
    value: u32,
) -> Result<(), NvmeDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(NvmeDriverErr::NoBar0)?;
    bar0.write32(offset + (index << 2), value);
    Ok(())
}
#[inline(always)]
pub fn read_reg(info: &PCIeInfo, offset: usize) -> Result<u32, NvmeDriverErr> {
    let bar0 = info.get_bar(0).ok_or(NvmeDriverErr::NoBar0)?;
    bar0.read32(offset).ok_or(NvmeDriverErr::ReadFailure)
}

#[inline(always)]
pub fn read_reg_array(info: &PCIeInfo, offset: usize, index: usize) -> Result<u32, NvmeDriverErr> {
    let bar0 = info.get_bar(0).ok_or(NvmeDriverErr::NoBar0)?;
    bar0.read32(offset + (index << 2))
        .ok_or(NvmeDriverErr::ReadFailure)
}
