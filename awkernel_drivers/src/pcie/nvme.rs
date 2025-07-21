use super::{PCIeDevice, PCIeDeviceErr, PCIeInfo};
use alloc::{collections::VecDeque, format, sync::Arc, vec::Vec};
use awkernel_lib::{
    addr::Addr,
    barrier::{bus_space_barrier, BUS_SPACE_BARRIER_READ, BUS_SPACE_BARRIER_WRITE},
    delay::wait_microsec,
    dma_pool::DMAPool,
    paging::PAGESIZE,
    sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock},
};

mod nvme_regs;
use nvme_regs::*;

const DEVICE_NAME: &str = "NVMe Controller";
const _DEVICE_SHORT_NAME: &str = "nvme";

pub const PAGE_SHIFT: u32 = PAGESIZE.trailing_zeros(); // 2^12 = 4096
pub const MAXPHYS: usize = 64 * 1024; /* max raw I/O transfer size - to be considered.TODO.*/

#[derive(Debug, Clone, Copy, Default)]
struct PollState {
    _sqe: SubQueueEntry,
    _cqe: ComQueueEntry,
}

enum CcbCookie {
    _Controller(DMAPool<IdentifyController>),
    _State(PollState),
}

struct Ccb {
    //_dmamap - TODO - this is not used for IdenifyController, so it is removed for now.

    // The following two fields are the replacement for OpenBSD's `cookie`.
    _cookie: Option<CcbCookie>,

    _done: Option<fn(&mut NvmeInner, &Ccb, &ComQueueEntry)>,
    _prpl_off: usize,
    _prpl_dva: u64,
    _prpl: Option<usize>,
    _id: u16,
}

struct CcbList {
    _free_list: VecDeque<u16>,
}

struct Queue {
    subq: Mutex<SubQueue>,
    comq: Mutex<ComQueue>,
    _id: u16,
    entries: u32,
}

impl Queue {
    fn submit(&self, info: &PCIeInfo, ccb: &Ccb) -> Result<(), NvmeDriverErr> {
        let mut node = MCSNode::new();
        let mut subq = self.subq.lock(&mut node);
        let mut tail = subq._tail;

        let sqe = &mut subq.sub_ring.as_mut()[tail as usize];
        *sqe = SubQueueEntry::default();

        if let Some(CcbCookie::_State(state)) = &ccb._cookie {
            *sqe = state._sqe;
        } else {
            return Err(NvmeDriverErr::CommandFailed);
        }
        sqe.cid = ccb._id;

        tail += 1;
        if tail >= self.entries {
            tail = 0;
        }
        subq._tail = tail;
        write_reg(info, subq._sqtdbl, subq._tail)?;

        Ok(())
    }
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
    mps: usize,
    _mdts: usize,
    _max_prpl: usize,
    ccb_list: Option<Mutex<CcbList>>,
    _ccbs: Option<Vec<Ccb>>,
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
            mps,
            _mdts: mdts,
            _max_prpl: max_prpl,
            ccb_list: None,
            _ccbs: None,
        })
    }

    fn enable(&self, admin_q: &Queue) -> Result<(), NvmeDriverErr> {
        let mut cc = read_reg(&self.info, NVME_CC)?;
        if cc & NVME_CC_EN != 0 {
            return self.ready(NVME_CSTS_RDY);
        }

        write_reg(
            &self.info,
            NVME_AQA,
            NVME_AQA_ACQS(admin_q.entries) | NVME_AQA_ASQS(admin_q.entries),
        )?;
        bus_space_barrier(BUS_SPACE_BARRIER_WRITE);

        let subq_phy_addr = {
            let mut node = MCSNode::new();
            let subq = admin_q.subq.lock(&mut node);
            subq.sub_ring.get_phy_addr().as_usize()
        };
        write_reg(&self.info, NVME_ASQ, (subq_phy_addr & 0xFFFFFFFF) as u32)?;
        write_reg(&self.info, NVME_ASQ + 4, (subq_phy_addr >> 32) as u32)?;
        bus_space_barrier(BUS_SPACE_BARRIER_WRITE);

        let comq_phy_addr = {
            let mut node = MCSNode::new();
            let comq = admin_q.comq.lock(&mut node);
            comq.com_ring.get_phy_addr().as_usize()
        };
        write_reg(&self.info, NVME_ACQ, (comq_phy_addr & 0xFFFFFFFF) as u32)?;
        write_reg(&self.info, NVME_ACQ + 4, (comq_phy_addr >> 32) as u32)?;
        bus_space_barrier(BUS_SPACE_BARRIER_WRITE);

        cc &= !(NVME_CC_IOCQES_MASK
            | NVME_CC_IOSQES_MASK
            | NVME_CC_SHN_MASK
            | NVME_CC_AMS_MASK
            | NVME_CC_MPS_MASK
            | NVME_CC_CSS_MASK);
        cc |= NVME_CC_IOSQES(6); /* Submission queue entry size == 2**6 (64) */
        cc |= NVME_CC_IOCQES(4); /* Completion queue entry size == 2**4 (16) */
        cc |= NVME_CC_SHN(NVME_CC_SHN_NONE);
        cc |= NVME_CC_CSS(NVME_CC_CSS_NVM);
        cc |= NVME_CC_AMS(NVME_CC_AMS_RR);
        cc |= NVME_CC_MPS(self.mps.trailing_zeros());
        cc |= NVME_CC_EN;

        write_reg(&self.info, NVME_CC, cc)?;
        bus_space_barrier(BUS_SPACE_BARRIER_READ | BUS_SPACE_BARRIER_WRITE);

        self.ready(NVME_CSTS_RDY)
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

    fn allocate_queue(&self, id: u16, entries: u32, dstrd: u32) -> Result<Queue, NvmeDriverErr> {
        let subq_size = core::mem::size_of::<SubRing>();
        let sub_ring_pages = subq_size.div_ceil(PAGESIZE);
        let sub_ring = DMAPool::new(self.info.segment_group as usize, sub_ring_pages)
            .ok_or(NvmeDriverErr::DMAPool)?;
        let sqtdbl = NVME_SQTDBL(id, dstrd);

        let subq = SubQueue {
            sub_ring,
            _sqtdbl: sqtdbl as usize,
            _tail: 0,
        };

        let comq_size = core::mem::size_of::<ComRing>();
        let com_ring_pages = comq_size.div_ceil(PAGESIZE);
        let com_ring = DMAPool::new(self.info.segment_group as usize, com_ring_pages)
            .ok_or(NvmeDriverErr::DMAPool)?;
        let cqhdbl = NVME_CQHDBL(id, dstrd);

        let comq = ComQueue {
            com_ring,
            _cqhdbl: cqhdbl as usize,
            _head: 0,
            _phase: NVME_CQE_PHASE,
        };

        let que = Queue {
            subq: Mutex::new(subq),
            comq: Mutex::new(comq),
            _id: id,
            entries,
        };

        Ok(que)
    }

    fn ccbs_alloc(&mut self, nccbs: u16) -> Result<(), NvmeDriverErr> {
        let mut ccbs = Vec::with_capacity(nccbs as usize);
        let mut free_list = VecDeque::with_capacity(nccbs as usize);

        // TODO - Since we won't use prpl* fields for identify controller command,
        // we can set prpl to None. We will implement prpl later when we support
        // commands that require PRPL.

        for i in 0..nccbs {
            let ccb = Ccb {
                _cookie: None,
                _done: None,
                _prpl_off: 0,
                _prpl_dva: 0,
                _prpl: None,
                _id: i,
            };
            ccbs.push(ccb);
            free_list.push_back(i);
        }

        self._ccbs = Some(ccbs);
        self.ccb_list = Some(Mutex::new(CcbList {
            _free_list: free_list,
        }));

        Ok(())
    }

    fn _ccb_get(&self) -> Result<Option<u16>, NvmeDriverErr> {
        let mut node = MCSNode::new();
        let ccb_list = self.ccb_list.as_ref().ok_or(NvmeDriverErr::InitFailure)?;
        let mut list = ccb_list.lock(&mut node);
        Ok(list._free_list.pop_front())
    }

    fn _ccb_put(&self, ccb_id: u16, sc_ccbs: &mut [Ccb]) -> Result<(), NvmeDriverErr> {
        let ccb = &mut sc_ccbs[ccb_id as usize];
        ccb._done = None;

        let mut node = MCSNode::new();
        let ccb_list = self.ccb_list.as_ref().ok_or(NvmeDriverErr::InitFailure)?;
        let mut list = ccb_list.lock(&mut node);
        list._free_list.push_front(ccb_id);

        Ok(())
    }
}

struct Nvme {
    // The order of lock acquisition must be as follows:
    //
    // 1. `NvmeInner`'s lock
    // 2. `Queue`'s lock
    // 3. `Queue`'s unlock
    // 4. `NvmeInner`'s unlock
    //
    // Otherwise, a deadlock will occur.
    _admin_q: Queue,
    inner: RwLock<NvmeInner>,
}
impl Nvme {
    fn new(info: PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        let mut inner = NvmeInner::new(info)?;

        inner.disable()?;

        let admin_q = inner.allocate_queue(NVME_ADMIN_Q, QUEUE_SIZE as u32, inner.dstrd)?;

        inner.ccbs_alloc(QUEUE_SIZE as u16)?;

        inner.enable(&admin_q)?;

        let nvme = Self {
            _admin_q: admin_q,
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
