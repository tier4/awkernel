use super::{registers, PCIeDevice, PCIeDeviceErr, PCIeInfo};
use alloc::{borrow::Cow, boxed::Box, collections::VecDeque, format, sync::Arc, vec, vec::Vec};
use awkernel_lib::{
    addr::Addr,
    barrier::{
        bus_space_barrier, membar_consumer, membar_producer, BUS_SPACE_BARRIER_READ,
        BUS_SPACE_BARRIER_WRITE,
    },
    delay::wait_microsec,
    dma_map::{DmaMap, DmaSyncOp, DmaTag},
    dma_pool::DMAPool,
    file::block_device::{BlockDeviceError, BlockResult},
    interrupt::IRQ,
    paging::PAGESIZE,
    storage::{self, StorageDevError, StorageDevice, StorageDeviceType},
    sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock},
};
use core::any::Any;

mod nvme_regs;
use nvme_regs::*;

// Helper function for returning CCBs to the pool
fn ccb_put_free(
    ccbs: &mut [Ccb],
    ccb_list: &Mutex<CcbList>,
    ccb_id: u16,
) -> Result<(), NvmeDriverErr> {
    let ccb = &mut ccbs[ccb_id as usize];

    ccb.transfer_id = None;
    ccb.done = None;

    let mut node = MCSNode::new();
    let mut list = ccb_list.lock(&mut node);
    list._free_list.push_front(ccb_id);

    Ok(())
}

const DEVICE_NAME: &str = " NVMe Controller";
const DEVICE_SHORT_NAME: &str = "nvme";

pub const PAGE_SHIFT: u32 = PAGESIZE.trailing_zeros(); // 2^12 = 4096
pub const MAXPHYS: usize = 64 * 1024; /* max raw I/O transfer size. TODO - to be considered. */
pub const NVME_TIMO_IDENT: u32 = 10000; /* ms to probe/identify */
pub const NVME_TIMO_DELAYNS: u64 = 10; /* ns to wait in poll loop */

// Queue entry size constants
const NVME_SQ_ENTRY_SIZE_SHIFT: u32 = 6; // Submission queue entry size == 2^6 (64 bytes)
const NVME_CQ_ENTRY_SIZE_SHIFT: u32 = 4; // Completion queue entry size == 2^4 (16 bytes)

// Default values for block devices
const DEFAULT_BLOCK_SIZE: usize = 512;
const DEFAULT_IO_TIMEOUT_MS: u32 = 5000; // 5 seconds

pub static NVME_DEVICE: RwLock<Option<Arc<Nvme>>> = RwLock::new(None); // TODO - this will be removed in the future, after the interrupt handller task for storage device is implemented.

// State for polling operations
struct PollState {
    _sqe: SubQueueEntry,
    _cqe: ComQueueEntry,
}

enum CcbCookie {
    Io {
        lba: u64,
        blocks: u32,
        nsid: u32,
        read: bool,
    },
    Flush {
        nsid: u32,
    },
    _State(PollState),
    _Controller(u64), // Physical address for controller identify
    _QueueCmd(SubQueueEntryQ), // Queue command
}

struct Ccb {
    transfer_id: Option<u16>, // Reference to StorageTransfer
    cookie: Option<CcbCookie>,
    done: Option<fn(u16, &ComQueueEntry, &mut [Ccb], &Mutex<CcbList>)>,
    _prpl_off: usize,
    _prpl_dva: u64,
    _prpl: Option<usize>,
    _id: u16,
    dmamap: Option<DmaMap>,    // DMA map for I/O data
    dma_loaded: bool,           // Track if map is loaded
}

struct CcbList {
    _free_list: VecDeque<u16>,
}

struct Queue {
    _id: u16, // Queue ID
    subq: Mutex<SubQueue>,
    comq: Mutex<ComQueue>,
    entries: u32,
}

impl Queue {
    fn submit<F>(&self, info: &PCIeInfo, ccb: &Ccb, fill: F) -> Result<(), NvmeDriverErr>
    where
        F: FnOnce(&Ccb, &mut SubQueueEntry),
    {
        let mut node = MCSNode::new();
        let mut subq = self.subq.lock(&mut node);
        let mut tail = subq._tail;

        let sqe = &mut subq.sub_ring.as_mut()[tail as usize];
        *sqe = SubQueueEntry::default();

        fill(ccb, sqe);
        sqe.cid = ccb._id;

        // Ensure all writes to the submission queue entry are complete
        // before updating the tail pointer (like OpenBSD's bus_dmamap_sync)
        membar_producer();

        tail += 1;
        if tail >= self.entries {
            tail = 0;
        }
        subq._tail = tail;

        // Ensure tail update is visible before doorbell write
        membar_producer();
        write_reg(info, subq._sqtdbl, subq._tail)?;

        Ok(())
    }

    fn complete(
        &self,
        info: &PCIeInfo,
        ccbs: &mut [Ccb],
        ccb_list: &Mutex<CcbList>,
    ) -> Result<bool, NvmeDriverErr> {
        let mut node = MCSNode::new();
        let mut comq = if let Some(guard) = self.comq.try_lock(&mut node) {
            guard
        } else {
            return Ok(false);
        };

        let mut head = comq._head;
        let mut rv = false;
        loop {
            let cqe = &comq.com_ring.as_ref()[head as usize];
            let flags = u16::from_le(cqe.flags);

            if (flags & NVME_CQE_PHASE) != comq._phase {
                break;
            }

            membar_consumer();

            let cid = cqe.cid;
            if cid as usize >= ccbs.len() {
                log::error!("Invalid CCB ID: {cid}");
                return Err(NvmeDriverErr::InvalidCcbId);
            }
            let done_fn = ccbs[cid as usize].done;

            if let Some(done_fn) = done_fn {
                done_fn(cid, cqe, ccbs, ccb_list);
            }

            head += 1;
            if head >= self.entries {
                head = 0;
                comq._phase ^= NVME_CQE_PHASE;
            }

            rv = true;
        }

        if rv {
            comq._head = head;
            write_reg(info, comq._cqhdbl, comq._head)?;
        }

        Ok(rv)
    }
}

struct NvmeInner {
    info: PCIeInfo,
    dstrd: u32,
    rdy_to: u32,
    mps: usize,
    _mdts: usize,
    _max_prpl: usize,
    ccb_list: Option<Mutex<CcbList>>,
    ccbs: Option<Vec<Ccb>>,
    ccb_prpls: Option<DMAPool<u64>>,
    nn: u32,
    identify: Option<IdentifyController>,
    namespaces: Vec<Option<IdentifyNamespace>>,
    pcie_int: PCIeInt,
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
            ccbs: None,
            ccb_prpls: None,
            nn: 0,
            identify: None,
            namespaces: Vec::new(),
            pcie_int: PCIeInt::None,
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
        write_reg(&self.info, NVME_ASQ, subq_phy_addr as u32)?;
        write_reg(
            &self.info,
            NVME_ASQ + 4,
            (subq_phy_addr as u64 >> 32) as u32,
        )?;
        bus_space_barrier(BUS_SPACE_BARRIER_WRITE);

        let comq_phy_addr = {
            let mut node = MCSNode::new();
            let comq = admin_q.comq.lock(&mut node);
            comq.com_ring.get_phy_addr().as_usize()
        };
        write_reg(&self.info, NVME_ACQ, comq_phy_addr as u32)?;
        write_reg(
            &self.info,
            NVME_ACQ + 4,
            (comq_phy_addr as u64 >> 32) as u32,
        )?;
        bus_space_barrier(BUS_SPACE_BARRIER_WRITE);

        cc &= !(NVME_CC_IOCQES_MASK
            | NVME_CC_IOSQES_MASK
            | NVME_CC_SHN_MASK
            | NVME_CC_AMS_MASK
            | NVME_CC_MPS_MASK
            | NVME_CC_CSS_MASK);
        cc |= NVME_CC_IOSQES(NVME_SQ_ENTRY_SIZE_SHIFT);
        cc |= NVME_CC_IOCQES(NVME_CQ_ENTRY_SIZE_SHIFT);
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
        let mut sub_ring: DMAPool<[SubQueueEntry; 128]> =
            DMAPool::new(self.info.segment_group as usize, sub_ring_pages)
                .ok_or(NvmeDriverErr::DMAPool)?;
        for i in 0..QUEUE_SIZE {
            sub_ring.as_mut()[i] = SubQueueEntry::default();
        }
        let sqtdbl = NVME_SQTDBL(id, dstrd);

        let subq = SubQueue {
            sub_ring,
            _sqtdbl: sqtdbl as usize,
            _tail: 0,
        };

        let comq_size = core::mem::size_of::<ComRing>();
        let com_ring_pages = comq_size.div_ceil(PAGESIZE);
        let mut com_ring: DMAPool<[ComQueueEntry; 128]> =
            DMAPool::new(self.info.segment_group as usize, com_ring_pages)
                .ok_or(NvmeDriverErr::DMAPool)?;
        for i in 0..QUEUE_SIZE {
            com_ring.as_mut()[i] = ComQueueEntry::default();
        }

        let cqhdbl = NVME_CQHDBL(id, dstrd);

        let comq = ComQueue {
            com_ring,
            _cqhdbl: cqhdbl as usize,
            _head: 0,
            _phase: NVME_CQE_PHASE,
        };

        let que = Queue {
            _id: id,
            subq: Mutex::new(subq),
            comq: Mutex::new(comq),
            entries,
        };

        Ok(que)
    }

    fn ccbs_alloc(&mut self, nccbs: u16) -> Result<(), NvmeDriverErr> {
        let mut ccbs = Vec::with_capacity(nccbs as usize);
        let mut free_list = VecDeque::with_capacity(nccbs as usize);

        let prpl_size = core::mem::size_of::<u64>() * self._max_prpl * nccbs as usize;
        let prpl_pages = prpl_size.div_ceil(PAGESIZE);

        let prpl_dma = DMAPool::<u64>::new(self.info.segment_group as usize, prpl_pages)
            .ok_or(NvmeDriverErr::DMAPool)?;

        let prpl_virt_base = prpl_dma.get_virt_addr().as_usize();
        let prpl_phys_base = prpl_dma.get_phy_addr().as_usize() as u64;

        self.ccb_prpls = Some(prpl_dma);

        let mut off = 0;
        for i in 0..nccbs {
            // Create DMA map for this CCB (for I/O data)
            let tag = DmaTag::new_64bit();
            let dmamap = DmaMap::new(tag, self._mdts).ok();
            
            let ccb = Ccb {
                transfer_id: None,
                cookie: None,
                done: None,
                _prpl_off: off,
                _prpl_dva: prpl_phys_base + off as u64,
                _prpl: Some(prpl_virt_base + off),
                _id: i,
                dmamap,
                dma_loaded: false,
            };
            ccbs.push(ccb);
            free_list.push_back(i);

            off += core::mem::size_of::<u64>() * self._max_prpl;
        }

        self.ccbs = Some(ccbs);
        self.ccb_list = Some(Mutex::new(CcbList {
            _free_list: free_list,
        }));

        Ok(())
    }

    fn ccbs_free(&mut self) {
        // Clean up DMA maps before dropping CCBs
        if let Some(ccbs) = &mut self.ccbs {
            for ccb in ccbs {
                if ccb.dma_loaded {
                    if let Some(ref mut dmamap) = ccb.dmamap {
                        dmamap.unload();
                    }
                }
                // DmaMap will be dropped when ccb is dropped
            }
        }
        
        self.ccb_list = None;
        self.ccbs = None;
        self.ccb_prpls = None;
    }

    fn ccb_get(&self) -> Result<Option<u16>, NvmeDriverErr> {
        let mut node = MCSNode::new();
        let ccb_list = self.ccb_list.as_ref().ok_or(NvmeDriverErr::InitFailure)?;
        let mut list = ccb_list.lock(&mut node);
        Ok(list._free_list.pop_front())
    }

    fn ccb_put(&mut self, ccb_id: u16) -> Result<(), NvmeDriverErr> {
        let ccbs = self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?;
        let ccb = &mut ccbs[ccb_id as usize];
        ccb.transfer_id = None;
        ccb.done = None;

        let mut node = MCSNode::new();
        let ccb_list = self.ccb_list.as_ref().ok_or(NvmeDriverErr::InitFailure)?;
        let mut list = ccb_list.lock(&mut node);
        list._free_list.push_front(ccb_id);

        Ok(())
    }

    fn poll_fill(ccb: &Ccb, sqe: &mut SubQueueEntry) {
        if let Some(CcbCookie::_State(state)) = &ccb.cookie {
            *sqe = state._sqe;
        }
    }

    fn poll_done(ccb_id: u16, cqe: &ComQueueEntry, ccbs: &mut [Ccb], _ccb_list: &Mutex<CcbList>) {
        let ccb = &mut ccbs[ccb_id as usize];
        if let Some(CcbCookie::_State(state)) = &mut ccb.cookie {
            state._cqe = *cqe;
            state._cqe.flags |= NVME_CQE_PHASE.to_le();
        }
    }

    fn poll<F>(&mut self, q: &Queue, ccb_id: u16, fill_fn: F, ms: u32) -> Result<u16, NvmeDriverErr>
    where
        F: FnOnce(&Ccb, &mut SubQueueEntry),
    {
        let mut state = PollState {
            _sqe: SubQueueEntry::default(),
            _cqe: ComQueueEntry::default(),
        };

        {
            let ccbs = self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?;
            let ccb = &mut ccbs[ccb_id as usize];
            fill_fn(ccb, &mut state._sqe);
        }

        let (original_done, original_cookie) = {
            let ccbs = self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?;
            let ccb = &mut ccbs[ccb_id as usize];
            let done = ccb.done;
            let cookie = ccb.cookie.take();

            ccb.done = Some(Self::poll_done);
            ccb.cookie = Some(CcbCookie::_State(state));

            (done, cookie)
        };

        {
            let ccbs = self.ccbs.as_ref().ok_or(NvmeDriverErr::InitFailure)?;
            let ccb = &ccbs[ccb_id as usize];
            q.submit(&self.info, ccb, Self::poll_fill)?;
        }

        let mut us = if ms == 0 { u32::MAX } else { ms * 1000 };
        loop {
            let ccbs = self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?;
            let ccb = &ccbs[ccb_id as usize];
            let phase_set = match &ccb.cookie {
                Some(CcbCookie::_State(state)) => state._cqe.flags & NVME_CQE_PHASE.to_le() != 0,
                _ => return Err(NvmeDriverErr::NoCcb),
            };
            if phase_set {
                break;
            }

            let ccb_list = self.ccb_list.as_ref().ok_or(NvmeDriverErr::InitFailure)?;
            if !q.complete(&self.info, ccbs, ccb_list)? {
                wait_microsec(NVME_TIMO_DELAYNS);
            }

            bus_space_barrier(BUS_SPACE_BARRIER_READ);

            if ms != 0 {
                if us <= NVME_TIMO_DELAYNS as u32 {
                    break;
                }
                us -= NVME_TIMO_DELAYNS as u32;
            }
        }

        let cqe = {
            let ccbs = self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?;
            let ccb = &mut ccbs[ccb_id as usize];
            let cqe = match &ccb.cookie {
                Some(CcbCookie::_State(state)) => state._cqe,
                _ => return Err(NvmeDriverErr::NoCcb),
            };
            ccb.cookie = original_cookie;
            if let Some(done_fn) = original_done {
                let ccb_list = self.ccb_list.as_ref().ok_or(NvmeDriverErr::InitFailure)?;
                done_fn(ccb_id, &cqe, ccbs, ccb_list);
            }
            cqe
        };

        let flags = u16::from_le(cqe.flags);

        Ok(flags & !NVME_CQE_PHASE)
    }

    fn fill_identify(ccb: &Ccb, sqe: &mut SubQueueEntry) {
        sqe.opcode = NVM_ADMIN_IDENTIFY;
        if let Some(CcbCookie::_Controller(phy_addr)) = ccb.cookie.as_ref() {
            unsafe {
                sqe.entry.prp[0] = phy_addr.to_le();
            }
        }
        sqe.cdw10 = 1_u32.to_le();
    }

    fn sqe_fill(ccb: &Ccb, sqe: &mut SubQueueEntry) {
        if let Some(CcbCookie::_QueueCmd(sqe_q)) = &ccb.cookie {
            unsafe {
                let sqe_ptr = sqe as *mut SubQueueEntry as *mut u8;
                let sqe_q_ptr = sqe_q as *const SubQueueEntryQ as *const u8;
                core::ptr::copy_nonoverlapping(
                    sqe_q_ptr,
                    sqe_ptr,
                    core::mem::size_of::<SubQueueEntryQ>(),
                );
            }
        } else if let Some(CcbCookie::_State(state)) = &ccb.cookie {
            *sqe = state._sqe;
        }
    }

    fn create_io_queue(&mut self, admin_q: &Queue, io_q: &Queue) -> Result<(), NvmeDriverErr> {
        let mut sqe = SubQueueEntryQ::default();

        let ccb_id = self.ccb_get()?.ok_or(NvmeDriverErr::NoCcb)?;

        // Create I/O Completion Queue
        sqe.opcode = NVM_ADMIN_ADD_IOCQ;
        sqe.prp1 = {
            let mut node = MCSNode::new();
            let comq = io_q.comq.lock(&mut node);
            comq.com_ring.get_phy_addr().as_usize() as u64
        }
        .to_le();

        sqe.qsize = ((io_q.entries - 1) as u16).to_le();
        sqe.qid = io_q._id.to_le();
        sqe.qflags = NVM_SQE_CQ_IEN | NVM_SQE_Q_PC;
        // ENHANCE: It better to use a separate interrupt vector for I/O queues and not reuse the same ID as the admin queue. However, this is how OpenBSD does it, so we follow that for now.
        {
            let ccbs = self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?;
            let ccb = &mut ccbs[ccb_id as usize];
            ccb.cookie = Some(CcbCookie::_QueueCmd(sqe));
            ccb.done = None;
        }

        let rv = self.poll(admin_q, ccb_id, Self::sqe_fill, NVME_TIMO_QOP)?;

        if rv != 0 {
            self.ccb_put(ccb_id)?;
            log::error!("Create I/O Completion Queue failed with status: 0x{rv:x}");
            return Err(NvmeDriverErr::CommandFailed);
        }

        // Create I/O Submission Queue - reuse the same CCB
        sqe = SubQueueEntryQ::default();
        sqe.opcode = NVM_ADMIN_ADD_IOSQ;
        sqe.prp1 = {
            let mut node = MCSNode::new();
            let subq = io_q.subq.lock(&mut node);
            subq.sub_ring.get_phy_addr().as_usize() as u64
        }
        .to_le();

        sqe.qid = io_q._id.to_le();
        sqe.qsize = ((io_q.entries - 1) as u16).to_le();
        sqe.cqid = io_q._id.to_le();
        sqe.qflags = NVM_SQE_Q_PC;
        {
            let ccbs = self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?;
            let ccb = &mut ccbs[ccb_id as usize];
            ccb.cookie = Some(CcbCookie::_QueueCmd(sqe));
            ccb.done = None;
        }

        let rv = self.poll(admin_q, ccb_id, Self::sqe_fill, NVME_TIMO_QOP)?;

        self.ccb_put(ccb_id)?;

        if rv != 0 {
            log::error!("Create I/O Submission Queue failed with status: 0x{rv:x}");
            return Err(NvmeDriverErr::CommandFailed);
        }

        Ok(())
    }

    fn identify(&mut self, admin_q: &Queue) -> Result<(), NvmeDriverErr> {
        let ccb_id = self.ccb_get()?.ok_or(NvmeDriverErr::NoCcb)?;

        let dma_size = core::mem::size_of::<IdentifyController>();
        let pages = dma_size.div_ceil(PAGESIZE);
        let mem: DMAPool<IdentifyController> =
            DMAPool::new(self.info.segment_group as usize, pages).ok_or(NvmeDriverErr::DMAPool)?;
        let ptr = mem.get_virt_addr().as_ptr::<IdentifyController>();

        {
            let sc_ccbs = self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?;
            let ccb = &mut sc_ccbs[ccb_id as usize];
            ccb.cookie = Some(CcbCookie::_Controller(mem.get_phy_addr().as_usize() as u64));
            ccb.done = None;
        }

        let rv = self.poll(admin_q, ccb_id, Self::fill_identify, NVME_TIMO_IDENT)?;
        self.ccb_put(ccb_id)?;

        if rv != 0 {
            return Err(NvmeDriverErr::CommandFailed);
        }

        let id = unsafe { &*ptr };

        let serial = core::str::from_utf8(&id.sn).unwrap_or("unknown");
        let model = core::str::from_utf8(&id.mn).unwrap_or("unknown");
        let firmware = core::str::from_utf8(&id.fr).unwrap_or("unknown");

        self.nn = u32::from_le(id.nn);

        log::info!(
            "NVMe Controller - Serial: {}, Model: {}, Firmware: {}, Namespaces: {}",
            serial.trim(),
            model.trim(),
            firmware.trim(),
            self.nn
        );

        // At least one Apple NVMe device presents a second, bogus disk that is
        // inaccessible, so cap targets at 1.
        let mn = id.mn;
        if self.nn > 1
            && (mn.len() >= 5
                && mn[0] == b'A'
                && mn[1] == b'P'
                && mn[2] == b'P'
                && mn[3] == b'L'
                && mn[4] == b'E')
        {
            self.nn = 1;
        }

        self.identify = Some(*id);

        Ok(())
    }

    fn namespace_size(ns: &IdentifyNamespace) -> u64 {
        let ncap = u64::from_le(ns.ncap); // Max allowed allocation.
        let nsze = u64::from_le(ns.nsze);

        if (ns.nsfeat & NVME_ID_NS_NSFEAT_THIN_PROV) != 0 && ncap < nsze {
            ncap
        } else {
            nsze
        }
    }

    fn identify_namespace(&mut self, admin_q: &Queue, nsid: u32) -> Result<bool, NvmeDriverErr> {
        let ccb_id = self.ccb_get()?.ok_or(NvmeDriverErr::NoCcb)?;

        let dma_size = core::mem::size_of::<IdentifyNamespace>();
        let pages = dma_size.div_ceil(PAGESIZE);
        let mem: DMAPool<IdentifyNamespace> =
            DMAPool::new(self.info.segment_group as usize, pages).ok_or(NvmeDriverErr::DMAPool)?;

        let mut sqe = SubQueueEntry {
            opcode: NVM_ADMIN_IDENTIFY,
            nsid: nsid.to_le(),
            ..Default::default()
        };
        unsafe {
            sqe.entry.prp[0] = (mem.get_phy_addr().as_usize() as u64).to_le();
        }

        {
            let sc_ccbs = self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?;
            let ccb = &mut sc_ccbs[ccb_id as usize];
            ccb.cookie = Some(CcbCookie::_State(PollState {
                _sqe: sqe,
                _cqe: ComQueueEntry::default(),
            }));
            ccb.done = None;
        }

        let rv = self.poll(admin_q, ccb_id, Self::sqe_fill, NVME_TIMO_IDENT)?;

        self.ccb_put(ccb_id)?;

        if rv != 0 {
            return Ok(false); // Namespace not found.
        }

        let ptr = mem.get_virt_addr().as_ptr::<IdentifyNamespace>();
        let ident = unsafe { &*ptr };

        // Note: For thin-provisioned namespaces, this might skip namespaces that could be
        // allocated later. However, we maintain this check following the OpenBSD behavior, which skips namespaces with zero size.
        if Self::namespace_size(ident) > 0 {
            // Commit namespace if it has a size greater than zero
            self.namespaces.push(Some(*ident));
            Ok(true)
        } else {
            // Don't attach a namespace if its size is zero
            self.namespaces.push(None);
            Ok(false)
        }
    }

    /// Fill I/O command in submission queue entry
    /// Based on OpenBSD's nvme_scsi_io_fill()
    fn io_fill(ccb: &Ccb, sqe: &mut SubQueueEntry) {
        if let Some(CcbCookie::Io {
            lba,
            blocks,
            nsid,
            read,
        }) = &ccb.cookie
        {
            // Cast to I/O-specific SQE type
            let sqe_io = unsafe { &mut *(sqe as *mut SubQueueEntry as *mut SubQueueEntryIo) };

            // Set opcode based on direction (from OpenBSD)
            sqe_io.opcode = if *read { NVM_CMD_READ } else { NVM_CMD_WRITE };

            // Set namespace ID
            sqe_io.nsid = u32::to_le(*nsid);

            // Set LBA and block count
            sqe_io.slba = u64::to_le(*lba);
            sqe_io.nlb = u16::to_le((*blocks - 1) as u16); // NLB is 0-based

            // Handle PRP entries based on transfer size
            if let Some(prpl_ptr) = ccb._prpl {
                // First PRP is always stored at the beginning of the PRP list
                let first_prp = unsafe { *(prpl_ptr as *const u64) };
                unsafe {
                    sqe_io.entry.prp[0] = first_prp;
                }

                // Check if we need PRP2 (more than one page)
                // The number of blocks tells us how many pages we need
                let pages_needed = *blocks as usize; // Assuming 1 block = 1 page for now

                if pages_needed > 1 {
                    if pages_needed == 2 {
                        // For exactly 2 pages, PRP2 points directly to the second page
                        let second_prp = unsafe { *((prpl_ptr as *const u64).add(1)) };
                        unsafe {
                            sqe_io.entry.prp[1] = second_prp;
                        }
                    } else {
                        // For > 2 pages, PRP2 points to the PRP list (starting from second entry)
                        unsafe {
                            sqe_io.entry.prp[1] =
                                ccb._prpl_dva + core::mem::size_of::<u64>() as u64;
                        }
                    }
                }
            }
        } else {
            log::error!("io_fill called with non-IO cookie");
        }
    }

    /// Process I/O command completion
    /// Based on OpenBSD's nvme_scsi_io_done()
    fn io_done(ccb_id: u16, cqe: &ComQueueEntry, ccbs: &mut [Ccb], ccb_list: &Mutex<CcbList>) {
        let ccb = &mut ccbs[ccb_id as usize];
        let flags = u16::from_le(cqe.flags);
        let status = (flags >> 1) & 0x7ff; // Extract status code

        // Sync and unload CCB's DMA map (following OpenBSD pattern)
        if ccb.dma_loaded {
            if let Some(ref mut dmamap) = ccb.dmamap {
                // Get read flag from cookie to determine sync operation
                let is_read = if let Some(CcbCookie::Io { read, .. }) = ccb.cookie {
                    read
                } else {
                    true // Default to read if cookie is wrong type
                };
                
                // Sync DMA map after operation (PostRead/PostWrite)
                let sync_op = if is_read {
                    DmaSyncOp::PostRead
                } else {
                    DmaSyncOp::PostWrite
                };
                let _ = dmamap.sync(0, dmamap.mapsize(), sync_op);
                
                // Unload the DMA map (like OpenBSD's bus_dmamap_unload)
                dmamap.unload();
                ccb.dma_loaded = false;
            }
        }

        // Mark the transfer as completed
        if let Some(transfer_id) = ccb.transfer_id {
            let _ = storage::transfer_mark_completed(transfer_id, status as u16);
        }

        if status == NVME_CQE_SC_SUCCESS {
            if let Some(CcbCookie::Io {
                lba,
                blocks,
                nsid,
                read,
            }) = &ccb.cookie
            {
                log::debug!(
                    "NVMe I/O completed: {} {} blocks at LBA {} on nsid {}",
                    if *read { "read" } else { "write" },
                    blocks,
                    lba,
                    nsid
                );
            }
        } else {
            log::error!("NVMe I/O failed with status: 0x{status:x}");
        }

        // Return CCB to pool
        let _ = ccb_put_free(ccbs, ccb_list, ccb_id);
    }

    /// Process flush command completion
    /// Based on OpenBSD's nvme_scsi_sync_done()
    fn sync_done(ccb_id: u16, cqe: &ComQueueEntry, ccbs: &mut [Ccb], ccb_list: &Mutex<CcbList>) {
        let ccb = &mut ccbs[ccb_id as usize];
        let flags = u16::from_le(cqe.flags);
        let status = (flags >> 1) & 0x7ff; // Extract status code

        if status == NVME_CQE_SC_SUCCESS {
            if let Some(CcbCookie::Flush { nsid }) = &ccb.cookie {
                log::debug!("NVMe flush completed on nsid {}", nsid);
            }
        } else {
            log::error!("NVMe flush failed with status: 0x{status:x}");
        }

        // Mark the transfer as completed if we have a transfer_id
        if let Some(transfer_id) = ccb.transfer_id {
            let _ = storage::transfer_mark_completed(transfer_id, status as u16);
        }

        // Return CCB to pool
        let _ = ccb_put_free(ccbs, ccb_list, ccb_id);
    }

    /// Fill flush command in submission queue entry
    /// Based on OpenBSD's nvme_scsi_sync_fill()
    fn sync_fill(ccb: &Ccb, sqe: &mut SubQueueEntry) {
        if let Some(CcbCookie::Flush { nsid }) = &ccb.cookie {
            // Clear the SQE first (following OpenBSD's pattern)
            *sqe = SubQueueEntry::default();
            sqe.opcode = NVM_CMD_FLUSH;
            sqe.nsid = u32::to_le(*nsid);
        } else {
            log::error!("sync_fill called with non-flush cookie");
        }
    }

    /// Submit I/O command with DMA map
    pub fn submit_io(&mut self, io_q: &Queue, transfer_id: u16, buf: &[u8]) -> Result<(), NvmeDriverErr> {
        use awkernel_lib::addr::virt_addr::VirtAddr;
        
        // Get transfer info for parameters (already set by storage layer)
        let (lba, blocks, nsid, read) = 
            storage::transfer_get_info(transfer_id).map_err(|_| NvmeDriverErr::InitFailure)?;

        // Get a CCB
        let ccb_id = self.ccb_get()?.ok_or(NvmeDriverErr::NoCcb)?;
        let ccb = &mut self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?[ccb_id as usize];

        // Load buffer into CCB's DMA map (like bus_dmamap_load in OpenBSD)
        if let Some(ref mut dmamap) = ccb.dmamap {
            let vaddr = VirtAddr::new(buf.as_ptr() as usize);
            dmamap.load(vaddr, buf.len()).map_err(|_| NvmeDriverErr::DmaError)?;
            
            // Sync for DMA (like bus_dmamap_sync in OpenBSD)
            let sync_op = if read {
                DmaSyncOp::PreRead
            } else {
                DmaSyncOp::PreWrite
            };
            dmamap.sync(0, buf.len(), sync_op).map_err(|_| NvmeDriverErr::DmaError)?;
            ccb.dma_loaded = true;
        } else {
            // No DMA map available for this CCB
            return Err(NvmeDriverErr::DmaError);
        }

        // Link CCB to transfer
        ccb.transfer_id = Some(transfer_id);

        // Set up the I/O cookie (using transfer's existing parameters)
        ccb.cookie = Some(CcbCookie::Io {
            lba,
            blocks,
            nsid,
            read,
        });

        // Set up done callback
        ccb.done = Some(Self::io_done);

        // Fill PRP list from DMA segments
        if let Some(ref dma_map) = ccb.dmamap {
            if let Some(prpl_ptr) = ccb._prpl {
                let segments = dma_map.get_segments();
                let num_segments = segments.len().min(self._max_prpl);

                let prp_list =
                    unsafe { core::slice::from_raw_parts_mut(prpl_ptr as *mut u64, num_segments) };

                for (i, seg) in segments.iter().take(num_segments).enumerate() {
                    prp_list[i] = seg.ds_addr.as_usize() as u64;
                }
            }
        }

        let poll = storage::transfer_is_poll_mode(transfer_id).unwrap_or(false);
        if poll {
            let timeout_ms = storage::transfer_get_timeout_ms(transfer_id).unwrap_or(DEFAULT_IO_TIMEOUT_MS);
            self.poll(io_q, ccb_id, Self::io_fill, timeout_ms)?;
        } else {
            io_q.submit(&self.info, ccb, Self::io_fill)?;
        }

        Ok(())
    }

    /// Submit flush command
    /// Based on OpenBSD's nvme_scsi_sync()
    pub fn submit_flush(&mut self, io_q: &Queue, transfer_id: u16) -> Result<(), NvmeDriverErr> {
        // Get transfer namespace ID
        let nsid = storage::transfer_get_nsid(transfer_id).map_err(|_| NvmeDriverErr::InitFailure)?;

        // Get a CCB
        let ccb_id = self.ccb_get()?.ok_or(NvmeDriverErr::NoCcb)?;
        let ccb = &mut self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?[ccb_id as usize];

        // Link CCB to transfer
        ccb.transfer_id = Some(transfer_id);

        // Set up the flush cookie
        ccb.cookie = Some(CcbCookie::Flush { nsid });

        // Set up done callback (following OpenBSD's nvme_scsi_sync)
        ccb.done = Some(Self::sync_done);

        let poll = storage::transfer_is_poll_mode(transfer_id).unwrap_or(false);
        if poll {
            let timeout_ms = storage::transfer_get_timeout_ms(transfer_id).unwrap_or(DEFAULT_IO_TIMEOUT_MS);
            self.poll(io_q, ccb_id, Self::sync_fill, timeout_ms)?;
        } else {
            io_q.submit(&self.info, ccb, Self::sync_fill)?;
        }

        Ok(())
    }

    fn intr(&mut self, admin_q: &Queue, io_q: &Queue) -> Result<bool, NvmeDriverErr> {
        let mut rv = false;

        if let Some(ccbs) = self.ccbs.as_mut() {
            let ccb_list = self.ccb_list.as_ref().ok_or(NvmeDriverErr::InitFailure)?;
            rv = io_q.complete(&self.info, ccbs, ccb_list)?;
        }

        if let Some(ccbs) = self.ccbs.as_mut() {
            let ccb_list = self.ccb_list.as_ref().ok_or(NvmeDriverErr::InitFailure)?;
            if admin_q.complete(&self.info, ccbs, ccb_list)? {
                rv = true;
            }
        }

        Ok(rv)
    }

    fn setup_interrupts(&mut self) {
        if let Ok(pcie_int) = self.allocate_msix() {
            self.pcie_int = pcie_int;
        } else if let Ok(pcie_int) = self.allocate_msi() {
            self.pcie_int = pcie_int;
        } else {
            self.pcie_int = PCIeInt::None;
        }
    }

    fn allocate_msix(&mut self) -> Result<PCIeInt, NvmeDriverErr> {
        let segment_group = self.info.get_segment_group();
        let bfd = self.info.get_bfd();

        let msix = self.info.get_msix_mut().ok_or(NvmeDriverErr::InitFailure)?;

        let irq_name = format!("{DEVICE_SHORT_NAME}-{bfd}-0");
        // Register single interrupt for both admin and I/O queues (like OpenBSD)
        // ENHANCE: It better to use a separate interrupt vector for I/O queues
        let mut irq = msix
            .register_handler(
                irq_name.into(),
                Box::new(|irq| {
                    awkernel_lib::storage::storage_interrupt(irq);
                }),
                segment_group as usize,
                awkernel_lib::cpu::raw_cpu_id() as u32,
                0,
            )
            .map_err(|e| {
                log::error!("Failed to register MSI-X handler: {:?}", e);
                NvmeDriverErr::InitFailure
            })?;

        irq.enable();

        if let Some(msi) = self.info.get_msi_mut() {
            msi.disable();
        }
        self.info.disable_legacy_interrupt();

        let msix = self.info.get_msix_mut().ok_or(NvmeDriverErr::InitFailure)?;
        msix.enable();

        Ok(PCIeInt::_MsiX(irq))
    }

    fn allocate_msi(&mut self) -> Result<PCIeInt, NvmeDriverErr> {
        if let Some(msix) = self.info.get_msix_mut() {
            msix.disable();
        }

        let segment_group = self.info.get_segment_group();
        let bfd = self.info.get_bfd();

        let msi = self.info.get_msi_mut().ok_or(NvmeDriverErr::InitFailure)?;

        msi.disable();

        let irq_name = format!("{DEVICE_SHORT_NAME}-{bfd}-0");
        let mut irq = msi
            .register_handler(
                irq_name.into(),
                Box::new(|irq| {
                    awkernel_lib::storage::storage_interrupt(irq);
                }),
                segment_group as usize,
                awkernel_lib::cpu::raw_cpu_id() as u32,
            )
            .map_err(|e| {
                log::error!("Failed to register MSI handler: {:?}", e);
                NvmeDriverErr::InitFailure
            })?;

        irq.enable();
        msi.enable();

        Ok(PCIeInt::_Msi(irq))
    }
}

pub struct Nvme {
    // The order of lock acquisition must be as follows:
    //
    // 1. `NvmeInner`'s lock
    // 2. `Queue`'s lock
    // 3. `Queue`'s unlock
    // 4. `NvmeInner`'s unlock
    //
    // Otherwise, a deadlock will occur.
    admin_q: Queue,
    io_q: Queue,
    inner: RwLock<NvmeInner>,
    device_id: u64, // Storage device ID
}

impl core::fmt::Debug for Nvme {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("Nvme")
            .field("device_id", &self.device_id)
            .field("admin_q", &"<Queue>")
            .field("io_q", &"<Queue>")
            .field("inner", &"<RwLock<NvmeInner>>")
            .finish()
    }
}

impl Nvme {
    fn new(mut info: PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        // Enable bus mastering and interrupts in PCIe command register
        let mut cmd = info.read_status_command();
        cmd.set(registers::StatusCommand::BUS_MASTER, true); // Enable DMA
        cmd.set(registers::StatusCommand::INTERRUPT_DISABLE, false); // Enable interrupts
        info.write_status_command(cmd);
        log::info!("NVMe: Enabled bus mastering and interrupts in PCIe command register");

        let mut inner = NvmeInner::new(info)?;

        inner.disable()?;

        let admin_q = inner.allocate_queue(NVME_ADMIN_Q, QUEUE_SIZE as u32, inner.dstrd)?;

        inner.ccbs_alloc(16)?;

        inner.enable(&admin_q)?;

        inner.identify(&admin_q)?;

        // We now know the real values of sc_mdts and sc_max_prpl.
        inner.ccbs_free();
        inner.ccbs_alloc(64)?;

        inner.setup_interrupts();
        write_reg(&inner.info, NVME_INTMC, 0x1)?;

        let io_q = inner.allocate_queue(1, QUEUE_SIZE as u32, inner.dstrd)?;

        inner.create_io_queue(&admin_q, &io_q)?;

        let nn = inner.nn;
        if nn > 0 {
            inner.namespaces.reserve_exact((nn + 1) as usize);
            let mut identified_count = 0;
            for nsid in 1..=nn {
                if inner.identify_namespace(&admin_q, nsid)? {
                    identified_count += 1;
                }
            }

            if identified_count < nn {
                log::info!("NVMe: Identified {identified_count} namespace(s), out of {nn} total");
            }
        }

        let nvme = Self {
            admin_q,
            io_q,
            inner: RwLock::new(inner),
            device_id: 0, // Will be set when registered with storage manager
        };

        Ok(nvme)
    }

    /// Debug function to log interrupt configuration
    pub fn debug_interrupt_config(&self) {
        let inner = self.inner.read();
        log::info!("=== NVMe Interrupt Configuration Debug ===");

        match &inner.pcie_int {
            PCIeInt::None => {
                log::warn!("No interrupts configured - device in polling mode only!");
            }
            PCIeInt::_Msi(irq) => {
                log::info!("MSI interrupt configured with IRQ {:?}", irq);
            }
            PCIeInt::_MsiX(irq) => {
                log::info!("MSI-X interrupt configured:");
                log::info!("  IRQ {} -> Both Admin and I/O queues", irq.get_irq());
            }
        }

        // Check controller interrupt mask register
        if let Ok(intms) = read_reg(&inner.info, NVME_INTMS) {
            log::info!("NVME_INTMS (Interrupt Mask Set): 0x{:08x}", intms);
        }
        if let Ok(intmc) = read_reg(&inner.info, NVME_INTMC) {
            log::info!("NVME_INTMC (Interrupt Mask Clear): 0x{:08x}", intmc);
        }

        log::info!("==========================================");
    }

    /// Submit a flush command
    pub fn flush(&self, nsid: u32, transfer_id: u16) -> Result<(), NvmeDriverErr> {
        // Set up the transfer for flush
        // Update transfer with namespace ID
        let _ = storage::transfer_set_params(
            transfer_id,
            storage::transfer_get_lba(transfer_id).unwrap_or(0),
            storage::transfer_get_blocks(transfer_id).unwrap_or(0),
            false, // flush is a write-type operation
            nsid,
        );

        // Submit the flush operation
        let mut inner = self.inner.write();
        inner.submit_flush(&self.io_q, transfer_id)?;

        // Return immediately - storage layer will wait for completion
        Ok(())
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

impl PCIeDevice for Arc<Nvme> {
    fn device_name(&self) -> alloc::borrow::Cow<'static, str> {
        PCIeDevice::device_name(&**self)
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NvmeDriverErr {
    InitFailure,
    NoBar0,
    ReadFailure,
    DMAPool,
    NotReady,
    CommandFailed,
    NoCcb,
    DmaError,
    IncompatiblePageSize,
    InvalidCcbId,
}

#[allow(dead_code)]
enum PCIeInt {
    None,
    _Msi(IRQ),
    _MsiX(IRQ),
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
            NvmeDriverErr::CommandFailed => PCIeDeviceErr::InitFailure,
            NvmeDriverErr::NoCcb => PCIeDeviceErr::InitFailure,
            NvmeDriverErr::DmaError => PCIeDeviceErr::InitFailure,
            NvmeDriverErr::IncompatiblePageSize => PCIeDeviceErr::InitFailure,
            NvmeDriverErr::InvalidCcbId => PCIeDeviceErr::CommandFailure,
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

pub(super) fn attach(
    mut info: PCIeInfo,
) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    // Map the memory regions of MMIO.
    if let Err(e) = info.map_bar() {
        log::warn!("NVMe: Failed to map the memory regions of MMIO: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }

    // Read capabilities of PCIe.
    info.read_capability();

    let nvme = Nvme::new(info)?;

    // Initialize the storage transfer pool if not already done
    storage::init_transfer_pool();

    // Register the controller with storage manager to get device_id
    // We need to temporarily wrap in Arc for registration
    let temp_arc = Arc::new(nvme);
    // Controller doesn't have a specific namespace, so pass None (pass concrete type)
    let device_id = storage::add_storage_device(temp_arc.clone(), None);

    // Get mutable access back to set device_id
    // This is safe because we're the only owner at this point
    let nvme_ptr = Arc::as_ptr(&temp_arc) as *mut Nvme;
    unsafe {
        (*nvme_ptr).device_id = device_id;
    }

    let nvme_arc = temp_arc;

    // Store the device globally
    let mut device = NVME_DEVICE.write();
    *device = Some(nvme_arc.clone());

    // Register each namespace as a separate storage device
    {
        let inner = nvme_arc.inner.read();
        for nsid in 1..=inner.nn {
            if inner
                .namespaces
                .get(nsid as usize - 1)
                .and_then(|ns| ns.as_ref())
                .is_some()
            {
                let namespace = NvmeNamespace::new(nvme_arc.clone(), nsid);
                let ns_arc = Arc::new(namespace);
                // Register with the specific namespace ID (pass concrete type)
                let storage_id = storage::add_storage_device(ns_arc.clone(), Some(nsid));

                // Set the device_id in the namespace
                let ns_ptr = Arc::as_ptr(&ns_arc) as *mut NvmeNamespace;
                unsafe {
                    (*ns_ptr).device_id = storage_id;
                }

                log::info!(
                    "NVMe: Registered namespace {} as storage device {}",
                    nsid,
                    storage_id
                );
            }
        }
    }

    Ok(nvme_arc as Arc<dyn PCIeDevice + Sync + Send>)
}

/// Helper function to validate buffer size for I/O operations
fn validate_io_buffer(
    block_size: usize,
    transfer_id: u16,
    buf_len: usize,
    is_write: bool,
) -> BlockResult<u32> {
    // Get transfer info to verify buffer size
    let (_lba, blocks, _nsid, _is_read) = storage::transfer_get_info(transfer_id)
        .map_err(|_| BlockDeviceError::IoError)?;
    
    let total_size = block_size * blocks as usize;
    
    // For writes, buffer must be exactly the right size
    // For reads, buffer must be at least the required size
    if is_write {
        if buf_len != total_size {
            return Err(BlockDeviceError::InvalidBlock);
        }
    } else {
        if buf_len < total_size {
            return Err(BlockDeviceError::InvalidBlock);
        }
    }
    
    Ok(blocks)
}

// StorageDevice implementation for NVMe
impl StorageDevice for Nvme {
    fn device_id(&self) -> u64 {
        self.device_id
    }

    fn device_name(&self) -> Cow<'static, str> {
        let inner = self.inner.read();
        let bfd = inner.info.get_bfd();
        format!("{bfd}: NVMe Controller").into()
    }

    fn device_short_name(&self) -> Cow<'static, str> {
        DEVICE_SHORT_NAME.into()
    }

    fn device_type(&self) -> StorageDeviceType {
        StorageDeviceType::NVMe
    }

    fn irqs(&self) -> Vec<u16> {
        let inner = self.inner.read();
        match &inner.pcie_int {
            PCIeInt::None => vec![],
            PCIeInt::_Msi(irq) => vec![irq.get_irq()],
            PCIeInt::_MsiX(irq) => vec![irq.get_irq()],
        }
    }

    fn interrupt(&self, _irq: u16) -> Result<(), StorageDevError> {
        let mut inner = self.inner.write();
        match inner.intr(&self.admin_q, &self.io_q) {
            Ok(_) => Ok(()),
            Err(_) => Err(StorageDevError::IoError),
        }
    }

    // Block device methods

    fn block_size(&self) -> usize {
        // For now, assume 512 byte sectors
        // TODO: Read actual block size from namespace data
        512
    }

    fn as_any(&self) -> &dyn core::any::Any {
        self
    }

    fn num_blocks(&self) -> u64 {
        // TODO: Read actual capacity from namespace data
        // For now return a placeholder
        1024 * 1024 // 512 MB with 512 byte blocks
    }

    fn read_blocks(&self, buf: &mut [u8], transfer_id: u16) -> BlockResult<()> {
        // Validate buffer size
        validate_io_buffer(self.block_size(), transfer_id, buf.len(), false)?;

        // Submit the I/O operation
        let mut inner = self.inner.write();
        inner
            .submit_io(&self.io_q, transfer_id, buf)
            .map_err(|_| BlockDeviceError::IoError)
    }

    fn write_blocks(&self, buf: &[u8], transfer_id: u16) -> BlockResult<()> {
        // Validate buffer size
        validate_io_buffer(self.block_size(), transfer_id, buf.len(), true)?;

        // Submit the I/O operation
        let mut inner = self.inner.write();
        inner
            .submit_io(&self.io_q, transfer_id, buf)
            .map_err(|_| BlockDeviceError::IoError)
    }

    fn flush(&self, transfer_id: u16) -> BlockResult<()> {
        // Namespace ID is already set by storage layer (0 for controller)
        // Submit the flush operation
        let mut inner = self.inner.write();
        inner
            .submit_flush(&self.io_q, transfer_id)
            .map_err(|_| BlockDeviceError::IoError)?;

        // Return immediately - storage layer will wait for completion
        Ok(())
    }
}

/// Represents a single NVMe namespace
pub struct NvmeNamespace {
    /// Shared reference to the NVMe controller
    controller: Arc<Nvme>,
    /// Namespace ID (1-based)
    namespace_id: u32,
    /// Storage device ID
    device_id: u64,
}

impl core::fmt::Debug for NvmeNamespace {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("NvmeNamespace")
            .field("namespace_id", &self.namespace_id)
            .field("device_id", &self.device_id)
            .finish()
    }
}

impl NvmeNamespace {
    pub fn new(controller: Arc<Nvme>, namespace_id: u32) -> Self {
        Self {
            controller,
            namespace_id,
            device_id: 0, // Will be set when registered
        }
    }

    pub fn set_device_id(&mut self, device_id: u64) {
        self.device_id = device_id;
    }
}

// StorageDevice implementation for NvmeNamespace
impl StorageDevice for NvmeNamespace {
    fn device_id(&self) -> u64 {
        self.device_id
    }

    fn device_name(&self) -> Cow<'static, str> {
        let inner = self.controller.inner.read();
        let bfd = inner.info.get_bfd();
        format!("{}: NVMe Namespace {}", bfd, self.namespace_id).into()
    }

    fn device_short_name(&self) -> Cow<'static, str> {
        // Extract controller number from device name
        let inner = self.controller.inner.read();
        let bfd = inner.info.get_bfd();
        format!(
            "nvme{}n{}",
            bfd.split(':').next().unwrap_or("nvme0"),
            self.namespace_id
        )
        .into()
    }

    fn device_type(&self) -> StorageDeviceType {
        StorageDeviceType::NVMe
    }

    fn irqs(&self) -> Vec<u16> {
        self.controller.irqs()
    }

    fn interrupt(&self, irq: u16) -> Result<(), StorageDevError> {
        self.controller.interrupt(irq)
    }

    fn block_size(&self) -> usize {
        let inner = self.controller.inner.read();
        if let Some(Some(ident)) = inner.namespaces.get(self.namespace_id as usize - 1) {
            let lbaf = nvme_id_ns_flbas(ident.flbas);
            if ident.nlbaf as usize > 16 {
                // Extended format
                let lbaf = lbaf | ((ident.flbas >> 1) & 0x3f);
                1 << ident.lbaf[lbaf as usize].lbads
            } else {
                1 << ident.lbaf[lbaf as usize].lbads
            }
        } else {
            DEFAULT_BLOCK_SIZE
        }
    }

    fn as_any(&self) -> &dyn Any {
        self
    }

    fn num_blocks(&self) -> u64 {
        let inner = self.controller.inner.read();
        if let Some(Some(ident)) = inner.namespaces.get(self.namespace_id as usize - 1) {
            NvmeInner::namespace_size(ident)
        } else {
            0
        }
    }

    fn read_blocks(
        &self,
        buf: &mut [u8],
        transfer_id: u16,
    ) -> BlockResult<()> {
        // Validate buffer size
        validate_io_buffer(self.block_size(), transfer_id, buf.len(), false)?;
        
        // Namespace ID is already correctly set by storage layer

        // Submit the I/O operation (passing buffer to submit_io)
        let mut inner = self.controller.inner.write();
        inner
            .submit_io(&self.controller.io_q, transfer_id, buf)
            .map_err(|_| BlockDeviceError::IoError)
    }

    fn write_blocks(
        &self,
        buf: &[u8],
        transfer_id: u16,
    ) -> BlockResult<()> {
        // Validate buffer size
        validate_io_buffer(self.block_size(), transfer_id, buf.len(), true)?;
        
        // Namespace ID is already correctly set by storage layer

        // Submit the I/O operation (passing buffer to submit_io)
        let mut inner = self.controller.inner.write();
        inner
            .submit_io(&self.controller.io_q, transfer_id, buf)
            .map_err(|_| BlockDeviceError::IoError)
    }

    fn flush(&self, transfer_id: u16) -> BlockResult<()> {
        // Call the controller's flush method with the provided transfer_id
        self.controller
            .flush(self.namespace_id, transfer_id)
            .map_err(|_| BlockDeviceError::IoError)
    }
}
