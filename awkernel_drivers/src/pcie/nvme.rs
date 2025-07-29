use super::{registers, PCIeDevice, PCIeDeviceErr, PCIeInfo};
use alloc::{
    borrow::Cow,
    boxed::Box,
    collections::{BTreeMap, VecDeque},
    format,
    sync::Arc,
    vec::Vec,
};
use core::sync::atomic::{AtomicBool, Ordering};
use awkernel_lib::{
    addr::Addr,
    barrier::{
        bus_space_barrier, membar_consumer, membar_producer, BUS_SPACE_BARRIER_READ, BUS_SPACE_BARRIER_WRITE,
    },
    delay::wait_microsec,
    dma_pool::DMAPool,
    interrupt::IRQ,
    paging::PAGESIZE,
    sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock},
};

mod nvme_regs;
use nvme_regs::*;

const DEVICE_NAME: &str = " NVMe Controller";
const _DEVICE_SHORT_NAME: &str = "nvme";

pub const PAGE_SHIFT: u32 = PAGESIZE.trailing_zeros(); // 2^12 = 4096
pub const MAXPHYS: usize = 64 * 1024; /* max raw I/O transfer size. TODO - to be considered. */
pub const NVME_TIMO_IDENT: u32 = 10000; /* ms to probe/identify */
pub const NVME_TIMO_DELAYNS: u64 = 10; /* ns to wait in poll loop */

// Global NVMe device instance (single device assumption)
pub static NVME_DEVICE: RwLock<Option<Arc<Nvme>>> = RwLock::new(None);

#[derive(Debug, Clone, Copy)]
enum NvmeQueueType {
    Admin,
    Io,
}

struct Namespace {
    ident: Option<IdentifyNamespace>,
}

/// Global interrupt handler for the single NVMe device
pub fn nvme_interrupt(irq: u16) {
    let device = NVME_DEVICE.read();
    if let Some(nvme) = device.as_ref() {
        let _ = nvme.process_interrupt(irq);
    }
}

#[derive(Debug, Clone, Copy, Default)]
struct PollState {
    _sqe: SubQueueEntry,
    _cqe: ComQueueEntry,
}

enum CcbCookie {
    _Controller(DMAPool<IdentifyController>),
    _State(PollState),
    _QueueCmd(SubQueueEntryQ),
    Io {
        lba: u64,
        blocks: u32,
        nsid: u32,
        read: bool,
    },
    Flush {
        nsid: u32,
    },
}

struct Ccb {
    //_dmamap - TODO - this is not used for IdenifyController, so it is removed for now.
    cookie: Option<CcbCookie>,

    done: Option<fn(&mut Ccb, &ComQueueEntry)>,
    _prpl_off: usize,
    _prpl_dva: u64,
    _prpl: Option<usize>,
    _id: u16,
    // Completion tracking for async operations (testing support)
    completed: Arc<AtomicBool>,
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

    fn complete(&self, info: &PCIeInfo, ccbs: &mut [Ccb]) -> Result<bool, NvmeDriverErr> {
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
            let ccb = &mut ccbs[cid as usize];

            if let Some(done_fn) = ccb.done {
                done_fn(ccb, cqe);
            } else {
                return Err(NvmeDriverErr::NoCallback);
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
    irq_to_queue: BTreeMap<u16, NvmeQueueType>,
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
            irq_to_queue: BTreeMap::new(),
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

        let prpl_size = core::mem::size_of::<u64>() * self._max_prpl * nccbs as usize;
        let prpl_pages = prpl_size.div_ceil(PAGESIZE);

        let prpl_dma = DMAPool::<u64>::new(self.info.segment_group as usize, prpl_pages)
            .ok_or(NvmeDriverErr::DMAPool)?;

        let prpl_virt_base = prpl_dma.get_virt_addr().as_usize();
        let prpl_phys_base = prpl_dma.get_phy_addr().as_usize() as u64;

        self.ccb_prpls = Some(prpl_dma);

        let mut off = 0;
        for i in 0..nccbs {
            let ccb = Ccb {
                cookie: None,
                done: None,
                _prpl_off: off,
                _prpl_dva: prpl_phys_base + off as u64,
                _prpl: Some(prpl_virt_base + off),
                _id: i,
                completed: Arc::new(AtomicBool::new(true)), // Initially completed (not in use)
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

    fn poll_done(ccb: &mut Ccb, cqe: &ComQueueEntry) {
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

            if !q.complete(&self.info, ccbs)? {
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
                done_fn(ccb, &cqe);
            }
            cqe
        };

        let flags = u16::from_le(cqe.flags);

        Ok(flags & !NVME_CQE_PHASE)
    }

    fn fill_identify(ccb: &Ccb, sqe: &mut SubQueueEntry) {
        sqe.opcode = NVM_ADMIN_IDENTIFY;
        if let Some(CcbCookie::_Controller(mem)) = ccb.cookie.as_ref() {
            unsafe {
                sqe.entry.prp[0] = (mem.get_phy_addr().as_usize() as u64).to_le();
            }
        }
        sqe.cdw10 = 1_u32.to_le();
    }

    fn sqe_fill(ccb: &Ccb, sqe: &mut SubQueueEntry) {
        match &ccb.cookie {
            Some(CcbCookie::_QueueCmd(sqe_q)) => {
                // Copy the queue command fields properly
                sqe.opcode = sqe_q.opcode;
                sqe.flags = sqe_q.flags;
                sqe.cid = sqe_q.cid;
                unsafe {
                    sqe.entry.prp[0] = sqe_q.prp1;
                }
                sqe.cdw10 = sqe_q.cdw10;
                sqe.cdw11 = sqe_q.cdw11;
                sqe.cdw12 = sqe_q.cdw12;
                sqe.cdw13 = sqe_q.cdw13;
                sqe.cdw14 = sqe_q.cdw14;
                sqe.cdw15 = sqe_q.cdw15;
            }
            Some(CcbCookie::_State(state)) => {
                // For generic SQE operations
                *sqe = state._sqe;
            }
            _ => {
                log::error!("NVMe: Invalid CCB cookie for SQE fill");
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
        
        // CDW10: Queue ID (bits 15:0) and Queue Size (bits 31:16)
        sqe.cdw10 = ((((io_q.entries - 1) as u32) << 16) | (io_q._id as u32)).to_le();
        
        // CDW11: Interrupt Vector (bits 31:16) and Queue Flags (bits 15:0)
        // For MSI-X, use vector 1 for I/O queue, for MSI use vector 0
        let interrupt_vector = match &self.pcie_int {
            PCIeInt::MsiX(_) => 1u32,  // I/O queue uses vector 1 in MSI-X
            _ => 0u32,  // Admin and I/O share vector 0 in MSI or no interrupts
        };
        let qflags = (NVM_SQE_CQ_IEN | NVM_SQE_Q_PC) as u32;
        sqe.cdw11 = ((interrupt_vector << 16) | qflags).to_le();
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
        
        // CDW10: Queue ID (bits 15:0) and Queue Size (bits 31:16)
        sqe.cdw10 = ((((io_q.entries - 1) as u32) << 16) | (io_q._id as u32)).to_le();
        
        // CDW11: CQ ID (bits 31:16) and Queue Flags (bits 15:0)
        sqe.cdw11 = (((io_q._id as u32) << 16) | (NVM_SQE_Q_PC as u32)).to_le();
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
            ccb.cookie = Some(CcbCookie::_Controller(mem));
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
            log::warn!("Failed to identify namespace {nsid}: status 0x{rv:x}");
            return Err(NvmeDriverErr::CommandFailed);
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

    /// Main interrupt handler for MSI/MSI-X interrupts
    fn nvme_intr(&mut self, admin_q: &Queue, io_q: &Queue) -> bool {
        let mut rv = false;

        // Process I/O queue completions first
        if let Some(ccbs) = self.ccbs.as_mut() {
            match io_q.complete(&self.info, ccbs) {
                Ok(completed) => {
                    if completed {
                        rv = true;
                    }
                }
                Err(e) => {
                    log::error!("nvme_intr: Error processing I/O completions: {:?}", e);
                }
            }
        }

        // Process admin queue completions
        if let Some(ccbs) = self.ccbs.as_mut() {
            match admin_q.complete(&self.info, ccbs) {
                Ok(completed) => {
                    if completed {
                        rv = true;
                    }
                }
                Err(e) => {
                    log::error!("nvme_intr: Error processing admin completions: {:?}", e);
                }
            }
        }

        rv
    }

    /// Legacy interrupt handler for INTx interrupts
    #[allow(dead_code)]
    fn nvme_intr_intx(&mut self, admin_q: &Queue, io_q: &Queue) -> bool {
        // Mask interrupts
        if let Err(e) = write_reg(&self.info, NVME_INTMS, 1) {
            log::error!("Failed to mask interrupts: {e:?}");
            return false;
        }

        let rv = self.nvme_intr(admin_q, io_q);

        // Unmask interrupts
        if let Err(e) = write_reg(&self.info, NVME_INTMC, 1) {
            log::error!("Failed to unmask interrupts: {e:?}");
        }

        rv
    }

    /// Fill I/O command in submission queue entry
    /// Based on OpenBSD's nvme_scsi_io_fill()
    fn nvme_io_fill(ccb: &Ccb, sqe: &mut SubQueueEntry) {
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

            // For now, we'll use PRP1 only (single page transfers)
            // TODO: Add PRPL support for multi-page transfers
            if let Some(prpl_ptr) = ccb._prpl {
                let prp_list = unsafe { core::slice::from_raw_parts(prpl_ptr as *const u64, 1) };
                unsafe {
                    sqe_io.entry.prp[0] = prp_list[0];
                }
            }
        } else {
            log::error!("nvme_io_fill called with non-IO cookie");
        }
    }

    /// Process I/O command completion
    /// Based on OpenBSD's nvme_scsi_io_done()
    fn nvme_io_done(ccb: &mut Ccb, cqe: &ComQueueEntry) {
        let flags = u16::from_le(cqe.flags);
        let status = (flags >> 1) & 0x7ff; // Extract status code

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
        
        // Mark the operation as completed for async waiting
        ccb.completed.store(true, Ordering::Release);
    }

    /// Process flush command completion
    /// Based on OpenBSD's nvme_scsi_sync_done()
    fn nvme_flush_done(ccb: &mut Ccb, cqe: &ComQueueEntry) {
        let flags = u16::from_le(cqe.flags);
        let status = (flags >> 1) & 0x7ff; // Extract status code

        if status == NVME_CQE_SC_SUCCESS {
            if let Some(CcbCookie::Flush { nsid }) = &ccb.cookie {
                log::debug!("NVMe flush completed on nsid {}", nsid);
            }
        } else {
            log::error!("NVMe flush failed with status: 0x{status:x}");
        }
        
        // Mark the operation as completed for async waiting
        ccb.completed.store(true, Ordering::Release);
    }

    /// Fill flush command in submission queue entry
    /// Based on OpenBSD's nvme_scsi_sync_fill()
    fn nvme_flush_fill(ccb: &Ccb, sqe: &mut SubQueueEntry) {
        if let Some(CcbCookie::Flush { nsid }) = &ccb.cookie {
            // Clear the SQE first (following OpenBSD's pattern)
            *sqe = SubQueueEntry::default();
            sqe.opcode = NVM_CMD_FLUSH;
            sqe.nsid = u32::to_le(*nsid);
        } else {
            log::error!("nvme_flush_fill called with non-flush cookie");
        }
    }

    /// Submit I/O command to the I/O queue
    /// Based on OpenBSD's nvme_scsi_io()
    #[allow(clippy::too_many_arguments)]
    pub fn submit_io(
        &mut self,
        io_q: &Queue,
        nsid: u32,
        lba: u64,
        blocks: u32,
        data_phys: u64,
        read: bool,
        poll: bool,
    ) -> Result<(), NvmeDriverErr> {
        // Get a CCB
        let ccb_id = self.ccb_get()?.ok_or(NvmeDriverErr::NoCcb)?;
        let ccb = &mut self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?[ccb_id as usize];

        // Set up the I/O cookie
        ccb.cookie = Some(CcbCookie::Io {
            lba,
            blocks,
            nsid,
            read,
        });

        // Set up done callback (following OpenBSD's nvme_scsi_io)
        ccb.done = Some(Self::nvme_io_done);

        // Store the physical address in the PRPL
        if let Some(prpl_ptr) = ccb._prpl {
            let prp_list = unsafe { core::slice::from_raw_parts_mut(prpl_ptr as *mut u64, 1) };
            prp_list[0] = data_phys;
        }

        if poll {
            // Synchronous polling mode - use the poll() function like OpenBSD
            self.poll(io_q, ccb_id, Self::nvme_io_fill, 30000)?; // 30 second timeout
            let _ = self.ccb_put(ccb_id);
        } else {
            // Asynchronous mode
            // Clear the completion flag before submitting
            ccb.completed.store(false, Ordering::Release);
            
            // Get a clone of the completion flag to wait on
            let completion_flag = ccb.completed.clone();
            
            // Submit the command
            io_q.submit(&self.info, ccb, Self::nvme_io_fill)?;
            
            // For testing purposes, wait for async completion
            // In a real system, the upper layer (SCSI) would handle this
            let mut iterations = 0;
            const MAX_ITERATIONS: u32 = 4_000_000; // 40 seconds with 10us delays
            
            loop {
                // Check if the interrupt handler has marked it complete
                if completion_flag.load(Ordering::Acquire) {
                    break;
                }
                
                if iterations >= MAX_ITERATIONS {
                    let _ = self.ccb_put(ccb_id);
                    return Err(NvmeDriverErr::CommandTimeout);
                }
                
                wait_microsec(10); // Wait for interrupt
                iterations += 1;
            }
            
            let _ = self.ccb_put(ccb_id);
        }

        Ok(())
    }

    /// Submit flush command
    /// Based on OpenBSD's nvme_scsi_sync()
    pub fn submit_flush(
        &mut self,
        io_q: &Queue,
        nsid: u32,
        poll: bool,
    ) -> Result<(), NvmeDriverErr> {
        // Get a CCB
        let ccb_id = self.ccb_get()?.ok_or(NvmeDriverErr::NoCcb)?;
        let ccb = &mut self.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?[ccb_id as usize];

        // Set up the flush cookie
        ccb.cookie = Some(CcbCookie::Flush { nsid });

        // Set up done callback (following OpenBSD's nvme_scsi_sync)
        ccb.done = Some(Self::nvme_flush_done);

        if poll {
            // Synchronous polling mode - use the poll() function like OpenBSD
            log::info!("Polling for flush completion, ccb_id={ccb_id}");
            self.poll(io_q, ccb_id, Self::nvme_flush_fill, 10000)?; // 10 second timeout
            log::info!("Flush completed successfully");
            let _ = self.ccb_put(ccb_id);
        } else {
            // Asynchronous mode
            // Clear the completion flag before submitting
            ccb.completed.store(false, Ordering::Release);
            
            // Get a clone of the completion flag to wait on
            let completion_flag = ccb.completed.clone();
            
            // Submit the command
            io_q.submit(&self.info, ccb, Self::nvme_flush_fill)?;
            
            // For testing purposes, wait for async completion
            // In a real system, the upper layer (SCSI) would handle this
            let mut iterations = 0;
            const MAX_ITERATIONS: u32 = 4_000_000; // 40 seconds with 10us delays
            
            loop {
                // Check if the interrupt handler has marked it complete
                if completion_flag.load(Ordering::Acquire) {
                    break;
                }
                
                if iterations >= MAX_ITERATIONS {
                    let _ = self.ccb_put(ccb_id);
                    return Err(NvmeDriverErr::CommandTimeout);
                }
                
                wait_microsec(10); // Wait for interrupt
                iterations += 1;
            }
            
            // Free the CCB now that it's complete
            let _ = self.ccb_put(ccb_id);
        }

        Ok(())
    }
}

// Interrupt configuration for the NVMe device
// The IRQ values are stored here for record-keeping, while actual interrupt
// routing uses the irq_to_queue map for efficiency
enum PCIeInt {
    None,
    Msi(IRQ),
    MsiX(Vec<(IRQ, NvmeQueueType)>),
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
}

impl Nvme {
    fn process_interrupt(&self, irq: u16) -> Result<(), NvmeDriverErr> {
        let inner = self.inner.read();
        let queue_type = match inner.irq_to_queue.get(&irq) {
            Some(qt) => *qt,
            None => {
                log::warn!("IRQ {} not found in irq_to_queue map", irq);
                return Ok(());
            }
        };

        drop(inner); // Release read lock

        match queue_type {
            NvmeQueueType::Admin | NvmeQueueType::Io => {
                let mut inner = self.inner.write();
                inner.nvme_intr(&self.admin_q, &self.io_q);
                Ok(())
            }
        }
    }

    /// Debug function to log interrupt configuration
    pub fn debug_interrupt_config(&self) {
        let inner = self.inner.read();
        log::info!("=== NVMe Interrupt Configuration Debug ===");
        
        match &inner.pcie_int {
            PCIeInt::None => {
                log::warn!("No interrupts configured - device in polling mode only!");
            }
            PCIeInt::Msi(irq) => {
                log::info!("MSI interrupt configured with IRQ {:?}", irq);
            }
            PCIeInt::MsiX(irqs) => {
                log::info!("MSI-X interrupts configured:");
                for (irq, queue_type) in irqs {
                    log::info!("  IRQ {} -> {:?} queue", irq.get_irq(), queue_type);
                }
            }
        }
        
        log::info!("IRQ to queue mapping:");
        for (irq, queue_type) in &inner.irq_to_queue {
            log::info!("  IRQ {} -> {:?}", irq, queue_type);
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
}

fn setup_interrupts(inner: &mut NvmeInner) -> PCIeInt {
    let segment_group = inner.info.get_segment_group();
    let bfd = inner.info.get_bfd();
    log::info!("Setting up NVMe interrupts for {}", bfd);

    // Try MSI-X first
    if let Some(msix) = inner.info.get_msix_mut() {
        log::info!("MSI-X capability found, attempting to register handlers");
        let mut irqs = Vec::new();

        // Register admin queue interrupt (vector 0)
        match msix.register_handler(
            Cow::from(format!("nvme-{bfd}-admin")),
            Box::new(|irq| {
                nvme_interrupt(irq);
            }),
            segment_group as usize,
            0, // target CPU
            0, // MSI-X entry 0 for admin queue
        ) {
            Ok(irq_admin) => {
                let irq_num = irq_admin.get_irq();
                log::info!("Registered admin queue interrupt: IRQ {}", irq_num);
                irqs.push((irq_admin, NvmeQueueType::Admin));
                inner.irq_to_queue.insert(irq_num, NvmeQueueType::Admin);

                // Register I/O queue interrupt (vector 1)
                match msix.register_handler(
                    Cow::from(format!("nvme-{bfd}-io")),
                    Box::new(|irq| {
                        nvme_interrupt(irq);
                    }),
                    segment_group as usize,
                    0, // target CPU
                    1, // MSI-X entry 1 for I/O queue
                ) {
                    Ok(irq_io) => {
                        let irq_num = irq_io.get_irq();
                        log::info!("Registered I/O queue interrupt: IRQ {}", irq_num);
                        irqs.push((irq_io, NvmeQueueType::Io));
                        inner.irq_to_queue.insert(irq_num, NvmeQueueType::Io);

                        // Enable MSI-X
                        msix.enable();
                        log::info!("NVMe: MSI-X interrupts enabled successfully");
                        return PCIeInt::MsiX(irqs);
                    }
                    Err(e) => {
                        log::error!("Failed to register I/O queue interrupt: {:?}", e);
                    }
                }
            }
            Err(e) => {
                log::error!("Failed to register admin queue interrupt: {:?}", e);
            }
        }

        // If MSI-X failed, disable it
        msix.disable();
        log::warn!("MSI-X setup failed, disabling MSI-X");
    } else {
        log::info!("No MSI-X capability found");
    }

    // Try MSI
    if let Some(msi) = inner.info.get_msi_mut() {
        log::info!("MSI capability found, attempting to register handler");
        msi.disable();

        match msi.register_handler(
            Cow::from(format!("nvme-{bfd}")),
            Box::new(|irq| {
                nvme_interrupt(irq);
            }),
            segment_group as usize,
            0, // target CPU
        ) {
            Ok(mut irq) => {
                // For MSI, both queues share the same interrupt
                let irq_num = irq.get_irq();
                log::info!("Registered MSI interrupt: IRQ {}", irq_num);
                inner.irq_to_queue.insert(irq_num, NvmeQueueType::Admin);
                irq.enable();
                msi.enable();
                log::info!("NVMe: MSI interrupts enabled successfully");
                return PCIeInt::Msi(irq);
            }
            Err(e) => {
                log::error!("Failed to register MSI handler: {:?}", e);
            }
        }
    } else {
        log::info!("No MSI capability found");
    }

    // Fall back to polling mode
    log::warn!("NVMe: No MSI-X/MSI support, falling back to polling mode");
    PCIeInt::None
}

impl Nvme {
    fn new(mut info: PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        // Enable bus mastering and interrupts in PCIe command register
        let mut cmd = info.read_status_command();
        cmd.set(registers::StatusCommand::BUS_MASTER, true);  // Enable DMA
        cmd.set(registers::StatusCommand::INTERRUPT_DISABLE, false);  // Enable interrupts
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

        // Setup interrupts BEFORE creating I/O queue so we know which interrupt vector to use
        inner.pcie_int = setup_interrupts(&mut inner);

        // Unmask interrupts BEFORE creating I/O queue (like OpenBSD does)
        match &inner.pcie_int {
            PCIeInt::MsiX(_) => {
                // Unmask both admin (vector 0) and I/O (vector 1) interrupts
                write_reg(&inner.info, NVME_INTMC, 0x3)?; // bits 0 and 1
            }
            _ => {
                // For MSI or no interrupts, just unmask vector 0
                write_reg(&inner.info, NVME_INTMC, 0x1)?;
            }
        }

        let io_q = inner.allocate_queue(1, QUEUE_SIZE as u32, inner.dstrd)?;

        inner.create_io_queue(&admin_q, &io_q)?;

        let nn = inner.nn;
        if nn > 0 {
            inner.namespaces.reserve_exact((nn + 1) as usize);
            let mut identified_count = 0;
            for nsid in 1..=nn {
                if let Ok(attached) = inner.identify_namespace(&admin_q, nsid) {
                    if attached {
                        identified_count += 1;
                    }
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
        };

        Ok(nvme)
    }

    /// Submit an I/O command (read or write)
    /// Modeled after OpenBSD's nvme_scsi_io()
    fn nvme_io_submit(
        &self,
        nsid: u32,
        lba: u64,
        blocks: u32,
        data_phys: u64,
        read: bool,
        poll: bool,
    ) -> Result<(u16, Arc<AtomicBool>), NvmeDriverErr> {
        if poll {
            // For polling mode, we can hold the lock throughout
            let mut inner = self.inner.write();
            inner.submit_io(&self.io_q, nsid, lba, blocks, data_phys, read, poll)?;
            // For polling mode, we don't need to wait - submit_io handles it
            Ok((0, Arc::new(AtomicBool::new(true))))
        } else {
            // For interrupt mode, follow OpenBSD's pattern:
            // 1. Get CCB
            // 2. Setup CCB (cookie, done callback, data)
            // 3. Submit
            // 4. Return CCB ID and completion flag for caller
            
            // Get a CCB
            let ccb_id = {
                let inner = self.inner.write();
                inner.ccb_get()?.ok_or(NvmeDriverErr::NoCcb)?
            };
            
            // Set up the CCB (like OpenBSD's nvme_scsi_io setting up ccb)
            let completion_flag = {
                let mut inner = self.inner.write();
                let ccb = &mut inner.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?[ccb_id as usize];
                
                // Set up the I/O cookie
                ccb.cookie = Some(CcbCookie::Io {
                    lba,
                    blocks,
                    nsid,
                    read,
                });
                
                // Set up done callback
                ccb.done = Some(NvmeInner::nvme_io_done);
                
                // Store the physical address in the PRPL
                if let Some(prpl_ptr) = ccb._prpl {
                    let prp_list = unsafe { core::slice::from_raw_parts_mut(prpl_ptr as *mut u64, 1) };
                    prp_list[0] = data_phys;
                }
                
                // Clear the completion flag before submitting
                ccb.completed.store(false, Ordering::Release);
                
                // Get a clone of the completion flag to return
                ccb.completed.clone()
            };
            
            // Submit the command (like OpenBSD's nvme_q_submit)
            {
                let inner = self.inner.read();
                self.io_q.submit(&inner.info, &inner.ccbs.as_ref().ok_or(NvmeDriverErr::InitFailure)?[ccb_id as usize], NvmeInner::nvme_io_fill)?;
            }
            
            Ok((ccb_id, completion_flag))
        }
    }

    /// Wait for I/O completion and cleanup CCB
    /// This is for testing purposes - in a real system, the upper layer would handle this
    fn wait_for_completion(&self, ccb_id: u16, completion_flag: Arc<AtomicBool>) -> Result<(), NvmeDriverErr> {
        // For testing purposes, wait for async completion
        // In a real system, the upper layer (SCSI) would handle this
        let mut iterations = 0;
        const MAX_ITERATIONS: u32 = 4_000_000; // 40 seconds with 10us delays
        
        loop {
            if completion_flag.load(Ordering::Acquire) {
                break;
            }
            
            if iterations >= MAX_ITERATIONS {
                let mut inner = self.inner.write();
                let _ = inner.ccb_put(ccb_id);
                return Err(NvmeDriverErr::CommandTimeout);
            }
            
            wait_microsec(10);
            iterations += 1;
        }
        
        // Free the CCB
        let mut inner = self.inner.write();
        let _ = inner.ccb_put(ccb_id);
        Ok(())
    }

    /// Submit a read command
    pub fn read_sectors(
        &self,
        nsid: u32,
        lba: u64,
        blocks: u32,
        data_phys: u64,
        poll: bool,
    ) -> Result<(), NvmeDriverErr> {
        let (ccb_id, completion_flag) = self.nvme_io_submit(nsid, lba, blocks, data_phys, true, poll)?;
        
        if !poll {
            // For testing, wait for completion
            // In a real system, we'd return immediately like OpenBSD
            self.wait_for_completion(ccb_id, completion_flag)?;
        }
        
        Ok(())
    }

    /// Submit a write command
    pub fn write_sectors(
        &self,
        nsid: u32,
        lba: u64,
        blocks: u32,
        data_phys: u64,
        poll: bool,
    ) -> Result<(), NvmeDriverErr> {
        let (ccb_id, completion_flag) = self.nvme_io_submit(nsid, lba, blocks, data_phys, false, poll)?;
        
        if !poll {
            // For testing, wait for completion
            // In a real system, we'd return immediately like OpenBSD
            self.wait_for_completion(ccb_id, completion_flag)?;
        }
        
        Ok(())
    }

    /// Submit a flush command (sync cache)
    /// Modeled after OpenBSD's nvme_scsi_sync()
    fn nvme_sync_submit(&self, nsid: u32, poll: bool) -> Result<(u16, Arc<AtomicBool>), NvmeDriverErr> {
        if poll {
            // For polling mode, we can hold the lock throughout
            let mut inner = self.inner.write();
            inner.submit_flush(&self.io_q, nsid, poll)?;
            // For polling mode, we don't need to wait - submit_flush handles it
            Ok((0, Arc::new(AtomicBool::new(true))))
        } else {
            // For interrupt mode, follow OpenBSD's pattern:
            // 1. Get CCB
            // 2. Setup CCB (cookie, done callback)
            // 3. Submit
            // 4. Return CCB ID and completion flag for caller
            
            // Get a CCB
            let ccb_id = {
                let inner = self.inner.write();
                inner.ccb_get()?.ok_or(NvmeDriverErr::NoCcb)?
            };
            
            // Set up the CCB (like OpenBSD's nvme_scsi_sync setting up ccb)
            let completion_flag = {
                let mut inner = self.inner.write();
                let ccb = &mut inner.ccbs.as_mut().ok_or(NvmeDriverErr::InitFailure)?[ccb_id as usize];
                
                // Set up the flush cookie
                ccb.cookie = Some(CcbCookie::Flush { nsid });
                
                // Set up done callback
                ccb.done = Some(NvmeInner::nvme_flush_done);
                
                // Clear the completion flag before submitting
                ccb.completed.store(false, Ordering::Release);
                
                // Get a clone of the completion flag to return
                ccb.completed.clone()
            };
            
            // Submit the command (like OpenBSD's nvme_q_submit)
            {
                let inner = self.inner.read();
                self.io_q.submit(&inner.info, &inner.ccbs.as_ref().ok_or(NvmeDriverErr::InitFailure)?[ccb_id as usize], NvmeInner::nvme_flush_fill)?;
            }
            
            Ok((ccb_id, completion_flag))
        }
    }

    /// Submit a flush command
    pub fn flush(&self, nsid: u32, poll: bool) -> Result<(), NvmeDriverErr> {
        let (ccb_id, completion_flag) = self.nvme_sync_submit(nsid, poll)?;
        
        if !poll {
            // For testing, wait for completion
            // In a real system, we'd return immediately like OpenBSD
            self.wait_for_completion(ccb_id, completion_flag)?;
        }
        
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
        (**self).device_name()
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
    NoCallback,
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
            NvmeDriverErr::NoCallback => PCIeDeviceErr::CommandFailure,
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
    let nvme_arc = Arc::new(nvme);

    // Store the device globally
    let mut device = NVME_DEVICE.write();
    *device = Some(nvme_arc.clone());

    Ok(nvme_arc as Arc<dyn PCIeDevice + Sync + Send>)
}
