//! virtio-blk block device driver.
//!
//! Implements the virtio 1.x split-virtqueue block device protocol.
//! I/O is performed synchronously using polling (no interrupt required),
//! which fits the synchronous `StorageDevice` trait.
//!
//! # How virtio-blk works (plain explanation)
//!
//! A virtio device communicates through a shared memory ring called a
//! "virtqueue".  The driver places a *request* (header + data + status)
//! into the queue, then writes to a doorbell register ("kick") to wake the
//! device.  The device processes the request, writes a status byte, and
//! advances the "used" ring.  The driver checks the used ring to know when
//! the request is complete.
//!
//! For reads:  header says "read sector N" → device fills our data buffer.
//! For writes: header says "write sector N" + we fill the data buffer → device writes to disk.

use crate::pcie::{
    capability::virtio::VirtioCap,
    pcie_id,
    virtio::{
        config::{
            virtio_blk_config::VirtioBlkConfig,
            virtio_common_config::VirtioCommonConfig,
            virtio_notify_config::VirtioNotifyConfig,
        },
        VirtioDriverErr,
    },
    PCIeDevice, PCIeDeviceErr, PCIeInfo,
};
use alloc::{
    borrow::Cow,
    collections::LinkedList,
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::{
    addr::Addr,
    barrier::{membar_consumer, membar_producer},
    dma_pool::DMAPool,
    paging::PAGESIZE,
    storage::{
        add_storage_device,
        storage_device::{StorageDevError, StorageDevice, StorageDeviceType},
    },
    sync::rwlock::RwLock,
};

const VIRTIO_BLK_ID: u16 = 0x1042;

// ── Feature bits ──────────────────────────────────────────────────────────────
const VIRTIO_F_VERSION_1: u64 = 1 << 32;
const VIRTIO_F_ACCESS_PLATFORM: u64 = 1 << 33;
const VIRTIO_F_NOTIFY_ON_EMPTY: u64 = 1 << 24;

// ── Device status bits ────────────────────────────────────────────────────────
const STATUS_RESET: u8 = 0;
const STATUS_ACK: u8 = 1;
const STATUS_DRIVER: u8 = 2;
const STATUS_DRIVER_OK: u8 = 4;
const STATUS_FEATURES_OK: u8 = 8;
const STATUS_FAILED: u8 = 128;

// ── Virtio capability types ───────────────────────────────────────────────────
const VIRTIO_PCI_CAP_COMMON_CFG: u8 = 1;
const VIRTIO_PCI_CAP_NOTIFY_CFG: u8 = 2;
const VIRTIO_PCI_CAP_DEVICE_CFG: u8 = 4;

// ── MSI-X "no vector" sentinel ────────────────────────────────────────────────
const VIRTIO_MSI_NO_VECTOR: u16 = 0xFFFF;

// ── Block request types ───────────────────────────────────────────────────────
const VIRTIO_BLK_T_IN: u32 = 0; // read from device
const VIRTIO_BLK_T_OUT: u32 = 1; // write to device

// ── Status byte values ────────────────────────────────────────────────────────
const VIRTIO_BLK_S_OK: u8 = 0;
const _VIRTIO_BLK_S_IOERR: u8 = 1;
const _VIRTIO_BLK_S_UNSUPP: u8 = 2;

// ── Virtqueue descriptor flags ────────────────────────────────────────────────
const VIRTQ_DESC_F_NEXT: u16 = 1;
const VIRTQ_DESC_F_WRITE: u16 = 2; // device-writable (driver reads from device)

// ── Queue constants ───────────────────────────────────────────────────────────
const MAX_VQ_SIZE: usize = 256;
/// Maximum bytes transferred in one virtio-blk request.
/// 64 KiB is more than enough for FAT operations.
const MAX_TRANSFER_BYTES: usize = 64 * 1024;

// ─────────────────────────────────────────────────────────────────────────────
// Virtqueue DMA layout (identical to virtio-net: 3 pages)
// ─────────────────────────────────────────────────────────────────────────────

#[repr(C, packed)]
#[derive(Default, Copy, Clone)]
struct VirtqDesc {
    addr: u64,
    len: u32,
    flags: u16,
    next: u16,
}

#[repr(C, packed)]
struct VirtqAvail {
    flags: u16,
    idx: u16,
    ring: [u16; MAX_VQ_SIZE],
    used_event: u16,
}

impl Default for VirtqAvail {
    fn default() -> Self {
        VirtqAvail { flags: 0, idx: 0, ring: [0; MAX_VQ_SIZE], used_event: 0 }
    }
}

#[repr(C, packed)]
#[derive(Default, Copy, Clone)]
struct VirtqUsedElem {
    id: u32,
    len: u32,
}

#[repr(C, packed)]
struct VirtqUsed {
    flags: u16,
    idx: u16,
    ring: [VirtqUsedElem; MAX_VQ_SIZE],
    avail_event: u16,
}

impl Default for VirtqUsed {
    fn default() -> Self {
        VirtqUsed { flags: 0, idx: 0, ring: [VirtqUsedElem::default(); MAX_VQ_SIZE], avail_event: 0 }
    }
}

#[repr(C, packed)]
struct VirtqDMA {
    desc: [VirtqDesc; MAX_VQ_SIZE], // 4096 bytes
    avail: VirtqAvail,              // 518 bytes
    _pad: [u8; 3578],
    used: VirtqUsed,                // 2054 bytes
    _pad2: [u8; 2042],
}

impl Default for VirtqDMA {
    fn default() -> Self {
        VirtqDMA {
            desc: [VirtqDesc::default(); MAX_VQ_SIZE],
            avail: VirtqAvail::default(),
            _pad: [0; 3578],
            used: VirtqUsed::default(),
            _pad2: [0; 2042],
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Block request / response structures
// ─────────────────────────────────────────────────────────────────────────────

/// Header placed in front of every block I/O request (device reads this).
#[repr(C, packed)]
#[derive(Default, Copy, Clone)]
struct VirtioBlkReq {
    request_type: u32, // VIRTIO_BLK_T_IN / OUT / FLUSH
    reserved: u32,
    sector: u64, // starting 512-byte sector number (LBA)
}

/// Single-byte status written back by the device after completing a request.
#[repr(C)]
#[derive(Default, Copy, Clone)]
struct VirtioBlkStatus {
    status: u8, // 0 = OK
}

// ─────────────────────────────────────────────────────────────────────────────
// BlkVirtq — the single request queue for virtio-blk
// ─────────────────────────────────────────────────────────────────────────────

#[derive(Copy, Clone)]
struct VirtqEntry {
    index: u16,
    next: i16,
}

struct BlkVirtq {
    vq_dma: DMAPool<VirtqDMA>,
    vq_freelist: LinkedList<usize>,
    vq_entries: [VirtqEntry; MAX_VQ_SIZE],
    vq_num: usize,
    vq_mask: usize,
    vq_avail_idx: u16,
    vq_used_idx: u16,
    _vq_index: u16,

    /// DMA-mapped request header (shared across requests, single-thread safe
    /// because BlkVirtq is protected by VirtioBlk's RwLock).
    req: DMAPool<VirtioBlkReq>,
    /// DMA-mapped data buffer (device writes read results here / reads write data from here).
    data_buf: DMAPool<[u8; MAX_TRANSFER_BYTES]>,
    /// DMA-mapped status byte written by the device.
    status: DMAPool<VirtioBlkStatus>,
}

impl BlkVirtq {
    fn init(&mut self) {
        self.vq_freelist = LinkedList::new();
        for i in (0..self.vq_num).rev() {
            self.vq_freelist.push_front(i);
            self.vq_entries[i].index = i as u16;
        }
        self.vq_avail_idx = 0;
        self.vq_used_idx = 0;
    }

    fn alloc_entry(&mut self) -> Option<usize> {
        self.vq_freelist.pop_front()
    }

    fn free_entry(&mut self, slot: usize) {
        self.vq_freelist.push_front(slot);
    }

    fn enqueue_prep(&mut self) -> Option<usize> {
        let slot = self.alloc_entry()?;
        self.vq_entries[slot].next = -1;
        Some(slot)
    }

    fn enqueue_reserve(&mut self, slot: usize, nsegs: usize) -> Result<(), VirtioDriverErr> {
        self.vq_entries[slot].next = self.vq_entries[slot].index as i16;
        let mut s = slot;
        for _ in 0..nsegs - 1 {
            let next = match self.alloc_entry() {
                Some(n) => n,
                None => {
                    self.vq_dma.as_mut().desc[s].flags = 0;
                    self.enqueue_abort(slot);
                    return Err(VirtioDriverErr::NoSlot);
                }
            };
            self.vq_dma.as_mut().desc[s].flags = VIRTQ_DESC_F_NEXT;
            self.vq_dma.as_mut().desc[s].next = next as u16;
            s = next;
        }
        self.vq_dma.as_mut().desc[s].flags = 0;
        Ok(())
    }

    /// Add one descriptor to the chain.
    /// `device_writes`: if true the device writes into this buffer (set WRITE flag).
    fn enqueue(&mut self, slot: usize, phy: usize, len: usize, device_writes: bool) {
        let next = self.vq_entries[slot].next;
        debug_assert!(next >= 0);
        let desc = &mut self.vq_dma.as_mut().desc[next as usize];
        desc.addr = phy as u64;
        desc.len = len as u32;
        if device_writes {
            desc.flags |= VIRTQ_DESC_F_WRITE;
        }
        self.vq_entries[slot].next = desc.next as i16;
    }

    fn enqueue_commit(&mut self, slot: usize) {
        let avail = &mut self.vq_dma.as_mut().avail;
        avail.ring[self.vq_avail_idx as usize & self.vq_mask] = slot as u16;
        self.vq_avail_idx += 1;
    }

    fn publish_avail_idx(&mut self) {
        membar_producer();
        self.vq_dma.as_mut().avail.idx = self.vq_avail_idx;
    }

    fn dequeue_commit(&mut self, slot: usize) {
        let mut s = slot;
        while self.vq_dma.as_ref().desc[s].flags & VIRTQ_DESC_F_NEXT != 0 {
            let next = self.vq_dma.as_ref().desc[s].next as usize;
            self.free_entry(s);
            s = next;
        }
        self.free_entry(s);
    }

    fn enqueue_abort(&mut self, slot: usize) {
        if self.vq_entries[slot].next < 0 {
            self.free_entry(slot);
            return;
        }
        let mut s = slot;
        while self.vq_dma.as_mut().desc[s].flags & VIRTQ_DESC_F_NEXT != 0 {
            self.free_entry(s);
            s = self.vq_dma.as_mut().desc[s].next as usize;
        }
        self.free_entry(s);
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// VirtioBlkInner — all mutable state, protected by RwLock
// ─────────────────────────────────────────────────────────────────────────────

struct VirtioBlkInner {
    info: PCIeInfo,
    common_cfg: VirtioCommonConfig,
    blk_cfg: VirtioBlkConfig,
    notify_cfg: VirtioNotifyConfig,
    notify_off_multiplier: u32,
    active_features: u64,
    vq: BlkVirtq,
    capacity_sectors: u64, // total 512-byte sectors
}

impl VirtioBlkInner {
    fn cap_find(&self, cfg_type: u8) -> Result<VirtioCap, VirtioDriverErr> {
        for cap in &self.info.virtio_caps {
            if cap.get_cfg_type() == cfg_type {
                return Ok(cap.clone());
            }
        }
        Err(VirtioDriverErr::NoCap)
    }

    fn attach(&mut self) -> Result<(), VirtioDriverErr> {
        // 1. Find capability regions
        let common_cap = self.cap_find(VIRTIO_PCI_CAP_COMMON_CFG)?;
        let device_cap = self.cap_find(VIRTIO_PCI_CAP_DEVICE_CFG)?;
        let notify_cap = self.cap_find(VIRTIO_PCI_CAP_NOTIFY_CFG)?;

        self.notify_off_multiplier = notify_cap.get_notify_off_multiplier();

        self.common_cfg.init(&self.info, common_cap)?;
        self.blk_cfg.init(&self.info, device_cap)?;
        self.notify_cfg.init(&self.info, notify_cap)?;

        // 2. Reset → ACK → DRIVER
        self.common_cfg.virtio_set_device_status(STATUS_RESET)?;
        self.common_cfg.virtio_set_device_status(STATUS_ACK)?;
        self.common_cfg.virtio_set_device_status(STATUS_DRIVER)?;

        // 3. Feature negotiation (require VERSION_1 only)
        let mut driver_features: u64 = VIRTIO_F_VERSION_1 | VIRTIO_F_ACCESS_PLATFORM;
        driver_features &= !VIRTIO_F_NOTIFY_ON_EMPTY;

        let device_features = self.common_cfg.virtio_get_device_features()?;
        let negotiated = device_features & driver_features;

        self.common_cfg.virtio_set_driver_features(negotiated);
        self.common_cfg.virtio_set_device_status(STATUS_FEATURES_OK)?;

        let status = self.common_cfg.virtio_get_device_status()?;
        if status & STATUS_FEATURES_OK == 0 {
            self.common_cfg.virtio_set_device_status(STATUS_FAILED)?;
            return Err(VirtioDriverErr::InitFailure);
        }
        if negotiated & VIRTIO_F_VERSION_1 == 0 {
            self.common_cfg.virtio_set_device_status(STATUS_FAILED)?;
            return Err(VirtioDriverErr::InitFailure);
        }
        self.active_features = negotiated;

        // 4. Read device geometry
        self.capacity_sectors = self.blk_cfg.capacity()?;

        // 5. Allocate virtqueue 0
        self.common_cfg.virtio_set_queue_select(0)?;
        let vq_size = self.common_cfg.virtio_get_queue_size()? as usize;
        if vq_size == 0 || (vq_size & (vq_size - 1)) != 0 || vq_size > MAX_VQ_SIZE {
            self.common_cfg.virtio_set_device_status(STATUS_FAILED)?;
            return Err(VirtioDriverErr::InvalidQueueSize);
        }

        let pages = core::mem::size_of::<VirtqDMA>().div_ceil(PAGESIZE);
        let mut vq_dma: DMAPool<VirtqDMA> =
            DMAPool::new(0, pages).ok_or(VirtioDriverErr::DMAPool)?;
        *vq_dma.as_mut() = VirtqDMA::default();

        let req: DMAPool<VirtioBlkReq> =
            DMAPool::new(0, 1).ok_or(VirtioDriverErr::DMAPool)?;
        let data_buf: DMAPool<[u8; MAX_TRANSFER_BYTES]> =
            DMAPool::new(0, MAX_TRANSFER_BYTES.div_ceil(PAGESIZE))
                .ok_or(VirtioDriverErr::DMAPool)?;
        let status: DMAPool<VirtioBlkStatus> =
            DMAPool::new(0, 1).ok_or(VirtioDriverErr::DMAPool)?;

        let mut vq = BlkVirtq {
            vq_dma,
            vq_freelist: LinkedList::new(),
            vq_entries: [VirtqEntry { index: 0, next: -1 }; MAX_VQ_SIZE],
            vq_num: vq_size,
            vq_mask: vq_size - 1,
            vq_avail_idx: 0,
            vq_used_idx: 0,
            _vq_index: 0,
            req,
            data_buf,
            status,
        };
        vq.init();
        self.vq = vq;

        // 6. Disable MSI-X for polling mode (VIRTIO_MSI_NO_VECTOR = 0xFFFF)
        self.common_cfg
            .virtio_set_config_msix_vector(VIRTIO_MSI_NO_VECTOR)?;
        self.common_cfg.virtio_set_queue_select(0)?;
        self.common_cfg
            .virtio_set_queue_msix_vector(VIRTIO_MSI_NO_VECTOR)?;

        // 7. Register queue physical addresses
        let phy_addr = self.vq.vq_dma.get_phy_addr().as_usize() as u64;
        let avail_offset = 4096u64;
        let used_offset = 8192u64;
        self.common_cfg.virtio_set_queue_select(0)?;
        self.common_cfg.virtio_set_queue_desc(phy_addr)?;
        self.common_cfg.virtio_set_queue_avail(phy_addr + avail_offset)?;
        self.common_cfg.virtio_set_queue_used(phy_addr + used_offset)?;
        self.common_cfg.virtio_set_queue_enable(1)?;

        // 8. Signal DRIVER_OK
        self.common_cfg.virtio_set_device_status(STATUS_DRIVER_OK)?;

        log::info!(
            "virtio-blk: attached, capacity = {} sectors ({} MiB)",
            self.capacity_sectors,
            self.capacity_sectors / 2048
        );

        Ok(())
    }

    /// Kick (notify) the device that queue 0 has new entries.
    fn kick(&mut self) -> Result<(), VirtioDriverErr> {
        self.common_cfg.virtio_set_queue_select(0)?;
        let notify_off = self.common_cfg.virtio_get_queue_notify_off()? as usize;
        let offset = notify_off * self.notify_off_multiplier as usize;
        self.notify_cfg.virtio_set_notify(offset, 0)
    }

    /// Submit a block I/O request and poll until the device completes it.
    ///
    /// `request_type`: `VIRTIO_BLK_T_IN` (read) or `VIRTIO_BLK_T_OUT` (write).
    /// The caller must copy data to/from `self.vq.data_buf` before/after this call.
    fn submit_and_poll(
        &mut self,
        request_type: u32,
        sector: u64,
        data_len: usize,
    ) -> Result<(), StorageDevError> {
        let is_read = request_type == VIRTIO_BLK_T_IN;

        // Fill request header
        *self.vq.req.as_mut() = VirtioBlkReq {
            request_type,
            reserved: 0,
            sector,
        };
        // Reset status to a non-OK sentinel so we can detect completion
        self.vq.status.as_mut().status = !VIRTIO_BLK_S_OK;

        // Build 3-descriptor chain: [header] → [data] → [status]
        let slot = self.vq.enqueue_prep().ok_or(StorageDevError::DeviceNotReady)?;
        self.vq
            .enqueue_reserve(slot, 3)
            .map_err(|_| StorageDevError::DeviceNotReady)?;

        // Descriptor 0: request header — device reads this
        let req_phy = self.vq.req.get_phy_addr().as_usize();
        self.vq
            .enqueue(slot, req_phy, core::mem::size_of::<VirtioBlkReq>(), false);

        // Descriptor 1: data buffer
        //   Read  → device writes into our buffer (device_writes = true)
        //   Write → device reads from our buffer   (device_writes = false)
        let data_phy = self.vq.data_buf.get_phy_addr().as_usize();
        self.vq.enqueue(slot, data_phy, data_len, is_read);

        // Descriptor 2: status byte — device always writes this
        let status_phy = self.vq.status.get_phy_addr().as_usize();
        self.vq.enqueue(slot, status_phy, 1, true);

        self.vq.enqueue_commit(slot);
        self.vq.publish_avail_idx();

        let saved_used = self.vq.vq_used_idx;

        // Kick the device
        self.kick().map_err(|_| StorageDevError::IoError)?;

        // Poll until the used ring advances (device signals completion)
        loop {
            membar_consumer();
            if self.vq.vq_dma.as_ref().used.idx != saved_used {
                break;
            }
            core::hint::spin_loop();
        }

        self.vq.vq_used_idx = self.vq.vq_used_idx.wrapping_add(1);
        self.vq.dequeue_commit(slot);

        if self.vq.status.as_ref().status != VIRTIO_BLK_S_OK {
            return Err(StorageDevError::IoError);
        }

        Ok(())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Public VirtioBlk struct + PCIeDevice + StorageDevice impls
// ─────────────────────────────────────────────────────────────────────────────

pub struct VirtioBlk {
    inner: RwLock<VirtioBlkInner>,
    irqs: Vec<u16>,
}

impl PCIeDevice for VirtioBlk {
    fn device_name(&self) -> Cow<'static, str> {
        "virtio-blk".into()
    }
}

impl StorageDevice for VirtioBlk {
    fn device_id(&self) -> u64 {
        0
    }

    fn device_name(&self) -> Cow<'static, str> {
        "virtio-blk".into()
    }

    fn device_short_name(&self) -> Cow<'static, str> {
        "vblk0".into()
    }

    fn device_type(&self) -> StorageDeviceType {
        StorageDeviceType::VirtIO
    }

    fn irqs(&self) -> Vec<u16> {
        self.irqs.clone()
    }

    fn interrupt(&self, _irq: u16) -> Result<(), StorageDevError> {
        Ok(()) // polling mode: no interrupt handling needed
    }

    fn block_size(&self) -> usize {
        512
    }

    fn num_blocks(&self) -> u64 {
        self.inner.read().capacity_sectors
    }

    fn read_blocks(&self, _buf: &mut [u8], _transfer_id: u16) -> Result<(), StorageDevError> {
        Err(StorageDevError::NotSupported)
    }

    fn write_blocks(&self, _buf: &[u8], _transfer_id: u16) -> Result<(), StorageDevError> {
        Err(StorageDevError::NotSupported)
    }

    fn read_blocks_at(&self, lba: u64, buf: &mut [u8]) -> Result<(), StorageDevError> {
        if buf.is_empty() {
            return Ok(());
        }
        if buf.len() % 512 != 0 {
            return Err(StorageDevError::InvalidBlock);
        }
        if buf.len() > MAX_TRANSFER_BYTES {
            return Err(StorageDevError::NotSupported);
        }

        let mut inner = self.inner.write();

        inner.submit_and_poll(VIRTIO_BLK_T_IN, lba, buf.len())?;

        // Copy from DMA buffer to caller's buffer
        let src = inner.vq.data_buf.as_ref();
        buf.copy_from_slice(&src[..buf.len()]);

        Ok(())
    }

    fn write_blocks_at(&self, lba: u64, buf: &[u8]) -> Result<(), StorageDevError> {
        if buf.is_empty() {
            return Ok(());
        }
        if buf.len() % 512 != 0 {
            return Err(StorageDevError::InvalidBlock);
        }
        if buf.len() > MAX_TRANSFER_BYTES {
            return Err(StorageDevError::NotSupported);
        }

        let mut inner = self.inner.write();

        // Copy caller's data into DMA buffer before handing to device.
        // Block ensures the &mut borrow of data_buf ends before submit_and_poll borrows inner.
        {
            let dst = inner.vq.data_buf.as_mut();
            dst[..buf.len()].copy_from_slice(buf);
        }

        inner.submit_and_poll(VIRTIO_BLK_T_OUT, lba, buf.len())?;

        Ok(())
    }

    fn flush(&self, _transfer_id: u16) -> Result<(), StorageDevError> {
        // Polling-mode writes are synchronous; no explicit flush needed.
        Ok(())
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// PCIe entry points
// ─────────────────────────────────────────────────────────────────────────────

pub fn match_device(vendor: u16, id: u16) -> bool {
    vendor == pcie_id::VIRTIO_VENDOR_ID && id == VIRTIO_BLK_ID
}

pub fn attach(mut info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    if info.get_revision_id() == 0 {
        return Err(PCIeDeviceErr::RevisionIDMismatch);
    }

    if let Err(e) = info.map_bar() {
        log::warn!("virtio-blk: failed to map BAR: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }
    info.read_capability();

    // Build a dummy BlkVirtq so we can construct the inner before attach().
    let dummy_vq_dma: DMAPool<VirtqDMA> =
        DMAPool::new(0, core::mem::size_of::<VirtqDMA>().div_ceil(PAGESIZE))
            .ok_or(PCIeDeviceErr::InitFailure)?;
    let dummy_req: DMAPool<VirtioBlkReq> =
        DMAPool::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;
    let dummy_data: DMAPool<[u8; MAX_TRANSFER_BYTES]> =
        DMAPool::new(0, MAX_TRANSFER_BYTES.div_ceil(PAGESIZE))
            .ok_or(PCIeDeviceErr::InitFailure)?;
    let dummy_status: DMAPool<VirtioBlkStatus> =
        DMAPool::new(0, 1).ok_or(PCIeDeviceErr::InitFailure)?;

    let dummy_blk_vq = BlkVirtq {
        vq_dma: dummy_vq_dma,
        vq_freelist: LinkedList::new(),
        vq_entries: [VirtqEntry { index: 0, next: -1 }; MAX_VQ_SIZE],
        vq_num: 0,
        vq_mask: 0,
        vq_avail_idx: 0,
        vq_used_idx: 0,
        _vq_index: 0,
        req: dummy_req,
        data_buf: dummy_data,
        status: dummy_status,
    };

    let mut inner = VirtioBlkInner {
        info,
        common_cfg: VirtioCommonConfig::new(),
        blk_cfg: VirtioBlkConfig::new(),
        notify_cfg: VirtioNotifyConfig::new(),
        notify_off_multiplier: 0,
        active_features: 0,
        vq: dummy_blk_vq,
        capacity_sectors: 0,
    };

    inner.attach()?;

    let blk = Arc::new(VirtioBlk {
        inner: RwLock::new(inner),
        irqs: Vec::new(), // polling mode — no IRQs registered
    });

    // Register with the storage manager and attempt to mount FAT.
    let device_id = add_storage_device(blk.clone());
    log::info!("virtio-blk: registered as storage device id={device_id}");

    {
        use awkernel_lib::file::fatfs::mount_or_format_fatfs;
        match mount_or_format_fatfs(blk.clone()) {
            Ok(()) => log::info!("virtio-blk: FAT filesystem ready."),
            Err(e) => log::warn!("virtio-blk: FAT mount failed: {e}"),
        }
    }

    Ok(blk)
}
