//! This is a skelton of a PCIe device driver.

use alloc::{borrow::Cow, boxed::Box, collections::BTreeMap, format, sync::Arc, vec::Vec};
use awkernel_lib::{
    addr::Addr,
    dma_pool::DMAPool,
    interrupt::IRQ,
    net::{
        ether::{ETHER_ADDR_LEN, ETHER_MAX_LEN, ETHER_TYPE_VLAN},
        multicast::MulticastAddrs,
        net_device::{self, LinkStatus, NetCapabilities, NetDevice, NetFlags},
        toeplitz::stoeplitz_to_key,
    },
    paging::PAGESIZE,
    sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock},
};
use i225::{igc_get_flash_presence_i225, I225Flash, I225NoFlash};
use igc_api::{igc_set_mac_type, igc_setup_init_funcs};
use igc_defines::*;
use igc_hw::{IgcFcMode, IgcHw, IgcMacType, IgcMediaType, IgcOperations};

use crate::pcie::{
    intel::igc::{
        i225::{igc_set_eee_i225, IGC_MRQC_ENABLE_RSS_4Q, IGC_SRRCTL_DROP_EN},
        igc_base::{
            IgcAdvRxDesc, IgcAdvTxDesc, IGC_RXDCTL_QUEUE_ENABLE, IGC_SRRCTL_BSIZEPKT_SHIFT,
            IGC_SRRCTL_DESCTYPE_ADV_ONEBUF,
        },
        igc_mac::igc_clear_hw_cntrs_base_generic,
    },
    PCIeDevice, PCIeDeviceErr, PCIeInfo,
};

mod i225;
mod igc_api;
mod igc_base;
mod igc_defines;
mod igc_hw;
mod igc_mac;
mod igc_nvm;
mod igc_phy;
mod igc_regs;

const AUTONEG_ADV_DEFAULT: u16 = ADVERTISE_10_HALF
    | ADVERTISE_10_FULL
    | ADVERTISE_100_HALF
    | ADVERTISE_100_FULL
    | ADVERTISE_1000_FULL
    | ADVERTISE_2500_FULL;

const AUTO_ALL_MODES: u8 = 0;

const MAX_NUM_MULTICAST_ADDRESSES: usize = 128;

const IGC_FC_PAUSE_TIME: u16 = 0x0680;

const IGC_TXPBSIZE: u32 = 20408;
const IGC_DMCTLX_DCFLUSH_DIS: u32 = 0x80000000; // Disable DMA Coalesce Flush

const IGC_RX_PTHRESH: u32 = 8;
const IGC_RX_HTHRESH: u32 = 8;
const IGC_RX_WTHRESH: u32 = 4;

const IGC_MAX_VECTORS: u16 = 8;

const DEVICE_SHORT_NAME: &str = "igc";

const IGC_DEFAULT_RXD: usize = 1024;
const IGC_DEFAULT_TXD: usize = 1024;

const MAX_INTS_PER_SEC: u32 = 8000;
const DEFAULT_ITR: u32 = 1000000000 / (MAX_INTS_PER_SEC * 256);

const MAX_FRAME_SIZE: u32 = 9234;
const RX_BUFFER_SIZE: usize = 4096 * 3;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IgcDriverErr {
    NoBar0,
    ReadFailure,
    MacInit,
    MasterRequestsPending,
    Reset,
    NVM,
    SwfwSync,
    BlkPhyReset,
    Param,
    Phy,
    Config,
    DmaPoolAlloc,
}

type RxRing = [IgcAdvRxDesc; IGC_DEFAULT_RXD];
type TxRing = [IgcAdvTxDesc; IGC_DEFAULT_TXD];

type RxBuffer = [[u8; RX_BUFFER_SIZE]; IGC_DEFAULT_RXD];

struct Rx {
    next_to_check: usize,
    last_desc_filled: usize,
    rx_desc_ring: DMAPool<RxRing>,

    read_buf: Option<DMAPool<RxBuffer>>,
    slots: usize,

    // Statistics
    dropped_pkts: u64,
}

struct Tx {
    next_avail_desc: usize,
    next_to_clean: usize,
    tx_desc_ring: DMAPool<TxRing>,
}

struct Queue {
    rx: Mutex<Rx>,
    tx: Mutex<Tx>,
    me: usize,
}

/// Check if the device is an Intel I225/I226.
pub fn match_device(vendor: u16, id: u16) -> bool {
    igc_hw::IGC_DEVICES.contains(&(vendor, id))
}

/// Attach the device to the system.
/// This function is also called by `crate::pcie::PCIeInfo::attach`
/// to attach the device to the system.
pub fn attach(mut info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    // Initialize PCIeInfo

    // Map the memory regions of MMIO.
    if let Err(e) = info.map_bar() {
        log::warn!("Failed to map the memory regions of MMIO: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }

    // Read capabilities of PCIe.
    info.read_capability();

    let igc = Igc::new(info)?;

    let result = Arc::new(igc);

    // Add the network interface, if needed.
    awkernel_lib::net::add_interface(result.clone(), None);

    Ok(result)
}

#[derive(Debug)]
struct LinkInfo {
    link_active: bool,
    link_speed: Option<IgcSpeed>,
    link_duplex: Option<IgcDuplex>,
    link_status: LinkStatus,
}

struct QueueInfo {
    que: Vec<Queue>,
    irqs_to_queues: BTreeMap<u16, usize>,
    irqs_queues: Vec<IRQ>,
    irq_events: IRQ,
}

pub struct IgcInner {
    ops: Box<dyn IgcOperations + Sync + Send>,
    info: PCIeInfo,
    hw: IgcHw,
    link_info: LinkInfo,
    mta: Box<[[u8; ETHER_ADDR_LEN]; MAX_NUM_MULTICAST_ADDRESSES]>, // Multicast address table
    multicast_addrs: MulticastAddrs,
    if_flags: NetFlags,
    queue_info: QueueInfo,
    capabilities: net_device::NetCapabilities,
}

pub struct Igc {
    inner: RwLock<IgcInner>,
}

impl Igc {
    fn new(mut info: PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        use PCIeDeviceErr::InitFailure;

        let mut hw = IgcHw::default();
        hw.device_id = info.id;

        igc_set_mac_type(&mut hw).or(Err(InitFailure))?;

        let (irqs_queues, irq_events) = igc_allocate_pci_resources(&mut info)?;

        let (que, irqs_to_queues) = igc_allocate_queues(&info, &irqs_queues)?;

        let ops = igc_setup_init_funcs(&mut info, &mut hw).or(Err(InitFailure))?;

        hw.mac.autoneg = true;
        hw.phy.autoneg_wait_to_complete = false;
        hw.phy.autoneg_advertised = AUTONEG_ADV_DEFAULT;

        // Copper options.
        if hw.phy.media_type == IgcMediaType::Copper {
            hw.phy.mdix = AUTO_ALL_MODES;
        }

        // Set the max frame size.
        hw.mac.max_frame_size = MAX_FRAME_SIZE;

        if ops.check_reset_block(&mut info).is_err() {
            log::info!("PHY reset is blocked due to SOL/IDER session");
        }

        // Disable Energy Efficient Ethernet (EEE).
        hw.dev_spec.eee_disable = true;

        let link_info = match igc_attach_and_hw_control(ops.as_ref(), &mut info, &mut hw) {
            Ok(link_info) => link_info,
            Err(e) => {
                log::error!("igc: Failed to attach and get hardware control: {e:?}");
                let _ = igc_release_hw_control(&mut info);
                return Err(InitFailure);
            }
        };

        let queue_info = QueueInfo {
            que,
            irqs_to_queues,
            irqs_queues,
            irq_events,
        };

        let inner = RwLock::new(IgcInner::new(ops, info, hw, link_info, queue_info));

        let igc = Self { inner };
        let mac_addr = igc.mac_address();

        log::info!(
            "{}:{}: MAC = {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
            igc.device_short_name(),
            igc.device_name(),
            mac_addr[0],
            mac_addr[1],
            mac_addr[2],
            mac_addr[3],
            mac_addr[4],
            mac_addr[5]
        );

        Ok(igc)
    }
}

impl PCIeDevice for Igc {
    fn device_name(&self) -> Cow<'static, str> {
        "Intel I225/I226 2.5 GbE".into()
    }
}

impl NetDevice for Igc {
    fn add_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), net_device::NetDevError> {
        let mut inner = self.inner.write();
        inner.multicast_addrs.add_addr(*addr);

        inner
            .igc_iff()
            .or(Err(net_device::NetDevError::DeviceError))
    }

    fn remove_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), net_device::NetDevError> {
        let mut inner = self.inner.write();
        inner.multicast_addrs.remove_addr(addr);

        inner
            .igc_iff()
            .or(Err(net_device::NetDevError::DeviceError))
    }

    fn can_send(&self) -> bool {
        // TODO
        false
    }

    fn capabilities(&self) -> net_device::NetCapabilities {
        // TODO
        net_device::NetCapabilities::empty()
    }

    fn device_short_name(&self) -> Cow<'static, str> {
        DEVICE_SHORT_NAME.into()
    }

    fn down(&self) -> Result<(), net_device::NetDevError> {
        let mut inner = self.inner.write();
        inner
            .igc_stop()
            .or(Err(net_device::NetDevError::DeviceError))
    }

    fn flags(&self) -> net_device::NetFlags {
        // TODO
        net_device::NetFlags::empty()
    }

    fn interrupt(&self, _irq: u16) -> Result<(), net_device::NetDevError> {
        // TODO
        Ok(())
    }

    fn irqs(&self) -> Vec<u16> {
        let inner = self.inner.read();

        let mut result = Vec::with_capacity(inner.queue_info.irqs_queues.len() + 1);
        for irq in inner.queue_info.irqs_queues.iter() {
            result.push(irq.get_irq());
        }

        result.push(inner.queue_info.irq_events.get_irq());

        result
    }

    fn link_speed(&self) -> u64 {
        let inner = self.inner.read();
        inner.link_info.link_speed.map_or(0, |s| s as u64)
    }

    fn link_status(&self) -> net_device::LinkStatus {
        let inner = self.inner.read();
        inner.link_info.link_status
    }

    fn mac_address(&self) -> [u8; 6] {
        let inner = self.inner.read();
        inner.hw.mac.addr
    }

    fn num_queues(&self) -> usize {
        let inner = self.inner.read();
        inner.queue_info.que.len()
    }

    fn recv(
        &self,
        _que_id: usize,
    ) -> Result<Option<net_device::EtherFrameBuf>, net_device::NetDevError> {
        // TODO
        Ok(None)
    }

    fn send(
        &self,
        _data: net_device::EtherFrameRef,
        _que_id: usize,
    ) -> Result<(), net_device::NetDevError> {
        // TODO
        Ok(())
    }

    fn up(&self) -> Result<(), net_device::NetDevError> {
        // TODO
        Ok(())
    }

    fn rx_irq_to_que_id(&self, irq: u16) -> Option<usize> {
        let inner = self.inner.read();
        inner.queue_info.irqs_to_queues.get(&irq).copied()
    }
}

#[inline(always)]
fn write_flush(info: &PCIeInfo) -> Result<(), IgcDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.read32(igc_regs::IGC_STATUS)
        .ok_or(IgcDriverErr::ReadFailure)?;
    Ok(())
}

#[inline(always)]
fn read_reg(info: &PCIeInfo, offset: usize) -> Result<u32, IgcDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.read32(offset).ok_or(IgcDriverErr::ReadFailure)
}

#[inline(always)]
fn write_reg(info: &PCIeInfo, offset: usize, value: u32) -> Result<(), IgcDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.write32(offset, value);
    Ok(())
}

#[inline(always)]
fn read_reg_array(info: &PCIeInfo, offset: usize, index: usize) -> Result<u32, IgcDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.read32(offset + (index << 2))
        .ok_or(IgcDriverErr::ReadFailure)
}

#[inline(always)]
fn write_reg_array(
    info: &PCIeInfo,
    offset: usize,
    index: usize,
    value: u32,
) -> Result<(), IgcDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.write32(offset + (index << 2), value);
    Ok(())
}

/// Initialize the DMA Coalescing feature
fn igc_init_dmac(
    info: &mut PCIeInfo,
    hw: &IgcHw,
    pba: u32,
    sc_dmac: u32,
) -> Result<(), IgcDriverErr> {
    use igc_regs::*;

    let reg = !IGC_DMACR_DMAC_EN;

    let max_frame_size = hw.mac.max_frame_size;

    if sc_dmac == 0 {
        // Disabling it
        write_reg(info, IGC_DMACR, reg)?;
        return Ok(());
    } else {
        log::info!("igc: DMA Coalescing enabled");
    }

    // Set starting threshold
    write_reg(info, IGC_DMCTXTH, 0)?;

    let hwm = 64 * pba - max_frame_size / 16;
    let hwm = if hwm < 64 * (pba - 6) {
        64 * (pba - 6)
    } else {
        hwm
    };

    let mut reg = read_reg(info, IGC_FCRTC)?;
    reg &= !IGC_FCRTC_RTH_COAL_MASK;
    reg |= (hwm << IGC_FCRTC_RTH_COAL_SHIFT) & IGC_FCRTC_RTH_COAL_MASK;
    write_reg(info, IGC_FCRTC, reg)?;

    let dmac = pba - max_frame_size / 512;
    let dmac = if dmac < pba - 10 { pba - 10 } else { dmac };
    let mut reg = read_reg(info, IGC_DMACR)?;
    reg &= !IGC_DMACR_DMACTHR_MASK;
    reg |= (dmac << IGC_DMACR_DMACTHR_SHIFT) & IGC_DMACR_DMACTHR_MASK;

    // transition to L0x or L1 if available
    reg |= IGC_DMACR_DMAC_EN | IGC_DMACR_DMAC_LX_MASK;

    // Check if status is 2.5Gb backplane connection
    // before configuration of watchdog timer, which is
    // in msec values in 12.8usec intervals
    // watchdog timer= msec values in 32usec intervals
    // for non 2.5Gb connection
    let status = read_reg(info, IGC_STATUS)?;
    if status & IGC_STATUS_2P5_SKU != 0 && status & IGC_STATUS_2P5_SKU_OVER == 0 {
        reg |= (sc_dmac * 5) >> 6;
    } else {
        reg |= sc_dmac >> 5;
    }

    write_reg(info, IGC_DMACR, reg)?;

    write_reg(info, IGC_DMCRTRH, 0)?;

    // Set the interval before transition
    let mut reg = read_reg(info, IGC_DMCTLX)?;
    reg |= IGC_DMCTLX_DCFLUSH_DIS;

    // in 2.5Gb connection, TTLX unit is 0.4 usec
    // which is 0x4*2 = 0xA. But delay is still 4 usec
    let status = read_reg(info, IGC_STATUS)?;
    if status & IGC_STATUS_2P5_SKU != 0 && status & IGC_STATUS_2P5_SKU_OVER == 0 {
        reg |= 0xA;
    } else {
        reg |= 0x4;
    }

    write_reg(info, IGC_DMCTLX, reg)?;

    // free space in tx packet buffer to wake from DMA coal
    write_reg(
        info,
        IGC_DMCTXTH,
        (IGC_TXPBSIZE - (2 * max_frame_size)) >> 6,
    )?;

    // make low power state decision controlled by DMA coal
    let mut reg = read_reg(info, IGC_PCIEMISC)?;
    reg &= !IGC_PCIEMISC_LX_DECISION;
    write_reg(info, IGC_PCIEMISC, reg)?;

    Ok(())
}

fn igc_reset(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    sc_fc: IgcFcMode,
    sc_dmac: u32,
) -> Result<(), IgcDriverErr> {
    use igc_regs::*;

    // Let the firmware know the OS is in control
    igc_get_hw_control(info)?;

    // Packet Buffer Allocation (PBA)
    // Writing PBA sets the receive portion of the buffer
    // the remainder is used for the transmit buffer.
    let pba = IGC_PBA_34K;

    // These parameters control the automatic generation (Tx) and
    // response (Rx) to Ethernet PAUSE frames.
    // - High water mark should allow for at least two frames to be
    //   received after sending an XOFF.
    // - Low water mark works best when it is very near the high water mark.
    //   This allows the receiver to restart by sending XON when it has
    //   drained a bit. Here we use an arbitrary value of 1500 which will
    //   restart after one full frame is pulled from the buffer. There
    //   could be several smaller frames in the buffer and if so they will
    //   not trigger the XON until their total number reduces the buffer
    //   by 1500.
    // - The pause time is fairly large at 1000 x 512ns = 512 usec.
    let rx_buffer_size = (pba & 0xffff) << 10;
    hw.fc.high_water = rx_buffer_size - roundup2(hw.mac.max_frame_size, 1024);
    // 16-byte granularity
    hw.fc.low_water = hw.fc.high_water - 16;

    // locally set flow control value?
    if sc_fc != IgcFcMode::None {
        hw.fc.requested_mode = sc_fc;
    } else {
        hw.fc.requested_mode = IgcFcMode::Full;
    }

    hw.fc.pause_time = IGC_FC_PAUSE_TIME;

    hw.fc.send_xon = true;

    // Issue a global reset
    ops.reset_hw(info, hw)?;
    write_reg(info, IGC_WUC, 0)?;

    // and a re-init
    ops.init_hw(info, hw)?;

    // Setup DMA Coalescing
    igc_init_dmac(info, hw, pba, sc_dmac)?;

    write_reg(info, IGC_VET, ETHER_TYPE_VLAN as u32)?;
    ops.get_info(info, hw)?;
    ops.check_for_link(info, hw)?;

    Ok(())
}

/// igc_get_hw_control sets the {CTRL_EXT|FWSM}:DRV_LOAD bit.
/// For ASF and Pass Through versions of f/w this means
/// that the driver is loaded. For AMT version type f/w
/// this means that the network i/f is open.
fn igc_get_hw_control(info: &mut PCIeInfo) -> Result<(), IgcDriverErr> {
    let ctrl_ext = read_reg(info, igc_regs::IGC_CTRL_EXT)?;
    write_reg(
        info,
        igc_regs::IGC_CTRL_EXT,
        ctrl_ext | IGC_CTRL_EXT_DRV_LOAD,
    )
}

/// igc_release_hw_control resets {CTRL_EXT|FWSM}:DRV_LOAD bit.
/// For ASF and Pass Through versions of f/w this means that
/// the driver is no longer loaded. For AMT versions of the
/// f/w this means that the network i/f is closed.
fn igc_release_hw_control(info: &mut PCIeInfo) -> Result<(), IgcDriverErr> {
    let ctrl_ext = read_reg(info, igc_regs::IGC_CTRL_EXT)?;
    write_reg(
        info,
        igc_regs::IGC_CTRL_EXT,
        ctrl_ext & !IGC_CTRL_EXT_DRV_LOAD,
    )
}

fn roundup2<T>(size: T, unit: T) -> T
where
    T: Copy
        + core::ops::Add<Output = T>
        + core::ops::BitAnd<Output = T>
        + core::ops::Sub<Output = T>
        + core::ops::Not<Output = T>
        + From<u8>,
{
    let one = T::from(1);
    (size + unit - one) & !(unit - one)
}

impl IgcInner {
    fn new(
        ops: Box<dyn IgcOperations + Sync + Send>,
        info: PCIeInfo,
        hw: IgcHw,
        link_info: LinkInfo,
        queue_info: QueueInfo,
    ) -> Self {
        Self {
            ops,
            info,
            hw,
            link_info,
            mta: Box::new([[0; ETHER_ADDR_LEN]; MAX_NUM_MULTICAST_ADDRESSES]),
            multicast_addrs: MulticastAddrs::new(),
            if_flags: NetFlags::BROADCAST | NetFlags::SIMPLEX | NetFlags::MULTICAST,
            queue_info,
            capabilities: NetCapabilities::CSUM_IPv4
                | NetCapabilities::CSUM_TCPv4
                | NetCapabilities::CSUM_UDPv4
                | NetCapabilities::CSUM_TCPv6
                | NetCapabilities::CSUM_UDPv6
                | NetCapabilities::VLAN_MTU
                | NetCapabilities::VLAN_HWTAGGING,
        }
    }

    fn igc_iff(&mut self) -> Result<(), IgcDriverErr> {
        use igc_regs::*;

        for addr in self.mta.iter_mut() {
            *addr = [0; ETHER_ADDR_LEN];
        }

        let mut reg_rctl = read_reg(&self.info, IGC_RCTL)?;
        reg_rctl &= !(IGC_RCTL_UPE | IGC_RCTL_MPE);
        self.if_flags.remove(NetFlags::ALLMULTI);

        if self.if_flags.contains(NetFlags::PROMISC)
            || self.multicast_addrs.len() > MAX_NUM_MULTICAST_ADDRESSES
        {
            self.if_flags.insert(NetFlags::ALLMULTI);
            reg_rctl |= IGC_RCTL_MPE;
            if self.if_flags.contains(NetFlags::PROMISC) {
                reg_rctl |= IGC_RCTL_UPE;
            }
        } else {
            for (addr, mta) in self.multicast_addrs.iter().zip(self.mta.iter_mut()) {
                *mta = *addr;
            }

            self.ops.update_mc_addr_list(
                &mut self.info,
                &mut self.hw,
                &self.mta[0..self.multicast_addrs.len()],
            )?;
        }

        write_reg(&self.info, IGC_RCTL, reg_rctl)?;

        Ok(())
    }

    /// This routine disables all traffic on the adapter by issuing a
    /// global reset on the MAC.
    fn igc_stop(&mut self) -> Result<(), IgcDriverErr> {
        use igc_regs::*;

        // Tell the stack that the interface is no longer active.
        self.if_flags.remove(NetFlags::RUNNING);

        // Disable interrupts.
        igc_disable_intr(&mut self.info)?;

        self.ops.reset_hw(&mut self.info, &mut self.hw)?;
        write_reg(&self.info, IGC_WUC, 0)?;

        // TODO: Free transmit structures.

        // Free receive structures.
        for q in self.queue_info.que.iter_mut() {
            let mut node = MCSNode::new();
            let mut rx = q.rx.lock(&mut node);
            rx.read_buf = None; // Free the read buffer
        }

        // Update link status.
        igc_update_link_status(
            self.ops.as_ref(),
            &mut self.info,
            &mut self.hw,
            &mut self.link_info,
        )?;

        Ok(())
    }

    fn igc_init(&mut self) -> Result<(), IgcDriverErr> {
        use igc_regs::*;

        self.igc_stop()?;

        // Put the address into the receive address array.
        self.ops.rar_set(&mut self.info, &self.hw.mac.addr, 0)?;

        // Initialize the hardware.
        let sc_fc = IgcFcMode::None; // No flow control request.
        let sc_dmac = 0; // DMA Coalescing is disabled by default.

        igc_reset(
            self.ops.as_ref(),
            &mut self.info,
            &mut self.hw,
            sc_fc,
            sc_dmac,
        )?;
        igc_update_link_status(
            self.ops.as_ref(),
            &mut self.info,
            &mut self.hw,
            &mut self.link_info,
        )?;

        // Setup VLAN support, basic and offload if available.
        write_reg(&self.info, IGC_VET, ETHER_TYPE_VLAN as u32)?;

        // Prepare transmit descriptors and buffers.
        if let Err(e) = self.igc_setup_transmit_structures() {
            log::error!("igc: Could not setup transmit structures: {e:?}");
            self.igc_stop()?;
            return Err(e);
        }
        igc_initialize_transmit_unit(&self.info, &self.queue_info.que)?;

        // Prepare receive descriptors and buffers.
        if let Err(e) = self.igc_setup_receive_structures() {
            log::error!("igc: Could not setup receive structures: {e:?}");
            self.igc_stop()?;
            return Err(e);
        }
        igc_initialize_receive_unit(&self.info, &self.hw, &self.queue_info.que, sc_fc)?;

        if self.capabilities.contains(NetCapabilities::VLAN_HWTAGGING) {
            let mut ctrl = read_reg(&self.info, IGC_CTRL)?;
            ctrl |= IGC_CTRL_VME;
            write_reg(&self.info, IGC_CTRL, ctrl)?;
        }

        // Setup multicast table.
        self.igc_iff()?;

        igc_clear_hw_cntrs_base_generic(&self.info)?;

        let (msix_queuesmask, msix_linkmask) =
            igc_configure_queues(&self.info, &self.queue_info.que)?;

        // This clears any pending interrupts
        read_reg(&self.info, IGC_ICR)?;
        write_reg(&self.info, IGC_ICS, IGC_ICS_LSC)?;

        // The driver can now take control from firmware.
        igc_get_hw_control(&mut self.info)?;

        igc_set_eee_i225(&self.info, &self.hw, true, true, true)?;

        for (i, q) in self.queue_info.que.iter().enumerate() {
            let mut node = MCSNode::new();
            let mut rx = q.rx.lock(&mut node);
            if let Err(e) = rx.igc_rxfill() {
                log::error!("igc: Unable to fill any rx descriptors");
                drop(rx);
                self.igc_stop()?;
                return Err(e);
            }
            write_reg(
                &self.info,
                IGC_RDT(i),
                ((rx.last_desc_filled + 1) % rx.slots) as u32,
            )?;
        }

        igc_enable_intr(&mut self.info, msix_queuesmask, msix_linkmask)?;

        self.if_flags.insert(NetFlags::RUNNING);

        Ok(())
    }

    fn igc_setup_transmit_structures(&mut self) -> Result<(), IgcDriverErr> {
        for q in self.queue_info.que.iter() {
            let mut node = MCSNode::new();
            let mut tx = q.tx.lock(&mut node);
            tx.igc_setup_transmit_ring()?;
        }

        Ok(())
    }

    fn igc_setup_receive_structures(&mut self) -> Result<(), IgcDriverErr> {
        for q in self.queue_info.que.iter() {
            let mut node = MCSNode::new();
            let mut rx = q.rx.lock(&mut node);
            rx.igc_setup_receive_ring(&self.info)?;
        }

        Ok(())
    }
}

fn igc_attach_and_hw_control(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<LinkInfo, PCIeDeviceErr> {
    use PCIeDeviceErr::InitFailure;

    ops.reset_hw(info, hw).or(Err(InitFailure))?;

    // Make sure we have a good EEPROM before we read from it.
    if ops.validate(info, hw).is_err() {
        // Some PCI-E parts fail the first check due to
        // the link being in sleep state, call it again,
        // if it fails a second time its a real issue.
        ops.validate(info, hw).or(Err(InitFailure))?;
    }

    ops.read_mac_addr(info, hw).or(Err(InitFailure))?;

    if !igc_is_valid_ether_addr(&hw.mac.addr) {
        log::error!("igc: Invalid MAC address read from EEPROM");
        return Err(PCIeDeviceErr::InitFailure);
    }

    let sc_fc = IgcFcMode::None; // No flow control request.
    let sc_dmac = 0; // DMA Coalescing is disabled by default.

    igc_reset(ops, info, hw, sc_fc, sc_dmac).or(Err(InitFailure))?;

    hw.mac.get_link_status = true;
    let mut link_info = LinkInfo {
        link_active: false,
        link_speed: None,
        link_duplex: None,
        link_status: LinkStatus::Down,
    };
    igc_update_link_status(ops, info, hw, &mut link_info).or(Err(InitFailure))?;

    // The driver can now take control from firmware
    igc_get_hw_control(info).or(Err(InitFailure))?;

    Ok(link_info)
}

fn igc_is_valid_ether_addr(addr: &[u8; 6]) -> bool {
    // Check if the address is a multicast address or a zero address.
    !(addr[0] & 1 != 0 || addr.iter().all(|&x| x == 0))
}

/// Allocate PCI resources for the IGC device.
/// This function initialize IRQs for the IGC device,
/// and returns IRQs for the Rx/Tx queues and an IRQ for events.
fn igc_allocate_pci_resources(info: &mut PCIeInfo) -> Result<(Vec<IRQ>, IRQ), PCIeDeviceErr> {
    let bfd = info.get_bfd();
    let segment_number = info.segment_group as usize;

    let msix = info.get_msix_mut().ok_or(PCIeDeviceErr::InitFailure)?;

    let nmsix = msix.get_table_size();

    if nmsix <= 1 {
        log::error!("igc: not enough msi-x vectors");
        return Err(PCIeDeviceErr::InitFailure);
    }

    let nmsix = nmsix - 1; // Give one vector to events.

    let nqueues = if nmsix > IGC_MAX_VECTORS {
        IGC_MAX_VECTORS
    } else {
        nmsix
    };

    // Initialize the IRQs for the Rx/Tx queues.
    let mut irqs_queues = Vec::with_capacity(nqueues as usize);

    for q in 0..nqueues {
        let irq_name_rxtx = format!("{DEVICE_SHORT_NAME}-{bfd}-RxTx{q}");
        let mut irq_rxtx = msix
            .register_handler(
                irq_name_rxtx.into(),
                Box::new(move |irq| {
                    awkernel_lib::net::net_interrupt(irq);
                }),
                segment_number,
                awkernel_lib::cpu::raw_cpu_id() as u32,
                q as usize,
            )
            .or(Err(PCIeDeviceErr::InitFailure))?;
        irq_rxtx.enable();
        irqs_queues.push(irq_rxtx);
    }

    // Initialize the IRQs for the events.
    let irq_name_other = format!("{DEVICE_SHORT_NAME}-{bfd}-Other");
    let mut irq_other = msix
        .register_handler(
            irq_name_other.into(),
            Box::new(move |irq| {
                awkernel_lib::net::net_interrupt(irq);
            }),
            segment_number,
            awkernel_lib::cpu::raw_cpu_id() as u32,
            irqs_queues.len(),
        )
        .or(Err(PCIeDeviceErr::InitFailure))?;
    irq_other.enable();

    Ok((irqs_queues, irq_other))
}

fn igc_allocate_queues(
    info: &PCIeInfo,
    irqs: &[IRQ],
) -> Result<(Vec<Queue>, BTreeMap<u16, usize>), PCIeDeviceErr> {
    assert!(core::mem::size_of::<RxRing>() % PAGESIZE == 0);
    assert!(core::mem::size_of::<TxRing>() % PAGESIZE == 0);

    let mut irq_to_queue = BTreeMap::new();
    let mut que = Vec::with_capacity(irqs.len());

    for (n, irq) in irqs.iter().enumerate() {
        let irq_num = irq.get_irq();
        irq_to_queue.insert(irq_num, n);

        let rx = Mutex::new(Rx {
            next_to_check: 0,
            last_desc_filled: 0,
            rx_desc_ring: DMAPool::new(
                info.segment_group as usize,
                core::mem::size_of::<RxRing>() / PAGESIZE,
            )
            .ok_or(PCIeDeviceErr::InitFailure)?,
            read_buf: None,
            slots: IGC_DEFAULT_RXD,
            dropped_pkts: 0,
        });

        let tx = Mutex::new(Tx {
            next_avail_desc: 0,
            next_to_clean: 0,
            tx_desc_ring: DMAPool::new(
                info.segment_group as usize,
                core::mem::size_of::<TxRing>() / PAGESIZE,
            )
            .ok_or(PCIeDeviceErr::InitFailure)?,
        });

        que.push(Queue { rx, tx, me: n });
    }

    Ok((que, irq_to_queue))
}

fn igc_update_link_status(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    link_info: &mut LinkInfo,
) -> Result<(), IgcDriverErr> {
    if hw.mac.get_link_status {
        ops.check_for_link(info, hw)?;
    }

    link_info.link_status = if read_reg(info, igc_regs::IGC_STATUS)? & IGC_STATUS_LU != 0 {
        if !link_info.link_active {
            let (speed, duplex) = ops.get_link_up_info(info, hw)?;
            link_info.link_speed = Some(speed);
            link_info.link_duplex = Some(duplex);
            link_info.link_active = true;
        }

        if link_info.link_duplex == Some(IgcDuplex::Full) {
            LinkStatus::UpFullDuplex
        } else {
            LinkStatus::UpHalfDuplex
        }
    } else {
        if link_info.link_active {
            link_info.link_speed = None;
            link_info.link_duplex = None;
            link_info.link_active = false;
        }
        LinkStatus::Down
    };

    Ok(())
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum QueueType {
    Rx,
    Tx,
}

fn igc_set_queues(
    info: &PCIeInfo,
    entry: u32,
    vector: u32,
    qtype: QueueType,
) -> Result<(), IgcDriverErr> {
    let index = (entry >> 1) as usize;
    let mut ivar = read_reg_array(info, igc_regs::IGC_IVAR0, index)?;

    match qtype {
        QueueType::Tx => {
            if entry & 1 != 0 {
                ivar &= 0x00FFFFFF;
                ivar |= (vector | igc_defines::IGC_IVAR_VALID) << 24;
            } else {
                ivar &= 0xFFFF00FF;
                ivar |= (vector | igc_defines::IGC_IVAR_VALID) << 8;
            }
        }
        QueueType::Rx => {
            if entry & 1 != 0 {
                ivar &= 0xFF00FFFF;
                ivar |= (vector | igc_defines::IGC_IVAR_VALID) << 16;
            } else {
                ivar &= 0xFFFFFF00;
                ivar |= vector | igc_defines::IGC_IVAR_VALID;
            }
        }
    }
    write_reg_array(info, igc_regs::IGC_IVAR0, index, ivar)?;

    Ok(())
}

fn igc_enable_intr(
    info: &mut PCIeInfo,
    msix_queuesmask: u32,
    msix_linkmask: u32,
) -> Result<(), IgcDriverErr> {
    use igc_regs::*;

    let mask = msix_queuesmask | msix_linkmask;
    write_reg(info, IGC_EIAC, mask)?;
    write_reg(info, IGC_EIAM, mask)?;
    write_reg(info, IGC_EIMS, mask)?;
    write_reg(info, IGC_IMS, IGC_IMS_LSC)?;
    write_flush(info)?;

    Ok(())
}

fn igc_disable_intr(info: &mut PCIeInfo) -> Result<(), IgcDriverErr> {
    use igc_regs::*;

    write_reg(info, IGC_EIMC, 0xffffffff)?;
    write_reg(info, IGC_EIAC, 0)?;
    write_reg(info, IGC_IMC, 0xffffffff)?;
    write_flush(info)?;

    Ok(())
}

fn igc_configure_queues(info: &PCIeInfo, queues: &[Queue]) -> Result<(u32, u32), IgcDriverErr> {
    use igc_regs::*;

    // First turn on RSS capability
    write_reg(
        info,
        IGC_GPIE,
        IGC_GPIE_MSIX_MODE | IGC_GPIE_EIAME | IGC_GPIE_PBA | IGC_GPIE_NSICR,
    )?;

    // Set the starting interrupt rate
    let newitr = (4000000 / MAX_INTS_PER_SEC) & 0x7FFC | IGC_EITR_CNT_IGNR;

    let mut msix_queuesmask = 0;

    // Turn on MSI-X
    for q in queues.iter() {
        // RX entries
        igc_set_queues(info, q.me as u32, q.me as u32, QueueType::Rx)?;
        // TX entries
        igc_set_queues(info, q.me as u32, q.me as u32, QueueType::Tx)?;
        msix_queuesmask |= 1 << q.me;
        write_reg(info, IGC_EITR(q.me), newitr)?;
    }

    // And for the link interrupt
    let ivar = (queues.len() as u32 | IGC_IVAR_VALID) << 8;
    let msix_linkmask = 1 << queues.len();
    write_reg(info, IGC_IVAR_MISC, ivar)?;

    Ok((msix_queuesmask, msix_linkmask))
}

impl Tx {
    fn igc_setup_transmit_ring(&mut self) -> Result<(), IgcDriverErr> {
        // Clear the old ring contents
        for desc in self.tx_desc_ring.as_mut() {
            let read = unsafe { &mut desc.read };
            read.buffer_addr = 0;
            read.cmd_type_len = 0;
            read.olinfo_status = 0;
        }

        // Reset indices
        self.next_avail_desc = 0;
        self.next_to_clean = 0;

        Ok(())
    }
}

fn igc_initialize_transmit_unit(info: &PCIeInfo, queues: &[Queue]) -> Result<(), IgcDriverErr> {
    use igc_regs::*;

    // Setup the Base and Length of the TX descriptor ring.
    for (i, q) in queues.iter().enumerate() {
        let mut node = MCSNode::new();
        let txr = q.tx.lock(&mut node);

        let bus_addr = txr.tx_desc_ring.get_phy_addr();

        // Base and len of TX ring
        write_reg(info, IGC_TDLEN(i), txr.tx_desc_ring.get_size() as u32)?;
        write_reg(info, IGC_TDBAH(i), (bus_addr.as_usize() >> 32) as u32)?;
        write_reg(info, IGC_TDBAL(i), bus_addr.as_usize() as u32)?;

        // Init the HEAD/TAIL indices
        write_reg(info, IGC_TDT(i), 0)?;
        write_reg(info, IGC_TDH(i), 0)?;

        let mut txdctl = 0; // Clear txdctl
        txdctl |= 0x1f; // PTHRESH
        txdctl |= 1 << 8; // HTHREASH
        txdctl |= 1 << 16; // WTHREASH
        txdctl |= 1 << 22; // Reserved bit 22 must always be 1
        txdctl |= IGC_TXDCTL_GRAN;
        txdctl |= 1 << 25; // LWTHREASH

        write_reg(info, IGC_TXDCTL(i), txdctl)?;
    }

    // Program the Transmit Control Register
    let mut tctl = read_reg(info, IGC_TCTL)?;
    tctl &= !IGC_TCTL_CT;
    tctl |= IGC_TCTL_PSP | IGC_TCTL_RTLC | IGC_TCTL_EN | (IGC_COLLISION_THRESHOLD << IGC_CT_SHIFT);

    // This write will effectively turn on the transmit unit.
    write_reg(info, IGC_TCTL, tctl)?;

    Ok(())
}

impl Rx {
    /// Initialize a receive ring and its buffers.
    fn igc_setup_receive_ring(&mut self, info: &PCIeInfo) -> Result<(), IgcDriverErr> {
        // Clear the ring contents
        for desc in self.rx_desc_ring.as_mut() {
            let read = unsafe { &mut desc.read };
            read.hdr_addr = 0;
            read.pkt_addr = 0;
        }

        // Setup our descriptor indices.
        self.next_to_check = 0;
        self.last_desc_filled = self.rx_desc_ring.as_ref().len() - 1;

        let read_buf = DMAPool::new(
            info.segment_group as usize,
            core::mem::size_of::<RxBuffer>() / PAGESIZE,
        )
        .ok_or(IgcDriverErr::DmaPoolAlloc)?;
        self.read_buf = Some(read_buf);

        Ok(())
    }

    fn igc_rxfill(&mut self) -> Result<bool, IgcDriverErr> {
        let mut i = self.last_desc_filled;
        let mut post = false;

        let Some(read_buf) = self.read_buf.as_mut() else {
            return Err(IgcDriverErr::DmaPoolAlloc);
        };

        while self.slots > 0 {
            i += 1;
            if i == self.rx_desc_ring.as_ref().len() {
                i = 0;
            }

            let phy_addr = read_buf.get_phy_addr() + i * RX_BUFFER_SIZE;
            self.rx_desc_ring.as_mut()[i].read.pkt_addr = (phy_addr.as_usize() as u64).to_le();

            self.last_desc_filled = i;
            self.slots -= 1;

            post = true;
        }

        Ok(post)
    }
}

/// Initialise the RSS mapping for NICs that support multiple transmit/
/// receive rings.
fn igc_initialize_rss_mapping(info: &PCIeInfo, sc_nqueues: usize) -> Result<(), IgcDriverErr> {
    use igc_regs::*;

    // The redirection table controls which destination
    // queue each bucket redirects traffic to.
    // Each DWORD represents four queues, with the LSB
    // being the first queue in the DWORD.
    //
    // This just allocates buckets to queues using round-robin
    // allocation.
    //
    // NOTE: It Just Happens to line up with the default
    // RSS allocation method.

    // Warning FM follows
    let shift = 0;
    let mut reta = 0;
    for i in 0..128 {
        let mut queue_id = i % sc_nqueues;
        // Adjust if require
        queue_id <<= shift;

        // The low 8 bits are for hash value (n+0);
        // The next 8 bits are for hash value (n+1), etc.
        reta >>= 8;
        reta |= (queue_id) << 24;
        if i & 3 == 3 {
            write_reg(info, IGC_RETA(i >> 2), reta as u32)?;
            reta = 0;
        }
    }

    // MRQC: Multiple Receive Queues Command
    // Set queuing to RSS control, number depends on the device.
    let mut mrqc = IGC_MRQC_ENABLE_RSS_4Q;

    // Set up random bits
    let mut rss_key: [u32; 10] = [0; 10];
    let rss_key_u8 = unsafe { core::mem::transmute::<&mut [u32; 10], &mut [u8; 40]>(&mut rss_key) };
    stoeplitz_to_key(rss_key_u8);

    // Now fill our hash function seeds
    for (i, rk) in rss_key.iter().enumerate() {
        write_reg_array(info, IGC_RSSRK(0), i, *rk)?;
    }

    // Configure the RSS fields to hash upon.
    mrqc |= IGC_MRQC_RSS_FIELD_IPV4 | IGC_MRQC_RSS_FIELD_IPV4_TCP;
    mrqc |= IGC_MRQC_RSS_FIELD_IPV6 | IGC_MRQC_RSS_FIELD_IPV6_TCP;
    mrqc |= IGC_MRQC_RSS_FIELD_IPV6_TCP_EX;

    write_reg(info, IGC_MRQC, mrqc)?;

    Ok(())
}

fn igc_initialize_receive_unit(
    info: &PCIeInfo,
    hw: &IgcHw,
    queues: &[Queue],
    sc_fc: IgcFcMode,
) -> Result<(), IgcDriverErr> {
    use igc_regs::*;

    // Make sure receives are disabled while setting
    // up the descriptor ring.
    let mut rctl = read_reg(info, IGC_RCTL)?;
    write_reg(info, IGC_RCTL, rctl & !IGC_RCTL_EN)?;

    // Setup the Receive Control Register
    rctl &= !(3 << IGC_RCTL_MO_SHIFT);
    rctl |= IGC_RCTL_EN
        | IGC_RCTL_BAM
        | IGC_RCTL_LBM_NO
        | IGC_RCTL_RDMTS_HALF
        | (hw.mac.mc_filter_type << IGC_RCTL_MO_SHIFT);

    // Do not store bad packets
    rctl &= !IGC_RCTL_SBP;

    // Enable Long Packet receive
    if hw.mac.max_frame_size != ETHER_MAX_LEN as u32 {
        rctl |= IGC_RCTL_LPE;
    }

    // Strip the CRC
    rctl |= IGC_RCTL_SECRC;

    // Set the interrupt throttling rate. Value is calculated
    // as DEFAULT_ITR = 1/(MAX_INTS_PER_SEC * 256ns)
    write_reg(info, IGC_ITR, DEFAULT_ITR)?;

    let mut rxcsum = read_reg(info, IGC_RXCSUM)?;
    rxcsum &= !IGC_RXCSUM_PCSD;

    if queues.len() > 1 {
        rxcsum |= IGC_RXCSUM_PCSD;
    }

    write_reg(info, IGC_RXCSUM, rxcsum)?;

    if queues.len() > 1 {
        igc_initialize_rss_mapping(info, queues.len())?;
    }

    let mut srrctl = 2048 >> IGC_SRRCTL_BSIZEPKT_SHIFT;
    rctl |= IGC_RCTL_SZ_2048;

    // If TX flow control is disabled and there's > 1 queue defined,
    // enable DROP.
    //
    // This drops frames rather than hanging the RX MAC for all queues.
    if queues.len() > 1 && matches!(sc_fc, IgcFcMode::None | IgcFcMode::RxPause) {
        srrctl |= IGC_SRRCTL_DROP_EN;
    }

    // Setup the Base and Length of the RX descriptor rings.
    for (i, q) in queues.iter().enumerate() {
        write_reg(info, IGC_RXDCTL(i), 0)?;

        let mut node = MCSNode::new();
        let rxr = q.rx.lock(&mut node);

        let bus_addr = rxr.rx_desc_ring.get_phy_addr();

        srrctl |= IGC_SRRCTL_DESCTYPE_ADV_ONEBUF;

        write_reg(info, IGC_RDLEN(i), rxr.rx_desc_ring.get_size() as u32)?;
        write_reg(info, IGC_RDBAH(i), (bus_addr.as_usize() >> 32) as u32)?;
        write_reg(info, IGC_RDBAL(i), bus_addr.as_usize() as u32)?;
        write_reg(info, IGC_SRRCTL(i), srrctl)?;

        // Setup the Head and Tail Descriptor Pointers
        write_reg(info, IGC_RDH(i), 0)?;
        write_reg(info, IGC_RDT(i), 0)?;

        // Enable this Queue
        let mut rxdctl = read_reg(info, IGC_RXDCTL(i))?;
        rxdctl |= IGC_RXDCTL_QUEUE_ENABLE;
        rxdctl &= 0xfff00000;
        rxdctl |= IGC_RX_PTHRESH;
        rxdctl |= IGC_RX_HTHRESH << 8;
        rxdctl |= IGC_RX_WTHRESH << 16;
        write_reg(info, IGC_RXDCTL(i), rxdctl)?;
    }

    // Make sure VLAN Filters are off
    rctl &= !IGC_RCTL_VFE;

    // Write out the settings
    write_reg(info, IGC_RCTL, rctl)?;

    Ok(())
}
