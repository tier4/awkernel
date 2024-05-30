//! # Intel 10 Gigabit Ethernet Controller

use crate::pcie::{
    capability::msi::MultipleMessage, intel::ixgbe::ixgbe_hw::MacType, PCIeDevice, PCIeDeviceErr,
    PCIeInfo,
};
use alloc::{
    borrow::Cow,
    boxed::Box,
    collections::{BTreeMap, BTreeSet},
    format,
    sync::Arc,
    vec::Vec,
};
use awkernel_async_lib_verified::ringq::RingQ;
use awkernel_lib::{
    addr::{virt_addr::VirtAddr, Addr},
    console,
    delay::wait_microsec,
    dma_pool::DMAPool,
    interrupt::IRQ,
    net::{
        ether::{
            extract_headers, EtherExtracted, EtherHeader, NetworkHdr, TransportHdr, ETHER_CRC_LEN,
            ETHER_HDR_LEN, ETHER_MAX_LEN, ETHER_TYPE_VLAN,
        },
        in_cksum::in_pseudo,
        ip::Ip,
        ipv6::Ip6Hdr,
        net_device::{
            EtherFrameBuf, EtherFrameRef, LinkStatus, NetCapabilities, NetDevError, NetDevice,
            NetFlags, PacketHeaderFlags,
        },
        tcp::TCPHdr,
        udp::UDPHdr,
    },
    paging::PAGESIZE,
    sync::{
        mutex::{MCSNode, Mutex},
        rwlock::RwLock,
    },
};
use core::{
    fmt::{self, write, Debug},
    mem,
};
use memoffset::offset_of;
use rand::rngs::SmallRng;
use rand::Rng;
use rand::SeedableRng;

mod ixgbe_hw;
mod ixgbe_operations;
mod ixgbe_x540;

#[allow(dead_code)]
mod ixgbe_regs;

use ixgbe_hw::{get_num_queues, IxgbeHw};
use ixgbe_regs::*;

use self::ixgbe_operations::IxgbeOperations;

const DEVICE_NAME: &str = "Intel 10 Gigabit Ethernet Controller";
const DEVICE_SHORT_NAME: &str = "ixgbe";

enum QueueStatus {
    IxgbeQueueIdle,
    IxgbeQueueWorking,
    IxgbeQueueHung,
}

pub const MAX_NUM_MULTICAST_ADDRESSES: usize = 128;

const MCLSHIFT: u32 = 11;
const MCLBYTES: u32 = 1 << MCLSHIFT;
const MAXMCLBYTES: u32 = 64 * 1024;

type TxRing = [AdvTxDesc; DEFAULT_TXD];
type TxBuffer = [[u8; MCLBYTES as usize]; DEFAULT_TXD];

type RxRing = [AdvRxDesc; DEFAULT_RXD];
type RxBuffer = [[u8; MCLBYTES as usize]; DEFAULT_RXD];

pub struct Tx {
    tx_desc_head: usize,
    tx_desc_tail: usize,
    tx_desc_ring: DMAPool<TxRing>,
    txd_cmd: u32,
    //queue_status: QueueStatus,
    write_buf: Option<DMAPool<TxBuffer>>,
}
pub struct Rx {
    rx_desc_head: u32,
    rx_desc_tail: usize,
    rx_desc_ring: DMAPool<RxRing>,
    read_buf: Option<DMAPool<RxBuffer>>,
}

pub struct Queue {
    tx: Mutex<Tx>,
    rx: Mutex<Rx>,
    me: usize,
}

#[derive(Clone, Copy)]
struct TxRead {
    buffer_addr: u64, // Address of descriptor's data buf
    cmd_type_len: u32,
    olinfo_status: u32,
}

#[derive(Clone, Copy)]
struct TxWb {
    rsvd: u64, // Reserved
    nxtseq_seed: u32,
    status: u32,
}

union AdvTxDesc {
    read: TxRead,
    wb: TxWb,
}

#[derive(Clone, Copy)]
struct RxRead {
    pkt_addr: u64, // Packet buffer address
    hdr_addr: u64, // Header buffer address
}

#[derive(Clone, Copy)]
struct RxWb {
    lower_lo_dword: u32,
    lower_hi_dword: u32,
    upper_status_error: u32,
    upper_length: u16,
    upper_vlan: u16,
}

union AdvRxDesc {
    data: [u64; 2],
    read: RxRead,
    wb: RxWb,
}

struct AdvTxContextDescriptor {
    vlan_macip_lens: u32,
    seqnum_seed: u32,
    type_tucmd_mlhl: u32,
    mss_l4len_idx: u32,
}

struct IxgbeInner {
    info: PCIeInfo,
    hw: ixgbe_hw::IxgbeHw,
    ops: Box<dyn IxgbeOperations>,
    flags: NetFlags,
    capabilities: NetCapabilities,
    link_active: bool,
    link_speed: u32,
    link_state: ixgbe_hw::LinkState,
    pcie_int: PCIeInt,
    multicast_addr: BTreeSet<[u8; 6]>,
    max_frame_size: u16,
    //shadow_vfta: [u32; IXGBE_VFTA_SIZE],
    irq_to_rx_tx_link: BTreeMap<u16, IRQRxTxLink>,
    //msix_mask: u32,
    is_poll_mode: bool,
}

/// Intel Gigabit Ethernet Controller driver
pub struct Ixgbe {
    // The order of lock acquisition must be as follows:
    //
    // 1. `IgbInner`'s lock
    // 2. `Queue`'s lock
    // 3. `Queue`'s unlock
    // 4. `IgbInner`'s unlock
    //
    // Otherwise, a deadlock will occur.
    que: Vec<Queue>,
    inner: RwLock<IxgbeInner>,
}

pub fn match_device(vendor: u16, id: u16) -> bool {
    ixgbe_hw::IXGBE_DEVICES.contains(&(vendor, id))
}

pub fn attach(mut info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    // Initialize PCIeInfo

    // Map the memory regions of MMIO.
    if let Err(e) = info.map_bar() {
        log::warn!("Failed to map the memory regions of MMIO: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }

    //// Read capabilities of PCIe.
    info.read_capability();

    log::info!("attach!!!!!!!!!!!!!!!!!!!");

    let ixgbe = Ixgbe::new(info)?;

    //let result = Arc::new(ixgbe);

    //awkernel_lib::net::add_interface(result.clone(), None);

    //Ok(result)
    console::print("attached!!!!!!!!!!!!!\n");
    Err(PCIeDeviceErr::NotImplemented)
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IxgbeDriverErr {
    MemoryMapFailure,
    InitializeInterrupt,
    UnknownDeviceID,
    UnknownRevisionID,
    NotPciExpress,
    NoBar0,
    NoBar1,
    Bar1IsNotMMIO,
    ReadFailure,
    NotSupported,
    FailedFlashDescriptor,
    MasterDisableTimeout,
    PhyReset,
    PhyType,
    DMAPool,
    Eeprom,
    EepromChecksum,
    Phy,
    Config,
    Param,
    MacType,
    UnknownPhy,
    LinkSetup,
    AdapterStopped,
    InvalidMacAddr,
    DeviceNotSupported,
    MasterRequestsPending,
    InvalidLinkSettings,
    AutonegNotComplete,
    ResetFailed,
    SwfwSync,
    PhyAddrInvalid,
    I2c,
    SfpNotSupported,
    SfpNotPresent,
    SfpNoInitSeqPresent,
    NoSanAddrPtr,
    FdirReinitFailed,
    EepromVersion,
    NoSpace,
    Overtemp,
    FcNotNegotiated,
    FcNotSupported,
    SfpSetupNotComplete,
    PbaSection,
    InvalidArgument,
    HostInterfaceCommand,
    OutOfMem,
    BypassFwWriteFailure,
    FeatureNotSupported,
    EepromProtectedRegion,
    FdirCmdIncomplete,
    FwRespInvalid,
    TokenRetry,
    NotImplemented,
    InvalidPacket,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IRQRxTxLink {
    RxTx(usize),
    Link,          // Link status change
    Legacy(usize), // Rx, Tx or Link
}

#[derive(Debug)]
enum PCIeInt {
    None,
    Msi(IRQ),
    MsiX(Vec<(IRQ, IRQRxTxLink)>),
}

impl From<IxgbeDriverErr> for PCIeDeviceErr {
    fn from(value: IxgbeDriverErr) -> Self {
        log::error!("ixgbe: {:?}", value);

        match value {
            IxgbeDriverErr::NotImplemented => PCIeDeviceErr::NotImplemented,
            IxgbeDriverErr::ReadFailure => PCIeDeviceErr::ReadFailure,
            IxgbeDriverErr::InvalidPacket => PCIeDeviceErr::CommandFailure,
            _ => PCIeDeviceErr::InitFailure,
        }
    }
}

impl IxgbeInner {
    fn new(mut info: PCIeInfo) -> Result<(Self, Vec<Queue>), PCIeDeviceErr> {
        let (mut hw, ops) = ixgbe_hw::IxgbeHw::new(&mut info)?;

        // Allocate our TX/RX Queues
        let mut que = Vec::new();
        let que_num = get_num_queues(&hw);
        for i in 0..que_num {
            que.push(allocate_queue(&info, i)?);
        }

        let mut irq_to_rx_tx_link = BTreeMap::new();

        let mut que = Vec::new();

        let mut is_poll_mode = true; // TODO

        // Allocate MSI-X or MSI
        let pcie_int = if let Ok(pcie_int) = allocate_msix(&hw, &mut info, &que) {
            match &pcie_int {
                PCIeInt::MsiX(irqs) => {
                    for (irq, irq_rx_tx_link) in irqs.iter() {
                        let irq = irq.get_irq();
                        irq_to_rx_tx_link.insert(irq, *irq_rx_tx_link);
                    }
                }
                _ => unreachable!(),
            }

            is_poll_mode = false;
            pcie_int
        } else {
            PCIeInt::None
        };

        //ixgbe_init_hw();
        ops.mac_init_hw(&mut info, &mut hw)?;

        ops.phy_set_power(&info, &hw, true)?;

        // setup interface
        // TODO: Check if these are correct
        let flags = NetFlags::BROADCAST | NetFlags::SIMPLEX | NetFlags::MULTICAST;
        let mut capabilities = NetCapabilities::VLAN_MTU
            | NetCapabilities::VLAN_HWTAGGING
            | NetCapabilities::CSUM_IPv4
            | NetCapabilities::CSUM_UDPv4
            | NetCapabilities::CSUM_TCPv4
            | NetCapabilities::CSUM_UDPv6
            | NetCapabilities::CSUM_TCPv6
            | NetCapabilities::TSOv4
            | NetCapabilities::TSOv6;

        if MacType::IxgbeMac82598EB <= hw.get_mac_type() {
            // flags |= NetFlags::LR0;
            capabilities |= NetCapabilities::LRO;
        }
        let max_frame_size = IXGBE_MAX_FRAME_SIZE as u16;

        // Get the PCI-E bus info and determine LAN ID
        let businfo = ops.mac_get_bus_info(&mut info, &mut hw)?;
        hw.bus = businfo;

        // Set an initial default flow control value
        hw.fc.requested_mode = ixgbe_hw::FcMode::IxgbeFcFull;

        // let hardware know driver is loaded
        let mut ctrl_ext = ixgbe_hw::read_reg(&info, IXGBE_CTRL_EXT)?;
        ctrl_ext |= IXGBE_CTRL_EXT_DRV_LOAD;
        ixgbe_hw::write_reg(&info, IXGBE_CTRL_EXT, ctrl_ext)?;

        let ixgbe = Self {
            info,
            hw,
            ops,
            flags,
            capabilities,
            link_active: false,
            link_speed: IXGBE_LINK_SPEED_UNKNOWN,
            link_state: ixgbe_hw::LinkState::LinkStateDown,
            pcie_int,
            multicast_addr: BTreeSet::new(),
            max_frame_size,
            irq_to_rx_tx_link,
            is_poll_mode,
        };

        Ok((ixgbe, que))
    }

    fn init(&mut self, que: &[Queue]) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;

        self.stop(que)?;

        // reprogram the RAR[0] in case user changed it.
        self.ops.mac_set_rar(
            &self.info,
            self.hw.mac.num_rar_entries,
            0,
            &self.hw.mac.addr,
            0,
            IXGBE_RAH_AV,
        )?;
        self.hw.addr_ctrl.rar_used_count = 1;

        if let Err(e) = self.setup_transmit_structures(que) {
            log::error!("Could not setup transmit structures");
            self.stop(que)?;
            return Err(e);
        }

        self.ops.mac_init_hw(&mut self.info, &mut self.hw)?;
        self.initialize_transmit_unit(que)?;

        // Prepare receive descriptors and buffers
        if let Err(e) = self.setup_receive_structures(que) {
            log::error!("Could not setup receieve structures");
            self.stop(que)?;
            return Err(e);
        }

        // Configure RX settings
        self.initialize_receive_unit(que)?;

        // Enable SDP & MSIX interrupts based on adapter
        self.config_gpie()?;

        // Program promiscuous mode and multicast filters.
        self.iff()?;

        // Set MRU size
        let mut mhadd = ixgbe_hw::read_reg(&self.info, IXGBE_MHADD)?;
        mhadd &= !IXGBE_MHADD_MFS_MASK;
        mhadd |= (self.max_frame_size as u32) << IXGBE_MHADD_MFS_SHIFT;
        ixgbe_hw::write_reg(&self.info, IXGBE_MHADD, mhadd)?;

        let que_num = get_num_queues(&self.hw);
        // Now enable all the queues
        for i in 0..que_num {
            let mut txdctl = ixgbe_hw::read_reg(&self.info, IXGBE_TXDCTL(i))?;
            txdctl |= IXGBE_TXDCTL_ENABLE;
            // Set WTHRESH to 8, burst writeback
            txdctl |= 8 << 16;
            // When the internal queue falls below PTHRESH (16),
            // start prefetching as long as there are at least
            // HTHRESH (1) buffers ready.
            txdctl |= (16 << 0) | (1 << 8);
            ixgbe_hw::write_reg(&self.info, IXGBE_TXDCTL(i), txdctl)?;
        }

        for que in que.iter() {
            let mut node = MCSNode::new();
            let rx = que.rx.lock(&mut node);

            let mut rxdctl = ixgbe_hw::read_reg(&self.info, IXGBE_RXDCTL(que.me))?;
            if self.hw.mac.mac_type == IxgbeMac82598EB {
                // PTHRESH = 21
                // HTHRESH = 4
                // WTHRESH = 8
                rxdctl &= !0x3FFFFF;
                rxdctl |= 0x080420;
            }
            rxdctl |= IXGBE_RXDCTL_ENABLE;
            ixgbe_hw::write_reg(&self.info, IXGBE_RXDCTL(que.me), rxdctl)?;
            for _ in 0..10 {
                if ixgbe_hw::read_reg(&self.info, IXGBE_RXDCTL(que.me))? & IXGBE_RXDCTL_ENABLE != 0
                {
                    break;
                } else {
                    wait_microsec(1);
                }
            }
            ixgbe_hw::write_flush(&self.info)?;
            ixgbe_hw::write_reg(&self.info, IXGBE_RDT(que.me), rx.rx_desc_tail as u32)?;
        }

        self.setup_vlan_hw_support(que)?;

        // Enable Receive engine
        let mut rxctrl = ixgbe_hw::read_reg(&self.info, IXGBE_RXCTRL)?;
        if self.hw.mac.mac_type == IxgbeMac82598EB {
            rxctrl |= IXGBE_RXCTRL_DMBYPS;
        }
        rxctrl |= IXGBE_RXCTRL_RXEN;
        self.ops
            .mac_enable_rx_dma(&self.info, &mut self.hw, rxctrl)?;
        // Set up MSI/X routing
        self.configure_ivars(que)?;
        /* Set up auto-mask */
        if self.hw.mac.mac_type == IxgbeMac82598EB {
            ixgbe_hw::write_reg(&self.info, IXGBE_EIAM, IXGBE_EICS_RTX_QUEUE)?;
        } else {
            ixgbe_hw::write_reg(&self.info, IXGBE_EIAM_EX(0), 0xFFFFFFFF)?;
            ixgbe_hw::write_reg(&self.info, IXGBE_EIAM_EX(1), 0xFFFFFFFF)?;
        }

        // Check on any SFP devices that need to be kick-started
        if self.hw.phy.phy_type == ixgbe_hw::PhyType::IxgbePhyNone {
            self.ops.identify_phy(&self.info, &mut self.hw)?;
            // We may be better to print error message specifically for Err(SfpNotSupported) as OpenBSD does.
        }

        // Setup interrupt moderation
        let mut itr = (4000000 / IXGBE_INTS_PER_SEC) & 0xff8;
        if self.hw.mac.mac_type != IxgbeMac82598EB {
            itr |= IXGBE_EITR_LLI_MOD | IXGBE_EITR_CNT_WDIS;
        }
        ixgbe_hw::write_reg(&self.info, IXGBE_EITR(0), itr)?;

        // Set moderation on the Link interrupt
        let linkvec = que.len();
        ixgbe_hw::write_reg(&self.info, IXGBE_EITR(linkvec), IXGBE_LINK_ITR)?;

        // Enable power to the phy
        self.ops.phy_set_power(&self.info, &self.hw, true)?;

        self.config_link();

        Ok(())
    }

    fn stop(&mut self, que: &[Queue]) -> Result<(), IxgbeDriverErr> {
        self.flags.remove(NetFlags::RUNNING);

        self.disable_intr()?;

        self.ops.mac_reset_hw(&mut self.info, &mut self.hw)?;
        self.hw.adapter_stopped = false;
        self.ops.mac_stop_adapter(&mut self.info, &mut self.hw)?;

        self.ops.mac_set_rar(
            &self.info,
            self.hw.mac.num_rar_entries,
            0,
            &self.hw.mac.addr,
            0,
            IXGBE_RAH_AV,
        )?;

        //// let hardware know driver is unloading
        //let mut ctrl_ext = ixgbe_hw::read_reg(&self.info, IXGBE_CTRL_EXT)?;
        //ctrl_ext &= !IXGBE_CTRL_EXT_DRV_LOAD;
        //ixgbe_hw::write_reg(&self.info, IXGBE_CTRL_EXT, ctrl_ext);

        for que in que.iter() {
            let mut node = MCSNode::new();
            let mut tx = que.tx.lock(&mut node);
            tx.write_buf = None;

            let mut node = MCSNode::new();
            let mut rx = que.rx.lock(&mut node);
            rx.read_buf = None;
        }

        self.update_link_status()?;

        Ok(())
    }

    fn disable_intr(&self) -> Result<(), IxgbeDriverErr> {
        match self.pcie_int {
            PCIeInt::MsiX(_) => {
                ixgbe_hw::write_reg(&self.info, IXGBE_EIAC, 0)?;
                if self.hw.get_mac_type() == MacType::IxgbeMac82598EB {
                    ixgbe_hw::write_reg(&self.info, IXGBE_EIMC, u32::MAX)?;
                } else {
                    ixgbe_hw::write_reg(&self.info, IXGBE_EIMC, 0xFFFF0000)?;
                    ixgbe_hw::write_reg(&self.info, IXGBE_EIMC_EX(0), u32::MAX)?;
                    ixgbe_hw::write_reg(&self.info, IXGBE_EIMC_EX(1), u32::MAX)?;
                }
            }
            _ => (),
        }

        ixgbe_hw::write_flush(&self.info)
    }

    fn update_link_status(&mut self) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::LinkState::*;

        let (speed, link_up) = self.ops.mac_check_link(&self.info, &self.hw, false)?;
        self.link_speed = speed;
        self.link_active = link_up;

        let mut link_state = LinkStateDown;
        if link_up {
            link_state = LinkStateFullDuplex;
            // Update any Flow Control changes
            self.ops.mac_fc_enable(&self.info, &mut self.hw)?;
        }

        if self.link_state != link_state {
            self.link_state = link_state;
        }

        Ok(())
    }

    fn setup_transmit_structures(&self, que: &[Queue]) -> Result<(), IxgbeDriverErr> {
        for que in que.iter() {
            let mut node = MCSNode::new();
            let mut tx = que.tx.lock(&mut node);
            tx.tx_desc_tail = 0;
            tx.tx_desc_head = 0;

            let tx_desc_ring = tx.tx_desc_ring.as_mut();

            let tx_buffer_size = MCLBYTES as usize * DEFAULT_TXD;
            let write_buf = DMAPool::new(
                self.info.get_segment_group() as usize,
                tx_buffer_size / PAGESIZE,
            )
            .ok_or(IxgbeDriverErr::DMAPool)?;

            let buf_phy_addr = write_buf.get_phy_addr().as_usize();

            for (i, desc) in tx_desc_ring.iter_mut().enumerate() {
                desc.read.buffer_addr = (buf_phy_addr + i * MCLBYTES as usize) as u64;
                desc.read.cmd_type_len = 0;
                desc.read.olinfo_status = 0;
            }

            tx.write_buf = Some(write_buf);
        }

        Ok(())
    }

    fn initialize_transmit_unit(&mut self, que: &[Queue]) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;

        for que in que.iter() {
            let mut node = MCSNode::new();
            let mut tx = que.tx.lock(&mut node);

            // Setup descriptor base address
            ixgbe_hw::write_reg(
                &self.info,
                IXGBE_TDBAL(que.me),
                tx.tx_desc_ring.get_phy_addr().as_usize() as u32,
            )?;
            ixgbe_hw::write_reg(
                &self.info,
                IXGBE_TDBAH(que.me),
                (tx.tx_desc_ring.get_phy_addr().as_usize() as u64 >> 32) as u32,
            )?;
            ixgbe_hw::write_reg(
                &self.info,
                IXGBE_TDLEN(que.me),
                tx.tx_desc_ring.get_size() as u32,
            )?;

            // Setup the HW Tx Head and Tail descriptor pointers
            ixgbe_hw::write_reg(&self.info, IXGBE_TDH(que.me), 0)?;
            ixgbe_hw::write_reg(&self.info, IXGBE_TDT(que.me), 0)?;

            // Setup Transmit Descriptor Cmd Settings
            tx.txd_cmd = IXGBE_TXD_CMD_IFCS;

            let mut txctrl = match self.hw.mac.mac_type {
                IxgbeMac82598EB => ixgbe_hw::read_reg(&self.info, IXGBE_DCA_TXCTRL(que.me))?,
                _ => ixgbe_hw::read_reg(&self.info, IXGBE_DCA_TXCTRL_82599(que.me))?,
            };

            txctrl &= !(IXGBE_DCA_TXCTRL_DESC_WRO_EN);

            match self.hw.mac.mac_type {
                IxgbeMac82599EB => {
                    ixgbe_hw::write_reg(&self.info, IXGBE_DCA_TXCTRL(que.me), txctrl)?
                }
                _ => ixgbe_hw::write_reg(&self.info, IXGBE_DCA_TXCTRL_82599(que.me), txctrl)?,
            }
        }

        if self.hw.mac.mac_type != IxgbeMac82598EB {
            let mut dmatxctl = ixgbe_hw::read_reg(&self.info, IXGBE_DMATXCTL)?;
            dmatxctl |= IXGBE_DMATXCTL_TE as u32;
            ixgbe_hw::write_reg(&self.info, IXGBE_DMATXCTL, dmatxctl)?;
            // Disable arbiter to set MTQC
            let mut rttdcs = ixgbe_hw::read_reg(&self.info, IXGBE_RTTDCS)?;
            rttdcs |= IXGBE_RTTDCS_ARBDIS as u32;
            ixgbe_hw::write_reg(&self.info, IXGBE_RTTDCS, rttdcs)?;
            ixgbe_hw::write_reg(&self.info, IXGBE_MTQC, IXGBE_MTQC_64Q_1PB)?;
            rttdcs &= !IXGBE_RTTDCS_ARBDIS as u32;
            ixgbe_hw::write_reg(&self.info, IXGBE_RTTDCS, rttdcs)?;
        }

        // Enable TCP/UDP padding when using TSO
        let mut hlreg = ixgbe_hw::read_reg(&self.info, IXGBE_HLREG0)?;
        hlreg |= IXGBE_HLREG0_TXPADEN;
        ixgbe_hw::write_reg(&self.info, IXGBE_HLREG0, hlreg)?;

        Ok(())
    }

    fn setup_receive_structures(&mut self, que: &[Queue]) -> Result<(), IxgbeDriverErr> {
        for que in que.iter() {
            let mut node = MCSNode::new();
            let mut rx = que.rx.lock(&mut node);

            rx.rx_desc_tail = 0;
            rx.rx_desc_head = rx.rx_desc_ring.as_ref().len() as u32 - 1;

            let rx_desc_ring = rx.rx_desc_ring.as_mut();

            let rx_buffer_size = MCLBYTES as usize * DEFAULT_RXD;
            let read_buf = DMAPool::new(
                self.info.get_segment_group() as usize,
                rx_buffer_size / PAGESIZE,
            )
            .ok_or(IxgbeDriverErr::DMAPool)?;

            let buf_phy_addr = read_buf.get_phy_addr().as_usize();

            for (i, desc) in rx_desc_ring.iter_mut().enumerate() {
                desc.data = [0; 2];
                desc.read.pkt_addr = (buf_phy_addr + i * MCLBYTES as usize) as u64;
            }

            rx.read_buf = Some(read_buf);
        }

        Ok(())
    }

    fn initialize_receive_unit(&mut self, que: &[Queue]) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;

        // Make sure receives are disabled while
        // setting up the descriptor ring
        self.ops.mac_disable_rx(&self.info, &mut self.hw)?;

        // Enable broadcasts
        let mut fctrl = ixgbe_hw::read_reg(&self.info, IXGBE_FCTRL)?;
        fctrl |= IXGBE_FCTRL_BAM;
        if self.hw.mac.mac_type == IxgbeMac82598EB {
            fctrl |= IXGBE_FCTRL_DPF;
            fctrl |= IXGBE_FCTRL_PMCF;
        }
        ixgbe_hw::write_reg(&self.info, IXGBE_FCTRL, fctrl)?;

        let mut hlreg = ixgbe_hw::read_reg(&self.info, IXGBE_HLREG0)?;
        // Always enable jumbo frame reception
        hlreg |= IXGBE_HLREG0_JUMBOEN;
        // Always enable CRC stripping
        hlreg |= IXGBE_HLREG0_RXCRCSTRP;
        ixgbe_hw::write_reg(&self.info, IXGBE_HLREG0, hlreg)?;

        let bufsz = MCLBYTES >> IXGBE_SRRCTL_BSIZEHDRSIZE_SHIFT;
        for que in que.iter() {
            let mut node = MCSNode::new();
            let rx = que.rx.lock(&mut node);

            // Setup the Base and Length of the Rx Descriptor Ring
            ixgbe_hw::write_reg(
                &self.info,
                IXGBE_RDBAL(que.me),
                rx.rx_desc_ring.get_phy_addr().as_usize() as u32,
            )?;
            ixgbe_hw::write_reg(
                &self.info,
                IXGBE_RDBAH(que.me),
                (rx.rx_desc_ring.get_phy_addr().as_usize() as u64 >> 32) as u32,
            )?;
            ixgbe_hw::write_reg(
                &self.info,
                IXGBE_RDLEN(que.me),
                rx.rx_desc_ring.get_size() as u32,
            )?;

            // Set up the SRRCTL register
            let srrctl = bufsz | IXGBE_SRRCTL_DESCTYPE_ADV_ONEBUF;
            ixgbe_hw::write_reg(&self.info, IXGBE_SRRCTL(que.me), srrctl)?;

            // Setup the HW Rx Head and Tail Descriptor Pointers
            ixgbe_hw::write_reg(&self.info, IXGBE_RDH(que.me), 0)?;
            ixgbe_hw::write_reg(&self.info, IXGBE_RDT(que.me), 0)?;
        }

        if self.hw.mac.mac_type != IxgbeMac82598EB {
            let psrtype = IXGBE_PSRTYPE_TCPHDR
                | IXGBE_PSRTYPE_UDPHDR
                | IXGBE_PSRTYPE_IPV4HDR
                | IXGBE_PSRTYPE_IPV6HDR;
            ixgbe_hw::write_reg(&self.info, IXGBE_PSRTYPE(0) as usize, psrtype)?;
        }

        let mut rxcsum = ixgbe_hw::read_reg(&self.info, IXGBE_RXCSUM)?;
        rxcsum &= !IXGBE_RXCSUM_PCSD;

        self.initialize_rss_mapping()?;
        // Setup RSS
        let que_num = get_num_queues(&self.hw);
        if que_num > 1 {
            // RSS and RX IPP Checksum are mutually exclusive
            rxcsum |= IXGBE_RXCSUM_PCSD;
        }

        // Map QPRC/QPRDC/QPTC on a per queue basis
        self.map_queue_statistics()?;

        if rxcsum & IXGBE_RXCSUM_PCSD == 0 {
            rxcsum |= IXGBE_RXCSUM_IPPCSE;
        }
        ixgbe_hw::write_reg(&self.info, IXGBE_RXCSUM, rxcsum)?;

        Ok(())
    }

    fn initialize_rss_mapping(&self) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;

        // set up random bits
        let seed = [0x12u8; 32]; // 適当なシード値
        let mut rng = SmallRng::from_seed(seed);
        let mut rss_keys = [0u32; 10];
        for i in 0..10 {
            rss_keys[i] = rng.gen::<u32>();
            //rss_keys[i] = 0;
        }

        // Set multiplier for RETA setup and table size based on MAC
        let index_mult = match self.hw.mac.mac_type {
            IxgbeMac82598EB => 0x11,
            _ => 0x1,
        };
        let table_size = match self.hw.mac.mac_type {
            IxgbeMacX550 | IxgbeMacX550EMX | IxgbeMacX550EMA => 512,
            _ => 128,
        };

        // Set up the redirection table
        let mut j = 0;
        let que_num = get_num_queues(&self.hw);
        let mut queue_id;
        let mut reta = 0;
        for i in 0..table_size {
            if j == que_num {
                j = 0;
            }
            queue_id = j * index_mult;
            // The low 8 bits are for hash value (n+0);
            // The next 8 bits are for hash value (n+1), etc.
            reta = reta >> 8;
            reta = reta | ((queue_id as u32) << 24);
            if (i & 3) == 3 {
                if i < 128 {
                    ixgbe_hw::write_reg(&self.info, IXGBE_RETA(i >> 2), reta)?;
                } else {
                    ixgbe_hw::write_reg(&self.info, IXGBE_ERETA((i >> 2) - 32), reta)?;
                }
                reta = 0;
            }
        }

        // Now fill our hash function seeds
        for i in 0..10 {
            ixgbe_hw::write_reg(&self.info, IXGBE_RSSRK(i), rss_keys[i])?;
        }

        // Disable UDP - IP fragments aren't currently being handled
        // and so we end up with a mix of 2-tuple and 4-tuple
        // traffic.
        let mrqc = IXGBE_MRQC_RSSEN
            | IXGBE_MRQC_RSS_FIELD_IPV4
            | IXGBE_MRQC_RSS_FIELD_IPV4_TCP
            | IXGBE_MRQC_RSS_FIELD_IPV6_EX_TCP
            | IXGBE_MRQC_RSS_FIELD_IPV6_EX
            | IXGBE_MRQC_RSS_FIELD_IPV6
            | IXGBE_MRQC_RSS_FIELD_IPV6_TCP;
        ixgbe_hw::write_reg(&self.info, IXGBE_MRQC, mrqc)?;

        Ok(())
    }

    fn map_queue_statistics(&self) -> Result<(), IxgbeDriverErr> {
        let mut r;
        for i in 0..32 {
            // Queues 0-15 are mapped 1:1
            // Queue 0 -> Counter 0
            // Queue 1 -> Counter 1
            // Queue 2 -> Counter 2....
            // Queues 16-127 are mapped to Counter 0
            if i < 4 {
                r = i * 4 + 0;
                r |= (i * 4 + 1) << 8;
                r |= (i * 4 + 2) << 16;
                r |= (i * 4 + 3) << 24;
            } else {
                r = 0;
            }
            ixgbe_hw::write_reg(&self.info, IXGBE_RQSMR(i), r as u32)?;
            ixgbe_hw::write_reg(&self.info, IXGBE_TQSM(i), r as u32)?;
        }
        Ok(())
    }

    fn config_gpie(&self) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;

        let mut gpie = ixgbe_hw::read_reg(&self.info, IXGBE_GPIE)?;

        // Fan Failure Interrupt
        if self.info.id == IXGBE_DEV_ID_82598AT {
            gpie |= IXGBE_SDP1_GPIEN;
        }

        if self.hw.mac.mac_type == IxgbeMac82599EB {
            // Add for Module detection
            gpie |= IXGBE_SDP2_GPIEN;

            // Media ready
            if self.info.id != IXGBE_DEV_ID_82599_QSFP_SF_QP {
                gpie |= IXGBE_SDP1_GPIEN;
            }

            // Set LL interval to max to reduce the number of low latency
            // interrupts hitting the card when the ring is getting full.
            gpie |= 0xf << IXGBE_GPIE_LLI_DELAY_SHIFT;
        }

        match self.hw.mac.mac_type {
            IxgbeMacX540 | IxgbeMacX550EMX | IxgbeMacX550EMA => {
                // Thermal Failure Detection (X540)
                // Link Detection (X552 SFP+, X552/X557-AT)
                gpie |= IXGBE_SDP0_GPIEN_X540;

                // Set LL interval to max to reduce the number of low latency
                // interrupts hitting the card when the ring is getting full.
                gpie |= 0xf << IXGBE_GPIE_LLI_DELAY_SHIFT;
            }
            _ => (),
        }

        /* Enable Enhanced MSIX mode */
        gpie |= IXGBE_GPIE_MSIX_MODE;
        gpie |= IXGBE_GPIE_EIAME | IXGBE_GPIE_PBA_SUPPORT | IXGBE_GPIE_OCD;

        ixgbe_hw::write_reg(&self.info, IXGBE_GPIE, gpie)?;

        Ok(())
    }

    fn iff(&mut self) -> Result<(), IxgbeDriverErr> {
        let mut fctrl = ixgbe_hw::read_reg(&self.info, IXGBE_FCTRL)?;
        fctrl &= !(IXGBE_FCTRL_MPE | IXGBE_FCTRL_UPE);
        self.flags &= !NetFlags::ALLMULTI;

        if self.flags.contains(NetFlags::PROMISC)
            || self.multicast_addr.len() > MAX_NUM_MULTICAST_ADDRESSES
        {
            self.flags |= NetFlags::ALLMULTI;
            fctrl |= IXGBE_FCTRL_MPE;
            if self.flags.contains(NetFlags::PROMISC) {
                fctrl |= IXGBE_FCTRL_UPE;
            }
        } else {
            // Clear mta_shadow
            self.hw.mac.mta_shadow.fill(0);

            // Update mta_shadow
            for mc_addr in self.multicast_addr.iter() {
                log::debug!("Adding the multicast addresses");
                ixgbe_operations::set_mta(&mut self.hw, mc_addr);
            }
            // Enable mta
            for i in 0..self.hw.mac.mcft_size as usize {
                ixgbe_hw::write_reg_array(
                    &self.info,
                    IXGBE_MTA(0) as usize,
                    i,
                    self.hw.mac.mta_shadow[i],
                )?;
            }
            if self.hw.addr_ctrl.mta_in_use > 0 {
                ixgbe_hw::write_reg(
                    &self.info,
                    IXGBE_MCSTCTRL,
                    IXGBE_MCSTCTRL_MFE | self.hw.mac.mc_filter_type as u32,
                )?;
            }
        }

        ixgbe_hw::write_reg(&self.info, IXGBE_FCTRL, fctrl)
    }

    fn setup_vlan_hw_support(&self, que: &[Queue]) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;
        let mut ctrl = ixgbe_hw::read_reg(&self.info, IXGBE_VLNCTRL)?;

        // TODO: The functionality for VLAN filtering using VFTA is not currently supported

        if self.hw.mac.mac_type == IxgbeMac82598EB {
            ctrl |= IXGBE_VLNCTRL_VME;
        }
        ixgbe_hw::write_reg(&self.info, IXGBE_VLNCTRL, ctrl)?;

        // On 82599 the VLAN enable is per/queue in RXDCTL
        if self.hw.mac.mac_type != IxgbeMac82598EB {
            for q in que.iter() {
                ctrl = ixgbe_hw::read_reg(&self.info, IXGBE_RXDCTL(q.me))?;
                ctrl |= IXGBE_RXDCTL_VME;
                ixgbe_hw::write_reg(&self.info, IXGBE_RXDCTL(q.me), ctrl)?;
            }
        }
        Ok(())
    }

    fn configure_ivars(&self, que: &[Queue]) -> Result<(), IxgbeDriverErr> {
        let newitr = (4000000 / IXGBE_INTS_PER_SEC) & 0x0FF8;

        for q in que.iter() {
            let i = q.me as u8;
            // First the RX queue entry
            self.set_ivar(i, q.me as u8, 0)?;
            // ... and the TX
            self.set_ivar(i, q.me as u8, 1)?;
            // Set an Initial EITR value
            ixgbe_hw::write_reg(&self.info, IXGBE_EITR(q.me), newitr)?;
        }

        let linkvec = que.len() as u8;
        /* For the Link interrupt */
        self.set_ivar(1, linkvec, -1)?;

        Ok(())
    }

    // Setup the correct IVAR register for a particular MSIX interrupt
    //   (yes this is all very magic and confusing :)
    //  - entry is the register array entry
    //  - vector is the MSIX vector for this queue
    //  - rx_tx_misc is RX/TX/MISC
    fn set_ivar(&self, entryy: u8, vectorr: u8, rx_tx_misc: i8) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;

        let mut vector = vectorr;
        let mut entry = entryy;

        vector |= IXGBE_IVAR_ALLOC_VAL;
        match self.hw.mac.mac_type {
            IxgbeMac82598EB => {
                if rx_tx_misc == -1 {
                    entry = IXGBE_IVAR_OTHER_CAUSES_INDEX;
                } else {
                    entry += rx_tx_misc as u8 * 64;
                }
                let index = (entry >> 2) & 0x1F;
                let mut ivar = ixgbe_hw::read_reg(&self.info, IXGBE_IVAR(index as usize))?;
                ivar &= !((0xFF as u32) << (8 * (entry & 0x3)));
                ivar |= (vector as u32) << (8 * (entry & 0x3));
                ixgbe_hw::write_reg(&self.info, IXGBE_IVAR(index as usize), ivar)?;
            }
            IxgbeMac82599EB | IxgbeMacX540 | IxgbeMacX550 | IxgbeMacX550EMX | IxgbeMacX550EMA => {
                if rx_tx_misc == -1 {
                    /* MISC IVAR */
                    let index = (entry & 1) * 8;
                    let mut ivar = ixgbe_hw::read_reg(&self.info, IXGBE_IVAR_MISC)?;
                    ivar &= !((0xFF as u32) << index);
                    ivar |= (vector as u32) << index;
                    ixgbe_hw::write_reg(&self.info, IXGBE_IVAR_MISC, ivar)?;
                } else {
                    /* RX/TX IVARS */
                    let index = (16 * (entry & 1)) + (8 * rx_tx_misc as u8);
                    let mut ivar =
                        ixgbe_hw::read_reg(&self.info, IXGBE_IVAR((entry >> 1) as usize))?;
                    ivar &= !((0xFF as u32) << index);
                    ivar |= (vector as u32) << index;
                    ixgbe_hw::write_reg(&self.info, IXGBE_IVAR((entry >> 1) as usize), ivar)?;
                }
            }
            _ => (),
        }

        Ok(())
    }

    fn config_link(&mut self) -> Result<(), IxgbeDriverErr> {
        if self.is_sfp(&self.hw) {
            // TODO:
            return Err(IxgbeDriverErr::NotSupported);
        } else {
            let (speed, link_up) = self.ops.mac_check_link(&self.info, &self.hw, false)?;
            self.link_active = link_up;
            let autoneg = self.hw.phy.autoneg_advertised;
            if autoneg == IXGBE_LINK_SPEED_UNKNOWN {
                self.ops.mac_get_link_capabilities()?;
            }
        }

        Ok(())
    }

    fn is_sfp(&self, hw: &IxgbeHw) -> bool {
        use ixgbe_hw::PhyType::*;

        match hw.phy.phy_type {
            IxgbePhySfpAvago
            | IxgbePhySfpFtl
            | IxgbePhySfpIntel
            | IxgbePhySfpUnknown
            | IxgbePhySfpPassiveTyco
            | IxgbePhySfpPassiveUnknown
            | IxgbePhyQsfpPassiveUnknown
            | IxgbePhyQsfpActiveUnknown
            | IxgbePhyQsfpIntel
            | IxgbePhyQsfpUnknown => true,
            _ => false,
        }
    }
}

impl Ixgbe {
    fn new(info: PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        let (inner, que) = IxgbeInner::new(info)?;

        let ixgbe = Self {
            inner: RwLock::new(inner),
            que,
        };

        Ok(ixgbe)
    }
}

fn allocate_msix(
    hw: &ixgbe_hw::IxgbeHw,
    info: &mut PCIeInfo,
    que: &[Queue],
) -> Result<PCIeInt, IxgbeDriverErr> {
    let segment_number = info.segment_group as usize;
    let bfd = info.get_bfd();

    let msix = info
        .get_msix_mut()
        .ok_or(IxgbeDriverErr::InitializeInterrupt)?;

    let mut irqs = Vec::new();

    for q in que.iter() {
        let irq_name_rxtx = format!("{}-{}-RxTx{}", DEVICE_SHORT_NAME, bfd, q.me);
        let mut irq_rxtx = msix
            .register_handler(
                irq_name_rxtx.into(),
                Box::new(move |irq| {
                    awkernel_lib::net::net_interrupt(irq);
                }),
                segment_number,
                awkernel_lib::cpu::raw_cpu_id() as u32,
                q.me,
            )
            .or(Err(IxgbeDriverErr::InitializeInterrupt))?;
        irq_rxtx.enable();
        irqs.push((irq_rxtx, IRQRxTxLink::RxTx(q.me)));
    }

    let irq_name_tx = format!("{}-{}-Other", DEVICE_SHORT_NAME, bfd);
    let mut irq_other = msix
        .register_handler(
            irq_name_tx.into(),
            Box::new(move |irq| {
                awkernel_lib::net::net_interrupt(irq);
            }),
            segment_number,
            awkernel_lib::cpu::raw_cpu_id() as u32,
            que.len(),
        )
        .or(Err(IxgbeDriverErr::InitializeInterrupt))?;
    irq_other.enable();
    irqs.push((irq_other, IRQRxTxLink::Link));

    if let Some(msi) = info.get_msi_mut() {
        msi.disable();
    }
    info.disable_legacy_interrupt();

    let msix = info.get_msix_mut().unwrap();
    msix.enable();

    Ok(PCIeInt::MsiX(irqs))
}

// Allocate memory for the transmit and receive rings, and then
// the descriptors associated with each, called only once at attach.
fn allocate_queue(info: &PCIeInfo, que_id: usize) -> Result<Queue, IxgbeDriverErr> {
    let tx_size = core::mem::size_of::<AdvTxDesc>() * DEFAULT_TXD;
    assert_eq!(tx_size & (PAGESIZE - 1), 0);

    let rx_size = core::mem::size_of::<AdvRxDesc>() * DEFAULT_RXD;
    assert_eq!(rx_size & (PAGESIZE - 1), 0);

    let tx_desc_ring = DMAPool::new(info.segment_group as usize, tx_size / PAGESIZE)
        .ok_or(IxgbeDriverErr::DMAPool)?;
    let rx_desc_ring = DMAPool::new(info.segment_group as usize, rx_size / PAGESIZE)
        .ok_or(IxgbeDriverErr::DMAPool)?;

    let tx = Tx {
        tx_desc_head: 0,
        tx_desc_tail: 0,
        tx_desc_ring,
        txd_cmd: IXGBE_TXD_CMD_IFCS,
        write_buf: None,
    };

    let rx = Rx {
        rx_desc_head: 0,
        rx_desc_tail: 0,
        rx_desc_ring,
        read_buf: None,
    };

    let que = Queue {
        tx: Mutex::new(tx),
        rx: Mutex::new(rx),
        me: que_id,
    };

    Ok(que)
}

//===========================================================================
impl PCIeDevice for Ixgbe {
    fn device_name(&self) -> Cow<'static, str> {
        let (mac_type, bfd) = {
            let inner = self.inner.read();
            (inner.hw.get_mac_type(), inner.info.get_bfd())
        };

        let name = format!("{bfd}: {DEVICE_NAME} ({mac_type:?})");
        name.into()
    }
}

impl NetDevice for Ixgbe {
    fn num_queues(&self) -> usize {
        self.que.len()
    }

    fn flags(&self) -> NetFlags {
        let inner = self.inner.read();
        inner.flags
    }

    fn device_short_name(&self) -> Cow<'static, str> {
        let bfd = self.inner.read().info.get_bfd();
        let name = format!("{DEVICE_SHORT_NAME}-{bfd}");
        name.into()
    }

    fn capabilities(&self) -> NetCapabilities {
        let inner = self.inner.read();
        inner.capabilities
    }

    fn link_status(&self) -> LinkStatus {
        //let inner = self.inner.read();
        //if inner.link_active {
        //if inner.link_duplex == igb_hw::Duplex::Full {
        //LinkStatus::UpFullDuplex
        //} else {
        //LinkStatus::UpHalfDuplex
        //}
        //} else {
        LinkStatus::Down
        //}
    }

    fn link_speed(&self) -> u64 {
        //let inner = self.inner.read();

        //match inner.link_speed {
        //igb_hw::Speed::S10Mbps => 10,
        //igb_hw::Speed::S100Mbps => 100,
        //igb_hw::Speed::S1000Mbps => 1000,
        //igb_hw::Speed::None => 0,
        //}
        0
    }

    fn mac_address(&self) -> [u8; 6] {
        let inner = self.inner.read();

        inner.hw.get_mac_addr()
    }

    fn recv(&self, que_id: usize) -> Result<Option<EtherFrameBuf>, NetDevError> {
        //{
        //let mut node = MCSNode::new();
        //let mut rx = self.que[que_id].rx.lock(&mut node);

        //let data = rx.read_queue.pop();
        //if data.is_some() {
        //return Ok(data);
        //}
        //}

        //self.rx_recv(que_id).or(Err(NetDevError::DeviceError))?;

        //let mut node = MCSNode::new();
        //let mut rx = self.que[que_id].rx.lock(&mut node);
        //if let Some(data) = rx.read_queue.pop() {
        //Ok(Some(data))
        //} else {
        //Ok(None)
        //}
        Ok(None)
    }

    fn can_send(&self) -> bool {
        let inner = self.inner.read();
        if !inner.flags.contains(NetFlags::RUNNING) {
            return false;
        }

        if !inner.link_active {
            return false;
        };

        true
    }

    fn send(&self, data: EtherFrameRef, que_id: usize) -> Result<(), NetDevError> {
        //let frames = [data];
        //self.send(que_id, &frames).or(Err(NetDevError::DeviceError))
        Ok(())
    }

    fn up(&self) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();

        if !inner.flags.contains(NetFlags::UP) {
            if let Err(err_init) = inner.init(&self.que) {
                if let Err(err_stop) = inner.stop(&self.que) {
                    log::error!("igb: stop failed: {:?}", err_stop);
                }

                log::error!("igb: init failed: {:?}", err_init);
                Err(NetDevError::DeviceError)
            } else {
                inner.flags.insert(NetFlags::UP);
                Ok(())
            }
        } else {
            Err(NetDevError::AlreadyUp)
        }
    }

    fn down(&self) -> Result<(), NetDevError> {
        //let mut inner = self.inner.write();

        //if inner.flags.contains(NetFlags::UP) {
        //if let Err(e) = inner.stop(true, &self.que) {
        //log::error!("igb: stop failed: {:?}", e);
        //Err(NetDevError::DeviceError)
        //} else {
        //inner.flags.remove(NetFlags::UP);
        //Ok(())
        //}
        //} else {
        //Err(NetDevError::AlreadyDown)
        //}
        Ok(())
    }

    fn interrupt(&self, irq: u16) -> Result<(), NetDevError> {
        //self.intr(irq).or(Err(NetDevError::DeviceError))
        Ok(())
    }

    fn irqs(&self) -> Vec<u16> {
        let inner = self.inner.read();

        let mut result = Vec::new();
        for irq in inner.irq_to_rx_tx_link.keys() {
            if *irq != 0 {
                result.push(*irq);
            }
        }

        result
    }

    fn rx_irq_to_que_id(&self, _irq: u16) -> Option<usize> {
        Some(0) // Use only one queue
    }

    fn add_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        //let restart;

        //{
        //let mut inner = self.inner.write();
        //inner.multicast_addr.insert(*addr);

        //restart = inner.flags.contains(NetFlags::UP);
        //}

        //if restart {
        //self.down()?;
        //self.up()?;
        //}

        Ok(())
    }

    fn remove_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        //let restart;

        //{
        //let mut inner = self.inner.write();
        //inner.multicast_addr.remove(addr);

        //restart = inner.flags.contains(NetFlags::UP);
        //}

        //if restart {
        //self.down()?;
        //self.up()?;
        //}

        Ok(())
    }

    fn poll_in_service(&self) -> Result<(), NetDevError> {
        //self.intr(0).or(Err(NetDevError::DeviceError))
        Ok(())
    }

    fn poll_mode(&self) -> bool {
        // self.inner.read().is_poll_mode
        false
    }

    fn poll(&self) -> bool {
        //let inner = self.inner.read();
        //if let Ok(icr) = ixgbe_hw::read_reg(&inner.info, ICR) {
        //let _ = ixgbe_hw::write_reg(&inner.info, ICS, icr);
        //drop(inner);
        //icr != 0
        //} else {
        //false
        //}
        false
    }

    fn tick(&self) -> Result<(), NetDevError> {
        //let inner = self.inner.read();

        //if inner.is_poll_mode {
        //return Ok(());
        //}

        //let mut irqs = Vec::new();
        //for irq in inner.irq_to_rx_tx_link.keys() {
        //if *irq != 0 {
        //irqs.push(*irq);
        //}
        //}

        //drop(inner);

        //for irq in irqs {
        //let _ = self.intr(irq);
        //}

        Ok(())
    }

    fn tick_msec(&self) -> Option<u64> {
        Some(200)
    }
}
