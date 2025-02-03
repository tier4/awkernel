//! # Intel 10 Gigabit Ethernet Controller

use crate::pcie::{
    capability::msi::MultipleMessage,
    intel::ixgbe::ixgbe_hw::{MacType, MediaType},
    PCIeDevice, PCIeDeviceErr, PCIeInfo,
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
    addr::Addr,
    delay::{wait_microsec, wait_millisec},
    dma_pool::DMAPool,
    interrupt::IRQ,
    net::{
        ether::{
            extract_headers, EtherExtracted, EtherHeader, NetworkHdr, TransportHdr, ETHER_HDR_LEN,
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
use core::fmt::{self, Debug};
use ixgbe_operations::mng_enabled;
use memoffset::offset_of;
use rand::rngs::SmallRng;
use rand::Rng;
use rand::SeedableRng;

mod ixgbe_82599;
mod ixgbe_hw;
mod ixgbe_operations;
mod ixgbe_x540;
mod ixgbe_x550;

#[allow(dead_code)]
mod ixgbe_regs;

use ixgbe_hw::{get_num_queues, SmartSpeed};
use ixgbe_regs::*;

use self::ixgbe_operations::IxgbeOperations;

const DEVICE_NAME: &str = "Intel 10 Gigabit Ethernet Controller";
const DEVICE_SHORT_NAME: &str = "ixgbe";

const RECV_QUEUE_SIZE: usize = 32;

pub const MAX_NUM_MULTICAST_ADDRESSES: usize = 128;

const MCLSHIFT: u32 = 11;
const MCLBYTES: u32 = 1 << MCLSHIFT;
#[allow(dead_code)]
const MAXMCLBYTES: u32 = 64 * 1024;

type TxRing = [TxDescriptor; DEFAULT_TXD];
type TxBuffer = [[u8; MCLBYTES as usize]; DEFAULT_TXD];

type RxRing = [AdvRxDesc; DEFAULT_RXD];
type RxBuffer = [[u8; MCLBYTES as usize]; DEFAULT_RXD];

pub struct Tx {
    tx_desc_head: usize,
    tx_desc_tail: usize,
    tx_desc_ring: DMAPool<TxRing>,
    txd_cmd: u32,
    write_buf: Option<DMAPool<TxBuffer>>,
}
pub struct Rx {
    rx_desc_head: u32,
    rx_desc_tail: usize,
    rx_desc_ring: DMAPool<RxRing>,
    read_buf: Option<DMAPool<RxBuffer>>,

    read_queue: RingQ<EtherFrameBuf>,
}

pub struct Queue {
    tx: Mutex<Tx>,
    rx: Mutex<Rx>,
    me: usize,
}

#[derive(Clone, Copy)]
struct AdvTxDesc {
    buffer_addr: u64, // Address of descriptor's data buf
    cmd_type_len: u32,
    olinfo_status: u32,
}

#[allow(dead_code)]
#[derive(Clone, Copy)]
struct RxRead {
    pkt_addr: u64, // Packet buffer address
    hdr_addr: u64, // Header buffer address
}

#[allow(dead_code)]
#[derive(Clone, Copy)]
struct RxWb {
    lower_lo_dword: u32,
    lower_hi_dword: u32,
    upper_status_error: u32,
    upper_length: u16,
    upper_vlan: u16,
}

#[allow(dead_code)]
union AdvRxDesc {
    data: [u64; 2],
    read: RxRead,
    wb: RxWb,
}

#[derive(Debug, Clone, Copy)]
struct AdvTxContextDescriptor {
    vlan_macip_lens: u32,
    seqnum_seed: u32,
    type_tucmd_mlhl: u32,
    mss_l4len_idx: u32,
}

union TxDescriptor {
    adv_tx: AdvTxDesc,
    adv_ctx: AdvTxContextDescriptor,
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
    num_segs: u16,
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

    let ixgbe = Ixgbe::new(info)?;

    let result = Arc::new(ixgbe);

    awkernel_lib::net::add_interface(result.clone(), None);
    Ok(result)
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IxgbeDriverErr {
    InitializeInterrupt,
    UnknownDeviceID,
    NotPciExpress,
    NoBar0,
    ReadFailure,
    DMAPool,
    Eeprom,
    EepromChecksum,
    Phy,
    Config,
    LinkSetup,
    InvalidMacAddr,
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
    EepromVersion,
    Overtemp,
    FcNotNegotiated,
    SfpSetupNotComplete,
    InvalidArgument,
    HostInterfaceCommand,
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

impl fmt::Display for IxgbeDriverErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::InitializeInterrupt => write!(f, "Interrupt initialization failure."),
            Self::UnknownDeviceID => write!(f, "Unknown device id."),
            Self::NotPciExpress => write!(f, "Not a pci express device."),
            Self::NoBar0 => write!(f, "No BAR0."),
            Self::ReadFailure => write!(f, "Read failure."),
            Self::DMAPool => write!(f, "DMA pool failure."),
            Self::Eeprom => write!(f, "Eeprom failure."),
            Self::EepromChecksum => write!(f, "Wrong Eeprom checksum."),
            Self::Phy => write!(f, "PHY failure."),
            Self::Config => write!(f, "Configuration failure."),
            Self::LinkSetup => write!(f, "Link setup failure."),
            Self::InvalidMacAddr => write!(f, "Invalid Mac Address."),
            Self::MasterRequestsPending => write!(f, "Master requests pending."),
            Self::InvalidLinkSettings => write!(f, "Invalid link settings."),
            Self::AutonegNotComplete => write!(f, "Auto negotiation is not completed."),
            Self::ResetFailed => write!(f, "Reset failure."),
            Self::I2c => write!(f, "I2c failure."),
            Self::SwfwSync => write!(f, "Software firmware synchronization failure."),
            Self::PhyAddrInvalid => write!(f, "Phy address invalid."),
            Self::SfpNotSupported => write!(f, "Sfp not supported."),
            Self::SfpNotPresent => write!(f, "Sfp not present."),
            Self::SfpNoInitSeqPresent => write!(f, "Sfp no init sequence present."),
            Self::EepromVersion => write!(f, "Wrong eeprom version."),
            Self::Overtemp => write!(f, "Over temperature."),
            Self::FcNotNegotiated => write!(f, "Flow control not negotiated."),
            Self::SfpSetupNotComplete => write!(f, "Sfp setup not complete."),
            Self::InvalidArgument => write!(f, "Invalid argument."),
            Self::HostInterfaceCommand => write!(f, "Host interface command failure."),
            Self::NotImplemented => write!(f, "Not implemented."),
            Self::InvalidPacket => write!(f, "Invalid packet."),
        }
    }
}

impl IxgbeInner {
    fn new(mut info: PCIeInfo) -> Result<(Self, Vec<Queue>), PCIeDeviceErr> {
        let (mut hw, ops) = ixgbe_hw::IxgbeHw::new(&mut info)?;

        // Allocate our TX/RX Queues
        let mut que = Vec::new();
        let que_num = get_num_queues(&hw.mac.mac_type);
        for i in 0..que_num {
            que.push(allocate_queue(&info, i)?);
        }

        // ixgbe_identify_hardware()
        if hw.mac.mac_type != MacType::IxgbeMac82598EB {
            // Pick up the 82599 and VF settings */
            hw.phy.smart_speed = SmartSpeed::IxgbeSmartSpeedOn;
        }
        let num_segs = IXGBE_82599_SCATTER;

        let mut irq_to_rx_tx_link = BTreeMap::new();

        let is_poll_mode;

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
        } else if let Ok(pcie_int) = allocate_msi(&mut info) {
            match &pcie_int {
                PCIeInt::Msi(irq) => {
                    let irq = irq.get_irq();
                    irq_to_rx_tx_link.insert(irq, IRQRxTxLink::Legacy(0));
                }
                _ => unreachable!(),
            }

            is_poll_mode = false;
            pcie_int
        } else {
            irq_to_rx_tx_link.insert(0, IRQRxTxLink::Legacy(0));
            is_poll_mode = true;
            PCIeInt::None
        };

        ops.mac_init_hw(&mut info, &mut hw)?;
        ops.mac_enable_tx_laser(&info, &mut hw)?;
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

        if MacType::IxgbeMac82598EB != hw.get_mac_type() {
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
            num_segs,
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

        let que_num = get_num_queues(&self.hw.mac.mac_type);
        // Now enable all the queues
        for i in 0..que_num {
            let mut txdctl = ixgbe_hw::read_reg(&self.info, IXGBE_TXDCTL(i))?;
            txdctl |= IXGBE_TXDCTL_ENABLE;
            // Set WTHRESH to 8, burst writeback
            txdctl |= 8 << 16;
            // When the internal queue falls below PTHRESH (16),
            // start prefetching as long as there are at least
            // HTHRESH (1) buffers ready.
            txdctl |= 16 | (1 << 8);
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
                    wait_millisec(1);
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
        if let PCIeInt::MsiX(_) = self.pcie_int {
            self.configure_ivars(que)?;
            // Set up auto-mask
            if self.hw.mac.mac_type == IxgbeMac82598EB {
                ixgbe_hw::write_reg(&self.info, IXGBE_EIAM, IXGBE_EICS_RTX_QUEUE)?;
            } else {
                ixgbe_hw::write_reg(&self.info, IXGBE_EIAM_EX(0), 0xFFFFFFFF)?;
                ixgbe_hw::write_reg(&self.info, IXGBE_EIAM_EX(1), 0xFFFFFFFF)?;
            }
        } else {
            // Simple settings for Legacy/MSI
            self.set_ivar(0, 0, 0)?;
            self.set_ivar(0, 0, 1)?;
            ixgbe_hw::write_reg(&self.info, IXGBE_EIAM, IXGBE_EICS_RTX_QUEUE)?;
        }

        // Check on any SFP devices that need to be kick-started
        if self.hw.phy.phy_type == ixgbe_hw::PhyType::IxgbePhyNone {
            if let Err(e) = self.ops.phy_identify(&self.info, &mut self.hw) {
                if e == IxgbeDriverErr::SfpNotSupported {
                    log::error!("Unsupported SFP+ module type was detected.");
                }
            }
            // We may be better to print error message specifically for Err(SfpNotSupported) as OpenBSD does.
        }

        // Setup interrupt moderation
        let mut itr = (4000000 / IXGBE_INTS_PER_SEC) & 0xff8;
        if self.hw.mac.mac_type != IxgbeMac82598EB {
            itr |= IXGBE_EITR_LLI_MOD | IXGBE_EITR_CNT_WDIS;
        }
        ixgbe_hw::write_reg(&self.info, IXGBE_EITR(0), itr)?;

        if let PCIeInt::MsiX(_) = self.pcie_int {
            // Set moderation on the Link interrupt
            let linkvec = que.len();
            ixgbe_hw::write_reg(&self.info, IXGBE_EITR(linkvec), IXGBE_LINK_ITR)?;
        }

        // Enable power to the phy
        self.ops.phy_set_power(&self.info, &self.hw, true)?;

        // Config/Enable Link
        self.config_link()?;

        // Hardware Packet Buffer & Flow Control setup
        self.config_delay_values()?;

        // Initialize the FC settings
        self.ops.mac_start_hw(&self.info, &mut self.hw)?;

        // And now turn on interrupts
        self.enable_intr()?;
        self.enable_queues(que)?;

        self.flags |= NetFlags::RUNNING;

        Ok(())
    }

    fn stop(&mut self, que: &[Queue]) -> Result<(), IxgbeDriverErr> {
        self.flags.remove(NetFlags::RUNNING);

        self.disable_intr()?;

        self.ops.mac_reset_hw(&mut self.info, &mut self.hw)?;
        self.hw.adapter_stopped = false;
        self.ops.mac_stop_adapter(&mut self.info, &mut self.hw)?;

        if self.hw.mac.mac_type == MacType::IxgbeMac82599EB {
            ixgbe_operations::stop_mac_link_on_d3_82599(&*self.ops, &self.info, &mut self.hw)?;
            if self.ops.mac_get_media_type(&self.info, &mut self.hw)
                == MediaType::IxgbeMediaTypeFiber
                && !mng_enabled(&self.info, &self.hw)?
            {
                ixgbe_operations::disable_tx_laser_multispeed_fiber(&self.info, &self.hw)?;
            }
        }

        self.ops.mac_set_rar(
            &self.info,
            self.hw.mac.num_rar_entries,
            0,
            &self.hw.mac.addr,
            0,
            IXGBE_RAH_AV,
        )?;

        //From FreeBSD // let hardware know driver is unloading
        // let mut ctrl_ext = ixgbe_hw::read_reg(&self.info, IXGBE_CTRL_EXT)?;
        // ctrl_ext &= !IXGBE_CTRL_EXT_DRV_LOAD;
        // ixgbe_hw::write_reg(&self.info, IXGBE_CTRL_EXT, ctrl_ext);

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
        if let PCIeInt::MsiX(_) = self.pcie_int {
            ixgbe_hw::write_reg(&self.info, IXGBE_EIAC, 0)?;
        }

        if self.hw.get_mac_type() == MacType::IxgbeMac82598EB {
            ixgbe_hw::write_reg(&self.info, IXGBE_EIMC, u32::MAX)?;
        } else {
            ixgbe_hw::write_reg(&self.info, IXGBE_EIMC, 0xFFFF0000)?;
            ixgbe_hw::write_reg(&self.info, IXGBE_EIMC_EX(0), u32::MAX)?;
            ixgbe_hw::write_reg(&self.info, IXGBE_EIMC_EX(1), u32::MAX)?;
        }

        ixgbe_hw::write_flush(&self.info)
    }

    fn update_link_status(&mut self) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::LinkState::*;

        let (speed, link_up) = self.ops.mac_check_link(&self.info, &mut self.hw, false)?;
        self.link_speed = speed;
        self.link_active = link_up;

        let mut link_state = LinkStateDown;
        if link_up {
            link_state = LinkStateFullDuplex;
            // Update any Flow Control changes
            let _ = self.ops.mac_fc_enable(&self.info, &mut self.hw);
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
                desc.adv_tx.buffer_addr = (buf_phy_addr + i * MCLBYTES as usize) as u64;
                desc.adv_tx.cmd_type_len = 0;
                desc.adv_tx.olinfo_status = 0;
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
                IxgbeMac82598EB => {
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

        let bufsz = MCLBYTES >> IXGBE_SRRCTL_BSIZEPKT_SHIFT;
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
        let que_num = get_num_queues(&self.hw.mac.mac_type);
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
        let seed = [0x12u8; 32]; // Random seed value
        let mut rng = SmallRng::from_seed(seed);
        let mut rss_keys = [0u32; 10];
        for rss_key in &mut rss_keys {
            *rss_key = rng.gen::<u32>();
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
        let que_num = get_num_queues(&self.hw.mac.mac_type);
        let mut queue_id;
        let mut reta = 0;
        for i in 0..table_size {
            if j == que_num {
                j = 0;
            }
            queue_id = j * index_mult;
            // The low 8 bits are for hash value (n+0);
            // The next 8 bits are for hash value (n+1), etc.
            reta >>= 8;
            reta |= (queue_id as u32) << 24;
            if (i & 3) == 3 {
                if i < 128 {
                    ixgbe_hw::write_reg(&self.info, IXGBE_RETA(i >> 2), reta)?;
                } else {
                    ixgbe_hw::write_reg(&self.info, IXGBE_ERETA((i >> 2) - 32), reta)?;
                }
                reta = 0;
            }
            j += 1;
        }

        // Now fill our hash function seeds
        for (i, rss_key) in rss_keys.iter().enumerate() {
            ixgbe_hw::write_reg(&self.info, IXGBE_RSSRK(i), *rss_key)?;
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
                r = i * 4;
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

        if let PCIeInt::MsiX(_) = self.pcie_int {
            /* Enable Enhanced MSIX mode */
            gpie |= IXGBE_GPIE_MSIX_MODE;
            gpie |= IXGBE_GPIE_EIAME | IXGBE_GPIE_PBA_SUPPORT | IXGBE_GPIE_OCD;
        }

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
        // For the Link interrupt
        self.set_ivar(1, linkvec, -1)?;

        Ok(())
    }

    /// Setup the correct IVAR register for a particular MSIX interrupt
    ///   (yes this is all very magic and confusing :)
    ///  - entry is the register array entry
    ///  - vector is the MSIX vector for this queue
    ///  - rx_tx_misc is RX/TX/MISC
    fn set_ivar(
        &self,
        mut entry: u8,
        mut vector: u8,
        rx_tx_misc: i8,
    ) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;

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
                ivar &= !((0xFF_u32) << (8 * (entry & 0x3)));
                ivar |= (vector as u32) << (8 * (entry & 0x3));
                ixgbe_hw::write_reg(&self.info, IXGBE_IVAR(index as usize), ivar)?;
            }
            IxgbeMac82599EB | IxgbeMacX540 | IxgbeMacX550 | IxgbeMacX550EMX | IxgbeMacX550EMA => {
                if rx_tx_misc == -1 {
                    /* MISC IVAR */
                    let index = (entry & 1) * 8;
                    let mut ivar = ixgbe_hw::read_reg(&self.info, IXGBE_IVAR_MISC)?;
                    ivar &= !((0xFF_u32) << index);
                    ivar |= (vector as u32) << index;
                    ixgbe_hw::write_reg(&self.info, IXGBE_IVAR_MISC, ivar)?;
                } else {
                    /* RX/TX IVARS */
                    let index = (16 * (entry & 1)) + (8 * rx_tx_misc as u8);
                    let mut ivar =
                        ixgbe_hw::read_reg(&self.info, IXGBE_IVAR((entry >> 1) as usize))?;
                    ivar &= !((0xFF_u32) << index);
                    ivar |= (vector as u32) << index;
                    ixgbe_hw::write_reg(&self.info, IXGBE_IVAR((entry >> 1) as usize), ivar)?;
                }
            }
            _ => (),
        }

        Ok(())
    }

    fn config_link(&mut self) -> Result<(), IxgbeDriverErr> {
        if self.is_sfp() {
            if self.hw.phy.multispeed_fiber {
                self.ops.mac_setup_sfp(&self.info, &mut self.hw)?;
                self.ops.mac_enable_tx_laser(&self.info, &mut self.hw)?;
                self.handle_msf()?;
            } else {
                self.handle_mod()?;
            }
        } else {
            let (speed, link_up) = self.ops.mac_check_link(&self.info, &mut self.hw, false)?;
            self.link_active = link_up;
            self.link_speed = speed; // According to FreeBSD

            let mut _autoneg = self.hw.phy.autoneg_advertised;
            let _negotiate;
            if _autoneg == IXGBE_LINK_SPEED_UNKNOWN {
                (_autoneg, _negotiate) = self
                    .ops
                    .mac_get_link_capabilities(&self.info, &mut self.hw)?;
            }
            //TODO: Consider whether this is necessary.
            self.ops
                .mac_setup_link(&self.info, &mut self.hw, _autoneg, self.link_active)?;
        }

        Ok(())
    }

    /// SFP module interrupts handler
    fn handle_mod(&mut self) -> Result<(), IxgbeDriverErr> {
        match self.ops.phy_identify_sfp(&self.info, &mut self.hw) {
            Ok(_) => (),
            Err(e) => {
                if e == IxgbeDriverErr::SfpNotSupported {
                    log::error!("Unsupported SFP+ module type was detected!\n");
                }
                return Err(e);
            }
        }

        match self.ops.mac_setup_sfp(&self.info, &mut self.hw) {
            Ok(_) => (),
            Err(e) => {
                if e == IxgbeDriverErr::SfpNotSupported {
                    log::error!("Unsupported SFP+ module type was detected!");
                    log::error!("Setup failure - unsupported SFP+ module type!")
                }
                return Err(e);
            }
        }

        self.handle_msf()
    }

    /// MSF (multispeed fiber) interrupts handler
    fn handle_msf(&mut self) -> Result<(), IxgbeDriverErr> {
        let mut _autoneg = self.hw.phy.autoneg_advertised;
        let _negotiate;
        if self.hw.phy.autoneg_advertised == 0 {
            (_autoneg, _negotiate) = self
                .ops
                .mac_get_link_capabilities(&self.info, &mut self.hw)?;
        }

        self.ops
            .mac_setup_link(&self.info, &mut self.hw, _autoneg, true)
    }

    fn is_sfp(&self) -> bool {
        use ixgbe_hw::PhyType::*;

        matches!(
            self.hw.phy.phy_type,
            IxgbePhySfpAvago
                | IxgbePhySfpFtl
                | IxgbePhySfpIntel
                | IxgbePhySfpUnknown
                | IxgbePhySfpPassiveTyco
                | IxgbePhySfpPassiveUnknown
                | IxgbePhyQsfpPassiveUnknown
                | IxgbePhyQsfpActiveUnknown
                | IxgbePhyQsfpIntel
                | IxgbePhyQsfpUnknown
        )
    }

    /// Requires sc->max_frame_size to be set.
    fn config_delay_values(&mut self) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;
        let frame = self.max_frame_size as u32;

        // Calculate High Water
        let high_tmp = match self.hw.mac.mac_type {
            IxgbeMacX540 | IxgbeMacX550 | IxgbeMacX550EMX | IxgbeMacX550EMA => {
                IXGBE_DV_X540(frame, frame)
            }
            _ => IXGBE_DV(frame, frame),
        };
        let size = IXGBE_BT2KB(high_tmp);
        let rxpb = ixgbe_hw::read_reg(&self.info, IXGBE_RXPBSIZE(0))? >> 10;
        self.hw.fc.high_water[0] = rxpb - size;

        /* low_Now calculate Low Water */
        let tmp = match self.hw.mac.mac_type {
            IxgbeMacX540 | IxgbeMacX550 | IxgbeMacX550EMX | IxgbeMacX550EMA => {
                IXGBE_LOW_DV_X540(frame)
            }
            _ => IXGBE_LOW_DV(frame),
        };
        self.hw.fc.low_water[0] = IXGBE_BT2KB(tmp);

        self.hw.fc.pause_time = IXGBE_FC_PAUSE;
        self.hw.fc.send_xon = true;

        Ok(())
    }

    fn enable_intr(&self) -> Result<(), IxgbeDriverErr> {
        use ixgbe_hw::MacType::*;

        let mut mask = IXGBE_EIMS_ENABLE_MASK & !IXGBE_EIMS_RTX_QUEUE;
        // Enable Fan Failure detection
        if self.info.id == IXGBE_DEV_ID_82598AT {
            mask |= IXGBE_EIMS_GPI_SDP1;
        }

        match self.hw.mac.mac_type {
            IxgbeMac82599EB => {
                mask |= IXGBE_EIMS_ECC;
                // Temperature sensor on some adapters
                mask |= IXGBE_EIMS_GPI_SDP0;
                // SFP+ (RX_LOS_N & MOD_ABS_N)
                mask |= IXGBE_EIMS_GPI_SDP1;
                mask |= IXGBE_EIMS_GPI_SDP2;
            }
            IxgbeMacX540 => {
                mask |= IXGBE_EIMS_ECC;
                // Detect if Thermal Sensor is enabled
                let fwsm = ixgbe_hw::read_reg(&self.info, IXGBE_FWSM)?;
                if fwsm & IXGBE_FWSM_TS_ENABLED != 0 {
                    mask |= IXGBE_EIMS_TS;
                }
            }
            IxgbeMacX550 | IxgbeMacX550EMX | IxgbeMacX550EMA => {
                mask |= IXGBE_EIMS_ECC;
                // MAC thermal sensor is automatically enabled
                mask |= IXGBE_EIMS_TS;
                // Some devices use SDP0 for important information
                if self.info.id == IXGBE_DEV_ID_X550EM_X_SFP
                    || self.info.id == IXGBE_DEV_ID_X550EM_X_10G_T
                {
                    mask |= IXGBE_EIMS_GPI_SDP0_X540;
                }
            }
            _ => (),
        }

        ixgbe_hw::write_reg(&self.info, IXGBE_EIMS, mask)?;

        // With MSI-X we use auto clear
        if let PCIeInt::MsiX(_) = self.pcie_int {
            mask = IXGBE_EIMS_ENABLE_MASK;
            // Don't autoclear Link
            mask &= !IXGBE_EIMS_OTHER;
            mask &= !IXGBE_EIMS_LSC;
            ixgbe_hw::write_reg(&self.info, IXGBE_EIAC, mask)?;
        }

        ixgbe_hw::write_flush(&self.info)?;

        Ok(())
    }

    fn enable_queues(&self, que: &[Queue]) -> Result<(), IxgbeDriverErr> {
        for q in que.iter() {
            self.enable_queue(q.me as u32)?;
        }
        Ok(())
    }

    /// MSIX Interrupt Handlers
    fn enable_queue(&self, vector: u32) -> Result<(), IxgbeDriverErr> {
        let queue = 1u64 << vector;
        if self.hw.mac.mac_type == MacType::IxgbeMac82598EB {
            let mask = (IXGBE_EIMS_RTX_QUEUE as u64 & queue) as u32;
            ixgbe_hw::write_reg(&self.info, IXGBE_EIMS, mask)?;
        } else {
            let mask_low = (queue & 0xFFFFFFFF_u64) as u32;
            if mask_low != 0 {
                ixgbe_hw::write_reg(&self.info, IXGBE_EIMS_EX(0), mask_low)?;
            }
            let mask_high = (queue >> 32) as u32;
            if mask_high != 0 {
                ixgbe_hw::write_reg(&self.info, IXGBE_EIMS_EX(1), mask_high)?;
            }
        }

        Ok(())
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

    fn intr(&self, irq: u16) -> Result<(), IxgbeDriverErr> {
        let inner = self.inner.read();

        let reason = if let Some(reason) = inner.irq_to_rx_tx_link.get(&irq) {
            *reason
        } else {
            return Ok(());
        };

        match reason {
            IRQRxTxLink::Legacy(que_id) => {
                drop(inner);
                self.intr_legacy_and_link()?;

                let inner = self.inner.read();
                if inner.flags.contains(NetFlags::RUNNING) {
                    drop(inner);
                    self.rx_recv(que_id)?;
                    self.txeof(que_id)?;
                } else {
                    drop(inner);
                }

                let inner = self.inner.read();
                inner.enable_queues(&self.que)?;
                drop(inner);
            }
            IRQRxTxLink::RxTx(que_id) => {
                if inner.flags.contains(NetFlags::RUNNING) {
                    drop(inner);
                    self.rx_recv(que_id)?;
                    self.txeof(que_id)?;
                }

                let inner = self.inner.read();
                let queue = 1u64 << que_id;

                match inner.hw.mac.mac_type {
                    MacType::IxgbeMac82598EB => {
                        // TODO
                    }
                    _ => {
                        let mask_lo = (queue & 0xFFFFFFFF) as u32;
                        if mask_lo != 0 {
                            ixgbe_hw::write_reg(&inner.info, IXGBE_EIMS_EX(0), mask_lo)?;
                        }
                        let mask_hi = (queue >> 32) as u32;
                        if mask_hi != 0 {
                            ixgbe_hw::write_reg(&inner.info, IXGBE_EIMS_EX(0), mask_hi)?;
                        }
                    }
                }
            }
            IRQRxTxLink::Link => {
                drop(inner);
                self.intr_legacy_and_link()?;
            }
        }

        Ok(())
    }

    fn intr_legacy_and_link(&self) -> Result<(), IxgbeDriverErr> {
        let mut inner = self.inner.write();
        let mut reg_eicr;

        match inner.pcie_int {
            PCIeInt::MsiX(_) => {
                // Pause other interrupts
                ixgbe_hw::write_reg(&inner.info, IXGBE_EIMC, IXGBE_EIMC_OTHER)?;
                // First get the cause
                reg_eicr = ixgbe_hw::read_reg(&inner.info, IXGBE_EICS)?;
                // Be sure the queue bits are not cleared
                reg_eicr &= !IXGBE_EICR_RTX_QUEUE;
                // Clear interrupt with write
                ixgbe_hw::write_reg(&inner.info, IXGBE_EICR, reg_eicr)?;
            }
            _ => {
                // For Msi and Legacy
                reg_eicr = ixgbe_hw::read_reg(&inner.info, IXGBE_EICR)?;
                if reg_eicr == 0 {
                    inner.enable_intr()?;
                    inner.enable_queues(&self.que)?;
                }
            }
        }

        // Link status change
        if reg_eicr & IXGBE_EICR_LSC != 0 {
            ixgbe_hw::write_reg(&inner.info, IXGBE_EIMC, IXGBE_EIMC_LSC)?;
            inner.update_link_status()?;
        }

        if inner.hw.mac.mac_type != MacType::IxgbeMac82598EB {
            if reg_eicr & IXGBE_EICR_ECC != 0 {
                log::error!(
                    "{}: CRITICAL: ECC ERROR!! Please Reboot!!\n",
                    self.device_name()
                );
                ixgbe_hw::write_reg(&inner.info, IXGBE_EICR, IXGBE_EICR_ECC)?;
            }
            // Check for over temp condition
            if reg_eicr & IXGBE_EICR_TS != 0 {
                log::error!("CRITICAL: OVER TEMP!! PHY IS SHUT DOWN!!\n");
                ixgbe_hw::write_reg(&inner.info, IXGBE_EICR, IXGBE_EICR_TS)?;
            }
        }

        // Pluggable optics-related interrupt
        if inner.is_sfp() {
            let mod_mask;
            let msf_mask;
            if inner.info.get_id() == IXGBE_DEV_ID_X550EM_X_SFP {
                mod_mask = IXGBE_EICR_GPI_SDP0_X540;
                msf_mask = IXGBE_EICR_GPI_SDP1_X540;
            } else if inner.hw.mac.mac_type == MacType::IxgbeMacX540
                || inner.hw.mac.mac_type == MacType::IxgbeMacX550
                || inner.hw.mac.mac_type == MacType::IxgbeMacX550EMX
            {
                mod_mask = IXGBE_EICR_GPI_SDP2_X540;
                msf_mask = IXGBE_EICR_GPI_SDP1_X540;
            } else {
                mod_mask = IXGBE_EICR_GPI_SDP2;
                msf_mask = IXGBE_EICR_GPI_SDP1;
            }
            if reg_eicr & mod_mask != 0 {
                // Clear the interrupt
                ixgbe_hw::write_reg(&inner.info, IXGBE_EICR, mod_mask)?;
                inner.handle_mod()?;
            } else if (inner.hw.phy.media_type != MediaType::IxgbeMediaTypeCopper)
                && (reg_eicr & msf_mask != 0)
            {
                // Clear the interrupt
                ixgbe_hw::write_reg(&inner.info, IXGBE_EICR, msf_mask)?;
                inner.handle_msf()?;
            }
        }

        // Check for fan failure
        if inner.info.id == IXGBE_DEV_ID_82598AT && reg_eicr & IXGBE_EICR_GPI_SDP1 != 0 {
            log::error!("CRITICAL: FAN FAILURE!! REPLACE IMMEDIATELY!!\n");
            ixgbe_hw::write_reg(&inner.info, IXGBE_EICR, IXGBE_EICR_GPI_SDP1)?;
        }

        // External PHY interrupt
        if inner.info.id == IXGBE_DEV_ID_X550EM_X_10G_T && reg_eicr & IXGBE_EICR_GPI_SDP0_X540 != 0
        {
            // Clear the interrupt
            ixgbe_hw::write_reg(&inner.info, IXGBE_EICR, IXGBE_EICR_GPI_SDP0_X540)?;
            // TODO: The below is for X550em.
            // self.handle_phy()?;
        }

        ixgbe_hw::write_reg(&inner.info, IXGBE_EIMS, IXGBE_EIMS_OTHER | IXGBE_EIMS_LSC)?;

        Ok(())
    }

    #[allow(dead_code)]
    /// This is for X550em.
    fn handle_phy(&self) -> Result<(), IxgbeDriverErr> {
        Err(IxgbeDriverErr::NotImplemented)
    }

    fn rx_fill(&self, que_id: usize) -> Result<(), IxgbeDriverErr> {
        let inner = self.inner.read();

        let que = &self.que[que_id];

        let mut node = MCSNode::new();
        let mut rx = que.rx.lock(&mut node);

        let mut i = rx.rx_desc_head as usize;
        let mut prev;
        let rx_desc_tail = rx.rx_desc_tail;
        let rx_desc_ring = rx.rx_desc_ring.as_mut();

        loop {
            prev = i;
            i += 1;
            if i == rx_desc_ring.len() {
                i = 0;
            }

            if i == rx_desc_tail {
                break;
            }

            let desc = &mut rx_desc_ring[i];
            desc.wb.upper_status_error = 0;
            desc.wb.upper_length = MCLBYTES as u16;
        }

        rx.rx_desc_head = prev as u32;
        ixgbe_hw::write_reg(&inner.info, IXGBE_RDT(que.me), rx.rx_desc_head)?;

        Ok(())
    }

    fn rx_recv(&self, que_id: usize) -> Result<(), IxgbeDriverErr> {
        let que = &self.que[que_id];

        {
            let inner = self.inner.read();

            let mut node = MCSNode::new();
            let mut rx = que.rx.lock(&mut node);

            if rx.read_buf.is_none() {
                return Ok(());
            }

            let mut i = rx.rx_desc_tail;

            loop {
                if i == rx.rx_desc_head as usize {
                    break;
                }

                if rx.read_queue.is_full() {
                    break;
                }

                let rx_desc_ring = rx.rx_desc_ring.as_ref();
                let rx_desc_ring_len = rx_desc_ring.len();
                let desc = &rx_desc_ring[i];

                let staterr;
                unsafe {
                    staterr = u32::from_le(desc.wb.upper_status_error);
                }
                if staterr & IXGBE_RXD_STAT_DD == 0 {
                    break;
                }

                let len;
                let vtag;
                let eop;
                unsafe {
                    len = u16::from_le(desc.wb.upper_length);
                    vtag = u16::from_le(desc.wb.upper_vlan);
                    eop = (staterr & IXGBE_RXD_STAT_EOP) != 0;
                }

                if staterr & IXGBE_RXDADV_ERR_FRAME_ERR_MASK != 0 {
                    i += 1;
                    if i == rx_desc_ring_len {
                        i = 0;
                    }
                    continue;
                }

                let vlan = if staterr & IXGBE_RXD_STAT_VP != 0 {
                    Some(vtag)
                } else {
                    None
                };

                if !eop {
                    drop(rx);
                    drop(inner);
                    return self.recv_jumbo(que_id);
                } else {
                    let read_buf = rx.read_buf.as_ref().unwrap();
                    let src = &read_buf.as_ref()[i];
                    let data = src[0..len as usize].to_vec();
                    rx.read_queue.push(EtherFrameBuf { data, vlan }).unwrap();
                }

                i += 1;
                if i == rx_desc_ring_len {
                    i = 0;
                }
            }

            rx.rx_desc_tail = i;
        }

        self.rx_fill(que_id)?;

        Ok(())
    }

    fn recv_jumbo(&self, que_id: usize) -> Result<(), IxgbeDriverErr> {
        let que = &self.que[que_id];

        let mut node = MCSNode::new();
        let rx = que.rx.lock(&mut node);

        let _rx_desc_ring = rx.rx_desc_ring.as_ref();
        todo!()
    }

    fn txeof(&self, que_id: usize) -> Result<(), IxgbeDriverErr> {
        let reg_tdh = {
            let inner = self.inner.read();
            ixgbe_hw::read_reg(&inner.info, IXGBE_TDH(que_id))? as usize
        };

        let que = &self.que[que_id];

        let mut node = MCSNode::new();
        let mut tx = que.tx.lock(&mut node);

        tx.tx_desc_tail = reg_tdh;

        Ok(())
    }

    // TODO: Ipv6
    fn calc_pseudo_cksum(&self, ext: &EtherExtracted) -> u16 {
        match ext.network {
            NetworkHdr::Ipv4(ip_hdr) => {
                let ip_src = ip_hdr.ip_src.swap_bytes();
                let ip_dst = ip_hdr.ip_dst.swap_bytes();
                let len = ip_hdr.ip_len.swap_bytes() as u32 - core::mem::size_of::<Ip>() as u32;
                let protocol = ip_hdr.ip_p.swap_bytes() as u32;
                in_pseudo(ip_src, ip_dst, len + protocol)
            }
            NetworkHdr::Ipv6(_) => {
                /* TODO */
                0
            }
            NetworkHdr::None => 0,
        }
    }

    /// Advanced Context Descriptor setup for VLAN or CSUM
    /// Return `(offload: bool, vlan_macip_lens: u32, type_tucmd_mlhl: u32, olinfo_status: u32)`.
    #[allow(clippy::type_complexity)]
    fn tx_offload(
        &self,
        ether_frame: &EtherFrameRef,
    ) -> Result<(bool, u32, u32, u32, u16, Option<u8>), IxgbeDriverErr> {
        let mut vlan_macip_lens = 0;
        let mut olinfo_status = 0;
        let mut offload = false;

        let ext = extract_headers(ether_frame.data).or(Err(IxgbeDriverErr::InvalidPacket))?;

        // Depend on whether doing TSO or not
        // Indicate the whole packet as payload when not doing TSO
        olinfo_status |= (ether_frame.data.len() as u32) << IXGBE_ADVTXD_PAYLEN_SHIFT;

        vlan_macip_lens |=
            (core::mem::size_of::<EtherHeader>() as u32) << IXGBE_ADVTXD_MACLEN_SHIFT;

        let (iphlen, mut type_tucmd_mlhl) = match ext.network {
            NetworkHdr::Ipv4(ip) => {
                if ether_frame
                    .csum_flags
                    .contains(PacketHeaderFlags::IPV4_CSUM_OUT)
                {
                    olinfo_status |= IXGBE_TXD_POPTS_IXSM << 8;
                    offload = true;
                }
                ((ip.header_len() as u32), IXGBE_ADVTXD_TUCMD_IPV4)
            }
            NetworkHdr::Ipv6(_ip) => (
                core::mem::size_of::<Ip6Hdr>() as u32,
                IXGBE_ADVTXD_TUCMD_IPV6,
            ),
            _ => {
                return Ok((offload, vlan_macip_lens, 0, olinfo_status, 0, None));
            }
        };

        vlan_macip_lens |= iphlen;

        let (cksum, cksum_offset) = match ext.transport {
            TransportHdr::Tcp(_tcp) => {
                type_tucmd_mlhl |= IXGBE_ADVTXD_TUCMD_L4T_TCP;
                if ether_frame
                    .csum_flags
                    .contains(PacketHeaderFlags::TCP_CSUM_OUT)
                {
                    olinfo_status |= IXGBE_TXD_POPTS_TXSM << 8;
                    offload = true;
                    let cksumoff = ETHER_HDR_LEN as u8
                        + core::mem::size_of::<Ip>() as u8
                        + offset_of!(TCPHdr, th_sum) as u8;
                    (self.calc_pseudo_cksum(&ext), cksumoff)
                } else {
                    (0, 0)
                }
            }
            TransportHdr::Udp(_udp) => {
                type_tucmd_mlhl |= IXGBE_ADVTXD_TUCMD_L4T_UDP;
                if ether_frame
                    .csum_flags
                    .contains(PacketHeaderFlags::UDP_CSUM_OUT)
                {
                    olinfo_status |= IXGBE_TXD_POPTS_TXSM << 8;
                    offload = true;
                    let cksumoff = ETHER_HDR_LEN as u8
                        + core::mem::size_of::<Ip>() as u8
                        + offset_of!(UDPHdr, uh_sum) as u8;
                    (self.calc_pseudo_cksum(&ext), cksumoff)
                } else {
                    (0, 0)
                }
            }
            _ => (0, 0),
        };

        // TODO:: TCP_TSO

        Ok((
            offload,
            vlan_macip_lens,
            type_tucmd_mlhl,
            olinfo_status,
            cksum,
            Some(cksum_offset),
        ))
    }

    /// Return `(ntxc: u32, cmd_type_len: u32, olinfo_status: u32)`.
    fn tx_ctx_setup(
        &self,
        tx: &mut Tx,
        ether_frame: &EtherFrameRef,
        head: usize,
    ) -> Result<(u32, u32, u32, u16, Option<u8>), IxgbeDriverErr> {
        let mut cmd_type_len = 0;

        let (
            mut offload,
            mut vlan_macip_lens,
            mut type_tucmd_mlhl,
            olinfo_status,
            cksum_pseudo,
            cksum_offset,
        ) = self.tx_offload(ether_frame)?;

        // TODO: Configuration for VLAN when VLANTAG is set
        if let Some(vlan) = ether_frame.vlan {
            vlan_macip_lens |= (vlan as u32) << IXGBE_ADVTXD_VLAN_SHIFT;
            cmd_type_len |= IXGBE_ADVTXD_DCMD_VLE;
            offload |= true;
        }

        if !offload {
            return Ok((0, cmd_type_len, olinfo_status, 0, None));
        }

        type_tucmd_mlhl |= IXGBE_ADVTXD_DCMD_DEXT | IXGBE_ADVTXD_DTYP_CTXT;

        let desc = &mut tx.tx_desc_ring.as_mut()[head];
        // Now copy bits into descriptor
        desc.adv_ctx.vlan_macip_lens = u32::to_le(vlan_macip_lens);
        desc.adv_ctx.type_tucmd_mlhl = u32::to_le(type_tucmd_mlhl);
        desc.adv_ctx.seqnum_seed = u32::to_le(0);
        desc.adv_ctx.mss_l4len_idx = u32::to_le(0); // mss_l4_len_idx

        Ok((1, cmd_type_len, olinfo_status, cksum_pseudo, cksum_offset))
    }

    /// This routine maps the mbufs to tx descriptors, allowing the
    /// TX engine to transmit the packets.
    fn encap(&self, tx: &mut Tx, ether_frame: &EtherFrameRef) -> Result<usize, IxgbeDriverErr> {
        let len = ether_frame.data.len();
        if len > MCLBYTES as usize {
            return Err(IxgbeDriverErr::InvalidPacket);
        }

        let mut head = tx.tx_desc_head;

        let (ntxc, mut cmd_type_len, olinfo_status, _cksum_pseudo, _cksum_offset) =
            self.tx_ctx_setup(tx, ether_frame, head)?;

        // Basic descriptor defines
        cmd_type_len |= IXGBE_ADVTXD_DTYP_DATA | IXGBE_ADVTXD_DCMD_IFCS | IXGBE_ADVTXD_DCMD_DEXT;

        let tx_slots = tx.tx_desc_ring.as_ref().len();

        head += ntxc as usize;
        if head == tx_slots {
            head = 0;
        }
        let addr = unsafe {
            let write_buf = tx.write_buf.as_mut().unwrap();
            let dst = &mut write_buf.as_mut()[head];
            core::ptr::copy_nonoverlapping(ether_frame.data.as_ptr(), dst.as_mut_ptr(), len);
            // TODO: cksum offloading
            //if let Some(cksum_offset) = cksum_offset {
            //log::info!("cksum: {}", cksum_pseudo);
            //core::ptr::write(
            //dst.as_mut_ptr().add(cksum_offset as usize) as *mut u16,
            //cksum_pseudo.to_be(),
            //);
            //}
            (write_buf.get_phy_addr().as_usize() + head * MCLBYTES as usize) as u64
        };

        let desc = &mut tx.tx_desc_ring.as_mut()[head];
        desc.adv_tx.buffer_addr = u64::to_le(addr);
        desc.adv_tx.cmd_type_len = u32::to_le(
            tx.txd_cmd | cmd_type_len | IXGBE_TXD_CMD_EOP | IXGBE_TXD_CMD_RS | len as u32,
        );
        desc.adv_tx.olinfo_status = u32::to_le(olinfo_status);

        head += 1;
        if head == tx_slots {
            head = 0;
        }

        tx.tx_desc_head = head;

        Ok(ntxc as usize + 1)
    }

    fn send(&self, que_id: usize, ether_frames: &[EtherFrameRef]) -> Result<(), IxgbeDriverErr> {
        let inner = self.inner.read();

        if !inner.link_active {
            return Ok(());
        }

        let mut node = MCSNode::new();
        let mut tx = self.que[que_id].tx.lock(&mut node);

        let sc_tx_slots = tx.tx_desc_ring.as_ref().len();

        let head = tx.tx_desc_head;
        let mut free = tx.tx_desc_tail;
        if free <= head {
            free += sc_tx_slots;
        }
        free -= head;

        let mut post = false;
        for ether_frame in ether_frames.iter() {
            // Check that we have the minimal number of TX descriptors.
            // use 2 because cksum setup can use an extra slot
            if free <= inner.num_segs as usize + 2 {
                break;
            }

            let used = self.encap(&mut tx, ether_frame)?;

            free -= used;

            post = true;
        }

        if post {
            ixgbe_hw::write_reg(&inner.info, IXGBE_TDT(que_id), tx.tx_desc_head as u32)?;
        }

        drop(inner);

        Ok(())
    }
}

fn allocate_msix(
    _hw: &ixgbe_hw::IxgbeHw,
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

fn allocate_msi(info: &mut PCIeInfo) -> Result<PCIeInt, IxgbeDriverErr> {
    info.disable_legacy_interrupt();
    if let Some(msix) = info.get_msix_mut() {
        msix.disable();
    }

    let segment_number = info.get_segment_group() as usize;
    let irq_name = format!("{}-{}", DEVICE_SHORT_NAME, info.get_bfd());

    if let Some(msi) = info.get_msi_mut() {
        msi.disable();

        let mut irq = msi
            .register_handler(
                irq_name.into(),
                Box::new(|irq| {
                    awkernel_lib::net::net_interrupt(irq);
                }),
                segment_number,
                awkernel_lib::cpu::raw_cpu_id() as u32,
            )
            .or(Err(IxgbeDriverErr::InitializeInterrupt))?;

        msi.set_multiple_message_enable(MultipleMessage::One)
            .or(Err(IxgbeDriverErr::InitializeInterrupt))?;

        irq.enable();
        msi.enable();

        Ok(PCIeInt::Msi(irq))
    } else {
        Err(IxgbeDriverErr::InitializeInterrupt)
    }
}

/// Allocate memory for the transmit and receive rings, and then
/// the descriptors associated with each, called only once at attach.
fn allocate_queue(info: &PCIeInfo, que_id: usize) -> Result<Queue, IxgbeDriverErr> {
    let tx_size = core::mem::size_of::<TxDescriptor>() * DEFAULT_TXD;
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
        read_queue: RingQ::new(RECV_QUEUE_SIZE),
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
        let inner = self.inner.read();
        if inner.link_active {
            if inner.link_state == ixgbe_hw::LinkState::LinkStateFullDuplex {
                LinkStatus::UpFullDuplex
            } else {
                LinkStatus::UpHalfDuplex
            }
        } else {
            LinkStatus::Down
        }
    }

    fn link_speed(&self) -> u64 {
        let inner = self.inner.read();

        match inner.link_speed {
            speed if speed & IXGBE_LINK_SPEED_10GB_FULL != 0 => 10000,
            speed if speed & IXGBE_LINK_SPEED_5GB_FULL != 0 => 5000,
            speed if speed & IXGBE_LINK_SPEED_2_5GB_FULL != 0 => 2500,
            speed if speed & IXGBE_LINK_SPEED_1GB_FULL != 0 => 1000,
            speed if speed & IXGBE_LINK_SPEED_100_FULL != 0 => 100,
            speed if speed & IXGBE_LINK_SPEED_10_FULL != 0 => 10,
            _ => 0,
        }
    }

    fn mac_address(&self) -> [u8; 6] {
        let inner = self.inner.read();

        inner.hw.get_mac_addr()
    }

    fn recv(&self, que_id: usize) -> Result<Option<EtherFrameBuf>, NetDevError> {
        {
            let mut node = MCSNode::new();
            let mut rx = self.que[que_id].rx.lock(&mut node);

            let data = rx.read_queue.pop();
            if data.is_some() {
                return Ok(data);
            }
        }

        self.rx_recv(que_id).or(Err(NetDevError::DeviceError))?;

        let mut node = MCSNode::new();
        let mut rx = self.que[que_id].rx.lock(&mut node);
        if let Some(data) = rx.read_queue.pop() {
            Ok(Some(data))
        } else {
            Ok(None)
        }
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
        let frames = [data];
        self.send(que_id, &frames).or(Err(NetDevError::DeviceError))
    }

    fn up(&self) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();

        if !inner.flags.contains(NetFlags::UP) {
            if let Err(err_init) = inner.init(&self.que) {
                if let Err(err_stop) = inner.stop(&self.que) {
                    log::error!("ixgbe: stop failed: {:?}", err_stop);
                }

                log::error!("ixgbe: init failed: {:?}", err_init);
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
        let mut inner = self.inner.write();

        if inner.flags.contains(NetFlags::UP) {
            if let Err(e) = inner.stop(&self.que) {
                log::error!("ixgbe: stop failed: {:?}", e);
                Err(NetDevError::DeviceError)
            } else {
                inner.flags.remove(NetFlags::UP);
                Ok(())
            }
        } else {
            Err(NetDevError::AlreadyDown)
        }
    }

    fn interrupt(&self, irq: u16) -> Result<(), NetDevError> {
        self.intr(irq).or(Err(NetDevError::DeviceError))
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

    fn rx_irq_to_que_id(&self, irq: u16) -> Option<usize> {
        let inner = self.inner.read();

        for key in inner.irq_to_rx_tx_link.keys() {
            if *key == irq {
                if let IRQRxTxLink::RxTx(que_id) = inner.irq_to_rx_tx_link[key] {
                    return Some(que_id);
                } else {
                    return None;
                }
            }
        }

        None
    }

    fn add_multicast_addr(&self, _addr: &[u8; 6]) -> Result<(), NetDevError> {
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

    fn remove_multicast_addr(&self, _addr: &[u8; 6]) -> Result<(), NetDevError> {
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
        let inner = self.inner.read();

        if inner.is_poll_mode {
            return Ok(());
        }

        let mut irqs = Vec::new();
        for irq in inner.irq_to_rx_tx_link.keys() {
            if *irq != 0 {
                irqs.push(*irq);
            }
        }

        drop(inner);

        for irq in irqs {
            let _ = self.intr(irq);
        }

        Ok(())
    }

    fn tick_msec(&self) -> Option<u64> {
        Some(200)
    }
}
