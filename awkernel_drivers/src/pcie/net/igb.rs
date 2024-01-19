//! # Intel Gigabit Ethernet Controller

use crate::pcie::{
    capability::msi::MultipleMessage, net::igb::igb_hw::MacType, PCIeDevice, PCIeDeviceErr,
    PCIeInfo,
};
use alloc::{boxed::Box, sync::Arc, vec, vec::Vec};
use awkernel_async_lib_verified::ringq::RingQ;
use awkernel_lib::{
    addr::{virt_addr::VirtAddr, Addr},
    dma_pool::DMAPool,
    interrupt::IRQ,
    net::{
        ether::{
            extract_headers, EtherHeader, NetworkHdr, TransportHdr, ETHER_HDR_LEN, ETHER_MAX_LEN,
            ETHER_TYPE_VLAN,
        },
        ip::Ip,
        ipv6::Ip6Hdr,
        multicast::{ipv4_addr_to_mac_addr, MulticastIPv4},
        tcp::TCPHdr,
        udp::UDPHdr,
        EtherFrameBuf, EtherFrameRef, NetCapabilities, NetDevError, NetDevice, NetFlags,
        PacketHeaderFlags,
    },
    paging::{Frame, FrameAllocator, PageTable, PAGESIZE},
    sync::{
        mutex::{MCSNode, Mutex},
        rwlock::RwLock,
    },
};
use core::{
    fmt::{self, Debug},
    net::Ipv4Addr,
};
use memoffset::offset_of;

mod igb_hw;

#[allow(dead_code)]
mod igb_regs;

use igb_regs::*;

const DEVICE_NAME: &str = "igb: Intel Gigabit Ethernet Controller";
const DEVICE_SHORT_NAME: &str = "igb";

const RECV_QUEUE_SIZE: usize = 32;

pub const MAX_NUM_MULTICAST_ADDRESSES: usize = 128;

// Supported RX Buffer Sizes
const RXBUFFER_2048: u32 = 2048;
const RXBUFFER_4096: u32 = 4096;
const RXBUFFER_8192: u32 = 8192;
const _RXBUFFER_16384: u32 = 16384;

const TXBUFFER_16384: u32 = 16384;

/// Transmit Interrupt Delay Value.
///
/// Valid Range: 0-65535 (0=off)
/// Default Value: 64
///   This value delays the generation of transmit interrupts in units of
///   1.024 microseconds. Transmit interrupt reduction can improve CPU
///   efficiency if properly tuned for specific network traffic. If the
///   system is reporting dropped transmits, this value may be set too high
///   causing the driver to run out of available transmit descriptors.
const DEFAULT_TIDV: u32 = 64;

/// Transmit Absolute Interrupt Delay Value.
///
/// (Not valid for 82542/82543/82544)
/// Valid Range: 0-65535 (0=off)
/// Default Value: 64
///   This value, in units of 1.024 microseconds, limits the delay in which a
///   transmit interrupt is generated. Useful only if EM_TIDV is non-zero,
///   this value ensures that an interrupt is generated after the initial
///   packet is sent on the wire within the set amount of time.  Proper tuning,
///   along with EM_TIDV, may improve traffic throughput in specific
///   network conditions.
const DEFAULT_TADV: u32 = 64;

/// Receive Interrupt Delay Timer (Packet Timer).
///
/// Valid Range: 0-65535 (0=off)
/// Default Value: 0
///   This value delays the generation of receive interrupts in units of 1.024
///   microseconds.  Receive interrupt reduction can improve CPU efficiency if
///   properly tuned for specific network traffic. Increasing this value adds
///   extra latency to frame reception and can end up decreasing the throughput
///   of TCP traffic. If the system is reporting dropped receives, this value
///   may be set too high, causing the driver to run out of available receive
///   descriptors.
///
///   CAUTION: When setting EM_RDTR to a value other than 0, adapters
///            may hang (stop transmitting) under certain network conditions.
///            If this occurs a WATCHDOG message is logged in the system
///            event log. In addition, the controller is automatically reset,
///            restoring the network connection. To eliminate the potential
///            for the hang ensure that EM_RDTR is set to 0.
const DEFAULT_RDTR: u32 = 0;

/// MAX_INTS_PER_SEC (ITR - Interrupt Throttle Register).
///
/// The Interrupt Throttle Register (ITR) limits the delivery of interrupts
/// to a reasonable rate by providing a guaranteed inter-interrupt delay
/// between interrupts asserted by the Ethernet controller.
const MAX_INTS_PER_SEC: u32 = 8000;
const DEFAULT_ITR: u32 = 1000000000 / (MAX_INTS_PER_SEC * 256);

type RxRing = [RxDescriptor; MAX_RXD];
type RxBuffer = [[u8; RXBUFFER_2048 as usize]; MAX_RXD];

type TxRing = [TxDescriptor; MAX_TXD];
type TxBuffer = [[u8; TXBUFFER_16384 as usize]; MAX_TXD];

struct Rx {
    rx_desc_head: u32,
    rx_desc_tail: usize,
    rx_desc_ring: DMAPool<RxRing>,

    read_buf: Option<DMAPool<RxBuffer>>,

    read_queue: RingQ<EtherFrameBuf>,

    // Statistics
    dropped_pkts: u64,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ActiveChecksumContext {
    None,
    TcpIP,
    UdpIP,
}

struct Tx {
    tx_desc_head: usize,
    tx_desc_tail: usize,
    tx_desc_ring: DMAPool<TxRing>,

    txd_cmd: u32,

    active_checksum_context: ActiveChecksumContext,

    write_buf: Option<DMAPool<TxBuffer>>,
}

struct Queue {
    tx: Mutex<Tx>,
    rx: Mutex<Rx>,
    me: usize,
    eims: u32,
}

/// Legacy Transmit Descriptor Format (16B)
#[derive(Debug, Clone, Copy)]
#[repr(C, packed)]
struct LegacyTxDescriptor {
    buf: u64,
    length: u16,
    cso: u8,
    cmd: u8,
    status: u8,
    css: u8,
    vtags: u16,
}

/// Advanced Transmit Descriptor Format (16B)
#[derive(Debug, Clone, Copy)]
#[repr(C, packed)]
struct AdvTxDescriptor {
    buf: u64,
    lower: u32,
    upper: u32,
}

/// Advanced Transmit Context Descriptor Format (16B)
#[derive(Debug, Clone, Copy)]
#[repr(C, packed)]
struct AdvTxContextDescriptor {
    vlan_macip_lens: u32,
    launch_time_or_seqnum_seed: u32,
    type_tucmd_mlhl: u32,
    mss_l4len_idx: u32,
}

#[derive(Debug, Clone, Copy)]
#[repr(C, packed)]
struct ContextDesc {
    ipcss: u8,  // IP checksum start
    ipcso: u8,  // IP checksum offset
    ipcse: u16, // IP checksum end
    tucss: u8,  // TCP/UDP checksum start
    tucso: u8,  // TCP/UDP checksum offset
    tucse: u16, // TCP/UDP checksum end
    cmd_and_length: u32,
    status: u8,  // Descriptor status
    hdr_len: u8, // Header length
    mss: u16,    // Maximum segment size
}

#[repr(C)]
/// Legacy Transmit Descriptor Format (16B)
union TxDescriptor {
    legacy: LegacyTxDescriptor,
    context_desc: ContextDesc,
    adv_tx: AdvTxDescriptor,
    adv_ctx: AdvTxContextDescriptor,
}

union RxDescriptor {
    data: [u64; 2],
    desc: RxDescriptorInner,
}

#[derive(Debug, Clone, Copy)]
#[repr(C, packed)]
/// Legacy Receive Descriptor Format (16B)
struct RxDescriptorInner {
    buf: u64,
    len: u16,
    checksum: u16,
    status: u8,
    error: u8,
    special: u16,
}

struct IgbInner {
    info: PCIeInfo,
    hw: igb_hw::IgbHw,

    flags: NetFlags,
    capabilities: NetCapabilities,
    link_active: bool,
    link_speed: igb_hw::Speed,
    link_duplex: igb_hw::Duplex,
    smart_speed: u32,
    pcie_int: PCIeInt,

    multicast_ipv4: MulticastIPv4,
}

/// Intel Gigabit Ethernet Controller driver
pub struct Igb {
    // The order of lock acquisition must be as follows:
    //
    // 1. `IgbInner`'s lock
    // 2. `Queue`'s lock
    // 3. `Queue`'s unlock
    // 4. `IgbInner`'s unlock
    //
    // Otherwise, a deadlock will occur.
    que: [Queue; 1],
    inner: RwLock<IgbInner>,
}

pub fn attach<F, FA, E>(
    mut info: PCIeInfo,
    page_table: &mut impl PageTable<F, FA, E>,
    page_allocator: &mut FA,
) -> Result<(), PCIeDeviceErr>
where
    F: Frame,
    FA: FrameAllocator<F, E>,
    E: Debug,
{
    // Initialize PCIeInfo

    // Map the memory regions of MMIO.
    if let Err(e) = info.map_bar(page_table, page_allocator) {
        log::warn!("Failed to map the memory regions of MMIO: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }

    // Read the capability of PCIe device.
    info.read_capability();

    let igb = Igb::new(info)?;
    let _ = igb.up();

    awkernel_lib::net::add_interface(Arc::new(igb), None);

    Ok(())
}

#[derive(Debug, Clone, Copy)]
pub enum IgbDriverErr {
    MemoryMapFailure,
    InitializeInterrupt,
    UnknownDeviceID,
    UnknownRevisionD,
    NotPciExpress,
    NoBar0,
    NoBar1,
    Bar1IsNotMMIO,
    ReadFailure,
    NotSupported,
    FailedFlashDescriptor,
    MasterDisableTimeout,
    PhyReset,
    Config,
    Reset,
    SwfwSync,
    Phy,
    Param,
    PhyType,
    EEPROM,
    DMAPool,
    HostInterfaceCommand,
    NotImplemented,
    InvalidPacket,
}

#[derive(Debug)]
struct MsiX {
    link_vec: u32,
    link_mask: u32,
    queues_mask: u32,
}

#[derive(Debug)]
enum PCIeInt {
    None,
    Msi(IRQ),
    MsiX(MsiX),
}

impl From<IgbDriverErr> for PCIeDeviceErr {
    fn from(value: IgbDriverErr) -> Self {
        log::error!("igb: {:?}", value);

        match value {
            IgbDriverErr::NotImplemented => PCIeDeviceErr::NotImplemented,
            IgbDriverErr::ReadFailure => PCIeDeviceErr::ReadFailure,
            IgbDriverErr::InvalidPacket => PCIeDeviceErr::CommandFailure,
            _ => PCIeDeviceErr::InitFailure,
        }
    }
}

impl fmt::Display for IgbDriverErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::MemoryMapFailure => {
                write!(f, "Memory map fault occurs during driver initialization.")
            }
            Self::InitializeInterrupt => write!(f, "Interrupt initialization failure."),
            Self::UnknownDeviceID => write!(f, "Unknown device id."),
            Self::UnknownRevisionD => write!(f, "Unknown revision id."),
            Self::NotPciExpress => write!(f, "Not a pci express device."),
            Self::NoBar0 => write!(f, "No BAR0."),
            Self::NoBar1 => write!(f, "No BAR1."),
            Self::Bar1IsNotMMIO => write!(f, "BAR1 is not MMIO."),
            Self::ReadFailure => write!(f, "Read failure."),
            Self::NotSupported => write!(f, "Not supported."),
            Self::FailedFlashDescriptor => write!(f, "Failed to flush descriptor."),
            Self::MasterDisableTimeout => write!(f, "Master disable timeout."),
            Self::PhyReset => write!(f, "PHY reset failure."),
            Self::Config => write!(f, "Configuration failure."),
            Self::Reset => write!(f, "Reset failure."),
            Self::SwfwSync => write!(f, "Software firmware synchronization failure."),
            Self::Phy => write!(f, "PHY failure."),
            Self::Param => write!(f, "Parameter failure."),
            Self::PhyType => write!(f, "PHY type failure."),
            Self::EEPROM => write!(f, "EEPROM failure."),
            Self::DMAPool => write!(f, "DMA pool failure."),
            Self::HostInterfaceCommand => write!(f, "Host interface command failure."),
            Self::NotImplemented => write!(f, "Not implemented."),
            Self::InvalidPacket => write!(f, "Invalid packet."),
        }
    }
}

impl IgbInner {
    fn new(mut info: PCIeInfo, que: &[Queue]) -> Result<Self, PCIeDeviceErr> {
        let mut hw = igb_hw::IgbHw::new(&mut info)?;

        let pcie_int = if let Ok(pcie_int) = allocate_msi(&mut info) {
            pcie_int
        } else {
            PCIeInt::None
        };

        // https://github.com/openbsd/src/blob/4d2f7ea336a48b11a249752eb2582887d8d4828b/sys/dev/pci/if_em_hw.c#L1260-L1263
        if (hw.get_mac_type() as u32) >= MacType::Em82571 as u32
            && !hw.get_initialize_hw_bits_disable()
        {
            for q in que.iter() {
                let offset = txdctl(q.me);
                let mut reg_txdctl = igb_hw::read_reg(&info, offset)?;
                reg_txdctl |= TXDCTL_COUNT_DESC;
                igb_hw::write_reg(&info, offset, reg_txdctl)?;
            }
        }

        hardware_init(&mut hw, &mut info)?;

        // Set the transmit descriptor write-back policy
        if (hw.get_mac_type() as u32) > MacType::Em82544 as u32 {
            for q in que.iter() {
                let ctrl = igb_hw::read_reg(&info, txdctl(q.me))?;
                let ctrl = (ctrl & !TXDCTL_WTHRESH) | TXDCTL_FULL_TX_DESC_WB;
                igb_hw::write_reg(&info, txdctl(q.me), ctrl)?;
            }
        }

        hw.read_mac_addr(&info)?;

        // setup interface
        let flags = NetFlags::BROADCAST | NetFlags::SIMPLEX | NetFlags::MULTICAST;
        let mut capabilities = NetCapabilities::VLAN_MTU | NetCapabilities::VLAN_HWTAGGING;

        if hw.get_mac_type() as u32 >= MacType::Em82543 as u32 {
            capabilities |= NetCapabilities::CSUM_TCPv4 | NetCapabilities::CSUM_UDPv4;
        }

        if MacType::Em82575 as u32 <= hw.get_mac_type() as u32
            && hw.get_mac_type() as u32 <= MacType::EmI210 as u32
        {
            capabilities |= NetCapabilities::CSUM_IPv4
                | NetCapabilities::CSUM_TCPv6
                | NetCapabilities::CSUM_UDPv6;
        }

        let perm_mac_addr = hw.get_perm_mac_addr();

        log::info!(
            "{:02x}:{:02x}:({:04x}:{:04x}): {}, MAC = {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
            info.segment_group,
            info.bus,
            info.vendor,
            info.id,
            DEVICE_NAME,
            perm_mac_addr[0],
            perm_mac_addr[1],
            perm_mac_addr[2],
            perm_mac_addr[3],
            perm_mac_addr[4],
            perm_mac_addr[5]
        );

        // Initialize statistics
        hw.clear_hw_cntrs(&info)?;

        hw.set_get_link_status(true);

        let igb = Self {
            info,
            hw,
            flags,
            capabilities,
            link_active: false,
            link_speed: igb_hw::Speed::None,
            link_duplex: igb_hw::Duplex::None,
            smart_speed: 0,
            pcie_int,
            multicast_ipv4: MulticastIPv4::new(),
        };

        igb.new2()
    }

    fn new2(mut self) -> Result<Self, PCIeDeviceErr> {
        self.update_link_status()?;

        // Indicate SOL/IDER usage
        if self.hw.check_phy_reset_block(&self.info).is_err() {
            log::warn!("igb: PHY reset is blocked due to SOL/IDER session.");
        }

        Ok(self)
    }

    fn update_link_status(&mut self) -> Result<(), IgbDriverErr> {
        if igb_hw::read_reg(&self.info, STATUS)? & STATUS_LU != 0 {
            if !self.link_active {
                let (link_speed, link_duplex) = self.hw.get_speed_and_duplex(&self.info)?;
                // Check if we may set SPEED_MODE bit on PCI-E
                if link_speed == igb_hw::Speed::S1000Mbps
                    && matches!(
                        self.hw.get_mac_type(),
                        MacType::Em82571
                            | MacType::Em82572
                            | MacType::Em82575
                            | MacType::Em82576
                            | MacType::Em82580
                    )
                {
                    const SPEED_MODE_BIT: u32 = 1 << 21; // On PCI-E MACs only

                    let tarc0 = igb_hw::read_reg(&self.info, TARC0)?;
                    igb_hw::write_reg(&self.info, TARC0, tarc0 | SPEED_MODE_BIT)?;
                }

                self.link_speed = link_speed;
                self.link_duplex = link_duplex;
                self.link_active = true;
                self.smart_speed = 0;
            }

            log::debug!("igb: link up");
        } else if self.link_active {
            self.link_speed = igb_hw::Speed::None;
            self.link_duplex = igb_hw::Duplex::None;
            self.link_active = false;
        }

        Ok(())
    }

    fn init(&mut self, que: &[Queue]) -> Result<(), IgbDriverErr> {
        use igb_hw::MacType::*;

        self.stop(false, que)?;

        // Packet Buffer Allocation (PBA)
        // Writing PBA sets the receive portion of the buffer
        // the remainder is used for the transmit buffer.
        //
        // Devices before the 82547 had a Packet Buffer of 64K.
        //   Default allocation: PBA=48K for Rx, leaving 16K for Tx.
        // After the 82547 the buffer was reduced to 40K.
        //   Default allocation: PBA=30K for Rx, leaving 10K for Tx.
        //   Note: default does not leave enough room for Jumbo Frame >10k.
        let pba = match self.hw.get_mac_type() {
            Em82547 | Em82547Rev2 => {
                return Err(IgbDriverErr::NotSupported);
            }
            Em82571 | Em82572 | Em82575 | Em82576 | Em82580 | Em80003es2lan | EmI350 => PBA_32K,
            EmI210 => PBA_34K,
            Em82573 => PBA_12K,
            Em82574 => PBA_20K,
            EmIch8lan => PBA_8K,
            EmIch9lan | EmIch10lan => {
                if self.hw.get_max_frame_size() > RXBUFFER_4096 {
                    PBA_14K
                } else {
                    PBA_10K
                }
            }
            EmPchlan | EmPch2lan | EmPchLpt | EmPchSpt | EmPchCnp | EmPchTgp | EmPchAdp => PBA_26K,
            _ => {
                if self.hw.get_max_frame_size() > RXBUFFER_8192 {
                    PBA_40K
                } else {
                    PBA_48K
                }
            }
        };
        igb_hw::write_reg(&self.info, PBA, pba)?;

        // Initialize the hardware
        hardware_init(&mut self.hw, &mut self.info)?;

        self.update_link_status()?;

        igb_hw::write_reg(&self.info, VET, ETHER_TYPE_VLAN as u32)?;
        if self.capabilities.contains(NetCapabilities::VLAN_HWTAGGING) {
            self.enable_hw_vlans()?;
        }

        // Prepare transmit descriptors and buffers
        self.setup_transmit_structures(que)?;
        self.initialize_transmit_unit(que)?;

        // Prepare receive descriptors and buffers
        self.setup_receive_structures(que)?;
        self.initialize_receive_unit(que)?;

        self.setup_queues_msix()?;

        self.iff()?;

        self.flags |= NetFlags::RUNNING;
        self.hw.clear_hw_cntrs(&self.info)?;

        self.enable_intr()?; // TODO

        // Don't reset the phy next time init gets called
        self.hw.set_phy_reset_disable(true);

        self.hw.check_for_link(&self.info)?;

        Ok(())
    }

    fn iff(&mut self) -> Result<(), IgbDriverErr> {
        if self.hw.get_mac_type() == MacType::Em82542Rev2_0 {
            return Err(IgbDriverErr::NotSupported);
        }

        let mut reg_ctrl = igb_hw::read_reg(&self.info, RCTL)?;
        reg_ctrl &= !(RCTL_MPE | RCTL_UPE);
        self.flags &= !NetFlags::ALLMULTI;

        if self.flags.contains(NetFlags::PROMISC)
            || self.multicast_ipv4.ranges_len() > 0
            || self.multicast_ipv4.addrs_len() > MAX_NUM_MULTICAST_ADDRESSES
        {
            self.flags |= NetFlags::ALLMULTI;
            reg_ctrl |= RCTL_MPE;
            if self.flags.contains(NetFlags::PROMISC) {
                reg_ctrl |= RCTL_UPE;
            }
        } else {
            self.hw.clear_mta(&self.info)?;

            for mc_addr in self.multicast_ipv4.addrs_iter() {
                let mc_addr = ipv4_addr_to_mac_addr(mc_addr);
                let hash_value = self.hw.hash_mc_addr(&mc_addr);
                self.hw.mta_set(&self.info, hash_value)?;
            }
        }

        igb_hw::write_reg(&self.info, RCTL, reg_ctrl)?;

        Ok(())
    }

    fn initialize_transmit_unit(&mut self, que: &[Queue]) -> Result<(), IgbDriverErr> {
        use igb_hw::MacType::*;

        for que in que.iter() {
            let mut node = MCSNode::new();
            let mut tx = que.tx.lock(&mut node);

            // Setup the Base and Length of the Tx Descriptor Ring
            igb_hw::write_reg(
                &self.info,
                tdlen_offset(que.me),
                tx.tx_desc_ring.get_size() as u32,
            )?;
            igb_hw::write_reg(
                &self.info,
                tdbah_offset(que.me),
                (tx.tx_desc_ring.get_phy_addr().as_usize() as u64 >> 32) as u32,
            )?;
            igb_hw::write_reg(
                &self.info,
                tdbal_offset(que.me),
                tx.tx_desc_ring.get_phy_addr().as_usize() as u32,
            )?;

            // Setup the HW Tx Head and Tail descriptor pointers
            igb_hw::write_reg(&self.info, tdt_offset(que.me), 0)?;
            igb_hw::write_reg(&self.info, tdh_offset(que.me), 0)?;

            // Set the default values for the Tx Inter Packet Gap timer
            let reg_tipg = match self.hw.get_mac_type() {
                Em82542Rev2_0 | Em82542Rev2_1 => {
                    DEFAULT_82542_TIPG_IPGT
                        | (DEFAULT_82542_TIPG_IPGR1 << E1000_TIPG_IPGR1_SHIFT)
                        | (DEFAULT_82542_TIPG_IPGR2 << E1000_TIPG_IPGR2_SHIFT)
                }
                Em80003es2lan => {
                    DEFAULT_82543_TIPG_IPGR1
                        | (DEFAULT_80003ES2LAN_TIPG_IPGR2 << E1000_TIPG_IPGR2_SHIFT)
                }
                _ => {
                    let reg_tipg = if matches!(
                        self.hw.get_media_type(),
                        igb_hw::MediaType::Fiber | igb_hw::MediaType::InternalSerdes
                    ) {
                        DEFAULT_82543_TIPG_IPGT_FIBER
                    } else {
                        DEFAULT_82543_TIPG_IPGT_COPPER
                    };

                    reg_tipg
                        | (DEFAULT_82543_TIPG_IPGR1 << E1000_TIPG_IPGR1_SHIFT)
                        | (DEFAULT_82543_TIPG_IPGR2 << E1000_TIPG_IPGR2_SHIFT)
                }
            };

            igb_hw::write_reg(&self.info, TIPG, reg_tipg)?;
            igb_hw::write_reg(&self.info, TIDV, DEFAULT_TIDV)?;
            if self.hw.get_mac_type() as u32 >= MacType::Em82540 as u32 {
                igb_hw::write_reg(&self.info, TADV, DEFAULT_TADV)?;
            }

            // Setup Transmit Descriptor Base Settings
            tx.txd_cmd = TXD32_CMD_IFCS | TXD32_CMD_IDE;

            if matches!(
                self.hw.get_mac_type(),
                Em82575 | Em82580 | Em82576 | EmI210 | EmI350
            ) {
                // 82575/6 need to enable the TX queue and lack the IDE bit
                let mut reg_tctl = igb_hw::read_reg(&self.info, txdctl_offset(que.me))?;
                reg_tctl |= TXDCTL_QUEUE_ENABLE;
                igb_hw::write_reg(&self.info, txdctl_offset(que.me), reg_tctl)?;
            }
        }

        // Program the Transmit Control Register
        let mut reg_tctl = TCTL_PSP | TCTL_EN | (COLLISION_THRESHOLD << CT_SHIFT);
        if self.hw.get_mac_type() as u32 >= MacType::Em82571 as u32 {
            reg_tctl |= TCTL_MULR;
        }
        if self.link_duplex == igb_hw::Duplex::Full {
            reg_tctl |= FDX_COLLISION_DISTANCE << COLD_SHIFT;
        } else {
            reg_tctl |= HDX_COLLISION_DISTANCE << COLD_SHIFT;
        }
        // This write will effectively turn on the transmit unit
        igb_hw::write_reg(&self.info, TCTL, reg_tctl)?;

        // SPT Si errata workaround to avoid data corruption
        if self.hw.get_mac_type() == MacType::EmPchSpt {
            let mut reg_val = igb_hw::read_reg(&self.info, IOSFPC)?;
            reg_val |= RCTL_RDMTS_HEX;
            igb_hw::write_reg(&self.info, IOSFPC, reg_val)?;

            let mut reg_val = igb_hw::read_reg(&self.info, TARC0)?;
            // i218-i219 Specification Update 1.5.4.5
            reg_val &= !TARC0_CB_MULTIQ_3_REQ;
            reg_val |= TARC0_CB_MULTIQ_2_REQ;
            igb_hw::write_reg(&self.info, TARC0, reg_val)?;
        }

        Ok(())
    }

    fn initialize_receive_unit(&mut self, que: &[Queue]) -> Result<(), IgbDriverErr> {
        use igb_hw::MacType::*;

        // Make sure receives are disabled while setting up the descriptor ring
        igb_hw::write_reg(&self.info, RCTL, 0)?;

        // Set the Receive Delay Timer Register
        igb_hw::write_reg(&self.info, RDTR, DEFAULT_RDTR | RDT_FPDB)?;

        if self.hw.get_mac_type() as u32 >= MacType::Em82540 as u32 {
            // Set the interrupt throttling rate.  Value is calculated
            // as DEFAULT_ITR = 1/(MAX_INTS_PER_SEC * 256ns)
            igb_hw::write_reg(&self.info, ITR, DEFAULT_ITR)?;
        }

        // Setup the Receive Control Register
        let mut reg_rctl = RCTL_EN | RCTL_BAM | RCTL_LBM_NO | RCTL_RDMTS_HALF;

        if self.hw.get_tbi_compatibility_on() {
            reg_rctl |= RCTL_SBP;
        }

        // The i350 has a bug where it always strips the CRC whether
        // asked to or not.  So ask for stripped CRC here and
        // cope in rxeof
        if matches!(self.hw.get_mac_type(), EmI210 | EmI350) {
            reg_rctl |= RCTL_SECRC;
        }

        reg_rctl |= RCTL_SZ_2048;

        if self.hw.get_max_frame_size() as usize != ETHER_MAX_LEN {
            reg_rctl |= RCTL_LPE;
        }

        // Enable 82543 Receive Checksum Offload for TCP and UDP
        if self.hw.get_mac_type() as u32 >= MacType::Em82543 as u32 {
            let mut reg_rxcsum = igb_hw::read_reg(&self.info, RXCSUM)?;
            reg_rxcsum |= RXCSUM_IPOFL | RXCSUM_TUOFL;
            igb_hw::write_reg(&self.info, RXCSUM, reg_rxcsum)?;
        }

        // XXX TEMPORARY WORKAROUND: on some systems with 82573
        // long latencies are observed, like Lenovo X60.
        if self.hw.get_mac_type() == MacType::Em82573 {
            igb_hw::write_reg(&self.info, RDTR, 0x20)?;
        }

        let que_len = que.len();
        for que in que.iter() {
            let mut node = MCSNode::new();
            let rx = que.rx.lock(&mut node);

            if que_len > 1 {
                // Disable Drop Enable for every queue, default has
                // it enabled for queues > 0
                let mut reg_srrctl = igb_hw::read_reg(&self.info, srrctl_offset(que.me))?;
                reg_srrctl &= !SRRCTL_DROP_EN;
                igb_hw::write_reg(&self.info, srrctl_offset(que.me), reg_srrctl)?;
            }

            // Setup the Base and Length of the Rx Descriptor Ring
            igb_hw::write_reg(
                &self.info,
                rdlen_offset(que.me),
                rx.rx_desc_ring.get_size() as u32,
            )?;
            igb_hw::write_reg(
                &self.info,
                rdbah_offset(que.me),
                (rx.rx_desc_ring.get_phy_addr().as_usize() as u64 >> 32) as u32,
            )?;
            igb_hw::write_reg(
                &self.info,
                rdbal_offset(que.me),
                rx.rx_desc_ring.get_phy_addr().as_usize() as u32,
            )?;

            if matches!(
                self.hw.get_mac_type(),
                Em82575 | Em82576 | Em82580 | EmI210 | EmI350
            ) {
                // 82575/6 need to enable the RX queue
                let mut reg = igb_hw::read_reg(&self.info, rxdctl_offset(que.me))?;
                reg |= RXDCTL_QUEUE_ENABLE;
                igb_hw::write_reg(&self.info, rxdctl_offset(que.me), reg)?;
            }
        }

        // Enable Receives
        igb_hw::write_reg(&self.info, RCTL, reg_rctl)?;

        // Setup the HW Rx Head and Tail Descriptor Pointers
        for que in que.iter() {
            let mut node = MCSNode::new();
            let rx = que.rx.lock(&mut node);

            igb_hw::write_reg(&self.info, rdh_offset(que.me), 0)?;
            igb_hw::write_reg(&self.info, rdt_offset(que.me), rx.rx_desc_head)?;
        }

        Ok(())
    }

    fn setup_queues_msix(&mut self) -> Result<(), IgbDriverErr> {
        let PCIeInt::MsiX(msix) = &mut self.pcie_int else {
            return Ok(());
        };

        // TODO
        Ok(())
    }

    /// This turns on the hardware offload of the VLAN
    /// tag stripping and insertion.
    fn enable_hw_vlans(&self) -> Result<(), IgbDriverErr> {
        let mut ctrl = igb_hw::read_reg(&self.info, CTRL)?;
        ctrl |= CTRL_VME;
        igb_hw::write_reg(&self.info, CTRL, ctrl)?;

        Ok(())
    }

    fn setup_transmit_structures(&mut self, que: &[Queue]) -> Result<(), IgbDriverErr> {
        for que in que.iter() {
            let mut node = MCSNode::new();
            let mut tx = que.tx.lock(&mut node);
            tx.tx_desc_tail = 0;
            tx.tx_desc_head = 0;

            let tx_desc_ring = tx.tx_desc_ring.as_mut();

            let tx_buffer_size = TXBUFFER_16384 as usize * MAX_TXD;
            let write_buf = DMAPool::new(
                self.info.get_segment_group() as usize,
                tx_buffer_size / PAGESIZE,
            )
            .ok_or(IgbDriverErr::DMAPool)?;

            let buf_phy_addr = write_buf.get_phy_addr().as_usize();

            for (i, desc) in tx_desc_ring.iter_mut().enumerate() {
                desc.legacy.buf = (buf_phy_addr + i * TXBUFFER_16384 as usize) as u64;
                desc.legacy.length = 0;
                desc.legacy.cso = 0;
                desc.legacy.cmd = 0;
                desc.legacy.status = 0;
                desc.legacy.css = 0;
                desc.legacy.vtags = 0;
            }

            tx.write_buf = Some(write_buf);
        }

        Ok(())
    }

    fn setup_receive_structures(&mut self, que: &[Queue]) -> Result<(), IgbDriverErr> {
        for que in que.iter() {
            let mut node = MCSNode::new();
            let mut rx = que.rx.lock(&mut node);

            rx.rx_desc_tail = 0;
            rx.rx_desc_head = rx.rx_desc_ring.as_ref().len() as u32 - 1;

            let rx_desc_ring = rx.rx_desc_ring.as_mut();

            let rx_buffer_size = RXBUFFER_2048 as usize * MAX_RXD;
            let read_buf = DMAPool::new(
                self.info.get_segment_group() as usize,
                rx_buffer_size / PAGESIZE,
            )
            .ok_or(IgbDriverErr::DMAPool)?;

            let buf_phy_addr = read_buf.get_phy_addr().as_usize();

            for (i, desc) in rx_desc_ring.iter_mut().enumerate() {
                desc.data = [0; 2];
                desc.desc.buf = (buf_phy_addr + i * RXBUFFER_2048 as usize) as u64;
                desc.desc.len = RXBUFFER_2048 as u16;
            }

            rx.read_buf = Some(read_buf);
        }

        Ok(())
    }

    fn stop(&mut self, softonly: bool, que: &[Queue]) -> Result<(), IgbDriverErr> {
        self.flags.remove(NetFlags::RUNNING);

        if !softonly {
            self.disable_intr()?;
        }

        if self.hw.get_mac_type() as u32 >= MacType::EmPchSpt as u32 {
            self.flush_desc_rings(que)?;
        }

        if !softonly {
            self.hw.reset_hw(&self.info)?;
        }

        for que in que.iter() {
            let mut node = MCSNode::new();
            let mut tx = que.tx.lock(&mut node);
            tx.write_buf = None;

            let mut node = MCSNode::new();
            let mut rx = que.rx.lock(&mut node);
            rx.read_buf = None;
        }

        Ok(())
    }

    /// Remove all descriptors from the descriptor rings.
    ///
    /// In i219, the descriptor rings must be emptied before resetting the HW
    /// or before changing the device state to D3 during runtime (runtime PM).
    ///
    /// Failure to do this will cause the HW to enter a unit hang state which can
    /// only be released by PCI reset on the device.
    fn flush_desc_rings(&mut self, que: &[Queue]) -> Result<(), IgbDriverErr> {
        const PCICFG_DESC_RING_STATUS: usize = 0xe4;
        const FLUSH_DESC_REQUIRED: u16 = 0x100;

        // First, disable MULR fix in FEXTNVM11
        let mut fextnvm11 = igb_hw::read_reg(&self.info, FEXTNVM11)?;
        fextnvm11 |= FEXTNVM11_DISABLE_MULR_FIX;
        igb_hw::write_reg(&self.info, FEXTNVM11, fextnvm11)?;

        // do nothing if we're not in faulty state, or if the queue is empty
        let tdlen = igb_hw::read_reg(&self.info, tdlen_offset(que[0].me))?;
        let hang_state = self.info.read_config_space_u16(PCICFG_DESC_RING_STATUS);
        if hang_state & FLUSH_DESC_REQUIRED == 0 || tdlen == 0 {
            return Ok(());
        }

        self.flush_tx_ring(0, que)?;

        // recheck, maybe the fault is caused by the rx ring
        let hang_state = self.info.read_config_space_u16(PCICFG_DESC_RING_STATUS);
        if hang_state & FLUSH_DESC_REQUIRED != 0 {
            self.flush_rx_ring(0, que)?;
        }

        Ok(())
    }

    /// We want to clear all pending descriptors from the TX ring.
    /// zeroing happens when the HW reads the regs. We assign the ring itself as
    /// the data of the next descriptor. We don't care about the data we are about
    /// to reset the HW.
    fn flush_tx_ring(&mut self, que_id: usize, que: &[Queue]) -> Result<(), IgbDriverErr> {
        let tctl = igb_hw::read_reg(&self.info, TCTL)?;
        igb_hw::write_reg(&self.info, TCTL, tctl | TCTL_EN)?;

        let que = &que[que_id];

        let mut node = MCSNode::new();
        let mut tx = que.tx.lock(&mut node);

        let buf = tx.tx_desc_ring.get_phy_addr().as_usize() as u64;

        let len = tx.tx_desc_ring.as_ref().len();
        let tx_desc_head = tx.tx_desc_head;
        let txd = &mut tx.tx_desc_ring.as_mut()[tx_desc_head];

        txd.legacy.buf = buf;
        txd.legacy.length = 512;
        txd.legacy.cso = 0;
        txd.legacy.cmd = TXD_CMD_IFCS;
        txd.legacy.status = 0;
        txd.legacy.css = 0;
        txd.legacy.vtags = 0;

        tx.tx_desc_head += 1;
        if tx.tx_desc_head == len {
            tx.tx_desc_head = 0;
        }

        igb_hw::write_reg(&self.info, tdt_offset(que.me), tx.tx_desc_head as u32)?;
        awkernel_lib::delay::wait_microsec(250);

        Ok(())
    }

    fn flush_rx_ring(&mut self, que_id: usize, que: &[Queue]) -> Result<(), IgbDriverErr> {
        let rctl = igb_hw::read_reg(&self.info, RCTL)?;
        igb_hw::write_reg(&self.info, RCTL, rctl & !RCTL_EN)?;
        igb_hw::write_flush(&self.info)?;
        awkernel_lib::delay::wait_microsec(150);

        let que = &que[que_id];

        let mut rxdctl = igb_hw::read_reg(&self.info, rxdctl_offset(que.me))?;
        // zero the lower 14 bits (prefetch and host thresholds)
        rxdctl &= 0xffffc000;

        // update thresholds: prefetch threshold to 31, host threshold to 1
        // and make sure the granularity is "descriptors" and not "cache lines"
        rxdctl |= 0x1F | (1 << 8) | RXDCTL_THRESH_UNIT_DESC;
        igb_hw::write_reg(&self.info, rxdctl_offset(que.me), rxdctl)?;

        // momentarily enable the RX ring for the changes to take effect
        igb_hw::write_reg(&self.info, RCTL, rctl | RCTL_EN)?;
        igb_hw::write_flush(&self.info)?;
        awkernel_lib::delay::wait_microsec(150);
        igb_hw::write_reg(&self.info, RCTL, rctl & !RCTL_EN)?;

        Ok(())
    }

    fn disable_intr(&self) -> Result<(), IgbDriverErr> {
        match self.pcie_int {
            PCIeInt::Msi(_) => {
                if self.hw.get_mac_type() == MacType::Em82542Rev2_0 {
                    igb_hw::write_reg(&self.info, IMC, !IMS_RXSEQ)
                } else {
                    igb_hw::write_reg(&self.info, IMC, 0xffffffff)
                }
            }
            PCIeInt::MsiX(_) => {
                igb_hw::write_reg(&self.info, EIMC, !0)?;
                igb_hw::write_reg(&self.info, EIAC, 0)
            }
            _ => Ok(()),
        }
    }

    fn enable_intr(&self) -> Result<(), IgbDriverErr> {
        match self.pcie_int {
            PCIeInt::Msi(_) => igb_hw::write_reg(&self.info, IMS, IMS_ENABLE_MASK),
            PCIeInt::MsiX(_) => todo!(), // em_enable_intr()
            _ => Ok(()),
        }
    }

    #[inline]
    fn check_for_link(&mut self) -> Result<(), IgbDriverErr> {
        self.hw.check_for_link(&self.info)?;
        Ok(())
    }
}

impl Igb {
    fn new(info: PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        let que = [allocate_desc_rings(&info)?];

        let inner = IgbInner::new(info, &que)?;

        let igb = Self {
            inner: RwLock::new(inner),
            que,
        };

        Ok(igb)
    }

    fn rx_fill(&self, que_id: usize) -> Result<(), IgbDriverErr> {
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
            desc.desc.status = 0;
            desc.desc.error = 0;
            desc.desc.len = RXBUFFER_2048 as u16;
        }

        rx.rx_desc_head = prev as u32;
        igb_hw::write_reg(&inner.info, rdt_offset(que.me), rx.rx_desc_head)?;

        Ok(())
    }

    fn rx_recv(&self, que_id: usize) -> Result<(), IgbDriverErr> {
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

                let desc = unsafe { &rx_desc_ring[i].desc };
                let status = desc.status;
                let errors = desc.error;

                if status & RXD_STAT_DD == 0 {
                    break;
                }

                if status & RXD_STAT_EOP == 0 {
                    drop(rx);
                    drop(inner);
                    return self.recv_jumbo(que_id);
                }

                let mut len = desc.len as usize;
                let vlan = if status & RXD_STAT_VP != 0 {
                    Some(u16::from_le(desc.special))
                } else {
                    None
                };

                let is_accept = if errors & RXD_ERR_FRAME_ERR_MASK != 0 {
                    if inner.hw.tbi_accept(
                        status,
                        errors,
                        len as u16,
                        VirtAddr::new(desc.buf as usize),
                    ) {
                        len -= 1;
                        true
                    } else {
                        rx.dropped_pkts += 1;
                        false
                    }
                } else {
                    true
                };

                if is_accept {
                    let mut data: Vec<u8> = Vec::with_capacity(len);

                    #[allow(clippy::uninit_vec)]
                    unsafe {
                        data.set_len(len);

                        let read_buf = rx.read_buf.as_mut().unwrap();
                        let src = &mut read_buf.as_mut()[i];
                        core::ptr::copy_nonoverlapping(src.as_ptr(), data.as_mut_ptr(), len);
                    }

                    rx.read_queue.push(EtherFrameBuf { data, vlan }).unwrap();
                };

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

    fn recv_jumbo(&self, que_id: usize) -> Result<(), IgbDriverErr> {
        let que = &self.que[que_id];

        let mut node = MCSNode::new();
        let rx = que.rx.lock(&mut node);

        let rx_desc_ring = rx.rx_desc_ring.as_ref();
        todo!()
    }

    /// Return `(used, lower, upper)`.
    fn transmit_checksum_setup(
        &self,
        tx: &mut Tx,
        ether_frame: EtherFrameRef,
        head: usize,
    ) -> Result<(usize, u32, u32), IgbDriverErr> {
        let txd_upper;
        let txd_lower;

        if ether_frame
            .csum_flags
            .contains(PacketHeaderFlags::TCP_CSUM_OUT)
        {
            txd_upper = TXD32_POPTS_TXSM << 8;
            txd_lower = TXD32_CMD_DEXT | TXD32_DTYP_D;
            if tx.active_checksum_context == ActiveChecksumContext::TcpIP {
                return Ok((0, txd_lower, txd_upper));
            } else {
                tx.active_checksum_context = ActiveChecksumContext::TcpIP;
            }
        } else if ether_frame
            .csum_flags
            .contains(PacketHeaderFlags::UDP_CSUM_OUT)
        {
            txd_upper = TXD32_POPTS_TXSM << 8;
            txd_lower = TXD32_CMD_DEXT | TXD32_DTYP_D;
            if tx.active_checksum_context == ActiveChecksumContext::UdpIP {
                return Ok((0, txd_lower, txd_upper));
            } else {
                tx.active_checksum_context = ActiveChecksumContext::UdpIP;
            }
        } else {
            return Ok((0, 0, 0));
        }

        let txd = &mut tx.tx_desc_ring.as_mut()[head];

        txd.context_desc.ipcss = ETHER_HDR_LEN as u8;
        txd.context_desc.ipcso = ETHER_HDR_LEN as u8 + offset_of!(Ip, ip_sum) as u8;
        txd.context_desc.ipcse =
            u16::to_le(ETHER_HDR_LEN as u16 + core::mem::size_of::<Ip>() as u16 - 1);

        txd.context_desc.tucss = ETHER_HDR_LEN as u8 + core::mem::size_of::<Ip>() as u8;
        txd.context_desc.tucse = 0;

        if tx.active_checksum_context == ActiveChecksumContext::TcpIP {
            txd.context_desc.tucso = ETHER_HDR_LEN as u8
                + core::mem::size_of::<Ip>() as u8
                + offset_of!(TCPHdr, th_sum) as u8;
        } else if tx.active_checksum_context == ActiveChecksumContext::UdpIP {
            txd.context_desc.tucso = ETHER_HDR_LEN as u8
                + core::mem::size_of::<Ip>() as u8
                + offset_of!(UDPHdr, uh_sum) as u8;
        }

        txd.context_desc.status = 0;
        txd.context_desc.hdr_len = 0;
        txd.context_desc.mss = 0;

        txd.context_desc.cmd_and_length = u32::to_le(tx.txd_cmd | TXD32_CMD_DEXT);

        Ok((1, txd_lower, txd_upper))
    }

    /// Return `(used, lower, upper)`.
    fn tx_ctx_setup(
        &self,
        mac_type: MacType,
        me: usize,
        tx: &mut Tx,
        ether_frame: EtherFrameRef,
        head: usize,
    ) -> Result<(usize, u32, u32), IgbDriverErr> {
        let mut olinfo_status = 0;
        let mut cmd_type_len = 0;
        let mut vlan_macip_lens = 0;
        let mut off = false;

        if let Some(vlan) = ether_frame.vlan {
            vlan_macip_lens |= (vlan << ADVTXD_VLAN_SHIFT) as u32;
            cmd_type_len |= ADVTXD_DCMD_VLE;
            off = true;
        }

        let ext = extract_headers(ether_frame.data).or(Err(IgbDriverErr::InvalidPacket))?;

        vlan_macip_lens |= (core::mem::size_of::<EtherHeader>() as u32) << ADVTXD_MACLEN_SHIFT;

        let (iphlen, mut type_tucmd_mlhl) = match ext.network {
            NetworkHdr::Ipv4(ip) => {
                if ether_frame
                    .csum_flags
                    .contains(PacketHeaderFlags::IPV4_CSUM_OUT)
                {
                    olinfo_status |= TXD32_POPTS_IXSM << 8;
                    off = true;
                }

                ((ip.header_len() as u32) << 2, ADVTXD_TUCMD_IPV4)
            }
            NetworkHdr::Ipv6(ip) => (core::mem::size_of::<Ip6Hdr>() as u32, ADVTXD_TUCMD_IPV6),
            _ => (0, 0),
        };

        cmd_type_len |= ADVTXD_DTYP_DATA | ADVTXD_DCMD_IFCS;
        cmd_type_len |= ADVTXD_DCMD_DEXT;
        vlan_macip_lens |= iphlen as u32;
        type_tucmd_mlhl |= ADVTXD_DCMD_DEXT | ADVTXD_DTYP_CTXT;

        match ext.transport {
            TransportHdr::Tcp(_tcp) => {
                type_tucmd_mlhl |= ADVTXD_TUCMD_L4T_TCP;
                if ether_frame
                    .csum_flags
                    .contains(PacketHeaderFlags::TCP_CSUM_OUT)
                {
                    olinfo_status |= TXD32_POPTS_TXSM << 8;
                    off = true;
                }
            }
            TransportHdr::Udp(_udp) => {
                type_tucmd_mlhl |= ADVTXD_TUCMD_L4T_UDP;
                if ether_frame
                    .csum_flags
                    .contains(PacketHeaderFlags::UDP_CSUM_OUT)
                {
                    olinfo_status |= TXD32_POPTS_TXSM << 8;
                    off = true;
                }
            }
            _ => (),
        }

        if !off {
            return Ok((0, cmd_type_len, olinfo_status));
        }

        let mss_l4len_idx = if mac_type == MacType::Em82575 {
            ((me & 0xff) as u32) << 4
        } else {
            0
        };

        let desc = &mut tx.tx_desc_ring.as_mut()[head];

        desc.adv_ctx.vlan_macip_lens = u32::to_le(vlan_macip_lens);
        desc.adv_ctx.type_tucmd_mlhl = u32::to_le(type_tucmd_mlhl);
        desc.adv_ctx.mss_l4len_idx = u32::to_le(mss_l4len_idx);
        desc.adv_ctx.launch_time_or_seqnum_seed = 0;

        Ok((1, cmd_type_len, olinfo_status))
    }

    fn intr(&self) -> Result<(), IgbDriverErr> {
        let reg_icr = {
            let inner = self.inner.read();
            let reg_icr = igb_hw::read_reg(&inner.info, ICR)?;

            if inner.hw.get_mac_type() as u32 >= MacType::Em82571 as u32
                && reg_icr & ICR_INT_ASSERTED == 0
            {
                return Ok(());
            }

            if inner.flags.contains(NetFlags::RUNNING) {
                drop(inner);
                self.rx_recv(0)?;
            }

            reg_icr
        };

        if reg_icr & (ICR_RXSEQ | ICR_LSC) != 0 {
            let mut inner = self.inner.write();
            inner.hw.set_get_link_status(true);
            inner.check_for_link()?;
            inner.update_link_status()?;
        }

        Ok(())
    }
}

fn allocate_msix(
    hw: &igb_hw::IgbHw,
    info: &mut PCIeInfo,
    que: &mut Queue,
) -> Result<PCIeInt, IgbDriverErr> {
    if info.get_msix_mut().is_none() {
        return Err(IgbDriverErr::InitializeInterrupt);
    }

    if !matches!(
        hw.get_mac_type(),
        MacType::Em82576 | MacType::Em82580 | MacType::EmI350 | MacType::EmI210
    ) {
        return Err(IgbDriverErr::InitializeInterrupt);
    }

    let vec = 0;
    que.me = vec;
    que.eims = 1 << vec;

    // Setup linkvector, use last queue vector + 1
    let vec = vec + 1;
    let link_vec = vec as u32;

    // TODO: register interrupt handler

    if let Some(msi) = info.get_msi_mut() {
        msi.disable();
    }
    info.disable_legacy_interrupt();

    let msix = info.get_msix_mut().unwrap();
    msix.enable();

    Ok(PCIeInt::MsiX(MsiX {
        link_vec,
        link_mask: 1 << link_vec,
        queues_mask: 0,
    }))
}

fn allocate_msi(info: &mut PCIeInfo) -> Result<PCIeInt, IgbDriverErr> {
    info.disable_legacy_interrupt();
    if let Some(msix) = info.get_msix_mut() {
        msix.disable();
    }

    if let Some(msi) = info.get_msi_mut() {
        msi.disable();

        if let Ok(mut irq) = awkernel_lib::interrupt::register_handler_for_pnp(
            DEVICE_SHORT_NAME,
            Box::new(|irq| {
                awkernel_lib::net::netif_interrupt(irq);
            }),
        ) {
            msi.set_multiple_message_enable(MultipleMessage::One)
                .or(Err(IgbDriverErr::InitializeInterrupt))?;
            msi.set_message_address(awkernel_lib::cpu::raw_cpu_id() as u32, irq.get_irq())
                .or(Err(IgbDriverErr::InitializeInterrupt))?;

            irq.enable();
            msi.enable();

            Ok(PCIeInt::Msi(irq))
        } else {
            Err(IgbDriverErr::InitializeInterrupt)
        }
    } else {
        Err(IgbDriverErr::InitializeInterrupt)
    }
}

fn allocate_desc_rings(info: &PCIeInfo) -> Result<Queue, IgbDriverErr> {
    let tx_size = core::mem::size_of::<TxDescriptor>() * MAX_TXD;
    assert_eq!(tx_size & (PAGESIZE - 1), 0);

    let rx_size = core::mem::size_of::<RxDescriptor>() * MAX_RXD;
    assert_eq!(rx_size & (PAGESIZE - 1), 0);

    let tx_desc_ring = DMAPool::new(info.segment_group as usize, tx_size / PAGESIZE)
        .ok_or(IgbDriverErr::DMAPool)?;
    let rx_desc_ring = DMAPool::new(info.segment_group as usize, rx_size / PAGESIZE)
        .ok_or(IgbDriverErr::DMAPool)?;

    let tx = Tx {
        tx_desc_head: 0,
        tx_desc_tail: 0,
        tx_desc_ring,
        txd_cmd: TXD32_CMD_IFCS,
        active_checksum_context: ActiveChecksumContext::None,
        write_buf: None,
    };

    let rx = Rx {
        rx_desc_head: 0,
        rx_desc_tail: 0,
        rx_desc_ring,
        read_buf: None,
        read_queue: RingQ::new(RECV_QUEUE_SIZE),
        dropped_pkts: 0,
    };

    let que = Queue {
        tx: Mutex::new(tx),
        rx: Mutex::new(rx),
        me: 0,
        eims: 1,
    };

    Ok(que)
}

/// Initialize the hardware to a configuration as specified by the
/// em_softc structure. The controller is reset, the EEPROM is
/// verified, the MAC address is set, then the shared initialization
/// routines are called.
///
/// https://github.com/openbsd/src/blob/18bc31b7ebc17ab66d1354464ff2ee3ba31f7750/sys/dev/pci/if_em.c#L1845
fn hardware_init(hw: &mut igb_hw::IgbHw, info: &mut PCIeInfo) -> Result<(), IgbDriverErr> {
    use igb_hw::MacType::*;

    if matches!(hw.get_mac_type(), igb_hw::MacType::EmPchSpt) {
        check_desc_ring(info)?;
    }

    // Issue a global reset
    hw.reset_hw(info)?;

    // Make sure we have a good EEPROM before we read from it
    if igb_hw::get_flash_presence_i210(&hw.get_mac_type(), info)?
        && hw.validate_eeprom_checksum(info).is_err()
    {
        // Some PCIe parts fail the first check due to
        // the link being in sleep state, call it again,
        // if it fails a second time its a real issue.
        hw.validate_eeprom_checksum(info)?
    }

    if self::igb_hw::get_flash_presence_i210(&hw.get_mac_type(), info)? {
        hw.read_part_num(info)?;
    }

    // Set up smart power down as default off on newer adapters
    if matches!(
        hw.get_mac_type(),
        Em82571 | Em82572 | Em82575 | Em82576 | Em82580 | EmI210 | EmI350
    ) {
        // Speed up time to link by disabling smart power down
        let phy_tmp = hw.read_phy_reg(info, IGP02E1000_PHY_POWER_MGMT)?;
        let phy_tmp = phy_tmp & !IGP02E1000_PM_SPD;
        hw.write_phy_reg(info, IGP02E1000_PHY_POWER_MGMT, phy_tmp)?;
    }

    hw.legacy_irq_quirk_spt(info)?;

    // Disable PCIe Active State Power Management (ASPM)
    disable_aspm(hw, info);

    hw.init_hw(info)?;
    hw.check_for_link(info)?;

    Ok(())
}

/// Disable the L0S and L1 LINK states.
fn disable_aspm(hw: &mut igb_hw::IgbHw, info: &mut PCIeInfo) {
    use crate::pcie::capability::pcie_cap::registers::LinkStatusControl;
    use igb_hw::MacType::*;

    if !matches!(hw.get_mac_type(), Em82571 | Em82572 | Em82573 | Em82574) {
        return;
    }

    let Some(cap) = info.get_pcie_cap_mut() else {
        return;
    };

    // Disable PCIe Active State Power Management (ASPM).
    let mut val = cap.get_link_status_control();

    match hw.get_mac_type() {
        Em82571 | Em82572 => {
            val.remove(LinkStatusControl::ASPM_L1);
        }
        Em82573 | Em82574 => {
            val.remove(LinkStatusControl::ASPM_L1 | LinkStatusControl::ASPM_L0S);
        }
        _ => (),
    }

    cap.set_link_status_control(val);
}

//===========================================================================
impl PCIeDevice for Igb {
    fn device_name(&self) -> &'static str {
        DEVICE_NAME
    }
}

impl NetDevice for Igb {
    fn flags(&self) -> NetFlags {
        let inner = self.inner.read();
        inner.flags
    }

    fn device_short_name(&self) -> &'static str {
        DEVICE_SHORT_NAME
    }

    fn capabilities(&self) -> NetCapabilities {
        let inner = self.inner.read();
        inner.capabilities
    }

    fn link_up(&self) -> bool {
        let inner = self.inner.read();
        inner.link_active
    }

    fn link_speed(&self) -> u64 {
        let inner = self.inner.read();

        match inner.link_speed {
            igb_hw::Speed::S10Mbps => 10,
            igb_hw::Speed::S100Mbps => 100,
            igb_hw::Speed::S1000Mbps => 1000,
            igb_hw::Speed::None => 0,
        }
    }

    fn full_duplex(&self) -> bool {
        let inner = self.inner.read();

        inner.link_duplex == igb_hw::Duplex::Full
    }

    fn mac_address(&self) -> [u8; 6] {
        let inner = self.inner.read();

        inner.hw.get_mac_addr()
    }

    fn can_send(&self) -> bool {
        let inner = self.inner.read();
        if inner.flags.contains(NetFlags::RUNNING) {
            // TODO
            false
        } else {
            false
        }
    }

    fn recv(&self) -> Option<EtherFrameBuf> {
        {
            let mut node = MCSNode::new();
            let mut rx = self.que[0].rx.lock(&mut node);

            let data = rx.read_queue.pop();
            if data.is_some() {
                return data;
            }
        }

        self.rx_recv(0).ok()?;

        let mut node = MCSNode::new();
        let mut rx = self.que[0].rx.lock(&mut node);
        rx.read_queue.pop()
    }

    fn send(&self, data: EtherFrameRef) -> Option<()> {
        // em_start()
        todo!()
    }

    fn up(&self) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();

        if !inner.flags.contains(NetFlags::UP) {
            if let Err(err_init) = inner.init(&self.que) {
                if let Err(err_stop) = inner.stop(true, &self.que) {
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
        let mut inner = self.inner.write();

        if inner.flags.contains(NetFlags::UP) {
            if let Err(e) = inner.stop(true, &self.que) {
                log::error!("igb: stop failed: {:?}", e);
                Err(NetDevError::DeviceError)
            } else {
                inner.flags.remove(NetFlags::UP);
                Ok(())
            }
        } else {
            Err(NetDevError::AlreadyDown)
        }
    }

    fn interrupt(&self, _irq: u16) -> Result<(), NetDevError> {
        self.intr().or(Err(NetDevError::DeviceError))?;
        Ok(())
    }

    fn irqs(&self) -> Vec<u16> {
        let inner = self.inner.read();

        match &inner.pcie_int {
            PCIeInt::MsiX(msix) => todo!(),
            PCIeInt::Msi(msi) => vec![msi.get_irq()],
            _ => vec![],
        }
    }

    fn add_multicast_addr_ipv4(&self, addr: Ipv4Addr) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();

        if inner.multicast_ipv4.add_addr(addr) {
            inner.iff().or(Err(NetDevError::DeviceError))?;
            Ok(())
        } else {
            Err(NetDevError::MulticastAddrError)
        }
    }

    fn add_multicast_range_ipv4(&self, start: Ipv4Addr, end: Ipv4Addr) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();

        if inner.multicast_ipv4.add_range(start, end) {
            inner.iff().or(Err(NetDevError::DeviceError))?;
            Ok(())
        } else {
            Err(NetDevError::MulticastAddrError)
        }
    }

    fn remove_multicast_addr_ipv4(&self, addr: Ipv4Addr) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();

        if inner.multicast_ipv4.remove_addr(addr) {
            inner.iff().or(Err(NetDevError::DeviceError))?;
            Ok(())
        } else {
            Err(NetDevError::MulticastAddrError)
        }
    }

    fn remove_multicast_range_ipv4(
        &self,
        start: Ipv4Addr,
        end: Ipv4Addr,
    ) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();

        if inner.multicast_ipv4.remove_range(start, end) {
            inner.iff().or(Err(NetDevError::DeviceError))?;
            Ok(())
        } else {
            Err(NetDevError::MulticastAddrError)
        }
    }
}

pub fn match_device(vendor: u16, id: u16) -> bool {
    igb_hw::E1000_DEVICES.contains(&(vendor, id))
}

fn check_desc_ring(info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IgbDriverErr::NoBar0)?;

    // First, disable MULR fix in FEXTNVM11
    let fextnvm11 =
        bar0.read32(FEXTNVM11).ok_or(IgbDriverErr::ReadFailure)? | FEXTNVM11_DISABLE_MULR_FIX;
    bar0.write32(FEXTNVM11, fextnvm11);

    let tdlen = bar0
        .read32(tdlen_offset(0))
        .ok_or(IgbDriverErr::ReadFailure)?;
    let hang_state = info.read_config_space_u32(PCICFG_DESC_RING_STATUS);
    if hang_state & FLUSH_DESC_REQUIRED == 0 || tdlen == 0 {
        return Ok(());
    }

    Err(IgbDriverErr::FailedFlashDescriptor)
}

#[inline(always)]
fn tdbal_offset(n: usize) -> usize {
    if n < 4 {
        0x03800 + (n * 0x100)
    } else {
        0x0E000 + (n * 0x40)
    }
}

#[inline(always)]
fn tdbah_offset(n: usize) -> usize {
    if n < 4 {
        0x03804 + (n * 0x100)
    } else {
        0x0E004 + (n * 0x40)
    }
}

#[inline(always)]
fn tdlen_offset(n: usize) -> usize {
    if n < 4 {
        0x03808 + (n * 0x100)
    } else {
        0x0E008 + (n * 0x40)
    }
}

#[inline(always)]
fn tdh_offset(n: usize) -> usize {
    if n < 4 {
        0x03810 + (n * 0x100)
    } else {
        0x0E010 + (n * 0x40)
    }
}

#[inline(always)]
fn tdt_offset(n: usize) -> usize {
    if n < 4 {
        0x03818 + (n * 0x100)
    } else {
        0x0E018 + (n * 0x40)
    }
}

#[inline(always)]
fn rxdctl_offset(n: usize) -> usize {
    if n < 4 {
        0x02828 + (n * 0x100)
    } else {
        0x0C028 + (n * 0x40)
    }
}

#[inline(always)]
fn txdctl_offset(n: usize) -> usize {
    if n < 4 {
        0x03828 + (n * 0x100)
    } else {
        0x0E028 + (n * 0x40)
    }
}

#[inline(always)]
fn srrctl_offset(n: usize) -> usize {
    if n < 4 {
        0x0280C + (n * 0x100)
    } else {
        0x0C00C + (n * 0x40)
    }
}

#[inline(always)]
fn rdbal_offset(n: usize) -> usize {
    if n < 4 {
        0x02800 + (n * 0x100)
    } else {
        0x0C000 + (n * 0x40)
    }
}

#[inline(always)]
fn rdbah_offset(n: usize) -> usize {
    if n < 4 {
        0x02804 + (n * 0x100)
    } else {
        0x0C004 + (n * 0x40)
    }
}

#[inline(always)]
fn rdlen_offset(n: usize) -> usize {
    if n < 4 {
        0x02808 + (n * 0x100)
    } else {
        0x0C008 + (n * 0x40)
    }
}

#[inline(always)]
fn rdh_offset(n: usize) -> usize {
    if n < 4 {
        0x02810 + (n * 0x100)
    } else {
        0x0C010 + (n * 0x40)
    }
}

#[inline(always)]
fn rdt_offset(n: usize) -> usize {
    if n < 4 {
        0x02818 + (n * 0x100)
    } else {
        0x0C018 + (n * 0x40)
    }
}
