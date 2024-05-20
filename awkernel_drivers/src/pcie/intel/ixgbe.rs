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
    fmt::{self, Debug},
    mem,
};
use memoffset::offset_of;

mod ixgbe_hw;
mod ixgbe_operations;
mod ixgbe_x540;

#[allow(dead_code)]
mod ixgbe_regs;

use ixgbe_hw::{get_num_queues, IxgbeHw};
use ixgbe_regs::*;

const DEVICE_NAME: &str = "Intel 10 Gigabit Ethernet Controller";
const DEVICE_SHORT_NAME: &str = "ixgbe";

enum QueueStatus {
    IxgbeQueueIdle,
    IxgbeQueueWorking,
    IxgbeQueueHung,
}

type TxRing = [AdvTxDesc; DEFAULT_TXD];

type RxRing = [AdvRxDesc; DEFAULT_RXD];

pub struct Tx {
    tx_desc_ring: DMAPool<TxRing>,
    //queue_status: QueueStatus,
}
pub struct Rx {
    rx_desc_ring: DMAPool<TxRing>,
}

pub struct Queue {
    txr: Mutex<Tx>,
    rxr: Mutex<Rx>,
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
    flags: NetFlags,
    capabilities: NetCapabilities,
    link_active: bool,
    //link_speed: igb_hw::Speed,
    //link_duplex: igb_hw::Duplex,
    //smart_speed: u32,
    pcie_int: PCIeInt,
    multicast_addr: BTreeSet<[u8; 6]>,

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
            que.push(allocate_queues(&info, i)?);
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
        ops.mac_reset_hw(&mut info, &mut hw)?;

        // setup interface
        // TODO: Check if these are correct
        let flags = NetFlags::BROADCAST | NetFlags::SIMPLEX | NetFlags::MULTICAST;
        let mut capabilities = NetCapabilities::VLAN_MTU | NetCapabilities::VLAN_HWTAGGING;

        let ixgbe = Self {
            info,
            hw,
            flags,
            capabilities,
            link_active: false,
            pcie_int,
            multicast_addr: BTreeSet::new(),
            irq_to_rx_tx_link,
            is_poll_mode,
        };

        Ok((ixgbe, que))
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
fn allocate_queues(info: &PCIeInfo, que_id: usize) -> Result<Queue, IxgbeDriverErr> {
    let tx_size = core::mem::size_of::<AdvTxDesc>() * DEFAULT_TXD;
    assert_eq!(tx_size & (PAGESIZE - 1), 0);

    let rx_size = core::mem::size_of::<AdvRxDesc>() * DEFAULT_RXD;
    assert_eq!(rx_size & (PAGESIZE - 1), 0);

    let tx_desc_ring = DMAPool::new(info.segment_group as usize, tx_size / PAGESIZE)
        .ok_or(IxgbeDriverErr::DMAPool)?;
    let rx_desc_ring = DMAPool::new(info.segment_group as usize, rx_size / PAGESIZE)
        .ok_or(IxgbeDriverErr::DMAPool)?;

    let tx = Tx { tx_desc_ring };

    let rx = Rx { rx_desc_ring };

    let que = Queue {
        txr: Mutex::new(tx),
        rxr: Mutex::new(rx),
        me: que_id,
    };

    Ok(que)
}
