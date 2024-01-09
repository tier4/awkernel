//! # Intel Gigabit Ethernet Controller

use crate::pcie::{
    capability::msi::MultipleMessage, net::igb::igb_hw::MacType, PCIeDevice, PCIeDeviceErr,
    PCIeInfo,
};
use alloc::{boxed::Box, sync::Arc, vec::Vec};
use awkernel_lib::{
    dma_pool::DMAPool,
    interrupt::IRQ,
    net::{NetCapabilities, NetDevice, NetFlags, NET_MANAGER},
    paging::{Frame, FrameAllocator, PageTable, PAGESIZE},
    sync::mutex::{MCSNode, Mutex},
};
use core::fmt::{self, Debug};

mod igb_hw;

#[allow(dead_code)]
mod igb_regs;

use igb_regs::*;

const DEVICE_NAME: &str = "igb: Intel Gigabit Ethernet Controller";
const DEVICE_SHORT_NAME: &str = "igb";

struct Rx {
    dma_alloc: DMAPool,
    rx_desc_head: usize,
    rx_desc_tail: usize,

    // Statistics
    dropped_pkts: u64,
}

struct Tx {
    dma_alloc: DMAPool,
    tx_desc_head: usize,
    tx_desc_tail: usize,
}

struct Queue {
    tx: Tx,
    rx: Rx,
    me: usize,
}

#[repr(C)]
/// Legacy Transmit Descriptor Format (16B)
struct TxDescriptor {
    buf: u64,
    length: u16,
    cso: u8,
    cmd: u8,
    status: u8,
    css: u8,
    vtags: u16,
}

#[repr(C)]
/// Legacy Receive Descriptor Format (16B)
struct RxDescriptor {
    buf: u64,
    len: u16,
    checksum: u16,
    status: u8,
    error: u8,
    vtags: u16,
}

/// Intel Gigabit Ethernet Controller driver
pub struct Igb {
    info: PCIeInfo,
    hw: igb_hw::IgbHw,
    que: [Queue; 1],

    irq: Option<u16>,

    flags: NetFlags,
    capabilities: NetCapabilities,
    icp_xxxx_is_link_up: bool,
    link_active: bool,
    link_speed: igb_hw::Speed,
    link_duplex: igb_hw::Duplex,
    smart_speed: u32,
    pcie_int: PCIeInt,
}

pub fn attach<F, FA, E>(
    mut info: PCIeInfo,
    dma_offset: usize,
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

    let igb = Igb::new(info, dma_offset, page_table, page_allocator)?;

    let node = &mut MCSNode::new();
    let mut net_master = NET_MANAGER.lock(node);
    net_master.add_interface(Arc::new(Mutex::new(Box::new(igb))));

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
}

#[derive(Debug)]
pub enum PCIeInt {
    MSI(IRQ),
    MSIX,
}

impl From<IgbDriverErr> for PCIeDeviceErr {
    fn from(value: IgbDriverErr) -> Self {
        log::error!("igb: {:?}", value);

        match value {
            IgbDriverErr::NotImplemented => PCIeDeviceErr::NotImplemented,
            IgbDriverErr::ReadFailure => PCIeDeviceErr::ReadFailure,
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
        }
    }
}

impl Igb {
    fn new<F, FA, E>(
        mut info: PCIeInfo,
        dma_offset: usize,
        page_table: &mut impl PageTable<F, FA, E>,
        page_allocator: &mut FA,
    ) -> Result<Self, PCIeDeviceErr>
    where
        F: Frame,
        FA: FrameAllocator<F, E>,
    {
        let mut hw = igb_hw::IgbHw::new(&mut info)?;

        let pcie_int = if let Ok(pcie_int) = allocate_msix(&mut info) {
            pcie_int
        } else {
            if let Ok(pcie_int) = allocate_msi(&mut info) {
                pcie_int
            } else {
                return Err(IgbDriverErr::InitializeInterrupt.into());
            }
        };

        if matches!(
            hw.get_mac_type(),
            MacType::Em82576 | MacType::Em82580 | MacType::EmI210 | MacType::EmI350
        ) {}

        let que = [allocate_desc_rings(&info)?];

        // https://github.com/openbsd/src/blob/4d2f7ea336a48b11a249752eb2582887d8d4828b/sys/dev/pci/if_em_hw.c#L1260-L1263
        if (hw.get_mac_type() as u32) >= MacType::Em82571 as u32
            && !hw.get_initialize_hw_bits_disable()
        {
            for q in que.iter() {
                let offset = txdctl(q.me);
                let mut reg_txdctl = igb_hw::read_reg(&info, offset)?;
                reg_txdctl |= TXDCTL_COUNT_DESC;
                igb_hw::write_reg(&mut info, offset, reg_txdctl)?;
            }
        }

        hardware_init(&mut hw, &mut info)?;

        // Set the transmit descriptor write-back policy
        if (hw.get_mac_type() as u32) > MacType::Em82544 as u32 {
            for q in que.iter() {
                let ctrl = igb_hw::read_reg(&info, txdctl(q.me))?;
                let ctrl = (ctrl & !TXDCTL_WTHRESH) | TXDCTL_FULL_TX_DESC_WB;
                igb_hw::write_reg(&mut info, txdctl(q.me), ctrl)?;
            }
        }

        hw.read_mac_addr(&info)?;

        // setup interface
        let flags = NetFlags::BROADCAST | NetFlags::SIMPLEX | NetFlags::MULTICAST;
        let mut capabilities = NetCapabilities::VLAN_MTU;

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
            "{:02x}:{:02x}:{:04x}:{:04x}: {}, MAC = {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
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
            que,
            irq: None,
            flags,
            capabilities,
            icp_xxxx_is_link_up: false,
            link_active: false,
            link_speed: igb_hw::Speed::None,
            link_duplex: igb_hw::Duplex::None,
            smart_speed: 0,
            pcie_int,
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
                    igb_hw::write_reg(&mut self.info, TARC0, tarc0 | SPEED_MODE_BIT)?;
                }

                self.link_speed = link_speed;
                self.link_duplex = link_duplex;
                self.link_active = true;
                self.smart_speed = 0;
            }
        } else {
            if self.link_active {
                self.link_speed = igb_hw::Speed::None;
                self.link_duplex = igb_hw::Duplex::None;
                self.link_active = false;
            }
        }

        Ok(())
    }

    fn init(&mut self) -> Result<(), IgbDriverErr> {
        // em_init()
        todo!()
    }

    fn stop(&mut self, softonly: bool) -> Result<(), IgbDriverErr> {
        // em_stop()

        self.flags.remove(NetFlags::RUNNING);

        if !softonly {
            // TODO: em_disable_intr()
        }

        if self.hw.get_mac_type() as u32 >= MacType::EmPchSpt as u32 {
            // TODO: em_flush_desc_rings()
        }

        if !softonly {
            self.hw.reset_hw(&self.info)?;
        }

        // TODO: em_free_transmit_structures()
        // TODO: em_free_receive_structures()

        todo!()
    }

    fn disalbe_intr(&self) -> Result<(), IgbDriverErr> {
        // em_disable_intr()
        todo!()
    }

    fn enalbe_intr(&self) -> Result<(), IgbDriverErr> {
        // em_enable_intr()
        todo!()
    }
}

fn allocate_msix(info: &PCIeInfo) -> Result<PCIeInt, IgbDriverErr> {
    // TODO
    Err(IgbDriverErr::InitializeInterrupt)
}

fn allocate_msi(info: &mut PCIeInfo) -> Result<PCIeInt, IgbDriverErr> {
    info.disable_legacy_interrupt();

    if let Some(msix) = info.get_msix_mut() {
        msix.disalbe();
    }

    let segment_group = info.get_segment_group();

    if let Some(msi) = info.get_msi_mut() {
        msi.disable();

        if let Ok(mut irq) = awkernel_lib::interrupt::register_handler_for_pnp(
            DEVICE_SHORT_NAME,
            Box::new(|_irq| {
                log::debug!("igb interrupt.");
            }),
        ) {
            msi.set_multiple_message_enable(MultipleMessage::One)
                .unwrap();

            #[cfg(feature = "x86")]
            msi.set_x86_interrupt(0, irq.get_irq(), false, false);

            irq.enable();

            msi.enable();

            Ok(PCIeInt::MSI(irq))
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

    let tx_dma_pool = DMAPool::new(info.segment_group as usize, tx_size / PAGESIZE)
        .ok_or(IgbDriverErr::DMAPool)?;
    let rx_dma_pool = DMAPool::new(info.segment_group as usize, rx_size / PAGESIZE)
        .ok_or(IgbDriverErr::DMAPool)?;

    let tx = Tx {
        tx_desc_head: 0,
        tx_desc_tail: 0,
        dma_alloc: tx_dma_pool,
    };

    let rx = Rx {
        rx_desc_head: 0,
        rx_desc_tail: 0,
        dma_alloc: rx_dma_pool,
        dropped_pkts: 0,
    };

    let que = Queue { tx, rx, me: 0 };

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
        self.flags
    }

    fn device_short_name(&self) -> &'static str {
        DEVICE_SHORT_NAME
    }

    fn capabilities(&self) -> NetCapabilities {
        self.capabilities
    }

    fn link_up(&self) -> bool {
        self.link_active
    }

    fn link_speed(&self) -> u64 {
        match self.link_speed {
            igb_hw::Speed::S10Mbps => 10,
            igb_hw::Speed::S100Mbps => 100,
            igb_hw::Speed::S1000Mbps => 1000,
            igb_hw::Speed::None => 0,
        }
    }

    fn full_duplex(&self) -> bool {
        self.link_duplex == igb_hw::Duplex::Full
    }

    fn mac_address(&self) -> [u8; 6] {
        self.hw.get_mac_addr()
    }

    fn can_send(&self) -> bool {
        todo!()
    }

    fn recv(&mut self) -> Option<Vec<u8>> {
        todo!()
    }

    fn send(&mut self, data: &[u8]) -> Option<()> {
        // em_start()
        todo!()
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
    let hang_state = info.read_config_space(PCICFG_DESC_RING_STATUS);
    if hang_state & FLUSH_DESC_REQUIRED == 0 || tdlen == 0 {
        return Ok(());
    }

    Err(IgbDriverErr::FailedFlashDescriptor)
}

fn tdlen_offset(n: usize) -> usize {
    if n < 4 {
        0x03808 + (n * 0x100)
    } else {
        0x0E008 + (n * 0x40)
    }
}
