//! # Intel Gigabit Ethernet Controller

use crate::pcie::{
    self,
    capability::{msi::MultipleMessage, pcie_cap},
    net::igb::igb_hw::MacType,
    BaseAddress, PCIeDevice, PCIeDeviceErr, PCIeInfo,
};
use alloc::{boxed::Box, sync::Arc, vec::Vec};
use awkernel_lib::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    dma_pool::DMAPool,
    net::{NetDevice, NET_MANAGER},
    paging::{Flags, Frame, FrameAllocator, PageTable, PAGESIZE},
    sync::mutex::{MCSNode, Mutex},
};
use core::{
    fmt::{self, Debug},
    hint::spin_loop,
    mem::size_of,
    ptr::write_bytes,
    slice,
    sync::atomic::{fence, Ordering::SeqCst},
};

mod igb_hw;
mod igb_regs;

use igb_regs::*;

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
    bar0: BaseAddress,

    // Receive Descriptor Ring
    rx_ring: &'static mut [RxDescriptor],
    rx_ring_pa: u64,
    rx_bufs: Vec<VirtAddr>,

    // Transmission Descriptor Ring
    tx_ring: &'static mut [TxDescriptor],
    tx_ring_pa: u64,
    tx_bufs: Vec<VirtAddr>,
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

    let mut igb = Igb::new(info, dma_offset, page_table, page_allocator)?;

    igb.init()?; // should be removed

    log::info!(
        "Intel GbE driver has been initialized. IRQ = {:?}, Info = {:?}",
        igb.irq,
        igb.info
    );

    let node = &mut MCSNode::new();
    let mut net_master = NET_MANAGER.lock(node);
    net_master.add_interface(Arc::new(Mutex::new(Box::new(igb))));

    Ok(())
}

pub fn activate() {
    todo!()
}

#[derive(Debug)]
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
}

impl From<IgbDriverErr> for PCIeDeviceErr {
    fn from(value: IgbDriverErr) -> Self {
        log::error!("igb: {:?}", value);
        PCIeDeviceErr::InitFailure
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

        log::debug!("igb: {:?}\r\n{:?}", hw, info);

        let perm_mac_addr = hw.get_perm_mac_addr();
        log::debug!(
            "igb: MAC = {:x}:{:x}:{:x}:{:x}:{:x}:{:x}",
            perm_mac_addr[0],
            perm_mac_addr[1],
            perm_mac_addr[2],
            perm_mac_addr[3],
            perm_mac_addr[4],
            perm_mac_addr[5]
        );

        return Err(PCIeDeviceErr::NotYetImplemented);

        loop {}

        let mut bar0 = info.get_bar(0).ok_or(PCIeDeviceErr::InitFailure)?;

        // allocate send and recv descriptor ring
        let tx_ring_len = PAGESIZE / size_of::<TxDescriptor>();
        let rx_ring_len = PAGESIZE / size_of::<RxDescriptor>();
        let (tx_ring_va, tx_ring_pa) = Self::create_ring(dma_offset, page_table, page_allocator)?;
        let (rx_ring_va, rx_ring_pa) = Self::create_ring(dma_offset, page_table, page_allocator)?;
        let tx_ring = unsafe {
            slice::from_raw_parts_mut(tx_ring_va.as_usize() as *mut TxDescriptor, tx_ring_len)
        };
        let rx_ring = unsafe {
            slice::from_raw_parts_mut(rx_ring_va.as_usize() as *mut RxDescriptor, rx_ring_len)
        };

        let mut rx_bufs = Vec::new();
        let mut tx_bufs = Vec::new();

        // allocate buffer for descriptors
        for tx_desc in tx_ring.iter_mut() {
            let (buf_va, buf_pa) = Self::allocate_buffer(dma_offset, page_table, page_allocator)?;
            tx_desc.buf = buf_pa.as_usize() as u64;
            tx_desc.status |= 1;
            tx_desc.length = 512;
            tx_desc.cmd = TX_CMD_IFCS;
            tx_bufs.push(buf_va);
        }

        for rx_desc in rx_ring.iter_mut() {
            let (buf_va, buf_pa) = Self::allocate_buffer(dma_offset, page_table, page_allocator)?;
            rx_desc.buf = buf_pa.as_usize() as u64;
            rx_bufs.push(buf_va);
        }

        Ok(Self {
            info,
            hw,
            que,
            bar0,
            rx_ring,
            rx_ring_pa: rx_ring_pa.as_usize() as u64,
            rx_bufs,
            tx_ring,
            tx_ring_pa: tx_ring_pa.as_usize() as u64,
            tx_bufs,
            irq: None,
        })
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
    const REG_SPACE_SIZE: u64 = 128 * 1024; // 128KiB

    fn init(&mut self) -> Result<(), PCIeDeviceErr> {
        use pcie::registers::StatusCommand;

        let csr = self.info.read_status_command();
        self.info.write_status_command(
            csr | StatusCommand::BUS_MASTER | StatusCommand::MEMORY_SPACE | StatusCommand::IO_SPACE,
        );

        if let Err(e) = unsafe { self.init_hw() } {
            log::error!("{}", e);
            return Err(PCIeDeviceErr::InitFailure);
        }

        Ok(())
    }
}

impl NetDevice for Igb {
    fn device_name(&self) -> &'static str {
        "igb"
    }

    fn link_up(&mut self) -> bool {
        unsafe { self.read_reg(STATUS) & STATUS_LU > 0 }
    }

    fn link_speed(&mut self) -> u64 {
        let status = unsafe { self.read_reg(STATUS) };
        let speed = (status >> 6) & 0b11;

        match speed {
            0b00 => 10,
            0b01 => 100,
            0b10 | 0b11 => 1000,
            _ => unreachable!(),
        }
    }

    fn full_duplex(&mut self) -> bool {
        unsafe { self.read_reg(STATUS) & STATUS_FD > 0 }
    }

    fn mac_address(&mut self) -> [u8; 6] {
        unsafe { self.get_mac() }
    }

    fn can_send(&self) -> bool {
        let tdt = unsafe { self.read_reg(TDT) };
        let tx_status = self.tx_ring[tdt as usize].status;

        tx_status & 1 != 0 && !unsafe { self.tx_ring_empty() }
    }

    fn recv(&mut self) -> Option<Vec<u8>> {
        let head = unsafe { self.read_reg(RDH) };
        let tail = unsafe { self.read_reg(RDT) };

        // receive ring is empty
        if head == tail {
            return None;
        }

        let curr_rdt = (tail + 1) % self.rx_ring.len() as u32;

        let rx_status = self.rx_ring[curr_rdt as usize].status;

        if rx_status & 1 == 0 {
            return None;
        }

        // Copy the data in buffer
        let buf_len = self.rx_ring[curr_rdt as usize].len as usize;
        let buf_addr = self.rx_bufs[curr_rdt as usize].as_mut_ptr();
        let data = unsafe { slice::from_raw_parts_mut(buf_addr, buf_len) }.to_vec();

        //===========================================
        fence(SeqCst);
        // Reset the descriptor.
        self.rx_ring[curr_rdt as usize].status = 0;
        fence(SeqCst);
        //===========================================
        // Increment tail pointer
        unsafe { self.write_reg(RDT, curr_rdt) };

        Some(data)
    }

    fn send(&mut self, data: &mut [u8]) -> Option<()> {
        if !self.can_send() {
            return None;
        }

        let head = unsafe { self.read_reg(TDH) };
        let tail = unsafe { self.read_reg(TDT) };

        let next_tail = (tail + 1) % self.tx_ring.len() as u32;

        let data_len = data.len();
        // data should not be longer than buffer
        if data_len >= PAGESIZE {
            return None;
        }

        if next_tail == head {
            return None;
        }

        //  By Datasheet 7.2.10.1.2
        if data_len >= 16288 {
            return None;
        }

        // Copy the data into the buffer
        let buf_ptr: *mut u8 = self.tx_bufs[tail as usize].as_mut_ptr();
        let buf = unsafe { slice::from_raw_parts_mut(buf_ptr, data_len) };
        buf.copy_from_slice(data);

        fence(SeqCst); // barrier

        // Mark this descriptor ready.
        self.tx_ring[tail as usize].status = 0;
        self.tx_ring[tail as usize].length = data_len as u16;
        self.tx_ring[tail as usize].cmd = (1 << 3) | (1 << 1) | (1 << 0);

        fence(SeqCst); // barrier

        // Increment tail pointer
        unsafe { self.write_reg(TDT, next_tail) };

        Some(())
    }
}

//===========================================================================
impl Igb {
    /// Initialize e1000's register
    ///
    /// https://github.com/openbsd/src/blob/f058c8dbc8e3b2524b639ac291b898c7cc708996/sys/dev/pci/if_em_hw.c#L1559
    unsafe fn init_hw(&mut self) -> Result<(), IgbDriverErr> {
        self.init_pcie_msi()?;

        // ============================================
        // 4.6.2: Global Reset and General Configuration

        self.disable_intr();
        self.reset();
        self.disable_intr();
        fence(SeqCst);

        // ============================================
        //  4.6.6 Transmit Initialization
        //  Install the transmit ring
        self.write_reg(TDBAL, self.tx_ring_pa as u32);
        self.write_reg(TDBAH, (self.tx_ring_pa >> 32) as u32);
        self.write_reg(TDLEN, core::mem::size_of_val(self.tx_ring) as u32);
        self.write_reg(TDH, 0);
        self.write_reg(TDT, 0);

        // Transmit Registers Initialization
        self.write_reg(TXDCTL, TXDCTL_GRAN | TXDCTL_WTHRESH);
        self.write_reg(TCTL, TCTL_COLD | TCTL_CT | TCTL_PSP | TCTL_EN);
        self.write_reg(TIPG, TIPG_IPGR2 | TIPG_IPGR1 | TIPG_IPGT);
        // ============================================
        // 4.6.5 Receive Initialization
        // Install the receive ring
        self.write_reg(RDBAL, self.rx_ring_pa as u32);
        assert_eq!(self.read_reg(RDBAL), self.rx_ring_pa as u32);
        self.write_reg(RDBAH, (self.rx_ring_pa >> 32) as u32);
        self.write_reg(RDLEN, core::mem::size_of_val(self.rx_ring) as u32);
        self.write_reg(RDH, 0);
        self.write_reg(RDT, (self.rx_ring.len() - 1) as u32);

        // Clear Multicast Table Array (MTA).
        for i in 0..128 {
            self.write_reg(MTA + i, 0);
        }

        let (rah_nvm, ral_nvm) = (self.read_reg(RAH), self.read_reg(RAL));

        // Receive Registers Initialization
        let (rah, ral) = self.read_mac();

        assert_eq!((rah, ral), (rah_nvm, ral_nvm));

        self.write_reg(
            RCTL,
            RCTL_SECRC | RCTL_BSEX | RCTL_BSIZE | RCTL_BAM | RCTL_EN,
        );

        // Initialize the RX Delay Timer Register and RX Interrupt Absolute Delay Timer
        self.write_reg(RDTR, 0);
        self.write_reg(RADV, 8);
        self.write_reg(ITR, 4000);

        fence(SeqCst);
        // ============================================
        self.read_reg(ICR);
        self.enable_intr();

        Ok(())
    }

    fn init_pcie_msi(&mut self) -> Result<u16, IgbDriverErr> {
        self.info.disable_legacy_interrupt();

        if let Some(msix) = self.info.get_msix_mut() {
            msix.disalbe();
        }

        if let Some(msi) = self.info.get_msi_mut() {
            msi.disable();

            if let Ok(irq) = awkernel_lib::interrupt::register_handler_for_pnp(
                "igb",
                Box::new(|_irq| {
                    log::debug!("igb interrupt.");
                }),
            ) {
                msi.set_multiple_message_enable(MultipleMessage::One)
                    .unwrap();

                #[cfg(feature = "x86")]
                msi.set_x86_interrupt(0, irq, false, false);

                self.irq = Some(irq);
                awkernel_lib::interrupt::enable_irq(irq);

                msi.enable();

                Ok(irq)
            } else {
                Err(IgbDriverErr::InitializeInterrupt)
            }
        } else {
            Err(IgbDriverErr::InitializeInterrupt)
        }
    }

    /// Allocate the buffer space for e1000's rx_ring
    fn allocate_buffer<F, FA, E>(
        dma_offset: usize,
        page_table: &mut impl PageTable<F, FA, E>,
        page_allocator: &mut FA,
    ) -> Result<(VirtAddr, PhyAddr), IgbDriverErr>
    where
        F: Frame,
        FA: FrameAllocator<F, E>,
    {
        let buffer_pa = if let Ok(frame) = page_allocator.allocate_frame() {
            frame.start_address()
        } else {
            return Err(IgbDriverErr::MemoryMapFailure);
        };

        let buffer_va = VirtAddr::new(dma_offset + buffer_pa.as_usize());

        unsafe {
            if page_table
                .map_to(
                    buffer_va,
                    buffer_pa,
                    Flags {
                        write: true,
                        execute: false,
                        cache: false,
                        write_through: false,
                        device: false,
                    },
                    page_allocator,
                )
                .is_err()
            {
                log::error!("igb: Error mapping frame.");
                return Err(IgbDriverErr::MemoryMapFailure);
            }
        };

        Ok((buffer_va, buffer_pa))
    }

    /// Create Receive and Transmit Buffer
    fn create_ring<F, FA, E>(
        dma_offset: usize,
        page_table: &mut impl PageTable<F, FA, E>,
        page_allocator: &mut FA,
    ) -> Result<(VirtAddr, PhyAddr), IgbDriverErr>
    where
        F: Frame,
        FA: FrameAllocator<F, E>,
    {
        let frame = if let Ok(frame) = page_allocator.allocate_frame() {
            frame
        } else {
            return Err(IgbDriverErr::MemoryMapFailure);
        };

        unsafe {
            let virt_addr = VirtAddr::new(frame.start_address().as_usize() + dma_offset);

            if page_table
                .map_to(
                    virt_addr,
                    frame.start_address(),
                    Flags {
                        write: true,
                        execute: false,
                        cache: false,
                        write_through: false,
                        device: false,
                    },
                    page_allocator,
                )
                .is_err()
            {
                log::error!("igb: Error mapping frame.");
                return Err(IgbDriverErr::MemoryMapFailure);
            }
        };

        let ring_pa = frame.start_address();
        let ring_va = dma_offset + ring_pa.as_usize();

        // clear the ring
        unsafe { write_bytes(ring_va as *mut u8, 0, PAGESIZE) };

        Ok((VirtAddr::new(ring_va), ring_pa))
    }

    /// Volatile write the certain register
    #[inline(always)]
    unsafe fn write_reg(&mut self, reg: usize, val: u32) {
        self.bar0.write32(reg, val);
    }

    /// Volatile read the e1000's  register
    #[inline(always)]
    unsafe fn read_reg(&self, reg: usize) -> u32 {
        self.bar0.read32(reg).unwrap()
    }

    /// Disable e1000's interrupt
    unsafe fn disable_intr(&mut self) {
        self.write_reg(IMC, !0);
    }

    /// Enable e1000' interrupt
    unsafe fn enable_intr(&mut self) {
        self.write_reg(IMS, IMS_ENABLE_MASK);
    }

    /// Read the MAC address through eeprom
    /// Divide the address into higher 32 bits and lower 32 bits.
    unsafe fn read_mac(&mut self) -> (u32, u32) {
        let ral = self.read_eeprom(0) | self.read_eeprom(1) << 16;

        let rah = self.read_eeprom(2) | (1 << 31);

        (rah, ral)
    }

    /// Read the MAC address through eeprom
    unsafe fn get_mac(&mut self) -> [u8; 6] {
        let mut addr = [0u8; 6];
        for i in 0..3 {
            let word = self.read_eeprom(i as u32);
            addr[i * 2] = (word & 0xFFFF) as u8;
            addr[i * 2 + 1] = (word >> 8) as u8;
        }
        addr
    }

    /// Read eeprom through port IO
    unsafe fn read_eeprom(&mut self, reg: u32) -> u32 {
        self.write_reg(EERD, 1 | (reg << 2));
        fence(SeqCst);
        while self.read_reg(EERD) & 2 == 0 {
            spin_loop();
        }
        fence(SeqCst);
        self.read_reg(EERD) >> 16
    }

    /// Issue a global reset to e1000
    unsafe fn reset(&mut self) {
        //  Assert a Device Reset Signal
        let ctrl = self.read_reg(CTRL) | CTRL_RST;
        self.write_reg(CTRL, ctrl);
        // GCR bit 22 should be set to 1b during initialization
        self.write_reg(GCR, 0b1 << 22);
    }

    /// Check whether the transmit ring is empty
    unsafe fn tx_ring_empty(&self) -> bool {
        let head = self.read_reg(TDH);
        let tail = self.read_reg(TDT);
        let next = (tail + 1) % self.tx_ring.len() as u32;

        head == next
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
