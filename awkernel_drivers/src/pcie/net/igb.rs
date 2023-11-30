//! # Intel Gigabit Ethernet Controller

use crate::pcie::{self, msi::MultipleMessage, BaseAddress, PCIeDevice, PCIeDeviceErr, PCIeInfo};
use alloc::{boxed::Box, sync::Arc, vec::Vec};
use awkernel_lib::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
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
    irq: Option<u16>,
    bar0: BaseAddress,
    hw: igb_hw::IgbHw,

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
}

impl From<IgbDriverErr> for PCIeDeviceErr {
    fn from(_value: IgbDriverErr) -> Self {
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

        hardware_init(&mut hw, &mut info)?;

        log::debug!("e1000: {:?}\r\n{:?}", hw, info);

        loop {}

        let bar0 = info.get_bar(0).ok_or(PCIeDeviceErr::InitFailure)?;

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

/// https://github.com/openbsd/src/blob/18bc31b7ebc17ab66d1354464ff2ee3ba31f7750/sys/dev/pci/if_em.c#L1845
fn hardware_init(hw: &mut igb_hw::IgbHw, info: &PCIeInfo) -> Result<(), IgbDriverErr> {
    if matches!(hw.get_mac_type(), igb_hw::MacType::EmPchSpt) {
        check_desc_ring(info)?;
    }

    hw.reset_hw(info)?;

    Ok(())
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
        self.bar0.write(reg, val);
    }

    /// Volatile read the e1000's  register
    #[inline(always)]
    unsafe fn read_reg(&self, reg: usize) -> u32 {
        self.bar0.read(reg).unwrap()
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
        bar0.read(FEXTNVM11).ok_or(IgbDriverErr::ReadFailure)? | FEXTNVM11_DISABLE_MULR_FIX;
    bar0.write(FEXTNVM11, fextnvm11);

    let tdlen = bar0
        .read(tdlen_offset(0))
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

//===========================================================================
// e1000's registers
const CTRL: usize = 0x00000; // Device Control Register
const EECD: usize = 0x00010; // EEPROM Control Register
const EERD: usize = 0x00014; // EEPROM Read Register
const ICR: usize = 0x000C0; // Interrupt Cause Read Register
const ITR: usize = 0x000C4; // Interrupt Throttling Rate Register
const _ICS: usize = 0x000C8; // Interrupt Cause Set Register
const IMC: usize = 0x000D8; // Interrupt Mask Clear Register
const PBA: usize = 0x01000; // Packet Buffer Allocation Register
const PBS: usize = 0x01008; // Packet Buffer Size
const SW_FW_SYNC: usize = 0x05B5C; // Software-Firmware Synchronization - RW

// Status Register
const STATUS: usize = 0x00008; // Device Status register
const STATUS_FD: u32 = 1 << 0; // Full Duplex
const STATUS_LU: u32 = 1 << 1; // Link Up
const STATUS_TBIMODE: u32 = 1 << 5; // TBI Mode

// Interrupt Mask Set/Read Register
const IMS: usize = 0x000D0;
const IMS_ENABLE_MASK: u32 = IMS_RXT0 | IMS_TXDW | IMS_RXDMT0 | IMS_RXSEQ | IMS_LSC;
const IMS_RXT0: u32 = 0x00000080; // Rx timer intr (ring 0)
const IMS_TXDW: u32 = 0x00000001; // Transmit Descriptor Written Back
const IMS_RXDMT0: u32 = 0x00000010; // Receive Descriptor Minimum Threshold hit (ring 0)
const IMS_RXSEQ: u32 = 0x00000008; //  Receive Sequence Error
const IMS_LSC: u32 = 0x00000004; // Link Status Change

// Transmit Registers
const TCTL: usize = 0x00400; // Transmit Control Register
const TIPG: usize = 0x00410; // Transmit IPG Register
const TDBAL: usize = 0x03800; // Transmit Descriptor Base Address Low
const TDBAH: usize = 0x03804; // Transmit Descriptor Base Address High
const TDLEN: usize = 0x03808; // Transmit Descriptor Length
const TDH: usize = 0x03810; // Transmit Descriptor Head
const TDT: usize = 0x03818; // Transmit Descriptor Tail
const TXDCTL: usize = 0x03828; // Transmit Descriptor Control

// Receive Registers
const RCTL: usize = 0x00100; // Receive Control Register
const RDBAL: usize = 0x02800; // Receive Descriptor Base Address Low
const RDBAH: usize = 0x02804; // Receive Descriptor Base Address High
const RDLEN: usize = 0x02808; // Receive Descriptor Base Length
const RDH: usize = 0x02810; // Receive Descriptor Head
const RDT: usize = 0x02818; // Receive Descriptor Tail
const RDTR: usize = 0x2820; // RX Delay Timer Register
const RADV: usize = 0x282C; // RX Interrupt Absolute Delay Timer
const MTA: usize = 0x05200; // Multicast Table Array
const RAL: usize = 0x05400; // Receive Address Low
const RAH: usize = 0x05404; // Receive Address High

const GCR: usize = 0x05B00; // 3GIO
const GCR_CMPL_TMOUT_MASK: u32 = 0x0000F000;
const GCR_CMPL_TMOUT_10_MS: u32 = 0x00001000;
const GCR_CMPL_TMOUT_RESEND: u32 = 0x00010000;
const GCR_CAP_VER2: u32 = 0x00040000;

const CTRL_RST: u32 = 1 << 26;
const CTRL_GIO_MASTER_DISABLE: u32 = 1 << 2;
const CTRL_I2C_ENA: u32 = 1 << 25;
const CTRL_PHY_RST: u32 = 1 << 31;

const TXDCTL_GRAN: u32 = 1 << 24;
const TXDCTL_WTHRESH: u32 = 1 << 16;

const TCTL_EN: u32 = 1 << 1; //  Transmitter Enable
const TCTL_PSP: u32 = 1 << 3; //  Pad short packets
const TCTL_CT: u32 = 0x0F << 4; // Collision Thresold

const TCTL_COLD: u32 = 0x3F << 12; // Collision Distance (FDX)
const TIPG_IPGT: u32 = 0x8;
const TIPG_IPGR1: u32 = 0x2 << 10;
const TIPG_IPGR2: u32 = 0xA << 20;

const RCTL_EN: u32 = 1 << 1; // Receive Control Register Enable
const RCTL_BAM: u32 = 1 << 15; // Broadcast Accept Mode
const RCTL_BSIZE: u32 = 11 << 16; // Receive Buffer Size (4096 Bytes)
const RCTL_BSEX: u32 = 1 << 25; // Buffer Size Extension
const RCTL_SECRC: u32 = 1 << 26; // Strip CRC from packet

// FEXTNVM registers
const _FEXTNVM7: usize = 0xe;
const _FEXTNVM7_SIDE_CLK_UNGATE: u32 = 0x04;
const _FEXTNVM7_DISABLE_SMB_PERST: u32 = 0x00000020;
const _FEXTNVM9: usize = 0x5bb4;
const _FEXTNVM9_IOSFSB_CLKGATE_DIS: u32 = 0x0800;
const _FEXTNVM9_IOSFSB_CLKREQ_DIS: u32 = 0x1000;
const FEXTNVM11: usize = 0x05bbc;
const FEXTNVM11_DISABLE_MULR_FIX: u32 = 0x00002000;

const _TX_CMD_EOP: u8 = 1 << 0; // End of Packet
const TX_CMD_IFCS: u8 = 1 << 1; // Insert FCS
const _TX_CMD_TSE: u8 = 1 << 2; // TCP Segmentation Enable
const _TX_CMD_RS: u8 = 1 << 3; // Report Status
const _TX_CMD_RPS_RSV: u8 = 1 << 4; // Report Packet Sent
const _TX_CMD_DEXT: u8 = 1 << 5; // Descriptor extension (0 = legacy)
const _TX_CMD_VLE: u8 = 1 << 6; // VLAN Packet Enable
const _TX_CMD_IDE: u8 = 1 << 7; // Interrupt Delay Enable

const PCICFG_DESC_RING_STATUS: usize = 0xe4;
const FLUSH_DESC_REQUIRED: u32 = 0x100;

// Extended Configuration Control and Size
const EXTCNF_CTRL: usize = 0x00F00;
const _EXTCNF_CTRL_PCIE_WRITE_ENABLE: u32 = 0x00000001;
const _EXTCNF_CTRL_PHY_WRITE_ENABLE: u32 = 0x00000002;
const _EXTCNF_CTRL_D_UD_ENABLE: u32 = 0x00000004;
const _EXTCNF_CTRL_D_UD_LATENCY: u32 = 0x00000008;
const _EXTCNF_CTRL_D_UD_OWNER: u32 = 0x00000010;
const EXTCNF_CTRL_MDIO_SW_OWNERSHIP: u32 = 0x00000020;
const _EXTCNF_CTRL_MDIO_HW_OWNERSHIP: u32 = 0x00000040;
const _EXTCNF_CTRL_EXT_CNF_POINTER: u32 = 0x0FFF0000;
const _EXTCNF_SIZE_EXT_PHY_LENGTH: u32 = 0x000000FF;
const _EXTCNF_SIZE_EXT_DOCK_LENGTH: u32 = 0x0000FF00;
const _EXTCNF_SIZE_EXT_PCIE_LENGTH: u32 = 0x00FF0000;
const _EXTCNF_CTRL_LCD_WRITE_ENABLE: u32 = 0x00000001;
const EXTCNF_CTRL_SWFLAG: u32 = 0x00000020;
const EXTCNF_CTRL_GATE_PHY_CFG: u32 = 0x00000080;

// FW Semaphore
const FWSM: usize = 0x05B54;

const _FWSM_MODE_MASK: u32 = 0x0000000E; /* FW mode */
const _FWSM_MODE_SHIFT: u32 = 1;
const _FWSM_ULP_CFG_DONE: u32 = 0x00000400; /* Low power cfg done */
const FWSM_FW_VALID: u32 = 0x00008000; /* FW established a valid mode */
const FWSM_RSPCIPHY: u32 = 0x00000040; /* Reset PHY on PCI reset */
const _FWSM_DISSW: u32 = 0x10000000; /* FW disable SW Write Access */
const _FWSM_SKUSEL_MASK: u32 = 0x60000000; /* LAN SKU select */
const _FWSM_SKUEL_SHIFT: u32 = 29;
const _FWSM_SKUSEL_EMB: u32 = 0x0; /* Embedded SKU */
const _FWSM_SKUSEL_CONS: u32 = 0x1; /* Consumer SKU */
const _FWSM_SKUSEL_PERF_100: u32 = 0x2; /* Perf & Corp 10/100 SKU */
const _FWSM_SKUSEL_PERF_GBE: u32 = 0x3; /* Perf & Copr GbE SKU */

// Management Control
const MANC: usize = 0x05820;

const _MANC_SMBUS_EN: u32 = 0x00000001; /* SMBus Enabled - RO */
const _MANC_ASF_EN: u32 = 0x00000002; /* ASF Enabled - RO */
const _MANC_R_ON_FORCE: u32 = 0x00000004; /* Reset on Force TCO - RO */
const _MANC_RMCP_EN: u32 = 0x00000100; /* Enable RCMP 026Fh Filtering */
const _MANC_0298_EN: u32 = 0x00000200; /* Enable RCMP 0298h Filtering */
const _MANC_IPV4_EN: u32 = 0x00000400; /* Enable IPv4 */
const _MANC_IPV6_EN: u32 = 0x00000800; /* Enable IPv6 */
const _MANC_SNAP_EN: u32 = 0x00001000; /* Accept LLC/SNAP */
const _MANC_ARP_EN: u32 = 0x00002000; /* Enable ARP Request Filtering */
const _MANC_NEIGHBOR_EN: u32 = 0x00004000; /* Enable Neighbor Discovery Filtering */
const _MANC_ARP_RES_EN: u32 = 0x00008000; /* Enable ARP response Filtering */
const _MANC_TCO_RESET: u32 = 0x00010000; /* TCO Reset Occurred */
const _MANC_RCV_TCO_EN: u32 = 0x00020000; /* Receive TCO Packets Enabled */
const _MANC_REPORT_STATUS: u32 = 0x00040000; /* Status Reporting Enabled */
const _MANC_RCV_ALL: u32 = 0x00080000; /* Receive All Enabled */
const MANC_BLK_PHY_RST_ON_IDE: u32 = 0x00040000; /* Block phy resets */
const _MANC_EN_MAC_ADDR_FILTER: u32 = 0x00100000; /* Enable MAC address filtering */
const _MANC_EN_MNG2HOST: u32 = 0x00200000; /* Enable MNG packets to host memory */
const _MANC_EN_IP_ADDR_FILTER: u32 = 0x00400000; /* Enable IP address filtering */
const _MANC_EN_XSUM_FILTER: u32 = 0x00800000; /* Enable checksum filtering */
const _MANC_BR_EN: u32 = 0x01000000; /* Enable broadcast filtering */
const _MANC_SMB_REQ: u32 = 0x01000000; /* SMBus Request */
const _MANC_SMB_GNT: u32 = 0x02000000; /* SMBus Grant */
const _MANC_SMB_CLK_IN: u32 = 0x04000000; /* SMBus Clock In */
const _MANC_SMB_DATA_IN: u32 = 0x08000000; /* SMBus Data In */
const _MANC_SMB_DATA_OUT: u32 = 0x10000000; /* SMBus Data Out */
const _MANC_SMB_CLK_OUT: u32 = 0x20000000; /* SMBus Clock Out */

const _MANC_SMB_DATA_OUT_SHIFT: u32 = 28; /* SMBus Data Out Shift */
const _MANC_SMB_CLK_OUT_SHIFT: u32 = 29; /* SMBus Clock Out Shift */

// SW Semaphore Register
const SWSM: usize = 0x05B50;
const SWSM_SMBI: u32 = 0x00000001; /* Driver Semaphore bit */
const SWSM_SWESMBI: u32 = 0x00000002; /* FW Semaphore bit */
const _SWSM_WMNG: u32 = 0x00000004; /* Wake MNG Clock */
const _SWSM_DRV_LOAD: u32 = 0x00000008; /* Driver Loaded Bit */

// Extended Device Control
const CTRL_EXT: usize = 0x00018;
const _CTRL_EXT_GPI0_EN: u32 = 0x00000001; /* Maps SDP4 to GPI0 */
const _CTRL_EXT_GPI1_EN: u32 = 0x00000002; /* Maps SDP5 to GPI1 */
const _CTRL_EXT_PHYINT_EN: u32 = _CTRL_EXT_GPI1_EN;
const _CTRL_EXT_GPI2_EN: u32 = 0x00000004; /* Maps SDP6 to GPI2 */
const _CTRL_EXT_LPCD: u32 = 0x00000004; /* LCD Power Cycle Done */
const _CTRL_EXT_GPI3_EN: u32 = 0x00000008; /* Maps SDP7 to GPI3 */
const _CTRL_EXT_SDP4_DATA: u32 = 0x00000010; /* Value of SW Defineable Pin 4 */
const _CTRL_EXT_SDP5_DATA: u32 = 0x00000020; /* Value of SW Defineable Pin 5 */
const _CTRL_EXT_PHY_INT: u32 = _CTRL_EXT_SDP5_DATA;
const _CTRL_EXT_SDP6_DATA: u32 = 0x00000040; /* Value of SW Defineable Pin 6 */
const _CTRL_EXT_SDP7_DATA: u32 = 0x00000080; /* Value of SW Defineable Pin 7 */
const CTRL_EXT_SDP3_DATA: u32 = 0x00000080; /* Value of SW Defineable Pin 3 */
const _CTRL_EXT_SDP4_DIR: u32 = 0x00000100; /* Direction of SDP4 0=in 1=out */
const _CTRL_EXT_SDP5_DIR: u32 = 0x00000200; /* Direction of SDP5 0=in 1=out */
const _CTRL_EXT_SDP6_DIR: u32 = 0x00000400; /* Direction of SDP6 0=in 1=out */
const _CTRL_EXT_SDP7_DIR: u32 = 0x00000800; /* Direction of SDP7 0=in 1=out */
const _CTRL_EXT_ASDCHK: u32 = 0x00001000; /* Initiate an ASD sequence */
const _CTRL_EXT_EE_RST: u32 = 0x00002000; /* Reinitialize from EEPROM */
const _CTRL_EXT_IPS: u32 = 0x00004000; /* Invert Power State */
const _CTRL_EXT_SPD_BYPS: u32 = 0x00008000; /* Speed Select Bypass */
const _CTRL_EXT_RO_DIS: u32 = 0x00020000; /* Relaxed Ordering disable */
const CTRL_EXT_LINK_MODE_MASK: u32 = 0x00C00000;
const _CTRL_EXT_LINK_MODE_GMII: u32 = 0x00000000;
const _CTRL_EXT_LINK_MODE_TBI: u32 = 0x00C00000;
const _CTRL_EXT_LINK_MODE_KMRN: u32 = 0x00000000;
const CTRL_EXT_LINK_MODE_PCIE_SERDES: u32 = 0x00C00000;
const CTRL_EXT_LINK_MODE_1000BASE_KX: u32 = 0x00400000;
const CTRL_EXT_LINK_MODE_SGMII: u32 = 0x00800000;
const _CTRL_EXT_WR_WMARK_MASK: u32 = 0x03000000;
const _CTRL_EXT_WR_WMARK_256: u32 = 0x00000000;
const _CTRL_EXT_WR_WMARK_320: u32 = 0x01000000;
const _CTRL_EXT_WR_WMARK_384: u32 = 0x02000000;
const _CTRL_EXT_WR_WMARK_448: u32 = 0x03000000;
const _CTRL_EXT_EXT_VLAN: u32 = 0x04000000;
const _CTRL_EXT_DRV_LOAD: u32 = 0x10000000; /* Driver loaded bit for FW */
const _CTRL_EXT_IAME: u32 = 0x08000000; /* Interrupt acknowledge Auto-mask */
const _CTRL_EXT_INT_TIMER_CLR: u32 = 0x20000000; /* Clear Interrupt timers after IMS clear */
const _CRTL_EXT_PB_PAREN: u32 = 0x01000000; /* packet buffer parity error detection enabled */
const _CTRL_EXT_DF_PAREN: u32 = 0x02000000; /* descriptor FIFO parity error detection enable */

const MDICNFG: usize = 0x00E04;
const MDICNFG_EXT_MDIO: u32 = 0x80000000; /* MDI ext/int destination */
const _MDICNFG_COM_MDIO: u32 = 0x40000000; /* MDI shared w/ lan 0 */
const _MDICNFG_PHY_MASK: u32 = 0x03E00000;
const _MDICNFG_PHY_SHIFT: u32 = 21;

// SFPI2C Command Register - RW
const I2CCMD: usize = 0x01028;
const I2CCMD_REG_ADDR_SHIFT: usize = 16;
const I2CCMD_PHY_ADDR_SHIFT: usize = 24;
const I2CCMD_OPCODE_READ: u32 = 0x08000000;
const I2CCMD_OPCODE_WRITE: u32 = 0x00000000;
const I2CCMD_READY: u32 = 0x20000000;
const I2CCMD_ERROR: u32 = 0x80000000;
const I2CCMD_PHY_TIMEOUT: u32 = 200;
const MAX_SGMII_PHY_REG_ADDR: u32 = 255;

// SFP modules ID memory locations
const SFF_IDENTIFIER_OFFSET: u32 = 0x00;
const SFF_IDENTIFIER_SFF: u8 = 0x02;
const SFF_IDENTIFIER_SFP: u8 = 0x03;
const SFF_ETH_FLAGS_OFFSET: u32 = 0x06;

// MDI Control
const MDIC: usize = 0x00020;
const _MDIC_DATA_MASK: u32 = 0x0000FFFF;
const _MDIC_REG_MASK: u32 = 0x001F0000;
const MDIC_REG_SHIFT: u32 = 16;
const _MDIC_PHY_MASK: u32 = 0x03E00000;
const MDIC_PHY_SHIFT: u32 = 21;
const MDIC_OP_WRITE: u32 = 0x04000000;
const MDIC_OP_READ: u32 = 0x08000000;
const MDIC_READY: u32 = 0x10000000;
const _MDIC_INT_EN: u32 = 0x20000000;
const MDIC_ERROR: u32 = 0x40000000;
const MDIC_DEST: u32 = 0x80000000;
