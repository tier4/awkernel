use crate::pcie::{DeviceInfo, PCIeDevice, PCIeDeviceErr};
use alloc::vec::Vec;
use awkernel_lib::arch::x86_64::mmu::map_to;
use awkernel_lib::arch::x86_64::page_allocator::PageAllocator;
use awkernel_lib::net::NetDevice;
use core::hint::spin_loop;
use core::mem::size_of;
use core::ptr::{read_volatile, write_bytes, write_volatile};
use core::sync::atomic::fence;
use core::sync::atomic::Ordering::SeqCst;
use core::{fmt, slice};
use x86_64::structures::paging::{FrameAllocator, OffsetPageTable, PageTableFlags, PhysFrame};
use x86_64::{PhysAddr, VirtAddr};

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

/// Intel e1000e driver
pub struct E1000E {
    register_start: usize,
    info: DeviceInfo,
    page_size: usize,

    // Receive Descriptor Ring
    rx_ring: &'static mut [RxDescriptor],
    rx_ring_pa: u64,
    rx_bufs: Vec<VirtAddr>,
    // Transmission Descriptor Ring
    tx_ring: &'static mut [TxDescriptor],
    tx_ring_pa: u64,
}

pub enum E1000EDriverErr {
    MemoryMapFailure,
}

impl From<E1000EDriverErr> for PCIeDeviceErr {
    fn from(_value: E1000EDriverErr) -> Self {
        PCIeDeviceErr::InitFailure
    }
}

impl fmt::Display for E1000EDriverErr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::MemoryMapFailure => {
                write!(f, "memory map fault occurs during driver initialization.")
            }
        }
    }
}

//===========================================================================
impl PCIeDevice for E1000E {
    const REG_SPACE_SIZE: u64 = 128 * 1024; // 128KiB

    fn init(&mut self) -> Result<(), PCIeDeviceErr> {
        assert_eq!(self.info.header_type, 0x0);
        // set up command register in config space
        // bit 0 : I/O Access
        // bit 1 : Memory Access
        // bit 2 : LAN R/W field Mastering
        let command_reg = self.info.addr + 0x4;
        unsafe {
            write_volatile(command_reg as *mut u16, 0b111);
        }

        if let Err(e) = unsafe { self.init_hw() } {
            log::error!("{}", e);
            return Err(PCIeDeviceErr::InitFailure);
        }

        Ok(())
    }

    fn new<T>(
        info: &DeviceInfo,
        page_table: &mut OffsetPageTable<'static>,
        page_allocator: &mut PageAllocator<T>,
        page_size: u64,
    ) -> Result<Self, PCIeDeviceErr>
    where
        T: Iterator<Item = PhysFrame> + Send,
    {
        let bar0 = unsafe { read_volatile((info.addr + 0x10) as *mut u32) };
        let register_start = (bar0 as usize) & 0xFFFFFFF0;
        let info = *info;

        // allocate virtual memory for register space
        Self::map_register_space(register_start, page_table, page_allocator, page_size)?;

        // allocate send and recv descriptor ring
        let tx_ring_len = page_size as usize / size_of::<TxDescriptor>();
        let rx_ring_len = page_size as usize / size_of::<RxDescriptor>();
        let (tx_ring_va, tx_ring_pa) = Self::create_ring(page_table, page_allocator, page_size)?;
        let (rx_ring_va, rx_ring_pa) = Self::create_ring(page_table, page_allocator, page_size)?;
        let tx_ring = unsafe {
            slice::from_raw_parts_mut(tx_ring_va.as_u64() as *mut TxDescriptor, tx_ring_len)
        };
        let rx_ring = unsafe {
            slice::from_raw_parts_mut(rx_ring_va.as_u64() as *mut RxDescriptor, rx_ring_len)
        };

        let mut rx_bufs = Vec::new();

        // allocate buffer for descriptors
        for tx_desc in tx_ring.iter_mut() {
            let (_, buf_pa) = Self::allocate_buffer(page_table, page_allocator)?;
            tx_desc.buf = buf_pa.as_u64();
            tx_desc.status |= 1;
        }

        for rx_desc in rx_ring.iter_mut() {
            let (buf_va, buf_pa) = Self::allocate_buffer(page_table, page_allocator)?;
            rx_desc.buf = buf_pa.as_u64();
            rx_bufs.push(buf_va);
        }

        Ok(Self {
            register_start,
            info,
            page_size: page_size as usize,
            rx_ring,
            rx_ring_pa: rx_ring_pa.as_u64(),
            rx_bufs,
            tx_ring,
            tx_ring_pa: tx_ring_pa.as_u64(),
        })
    }
}

impl NetDevice for E1000E {
    fn mac_address(&self) -> [u8; 6] {
        unsafe { self.get_mac() }
    }

    fn can_send(&self) -> bool {
        let tdt = unsafe { self.read_reg(TDT) };
        let tx_status = self.tx_ring[tdt as usize].status;

        tx_status & 1 != 0 && !unsafe { self.tx_ring_empty() }
    }

    fn recv(&mut self) -> Option<Vec<u8>> {
        if !self.can_send() {
            return None;
        }

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
        unsafe {
            self.write_reg(RDT, curr_rdt);
        }

        Some(data)
    }

    fn send(&mut self, data: &mut [u8]) -> Option<()> {
        let head = unsafe { self.read_reg(TDH) };
        let tail = unsafe { self.read_reg(TDT) };

        let next_tail = (tail + 1) % self.tx_ring.len() as u32;

        let data_len = data.len();
        // data should not be longer than buffer
        if data_len >= self.page_size {
            return None;
        }

        if next_tail == head {
            return None;
        }

        //  By Datasheet 7.2.10.1.2
        if data_len >= 16288 {
            return None;
        }

        // Copy the data into the buffer()
        self.tx_ring[tail as usize].status = 0;
        self.tx_ring[tail as usize].length = data_len as u16;
        self.tx_ring[tail as usize].cmd = (1 << 3) | (1 << 1) | (1 << 0);

        fence(SeqCst); // barrier

        // Increment tail pointer
        unsafe {
            self.write_reg(TDT, next_tail);
        }

        Some(())
    }
}

//===========================================================================
impl E1000E {
    /// Initialize e1000e's register
    unsafe fn init_hw(&mut self) -> Result<(), E1000EDriverErr> {
        log::info!("Initializing e1000e driver...");
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
        // Receive Registers Intialization
        let (rah, ral) = self.read_mac();
        assert_eq!((rah, ral), (rah_nvm, ral_nvm));

        self.write_reg(
            RCTL,
            RCTL_SECRC | RCTL_BSEX | RCTL_BSIZE | RCTL_BAM | RCTL_EN,
        );

        fence(SeqCst);
        // ============================================
        self.enable_intr();
        Ok(())
    }

    /// Create the memory map for e1000e's register space
    fn map_register_space<T>(
        register_start: usize,
        page_table: &mut OffsetPageTable<'static>,
        page_allocator: &mut PageAllocator<T>,
        page_size: u64,
    ) -> Result<(), E1000EDriverErr>
    where
        T: Iterator<Item = PhysFrame> + Send,
    {
        let mut start = register_start;
        let end = start + Self::REG_SPACE_SIZE as usize;
        let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;
        while start < end {
            if !unsafe { map_to(start, start, flags, page_table, page_allocator) } {
                return Err(E1000EDriverErr::MemoryMapFailure);
            }
            start += page_size as usize;
        }
        Ok(())
    }

    /// Allocate the buffer space for e1000e's rx_ring
    fn allocate_buffer<T>(
        page_table: &OffsetPageTable<'static>,
        page_allocator: &mut PageAllocator<T>,
    ) -> Result<(VirtAddr, PhysAddr), E1000EDriverErr>
    where
        T: Iterator<Item = PhysFrame> + Send,
    {
        let buffer_pa = if let Some(frame) = page_allocator.allocate_frame() {
            frame.start_address()
        } else {
            return Err(E1000EDriverErr::MemoryMapFailure);
        };
        let buffer_va = page_table.phys_offset() + buffer_pa.as_u64();
        Ok((buffer_va, buffer_pa))
    }

    /// Create Receive and Transmit Buffer
    fn create_ring<T>(
        page_table: &OffsetPageTable<'static>,
        page_allocator: &mut PageAllocator<T>,
        page_size: u64,
    ) -> Result<(VirtAddr, PhysAddr), E1000EDriverErr>
    where
        T: Iterator<Item = PhysFrame> + Send,
    {
        let frame = if let Some(frame) = page_allocator.allocate_frame() {
            frame
        } else {
            return Err(E1000EDriverErr::MemoryMapFailure);
        };

        let ring_pa = frame.start_address();
        let ring_va = page_table.phys_offset() + ring_pa.as_u64();

        // clear the ring
        unsafe {
            write_bytes(ring_va.as_u64() as *mut u8, 0, page_size as usize);
        }

        Ok((ring_va, ring_pa))
    }

    /// Volatile write the certain register
    unsafe fn write_reg(&self, reg: usize, val: u32) {
        (self.register_start as *mut u32)
            .add(reg / 4)
            .write_volatile(val)
    }

    /// Volatile read the e1000e's  register
    unsafe fn read_reg(&self, reg: usize) -> u32 {
        (self.register_start as *const u32)
            .add(reg / 4)
            .read_volatile()
    }

    /// Disable e1000e's interrupt
    unsafe fn disable_intr(&self) {
        self.write_reg(IMC, !0);
    }

    /// Enable e1000e' interrupt
    unsafe fn enable_intr(&self) {
        self.write_reg(IMS, IMS_ENABLE_MASK);
    }

    /// Read the MAC address through eeprom
    /// Divide the address into higher 32 bits and lower 32 bits.
    unsafe fn read_mac(&self) -> (u32, u32) {
        let ral = self.read_eeprom(0) | self.read_eeprom(1) << 16;

        let rah = self.read_eeprom(2) | (1 << 31);

        (rah, ral)
    }

    /// Read the MAC address through eeprom
    unsafe fn get_mac(&self) -> [u8; 6] {
        let mut addr = [0u8; 6];
        for i in 0..3 {
            let word = self.read_eeprom(i as u32);
            addr[i * 2] = (word & 0xFFFF) as u8;
            addr[i * 2 + 1] = (word >> 8) as u8;
        }
        addr
    }

    /// Read eeprom through port IO
    unsafe fn read_eeprom(&self, reg: u32) -> u32 {
        self.write_reg(EERD, 1 | (reg << 2));
        fence(SeqCst);
        while self.read_reg(EERD) & 2 == 0 {
            spin_loop();
        }
        fence(SeqCst);
        self.read_reg(EERD) >> 16
    }

    /// Issue a global reset to e1000e
    unsafe fn reset(&self) {
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

//===========================================================================
// e1000e's registers
const CTRL: usize = 0x00000; // Device Control Register
const _STATUS: usize = 0x00008; // Device Status register
const _EEC: usize = 0x00010; // EEPROM Control Register
const EERD: usize = 0x00014; // EEPROM Read Register
const IMC: usize = 0x000D8; // Interrupt Mask Clear Register

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
const MTA: usize = 0x05200; // Multicast Table Array
const RAL: usize = 0x05400; // Receive Address Low
const RAH: usize = 0x05404; // Receive Address High

const GCR: usize = 0x05B00; // 3GIO

const CTRL_RST: u32 = 0b1 << 26;

const TXDCTL_GRAN: u32 = 0b1 << 24;
const TXDCTL_WTHRESH: u32 = 0b1 << 16;

const TCTL_EN: u32 = 0b1 << 1; //  Transmitter Enable
const TCTL_PSP: u32 = 0b1 << 3; //  Pad short packets
const TCTL_CT: u32 = 0x0F << 4; // Collision Thresold

const TCTL_COLD: u32 = 0x3F << 12; // Collision Distance (FDX)
const TIPG_IPGT: u32 = 0x8;
const TIPG_IPGR1: u32 = 0x2 << 10;
const TIPG_IPGR2: u32 = 0xA << 20;

const RCTL_EN: u32 = 0b1 << 1; // Receive Control Register Enable
const RCTL_BAM: u32 = 0b1 << 15; // Broadcast Accept Mode
const RCTL_BSIZE: u32 = 0b11 << 16; // Receive Buffer Size (4096 Bytes)
const RCTL_BSEX: u32 = 0b1 << 25; // Buffer Size Extenson
const RCTL_SECRC: u32 = 0b1 << 26; // Strip CRC from packet
