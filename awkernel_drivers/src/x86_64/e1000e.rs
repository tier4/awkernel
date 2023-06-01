#![allow(dead_code)]
#![allow(unused_variables)]
use super::pcie::{DeviceInfo, PCIeDevice};
use crate::net::ether::{Ether, EtherErr};
use crate::x86_64::{OffsetPageTable, PageAllocator, PhysFrame};
use awkernel_lib::arch::x86_64::mmu::map_to;
use core::mem::size_of;
use core::ptr::{read_volatile, write_bytes, write_volatile};
use core::slice;
use smoltcp::phy::{self, DeviceCapabilities, Medium};
use x86_64::structures::paging::{FrameAllocator, PageTableFlags};
use x86_64::{PhysAddr, VirtAddr};

const BUFFER_PAGE_SIZE: usize = 4096;

#[repr(C)]
/// Legacy Transmit Descriptor Format
struct TxDescriptor {
    buf: u64,
    length: u16,
    cso: u8,
    cmd: u8,
    // Bit0: Descriptor done status
    // Bit4: Time stamp
    status: u8,
    css: u8,
    vtags: u16,
}

#[repr(C)]
/// Legacy Receive Descriptor Format
/// valid when RCTL.DTYP = 00b
/// and RFCTL.EXSTEN bit is clear
struct RxDescriptor {
    buf: u64,
    len: u16,
    checksum: u16,
    status: u8,
    error: u8,
    vtags: u16,
}

///! intel e1000e driver
pub struct E1000E {
    register_start: usize,
    register_end: usize,
    info: DeviceInfo,
    // ring buffer for receiving data
    rx_ring: &'static [RxDescriptor],
    rx_ring_pa: u64,
    // ring buffer for sending data
    tx_ring: &'static [TxDescriptor],
    tx_ring_pa: u64,
}

const E1000E_BAR0_MASK: usize = 0xFFFFFFF0;

impl PCIeDevice for E1000E {
    const ADDR_SPACE_SIZE: u64 = 128 * 1024; // 128KiB

    fn init(&mut self) {
        assert_eq!(self.info.header_type, 0x0);
        //  set up command register in config space
        // Bit 0 :  I/O Access
        // Bit 1 : Memory Access
        // Bit 2 : LAN R/W field Mastering
        let command_reg = self.info.addr + 0x4;
        unsafe {
            write_volatile(command_reg as *mut u16, 0b111);
        }

        if let Err(e) = unsafe { self.init_hw() } {
            panic!("failed to init the E1000E.");
        }
    }

    fn new<T>(
        info: &DeviceInfo,
        page_table: &mut OffsetPageTable<'static>,
        page_allocator: &mut PageAllocator<T>,
        page_size: u64,
    ) -> Self
    where
        T: Iterator<Item = PhysFrame> + Send,
    {
        let bar0 = unsafe { read_volatile((info.addr + 0x10) as *mut u32) };
        let register_start = (bar0 as usize) | E1000E_BAR0_MASK;
        let register_end = register_start + Self::ADDR_SPACE_SIZE as usize;
        let info = info.clone();

        // allocate virtual memory for register space
        Self::map_register_space(register_start, page_table, page_allocator, page_size);

        // allocate send and recv descriptor ring
        let tx_ring_len = page_size as usize / size_of::<TxDescriptor>();
        let rx_ring_len = page_size as usize / size_of::<RxDescriptor>();
        let (tx_ring_va, tx_ring_pa) = Self::create_ring(page_table, page_allocator, page_size);
        let (rx_ring_va, rx_ring_pa) = Self::create_ring(page_table, page_allocator, page_size);
        let tx_ring = unsafe {
            slice::from_raw_parts_mut(tx_ring_va.as_u64() as *mut TxDescriptor, tx_ring_len)
        };
        let rx_ring = unsafe {
            slice::from_raw_parts_mut(rx_ring_va.as_u64() as *mut RxDescriptor, rx_ring_len)
        };

        // allocate buffer for descriptors
        for tx_desc in tx_ring.iter_mut() {
            let (buf_va, buf_pa) = Self::allocate_buffer(page_table, page_allocator);
            tx_desc.buf = buf_pa.as_u64();
        }

        for rx_desc in rx_ring.iter_mut() {
            let (buf_va, buf_pa) = Self::allocate_buffer(page_table, page_allocator);
            rx_desc.buf = buf_pa.as_u64();
        }

        Self {
            register_start,
            register_end,
            info,
            rx_ring,
            rx_ring_pa: rx_ring_pa.as_u64(),
            tx_ring,
            tx_ring_pa: tx_ring_pa.as_u64(),
        }
    }
}

impl E1000E {
    fn map_register_space<T>(
        register_start: usize,
        page_table: &mut OffsetPageTable<'static>,
        page_allocator: &mut PageAllocator<T>,
        page_size: u64,
    ) where
        T: Iterator<Item = PhysFrame> + Send,
    {
        let mut start = register_start;
        let end = start + Self::ADDR_SPACE_SIZE as usize;
        let flags = PageTableFlags::PRESENT | PageTableFlags::WRITABLE | PageTableFlags::NO_EXECUTE;
        while start < end {
            unsafe {
                map_to(start, start, flags, page_table, page_allocator);
            }
            start += page_size as usize;
        }
    }

    // allocate buffer
    fn allocate_buffer<T>(
        page_table: &mut OffsetPageTable<'static>,
        page_allocator: &mut PageAllocator<T>,
    ) -> (VirtAddr, PhysAddr)
    where
        T: Iterator<Item = PhysFrame> + Send,
    {
        let buffer_pa = if let Some(frame) = page_allocator.allocate_frame() {
            frame.start_address()
        } else {
            panic!("failed to allocate buffer.");
        };
        let buffer_va = page_table.phys_offset() + buffer_pa.as_u64();
        (buffer_va, buffer_pa)
    }

    // create Tx Ring and Rx Ring
    fn create_ring<T>(
        page_table: &mut OffsetPageTable<'static>,
        page_allocator: &mut PageAllocator<T>,
        page_size: u64,
    ) -> (VirtAddr, PhysAddr)
    where
        T: Iterator<Item = PhysFrame> + Send,
    {
        let frame = if let Some(frame) = page_allocator.allocate_frame() {
            frame
        } else {
            panic!("failed to create nic ring.");
        };

        let ring_pa = frame.start_address();
        let ring_va = page_table.phys_offset() + ring_pa.as_u64();

        unsafe {
            write_bytes(ring_va.as_u64() as *mut u8, 0, page_size as usize);
        }

        (ring_va, ring_pa)
    }

    unsafe fn get_regs(&self) -> &mut [u32] {
        let regs_len = (Self::ADDR_SPACE_SIZE / 4) as usize;
        slice::from_raw_parts_mut(self.register_start as *mut u32, regs_len)
    }

    unsafe fn write_reg(&self, reg: usize, val: u32) {
        (self.register_start as *mut u32)
            .add(reg / 4)
            .write_volatile(val)
    }

    unsafe fn read_reg(&self, reg: usize) -> u32 {
        (self.register_start as *const u32)
            .add(reg / 4)
            .read_volatile()
    }

    unsafe fn reset(&self) {
        self.write_reg(IMS, 0);
        let val = self.read_reg(CTRL) | CTRL_RST;
        self.write_reg(CTRL, val);
        self.write_reg(IMS, 0);
    }
}

impl Ether for E1000E {
    // poll for the received packet
    fn recv(&self) -> Result<&mut [u8], EtherErr> {
        loop {}
    } // Initialize receive
    fn send(&self, buffer: &mut [u8]) -> Result<(), EtherErr> {
        unimplemented!()
    }

    unsafe fn init_hw(&mut self) -> Result<(), EtherErr> {
        log::info!("{:#x}", self.read_reg(STATUS));

        // PCIe Register
        // GCR bit 22 should be set to 1b during initialization
        self.write_reg(GCR, 0b1 << 22);
        // 4.6.2 Global Reset and General Configuration
        self.reset();

        // Setup the PHY and the link

        // 4.6.6 Transmit Initialization
        //  Install the transmit ring
        self.write_reg(TDBAL, self.tx_ring_pa as u32);
        self.write_reg(TDBAH, (self.tx_ring_pa >> 32) as u32);
        self.write_reg(TDLEN, self.rx_ring.len() as u32);
        self.write_reg(TDH, 0);
        self.write_reg(TDT, 0);
        // Transmit Registers Initialization
        self.write_reg(TXDCTL, TXDCTL_GRAN | TXDCTL_WTHRESH);
        self.write_reg(TCTL, TCTL_COLD | TCTL_CT | TCTL_PSP | TCTL_EN);
        self.write_reg(TIPG, TIPG_IPGR2 | TIPG_IPGR1 | TIPG_IPGT);
        //  4.6.5 Receive Initialization
        //  Install the receive ring
        self.write_reg(RDBAL, self.rx_ring_pa as u32);
        self.write_reg(RDBAH, (self.rx_ring_pa >> 32) as u32);
        self.write_reg(RDLEN, self.rx_ring.len() as u32);
        self.write_reg(RDH, 0);
        self.write_reg(RDT, (self.rx_ring.len() - 1) as u32);
        // Clear the Multicast Table Array
        for offset in 0..128 {
            self.write_reg(MTA + offset, 0);
        }
        // Receive Registers Intialization
        self.write_reg(RAH, 0); // MAC Low
        self.write_reg(RAL, 0); // MAC High
        self.write_reg(
            RCTL,
            RCTL_SECRC | RCTL_BSEX | RCTL_BSIZE | RCTL_BAM | RCTL_EN,
        );

        log::info!("{:#x}", self.read_reg(STATUS));

        // Enable interrupt

        Ok(())
    }
}

pub struct RxToken<'a>(&'a E1000E);

pub struct TxToken<'a>(&'a E1000E);

/// Adapting a lazy method such that
/// the receiving and sending operations only occur
/// when the tokens are consumed.
/// Thus the `receive` and ` transmit` only create the token.
impl<'a> phy::Device<'a> for E1000E {
    type RxToken = RxToken<'a> where Self : 'a;
    type TxToken = TxToken<'a> where Self : 'a;
    fn capabilities(&self) -> smoltcp::phy::DeviceCapabilities {
        let mut cap = DeviceCapabilities::default();
        cap.max_transmission_unit = 1536;
        cap.max_burst_size = Some(32);
        cap.medium = Medium::Ethernet;
        cap
    }

    fn receive(&mut self) -> Option<(Self::RxToken, Self::TxToken)> {
        None
    }

    fn transmit(&mut self) -> Option<Self::TxToken> {
        None
    }
}

impl<'a> phy::RxToken for RxToken<'a> {
    /// Store packet data into the buffer.
    /// Closure f will map the raw bytes to the form that
    /// could be used in the higher layer of smoltcp.
    fn consume<R, F>(self, timestamp: smoltcp::time::Instant, f: F) -> smoltcp::Result<R>
    where
        F: FnOnce(&mut [u8]) -> smoltcp::Result<R>,
    {
        let buffer = self.0.recv().unwrap();
        let result = f(buffer);
        result
    }
}

impl<'a> phy::TxToken for TxToken<'a> {
    /// create a buffer of size `len`
    /// Closure f will construct a packet in the buffer.
    /// Real packet data transmissions occur here.
    fn consume<R, F>(
        self,
        timestamp: smoltcp::time::Instant,
        len: usize,
        f: F,
    ) -> smoltcp::Result<R>
    where
        F: FnOnce(&mut [u8]) -> smoltcp::Result<R>,
    {
        // allocate a buffer for raw data
        let mut buffer: [u8; BUFFER_PAGE_SIZE] = [0; BUFFER_PAGE_SIZE];
        // construct packet in buffer
        let result = f(&mut buffer[0..len]);
        // send the buffer
        let _ = self.0.send(&mut buffer);
        result
    }
}

const CTRL: usize = 0x00000; // Device Control Register
const STATUS: usize = 0x00008; // Device Status register
const IMS: usize = 0x000D0; // Interrupt Mask Set/Read Register
const IMC: usize = 0x000D8; // Interrupt Mask Clear Register

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
