#![allow(dead_code)]
#![allow(unused_variables)]
use super::pcie::{DeviceInfo, PCIeDevice};
use crate::net::ether::{Ether, EtherErr};
use crate::net::mbuf::MBuf;
use crate::net::ring::{RecvRing, SendRing};
use crate::x86_64::{OffsetPageTable, PageAllocator, PhysFrame};
use awkernel_lib::arch::x86_64::mmu::map_to;
use core::cell::OnceCell;
use core::ptr::{read_volatile, write_volatile};
use smoltcp::phy;
use x86_64::structures::paging::PageTableFlags;

#[repr(C)]
struct TxDescriptor {}

#[repr(C)]
struct RxDesriptor {}

///! intel e1000e driver
pub struct E1000E {
    register_start: usize,
    register_end: usize,
    info: DeviceInfo,
    // ring buffer for receiving data
    rx_ring: OnceCell<RecvRing>,
    // ring buffer for sending data
    tx_ring: OnceCell<SendRing>,
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

        Self {
            register_start,
            register_end,
            info,
            rx_ring: OnceCell::new(),
            tx_ring: OnceCell::new(),
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

    // create Tx Ring and Rx Ring
    fn create_ring<T>(
        page_table: &mut OffsetPageTable<'static>,
        page_allocator: &mut PageAllocator<T>,
        page_size: u64,
    ) where
        T: Iterator<Item = PhysFrame> + Send,
    {

    }
}

impl Ether for E1000E {
    // poll for the received packet
    fn poll(&mut self) -> Result<(), EtherErr> {
        loop {}
    }
    // send packet data stored in buffer
    fn send(&mut self, buffer: &mut MBuf) -> Result<(), EtherErr> {
        unimplemented!()
    }

    fn init_hw(&mut self) -> Result<(), EtherErr> {
        // 1.Disable Interrupts

        // 2. Issue Global Reset and perform General Configuration

        // 3. Setup the PHY and the link

        // 4. Initialize all statistical counters

        // 5. Initialize receive

        // 6. Initialize transmit

        // 7. Enable interrupt

        Ok(())
    }
}

pub struct RxToken(MBuf);

pub struct TxToken(MBuf);

/// Adapting a lazy method such that
/// the receiving and sending operations only occur
/// when the tokens are consumed.
/// Thus the `receive` and ` transmit` only create the token.
impl phy::Device<'_> for E1000E {
    type RxToken = RxToken;
    type TxToken = TxToken;
    fn capabilities(&self) -> smoltcp::phy::DeviceCapabilities {
        unimplemented!()
    }

    fn receive(&mut self) -> Option<(Self::RxToken, Self::TxToken)> {
        None
    }

    fn transmit(&mut self) -> Option<Self::TxToken> {
        None
    }
}

impl phy::RxToken for RxToken {
    /// Store packet data into the buffer.
    /// Closure f will map the raw bytes to the form that
    /// could be used in the higher layer of smoltcp.
    fn consume<R, F>(self, timestamp: smoltcp::time::Instant, f: F) -> smoltcp::Result<R>
    where
        F: FnOnce(&mut [u8]) -> smoltcp::Result<R>,
    {
        unimplemented!()
    }
}

impl phy::TxToken for TxToken {
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

        // construct packet in buffer

        // send the buffer

        unimplemented!()
    }
}

// Interrupt Mask Set/Read Register
pub(crate) const _IMS: usize = 0x000D0;
// Interrupt Mask Clear Register
pub(crate) const _IMC: usize = 0x000D8;
