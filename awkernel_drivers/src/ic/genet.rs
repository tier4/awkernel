use awkernel_lib::{
    addr::{virt_addr::VirtAddr, Addr},
    net::{
        ether::ETHER_ADDR_LEN,
        net_device::{
            self, EtherFrameBuf, EtherFrameRef, NetCapabilities, NetDevError, NetDevice, NetFlags,
        },
    },
};

use alloc::{boxed::Box, vec::Vec};

pub const DMA_DEFAULT_QUEUE: u32 = 16;

mod registers {
    use awkernel_lib::mmio_rw;

    mmio_rw!(offset 0x000 => pub SYS_REV_CTRL<u32>);
    pub const REV_MAJOR: u32 = 0xf000000;
    pub const REV_MAJOR_SHIFT: u32 = 24;
    pub const REV_MAJOR_V5: u32 = 6;
    pub const REV_MINOR: u32 = 0xf0000;
    pub const REV_MINOR_SHIFT: u32 = 16;
    pub const REV_PHY: u32 = 0xffff;

    mmio_rw!(offset 0x008 => pub SYS_RBUF_FLUSH_CTRL<u32>);
    pub const SYS_RBUF_FLUSH_RESET: u32 = 1 << 1;

    mmio_rw!(offset 0x808 => pub UMAC_CMD<u32>);
    pub const UMAC_CMD_LCL_LOOP_EN: u32 = 1 << 15;
    pub const UMAC_CMD_SW_RESET: u32 = 1 << 13;
    pub const UMAC_CMD_PROMISC: u32 = 1 << 4;

    mmio_rw!(offset 0xd80 => pub UMAC_MIB_CTRL<u32>);
    pub const UMAC_MIB_RESET_TX: u32 = 1 << 2;
    pub const UMAC_MIB_RESET_RUNT: u32 = 1 << 1;
    pub const UMAC_MIB_RESET_RX: u32 = 1;

    pub const RX_BASE: usize = 0x2000;
    pub const TX_BASE: usize = 0x4000;

    mmio_rw!(offset RX_BASE + 0x1040 + 0x04 => pub RX_DMA_CTRL<u32>);
    pub const RX_DMA_CTRL_EN: u32 = 1;

    #[inline(always)]
    pub fn rx_dma_ctrl_rbuf_en(qid: u32) -> u32 {
        1 << (qid + 1)
    }

    mmio_rw!(offset TX_BASE + 0x1040 + 0x04 => pub TX_DMA_CTRL<u32>);
    pub const TX_DMA_CTRL_EN: u32 = 1;

    #[inline(always)]
    pub fn tx_dma_ctrl_rbuf_en(qid: u32) -> u32 {
        1 << (qid + 1)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GenetError {
    InvalidMajorVersion,
    InvalidMacAddress,
    DMAPoolAllocation,
    InvalidDMAPoolSize,
    InitializeInterrupt,
    Mii,
    NotYetImplemented,
}

pub struct Genet {}

impl NetDevice for Genet {
    fn add_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        todo!()
    }

    fn can_send(&self) -> bool {
        todo!()
    }

    fn capabilities(&self) -> NetCapabilities {
        todo!()
    }

    fn device_short_name(&self) -> alloc::borrow::Cow<'static, str> {
        "genet".into()
    }

    fn down(&self) -> Result<(), NetDevError> {
        todo!()
    }

    fn flags(&self) -> NetFlags {
        todo!()
    }

    fn link_speed(&self) -> u64 {
        todo!()
    }

    fn link_status(&self) -> net_device::LinkStatus {
        todo!()
    }

    fn mac_address(&self) -> [u8; 6] {
        todo!()
    }

    fn recv(&self, que_id: usize) -> Result<Option<EtherFrameBuf>, NetDevError> {
        todo!()
    }

    fn interrupt(&self, irq: u16) -> Result<(), NetDevError> {
        todo!()
    }

    fn send(&self, data: EtherFrameRef, que_id: usize) -> Result<(), NetDevError> {
        todo!()
    }

    fn up(&self) -> Result<(), NetDevError> {
        todo!()
    }

    fn remove_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        todo!()
    }

    fn irqs(&self) -> Vec<u16> {
        todo!()
    }

    fn num_queues(&self) -> usize {
        1
    }

    fn poll(&self) -> bool {
        todo!()
    }

    fn poll_in_service(&self) -> Result<(), NetDevError> {
        todo!()
    }

    fn poll_mode(&self) -> bool {
        false
    }

    fn rx_irq_to_que_id(&self, _irq: u16) -> Option<usize> {
        todo!()
    }

    fn tick(&self) -> Result<(), NetDevError> {
        todo!()
    }

    fn tick_msec(&self) -> Option<u64> {
        todo!()
    }
}

pub fn attach(
    base_addr: VirtAddr,
    irqs: &[u16],
    phy_mode: &str,
    phy_id: Option<u32>,
    mac_addr: &Option<[u8; ETHER_ADDR_LEN]>,
) -> Result<(), GenetError> {
    let base = base_addr.as_usize();

    let major =
        (registers::SYS_REV_CTRL.read(base) & registers::REV_MAJOR) >> registers::REV_MAJOR_SHIFT;

    if major != registers::REV_MAJOR_V5 {
        return Err(GenetError::InvalidMajorVersion);
    }

    let minor =
        (registers::SYS_REV_CTRL.read(base) & registers::REV_MINOR) >> registers::REV_MINOR_SHIFT;

    log::info!("GENET: version 5.{minor} phy {:04x}", registers::REV_PHY);

    // reset core
    reset(base_addr);

    // disable DMA
    dma_disable(base_addr);

    // Install interrupt handlers
    for irq in irqs {
        awkernel_lib::interrupt::register_handler(
            *irq,
            "genet".into(),
            Box::new(|irq| {
                awkernel_lib::net::net_interrupt(irq);
            }),
        )
        .or(Err(GenetError::InitializeInterrupt))?;
    }

    Err(GenetError::NotYetImplemented)
}

fn reset(base_addr: VirtAddr) {
    let base = base_addr.as_usize();

    let mut val = registers::SYS_RBUF_FLUSH_CTRL.read(base);
    val |= registers::SYS_RBUF_FLUSH_RESET;
    registers::SYS_RBUF_FLUSH_CTRL.write(val, base);
    awkernel_lib::delay::wait_microsec(10);

    val &= !registers::SYS_RBUF_FLUSH_RESET;
    registers::SYS_RBUF_FLUSH_CTRL.write(val, base);
    awkernel_lib::delay::wait_microsec(10);

    registers::SYS_RBUF_FLUSH_CTRL.write(0, base);
    awkernel_lib::delay::wait_microsec(10);

    registers::UMAC_CMD.write(0, base);
    registers::UMAC_CMD.write(
        registers::UMAC_CMD_LCL_LOOP_EN | registers::UMAC_CMD_SW_RESET,
        base,
    );
    awkernel_lib::delay::wait_microsec(10);
    registers::UMAC_CMD.write(0, base);

    registers::UMAC_MIB_CTRL.write(
        registers::UMAC_MIB_RESET_RUNT
            | registers::UMAC_MIB_RESET_RX
            | registers::UMAC_MIB_RESET_TX,
        base,
    );
    registers::UMAC_MIB_CTRL.write(0, base);
}

fn dma_disable(base_addr: VirtAddr) {
    let base = base_addr.as_usize();

    let mut val = registers::TX_DMA_CTRL.read(base);
    val &= !registers::TX_DMA_CTRL_EN;
    val &= !registers::tx_dma_ctrl_rbuf_en(DMA_DEFAULT_QUEUE);
    registers::TX_DMA_CTRL.write(val, base);

    let mut val = registers::RX_DMA_CTRL.read(base);
    val &= !registers::RX_DMA_CTRL_EN;
    val &= !registers::rx_dma_ctrl_rbuf_en(DMA_DEFAULT_QUEUE);
    registers::RX_DMA_CTRL.write(val, base);
}
