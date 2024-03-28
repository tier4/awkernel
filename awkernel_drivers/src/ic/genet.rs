//! # genet: Broadcom's Genet Ethernet controller.

use awkernel_lib::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    dma_pool::DMAPool,
    net::{
        ether::ETHER_ADDR_LEN,
        multicast::MulticastAddrs,
        net_device::{
            EtherFrameBuf, EtherFrameRef, LinkStatus, NetCapabilities, NetDevError, NetDevice,
            NetFlags,
        },
    },
    sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock},
};

use alloc::{boxed::Box, sync::Arc, vec::Vec};

use crate::{
    if_media::{ifm_subtype, IFM_1000_SX, IFM_1000_T, IFM_100_TX, IFM_AUTO, IFM_ETHER},
    mii::{self, mii_timer, ukphy::Ukphy, Mii, MiiData, MiiError, MiiFlags},
};

pub const DMA_DEFAULT_QUEUE: usize = 16;
pub const MAX_MDF_FILTER: usize = 17;

pub const TX_BUF_SIZE: usize = 2048;
pub const RX_BUF_SIZE: usize = 2048;
type RxBuffer = [[u8; RX_BUF_SIZE]; registers::DMA_DESC_COUNT];
type TxBuffer = [[u8; TX_BUF_SIZE]; registers::DMA_DESC_COUNT];

pub const MII_BUSY_RETRY: i32 = 1000;

pub const MCLSHIFT: u32 = 11; // convert bytes to m_buf clusters 2K cluster can hold Ether frame
pub const MCLBYTES: u32 = 1 << MCLSHIFT; // size of a m_buf cluster

mod registers {
    use awkernel_lib::{mmio_r, mmio_rw, mmio_w};

    use super::bits;

    pub const REV_MAJOR_V5: u8 = 6;
    pub const SYS_RBUF_FLUSH_RESET: u32 = 1 << 1;
    pub const RBUF_ALIGN_2B: u32 = 1 << 1;
    pub const SYS_PORT_MODE_EXT_GPHY: u32 = 3;

    pub const IRQ_TXDMA_DONE: u32 = 1 << 16;
    pub const IRQ_RXDMA_DONE: u32 = 1 << 13;

    mmio_r!(offset  0x000 => pub SYS_REV_CTRL<u32>);
    mmio_rw!(offset 0x004 => pub SYS_PORT_CTRL<u32>);
    mmio_rw!(offset 0x008 => pub SYS_RBUF_FLUSH_CTRL<u32>);

    mmio_rw!(offset 0x08c => pub EXT_RGMII_OOB_CTRL<u32>);

    mmio_rw!(offset 0x200 => pub INTRL2_CPU_STAT<u32>);
    mmio_rw!(offset 0x208 => pub INTRL2_CPU_CLEAR<u32>);
    mmio_rw!(offset 0x20c => pub INTRL2_CPU_STAT_MASK<u32>);
    mmio_rw!(offset 0x214 => pub INTRL2_CPU_CLEAR_MASK<u32>);

    pub const EXT_RGMII_OOB_ID_MODE_DISABLE: u32 = 1 << 16;
    pub const EXT_RGMII_OOB_RGMII_MODE_EN: u32 = 1 << 6;
    pub const EXT_RGMII_OOB_OOB_DISABLE: u32 = 1 << 5;
    pub const EXT_RGMII_OOB_RGMII_LINK: u32 = 1 << 4;

    mmio_rw!(offset 0x300 => pub RBUF_CTRL<u32>);
    mmio_rw!(offset 0x3b4 => pub RBUF_TBUF_SIZE_CTRL<u32>);

    pub const RX_BASE: usize = 0x2000;
    pub const TX_BASE: usize = 0x4000;

    pub const RX_DMA_CTRL_EN: u32 = 1;
    pub fn rx_dma_ctrl_rbuf_en(qid: usize) -> u32 {
        1 << (qid + 1)
    }

    pub const TX_DMA_CTRL_EN: u32 = 1;
    pub fn tx_dma_ctrl_rbuf_en(qid: usize) -> u32 {
        1 << (qid + 1)
    }

    pub const DMA_DESC_COUNT: usize = 256;
    pub const DMA_DESC_SIZE: usize = 12;
    pub const DMA_RING_SIZE: usize = 0x40;

    pub const TX_DESC_COUNT: usize = DMA_DESC_COUNT;
    pub const RX_DESC_COUNT: usize = DMA_DESC_COUNT;

    pub const RX_DMA_RING_BUF_SIZE_DESC_COUNT: u32 = bits(31, 16);
    pub const RX_DMA_RING_BUF_SIZE_BUF_LENGTH: u32 = bits(15, 0);
    pub const RX_DMA_XON_XOFF_THRES_LO: u32 = bits(31, 16);
    pub const RX_DMA_XON_XOFF_THRES_HI: u32 = bits(15, 0);
    pub const TX_DMA_RING_BUF_SIZE_DESC_COUNT: u32 = bits(31, 16);
    pub const TX_DMA_RING_BUF_SIZE_BUF_LENGTH: u32 = bits(15, 0);

    pub const RX_DESC_STATUS_BUFLEN: u32 = bits(27, 16);

    #[inline(always)]
    pub fn rx_dma_ringbase(qid: usize) -> usize {
        0xc00 + DMA_RING_SIZE * qid
    }

    #[inline(always)]
    pub fn rx_dma_write_ptr_lo(qid: usize) -> usize {
        rx_dma_ringbase(qid)
    }

    #[inline(always)]
    pub fn rx_dma_write_ptr_hi(qid: usize) -> usize {
        rx_dma_ringbase(qid) + 0x04
    }

    #[inline(always)]
    pub fn rx_dma_prod_index(qid: usize) -> usize {
        rx_dma_ringbase(qid) + 0x08
    }

    #[inline(always)]
    pub fn rx_dma_cons_index(qid: usize) -> usize {
        rx_dma_ringbase(qid) + 0x0c
    }

    #[inline(always)]
    pub fn rx_dma_ring_buf_size(qid: usize) -> usize {
        rx_dma_ringbase(qid) + 0x10
    }

    #[inline(always)]
    pub fn rx_dma_start_addr_lo(qid: usize) -> usize {
        rx_dma_ringbase(qid) + 0x14
    }

    #[inline(always)]
    pub fn rx_dma_start_addr_hi(qid: usize) -> usize {
        rx_dma_ringbase(qid) + 0x18
    }

    #[inline(always)]
    pub fn rx_dma_end_addr_lo(qid: usize) -> usize {
        rx_dma_ringbase(qid) + 0x1c
    }

    #[inline(always)]
    pub fn rx_dma_end_addr_hi(qid: usize) -> usize {
        rx_dma_ringbase(qid) + 0x20
    }

    #[inline(always)]
    pub fn rx_dma_xon_xoff_thres(qid: usize) -> usize {
        rx_dma_ringbase(qid) + 0x28
    }

    #[inline(always)]
    pub fn rx_dma_read_ptr_lo(qid: usize) -> usize {
        rx_dma_ringbase(qid) + 0x2c
    }

    #[inline(always)]
    pub fn rx_dma_read_ptr_hi(qid: usize) -> usize {
        rx_dma_ringbase(qid) + 0x30
    }

    #[inline(always)]
    pub fn tx_dma_ringbase(qid: usize) -> usize {
        0xc00 + DMA_RING_SIZE * qid
    }

    #[inline(always)]
    pub fn tx_dma_read_ptr_lo(qid: usize) -> usize {
        tx_dma_ringbase(qid)
    }

    #[inline(always)]
    pub fn tx_dma_read_ptr_hi(qid: usize) -> usize {
        tx_dma_ringbase(qid) + 0x04
    }

    #[inline(always)]
    pub fn tx_dma_cons_index(qid: usize) -> usize {
        tx_dma_ringbase(qid) + 0x08
    }

    #[inline(always)]
    pub fn tx_dma_prod_index(qid: usize) -> usize {
        tx_dma_ringbase(qid) + 0x0c
    }

    #[inline(always)]
    pub fn tx_dma_ring_buf_size(qid: usize) -> usize {
        tx_dma_ringbase(qid) + 0x10
    }

    #[inline(always)]
    pub fn tx_dma_start_addr_lo(qid: usize) -> usize {
        tx_dma_ringbase(qid) + 0x14
    }

    #[inline(always)]
    pub fn tx_dma_start_addr_hi(qid: usize) -> usize {
        tx_dma_ringbase(qid) + 0x18
    }

    #[inline(always)]
    pub fn tx_dma_end_addr_lo(qid: usize) -> usize {
        tx_dma_ringbase(qid) + 0x1c
    }

    #[inline(always)]
    pub fn tx_dma_end_addr_hi(qid: usize) -> usize {
        tx_dma_ringbase(qid) + 0x20
    }

    #[inline(always)]
    pub fn tx_dma_mbuf_done_thres(qid: usize) -> usize {
        tx_dma_ringbase(qid) + 0x24
    }

    #[inline(always)]
    pub fn tx_dma_flow_period(qid: usize) -> usize {
        tx_dma_ringbase(qid) + 0x28
    }

    #[inline(always)]
    pub fn tx_dma_write_ptr_lo(qid: usize) -> usize {
        tx_dma_ringbase(qid) + 0x2c
    }

    #[inline(always)]
    pub fn tx_dma_write_ptr_hi(qid: usize) -> usize {
        tx_dma_ringbase(qid) + 0x30
    }

    #[inline(always)]
    pub fn rx_desc_address_lo(idx: usize) -> usize {
        DMA_DESC_SIZE * idx + 0x04
    }

    #[inline(always)]
    pub fn rx_desc_address_hi(idx: usize) -> usize {
        DMA_DESC_SIZE * idx + 0x08
    }

    #[inline(always)]
    pub fn rx_desc_status(idx: usize) -> usize {
        DMA_DESC_SIZE * idx
    }

    mmio_rw!(offset RX_BASE => pub RX_DMA_BASE<u32>);
    mmio_rw!(offset TX_BASE => pub TX_DMA_BASE<u32>);

    mmio_rw!(offset RX_BASE + 0x1040 + 0x00 => pub RX_DMA_RING_CFG<u32>);
    mmio_rw!(offset RX_BASE + 0x1040 + 0x04 => pub RX_DMA_CTRL<u32>);
    mmio_rw!(offset RX_BASE + 0x1040 + 0x0c => pub RX_SCB_BURST_SIZE<u32>);

    mmio_rw!(offset TX_BASE + 0x1040 + 0x00 => pub TX_DMA_RING_CFG<u32>);
    mmio_rw!(offset TX_BASE + 0x1040 + 0x04 => pub TX_DMA_CTRL<u32>);
    mmio_rw!(offset TX_BASE + 0x1040 + 0x0c => pub TX_SCB_BURST_SIZE<u32>);

    pub const UMAC_CMD_LCL_LOOP_EN: u32 = 1 << 15;
    pub const UMAC_CMD_SW_RESET: u32 = 1 << 13;
    pub const UMAC_CMD_PROMISC: u32 = 1 << 4;
    pub const UMAC_CMD_TXEN: u32 = 1;
    pub const UMAC_CMD_RXEN: u32 = 1 << 1;
    pub const UMAC_MIB_RESET_TX: u32 = 1 << 2;
    pub const UMAC_MIB_RESET_RUNT: u32 = 1 << 1;
    pub const UMAC_MIB_RESET_RX: u32 = 1;

    pub const UMAC_CMD_SPEED: u32 = bits(3, 2);
    pub const UMAC_CMD_SPEED_10: u32 = 0;
    pub const UMAC_CMD_SPEED_100: u32 = 1;
    pub const UMAC_CMD_SPEED_1000: u32 = 2;

    mmio_rw!(offset 0x808 => pub UMAC_CMD<u32>);
    mmio_rw!(offset 0x80c => pub UMAC_MAC0<u32>);
    mmio_rw!(offset 0x810 => pub UMAC_MAC1<u32>);
    mmio_w!(offset 0x814 => pub UMAC_MAX_FRAME_LEN<u32>);
    mmio_w!(offset 0xb34 => pub UMAC_TX_FLUSH<u32>);
    mmio_w!(offset 0xd80 => pub UMAC_MIB_CTRL<u32>);
    mmio_w!(offset 0xe50 => pub UMAC_MDF_CTRL<u32>);
    mmio_w!(offset 0xe54 => pub UMAC_MDF_ADDR0<u32>);
    mmio_w!(offset 0xe58 => pub UMAC_MDF_ADDR1<u32>);

    pub const MDIO_START_BUSY: u32 = 1 << 29;
    pub const MDIO_READ: u32 = 1 << 27;
    pub const MDIO_WRITE: u32 = 1 << 26;
    pub const MDIO_PMD: u32 = bits(25, 21);
    pub const MDIO_REG: u32 = bits(20, 16);

    mmio_rw!(offset 0xe14 => pub MDIO_CMD<u32>);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GenetError {
    InvalidMajorVersion,
    InvalidMacAddress,
    DMAPoolAllocation,
    InvalidDMAPoolSize,
    Mii,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PhyMode {
    RGMIIId,
    RGMIIRxId,
    RGMIITxId,
    RGMII,
}

impl PhyMode {
    fn new(phy_mode: &str) -> Self {
        match phy_mode {
            "rgmii-id" => PhyMode::RGMIIId,
            "rgmii-rxid" => PhyMode::RGMIIRxId,
            "rgmii-txid" => PhyMode::RGMIITxId,
            _ => PhyMode::RGMII,
        }
    }
}

pub struct Genet {
    inner: RwLock<GenetInner>,
}

impl NetDevice for Genet {
    fn mac_address(&self) -> [u8; 6] {
        self.inner.read().mac_addr
    }

    fn num_queues(&self) -> usize {
        1
    }

    fn irqs(&self) -> Vec<u16> {
        self.inner.read().irqs.to_vec()
    }

    fn flags(&self) -> NetFlags {
        self.inner.read().flags
    }

    fn capabilities(&self) -> NetCapabilities {
        // 802.1Q VLAN-sized frames are supported
        NetCapabilities::VLAN_MTU
    }

    fn device_short_name(&self) -> alloc::borrow::Cow<'static, str> {
        "genet".into()
    }

    fn up(&self) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();

        if inner.flags.contains(NetFlags::UP) {
            return Err(NetDevError::AlreadyUp);
        }

        inner.init().or(Err(NetDevError::DeviceError))
    }

    fn down(&self) -> Result<(), NetDevError> {
        // TODO
        Ok(())
    }

    fn can_send(&self) -> bool {
        let inner = self.inner.read();
        inner.flags.contains(NetFlags::RUNNING)
    }

    fn interrupt(&self, _irq: u16) -> Result<(), NetDevError> {
        let inner = self.inner.read();
        inner.intr();
        Ok(())
    }

    fn link_status(&self) -> LinkStatus {
        let inner = self.inner.read();
        inner.mii_data.link_status()
    }

    fn link_speed(&self) -> u64 {
        // TODO
        1000
    }

    fn poll(&self) -> bool {
        false
    }

    fn poll_mode(&self) -> bool {
        false
    }

    fn poll_in_service(&self) -> Result<(), NetDevError> {
        // TODO
        Ok(())
    }

    fn recv(&self, que_id: usize) -> Result<Option<EtherFrameBuf>, NetDevError> {
        // TODO
        Ok(None)
    }

    fn send(&self, data: EtherFrameRef, que_id: usize) -> Result<(), NetDevError> {
        // TODO
        Ok(())
    }

    fn rx_irq_to_que_id(&self, irq: u16) -> Option<usize> {
        // TODO
        Some(DMA_DEFAULT_QUEUE)
    }

    fn add_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        // TODO
        Ok(())
    }

    fn remove_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        // TODO
        Ok(())
    }

    fn tick_msec(&self) -> Option<u64> {
        Some(500)
    }

    fn tick(&self) -> Result<(), NetDevError> {
        // Call every 500ms.
        let mut inner = self.inner.write();
        mii_timer(inner.as_mut());

        let pidx = registers::RX_DMA_BASE
            .read(registers::rx_dma_prod_index(DMA_DEFAULT_QUEUE) + inner.base_addr.as_usize())
            & 0xffff;
        let total = (pidx - inner.rx.as_ref().unwrap().pidx as u32) & 0xffff;

        log::debug!("RX: total = {}", total);

        Ok(())
    }
}

pub struct GenetInner {
    base_addr: VirtAddr,
    mac_addr: [u8; ETHER_ADDR_LEN],
    phy_mode: PhyMode,
    irqs: [u16; 2],
    flags: NetFlags,
    mulitcast_addrs: MulticastAddrs,
    mii_data: MiiData,
    tx: Option<Mutex<Tx>>,
    rx: Option<Rx>,
}

#[derive(Debug)]
struct Tx {
    next: usize,
    queued: usize,
    cidx: usize,
    pidx: usize,
    buf: DMAPool<TxBuffer>,
}

#[derive(Debug)]
struct Rx {
    next: usize,
    cidx: usize,
    pidx: usize,
    buf: DMAPool<RxBuffer>,
}

impl GenetInner {
    fn new(
        base_addr: VirtAddr,
        mac_addr: [u8; ETHER_ADDR_LEN],
        phy_mode: PhyMode,
        irqs: [u16; 2],
        mii_flags: MiiFlags,
    ) -> Result<Self, GenetError> {
        let flags = NetFlags::BROADCAST | NetFlags::MULTICAST | NetFlags::SIMPLEX;

        let mii_data = MiiData::new(mii_flags);

        let mut genet = Self {
            base_addr,
            mac_addr,
            phy_mode,
            irqs,
            flags,
            mulitcast_addrs: MulticastAddrs::new(),
            mii_data,
            tx: None,
            rx: None,
        };

        // Soft reset EMAC core
        genet.reset();

        Ok(genet)
    }

    fn update_link(&mut self) {
        let media_active = self.mii_data.get_media_active();
        let speed = if ifm_subtype(media_active) == IFM_1000_T
            || ifm_subtype(media_active) == IFM_1000_SX
        {
            registers::UMAC_CMD_SPEED_1000
        } else if ifm_subtype(media_active) == IFM_100_TX {
            registers::UMAC_CMD_SPEED_100
        } else {
            registers::UMAC_CMD_SPEED_10
        };

        let mut val = registers::EXT_RGMII_OOB_CTRL.read(self.base_addr.as_usize());
        val &= !registers::EXT_RGMII_OOB_OOB_DISABLE;
        val |= registers::EXT_RGMII_OOB_RGMII_LINK;
        val |= registers::EXT_RGMII_OOB_RGMII_MODE_EN;

        if self.phy_mode == PhyMode::RGMII {
            val |= registers::EXT_RGMII_OOB_ID_MODE_DISABLE;
        } else {
            val &= !registers::EXT_RGMII_OOB_ID_MODE_DISABLE;
        }

        registers::EXT_RGMII_OOB_CTRL.write(val, self.base_addr.as_usize());

        let mut val = registers::UMAC_CMD.read(self.base_addr.as_usize());

        val &= !registers::UMAC_CMD_SPEED;
        val |= shiftin(speed, registers::UMAC_CMD_SPEED);

        registers::UMAC_CMD.write(val, self.base_addr.as_usize());
    }

    fn reset(&mut self) {
        let base_addr = self.base_addr.as_usize();

        self.disable_dma();

        let mut val = registers::SYS_RBUF_FLUSH_CTRL.read(base_addr);
        val |= registers::SYS_RBUF_FLUSH_RESET;
        registers::SYS_RBUF_FLUSH_CTRL.write(val, base_addr);
        awkernel_lib::delay::wait_microsec(10);

        val &= !registers::SYS_RBUF_FLUSH_RESET;
        registers::SYS_RBUF_FLUSH_CTRL.write(val, base_addr);
        awkernel_lib::delay::wait_microsec(10);

        registers::SYS_RBUF_FLUSH_CTRL.write(0, base_addr);
        awkernel_lib::delay::wait_microsec(10);

        registers::UMAC_CMD.write(0, base_addr);
        registers::UMAC_CMD.write(
            registers::UMAC_CMD_LCL_LOOP_EN | registers::UMAC_CMD_SW_RESET,
            base_addr,
        );
        awkernel_lib::delay::wait_microsec(10);

        registers::UMAC_MIB_CTRL.write(
            registers::UMAC_MIB_RESET_RUNT
                | registers::UMAC_MIB_RESET_RX
                | registers::UMAC_MIB_RESET_TX,
            base_addr,
        );
        registers::UMAC_MIB_CTRL.write(0, base_addr);

        registers::UMAC_MAX_FRAME_LEN.write(1536, base_addr);

        let mut val = registers::RBUF_CTRL.read(base_addr);
        val |= registers::RBUF_ALIGN_2B;
        registers::RBUF_CTRL.write(val, base_addr);

        registers::RBUF_TBUF_SIZE_CTRL.write(1, base_addr);
    }

    fn disable_dma(&mut self) {
        let base_addr = self.base_addr.as_usize();

        // Disable receiver.
        let mut val = registers::UMAC_CMD.read(base_addr);
        val &= !registers::UMAC_CMD_RXEN;
        registers::UMAC_CMD.write(val, base_addr);

        // Stop receive DMA.
        let mut val = registers::RX_DMA_CTRL.read(base_addr);
        val &= !registers::RX_DMA_CTRL_EN;
        val &= !registers::rx_dma_ctrl_rbuf_en(DMA_DEFAULT_QUEUE);
        registers::RX_DMA_CTRL.write(val, base_addr);

        // Stop transmit DMA.
        let mut val = registers::TX_DMA_CTRL.read(base_addr);
        val &= !registers::TX_DMA_CTRL_EN;
        val &= !registers::tx_dma_ctrl_rbuf_en(DMA_DEFAULT_QUEUE);
        registers::TX_DMA_CTRL.write(val, base_addr);

        // Flush data in the TX FIFO.
        registers::UMAC_TX_FLUSH.write(1, base_addr);
        awkernel_lib::delay::wait_microsec(10);
        registers::UMAC_TX_FLUSH.write(0, base_addr);

        // Disable transmitter.
        let mut val = registers::UMAC_CMD.read(base_addr);
        val &= !registers::UMAC_CMD_TXEN;
        registers::UMAC_CMD.write(val, base_addr);
    }

    fn init(&mut self) -> Result<(), GenetError> {
        if self.flags.contains(NetFlags::RUNNING) {
            return Ok(());
        }

        if matches!(
            self.phy_mode,
            PhyMode::RGMII | PhyMode::RGMIIId | PhyMode::RGMIIRxId | PhyMode::RGMIITxId
        ) {
            registers::SYS_PORT_CTRL
                .write(registers::SYS_PORT_MODE_EXT_GPHY, self.base_addr.as_usize());
        }

        // Write hardware address
        registers::UMAC_MAC0.write(
            (self.mac_addr[3] as u32)
                | ((self.mac_addr[2] as u32) << 8)
                | ((self.mac_addr[1] as u32) << 16)
                | ((self.mac_addr[0] as u32) << 24),
            self.base_addr.as_usize(),
        );
        registers::UMAC_MAC1.write(
            (self.mac_addr[5] as u32) | ((self.mac_addr[4] as u32) << 8),
            self.base_addr.as_usize(),
        );

        // Setup RX filter
        self.setup_rxfilter();

        // Setup TX/RX rings
        self.init_rings(DMA_DEFAULT_QUEUE)?;

        // Enable transmitter and receiver
        let mut val = registers::UMAC_CMD.read(self.base_addr.as_usize());
        val |= registers::UMAC_CMD_TXEN;
        val |= registers::UMAC_CMD_RXEN;
        registers::UMAC_CMD.write(val, self.base_addr.as_usize());

        // Enable interrupts
        self.enable_intr();

        self.flags |= NetFlags::RUNNING;

        mii::mii_media_change(self).or(Err(GenetError::Mii))?;

        Ok(())
    }

    fn init_rings(&mut self, qid: usize) -> Result<(), GenetError> {
        let base_addr = self.base_addr.as_usize();

        let tx = Tx {
            next: 0,
            queued: 0,
            cidx: 0,
            pidx: 0,
            buf: DMAPool::new(0, registers::TX_DESC_COUNT).ok_or(GenetError::DMAPoolAllocation)?,
        };

        registers::TX_SCB_BURST_SIZE.write(0x08, base_addr);

        registers::TX_DMA_BASE.write(0, registers::tx_dma_read_ptr_lo(qid) + base_addr);
        registers::TX_DMA_BASE.write(0, registers::tx_dma_read_ptr_hi(qid) + base_addr);
        registers::TX_DMA_BASE.write(
            tx.cidx as u32,
            registers::tx_dma_cons_index(qid) + base_addr,
        );
        registers::TX_DMA_BASE.write(
            tx.pidx as u32,
            registers::tx_dma_prod_index(qid) + base_addr,
        );

        registers::TX_DMA_BASE.write(
            shiftin(
                registers::TX_DESC_COUNT as u32,
                registers::TX_DMA_RING_BUF_SIZE_DESC_COUNT,
            ) | shiftin(MCLBYTES, registers::TX_DMA_RING_BUF_SIZE_BUF_LENGTH),
            registers::tx_dma_ring_buf_size(qid) + base_addr,
        );
        registers::TX_DMA_BASE.write(0, registers::tx_dma_start_addr_lo(qid) + base_addr);
        registers::TX_DMA_BASE.write(0, registers::tx_dma_start_addr_hi(qid) + base_addr);
        registers::TX_DMA_BASE.write(
            (registers::TX_DESC_COUNT * registers::DMA_DESC_SIZE / 4 - 1) as u32,
            registers::tx_dma_end_addr_lo(qid) + base_addr,
        );

        registers::TX_DMA_BASE.write(0, registers::tx_dma_end_addr_hi(qid) + base_addr);
        registers::TX_DMA_BASE.write(1, registers::tx_dma_mbuf_done_thres(qid) + base_addr);
        registers::TX_DMA_BASE.write(0, registers::tx_dma_flow_period(qid) + base_addr);
        registers::TX_DMA_BASE.write(0, registers::tx_dma_write_ptr_lo(qid) + base_addr);
        registers::TX_DMA_BASE.write(0, registers::tx_dma_write_ptr_hi(qid) + base_addr);

        registers::TX_DMA_RING_CFG.write(1 << qid, base_addr);

        // Enable transmit DMA
        let mut val = registers::TX_DMA_CTRL.read(base_addr);
        val |= registers::TX_DMA_CTRL_EN;
        val |= registers::tx_dma_ctrl_rbuf_en(qid);
        registers::TX_DMA_CTRL.write(val, base_addr);

        let mut rx = Rx {
            next: 0,
            cidx: 0,
            pidx: 0,
            buf: DMAPool::new(0, registers::RX_DESC_COUNT).ok_or(GenetError::DMAPoolAllocation)?,
        };

        registers::RX_SCB_BURST_SIZE.write(0x08, base_addr);

        registers::RX_DMA_BASE.write(0, registers::rx_dma_write_ptr_lo(qid) + base_addr);
        registers::RX_DMA_BASE.write(0, registers::rx_dma_write_ptr_hi(qid) + base_addr);
        registers::RX_DMA_BASE.write(
            rx.pidx as u32,
            registers::rx_dma_prod_index(qid) + base_addr,
        );
        registers::RX_DMA_BASE.write(
            rx.cidx as u32,
            registers::rx_dma_cons_index(qid) + base_addr,
        );

        registers::RX_DMA_BASE.write(
            shiftin(
                registers::RX_DESC_COUNT as u32,
                registers::RX_DMA_RING_BUF_SIZE_DESC_COUNT,
            ) | shiftin(MCLBYTES, registers::RX_DMA_RING_BUF_SIZE_BUF_LENGTH),
            registers::rx_dma_ring_buf_size(qid) + base_addr,
        );

        registers::RX_DMA_BASE.write(0, registers::rx_dma_start_addr_lo(qid) + base_addr);
        registers::RX_DMA_BASE.write(0, registers::rx_dma_start_addr_hi(qid) + base_addr);

        registers::RX_DMA_BASE.write(
            (registers::RX_DESC_COUNT * registers::DMA_DESC_SIZE / 4 - 1) as u32,
            registers::rx_dma_end_addr_lo(qid) + base_addr,
        );
        registers::RX_DMA_BASE.write(0, registers::rx_dma_end_addr_hi(qid) + base_addr);

        registers::RX_DMA_BASE.write(
            shiftin(5, registers::RX_DMA_XON_XOFF_THRES_LO)
                | shiftin(
                    (registers::RX_DESC_COUNT >> 4) as u32,
                    registers::RX_DMA_XON_XOFF_THRES_HI,
                ),
            registers::rx_dma_xon_xoff_thres(qid) + base_addr,
        );
        registers::RX_DMA_BASE.write(0, registers::rx_dma_read_ptr_lo(qid) + base_addr);
        registers::RX_DMA_BASE.write(0, registers::rx_dma_read_ptr_hi(qid) + base_addr);

        registers::RX_DMA_RING_CFG.write(1 << qid, base_addr);

        self.fill_rx_ring(qid, &mut rx)?;

        let mut val = registers::RX_DMA_CTRL.read(base_addr);
        val |= registers::RX_DMA_CTRL_EN;
        val |= registers::rx_dma_ctrl_rbuf_en(qid);
        registers::RX_DMA_CTRL.write(val, base_addr);

        self.rx = Some(rx);

        Ok(())
    }

    fn fill_rx_ring(&mut self, qid: usize, rx: &mut Rx) -> Result<(), GenetError> {
        // TODO: fix me
        for i in 0..registers::RX_DESC_COUNT {
            let buf = rx.buf.as_ref();
            let buf = buf.get(i).ok_or(GenetError::InvalidDMAPoolSize)?;
            let addr = buf.as_ptr() as usize;

            self.setup_rxdesc(i, PhyAddr::new(addr));
        }

        Ok(())
    }

    fn setup_rxdesc(&mut self, index: usize, addr: PhyAddr) {
        let base_addr = self.base_addr.as_usize();
        registers::RX_DMA_BASE.write(
            addr.as_usize() as u32,
            registers::rx_desc_address_lo(index) + base_addr,
        );
        registers::RX_DMA_BASE.write(
            (addr.as_usize() >> 32) as u32,
            registers::rx_desc_address_hi(index) + base_addr,
        );
    }

    fn setup_rxfilter_mdf(&self, n: usize, ea: [u8; ETHER_ADDR_LEN]) {
        let addr0 = ((ea[0] as u32) << 8) | (ea[1] as u32);
        let addr1 = ((ea[2] as u32) << 24)
            | ((ea[3] as u32) << 16)
            | ((ea[4] as u32) << 8)
            | (ea[5] as u32);

        let base_addr = self.base_addr.as_usize() + n * 8;
        registers::UMAC_MDF_ADDR0.write(addr0, base_addr);
        registers::UMAC_MDF_ADDR1.write(addr1, base_addr);
    }

    fn setup_rxfilter(&mut self) {
        let base_addr = self.base_addr.as_usize();

        let mut cmd = registers::UMAC_CMD.read(base_addr);

        // Count the required number of hardware filters. We need one
        // for each multicast address, plus one for our own address and
        // the broadcast address.
        let n = self.mulitcast_addrs.len() + 2;

        if n > MAX_MDF_FILTER {
            self.flags |= NetFlags::ALLMULTI;
        } else {
            self.flags &= !NetFlags::ALLMULTI;
        }

        let mdf_ctrl;

        if self
            .flags
            .intersects(NetFlags::PROMISC | NetFlags::ALLMULTI)
        {
            cmd |= registers::UMAC_CMD_PROMISC;
            mdf_ctrl = 0;
        } else {
            cmd &= !registers::UMAC_CMD_PROMISC;

            self.setup_rxfilter_mdf(0, [0xff, 0xff, 0xff, 0xff, 0xff, 0xff]);
            self.setup_rxfilter_mdf(1, self.mac_addr);

            for (n, addr) in self.mulitcast_addrs.iter().enumerate() {
                self.setup_rxfilter_mdf(n + 2, *addr);
            }

            mdf_ctrl = bits(MAX_MDF_FILTER as u32 - 1, MAX_MDF_FILTER as u32 - n as u32);
        }

        registers::UMAC_CMD.write(cmd, base_addr);
        registers::UMAC_MDF_CTRL.write(mdf_ctrl, base_addr);
    }

    fn enable_intr(&mut self) {
        registers::INTRL2_CPU_CLEAR_MASK.write(
            registers::IRQ_TXDMA_DONE | registers::IRQ_RXDMA_DONE,
            self.base_addr.as_usize(),
        );
    }

    fn send(&self, ether_frames: &[EtherFrameRef]) -> Result<(), GenetError> {
        let Some(tx) = self.tx.as_ref() else {
            return Ok(());
        };

        let mut node = MCSNode::new();
        let mut tx = tx.lock(&mut node);

        let base_addr = self.base_addr.as_usize();

        // 801         index = sc->sc_tx.pidx & (TX_DESC_COUNT - 1);
        // 802         cnt = 0;

        let mut index = tx.pidx & (registers::TX_DESC_COUNT - 1);
        let mut cnt = 0;

        for frame in ether_frames.iter() {
            // 803
            // 804         for (;;) {
            // 805                 m = ifq_deq_begin(&ifp->if_snd);
            // 806                 if (m == NULL)
            // 807                         break;
            // 808
            // 809                 nsegs = genet_setup_txbuf(sc, index, m);
            // 810                 if (nsegs == -1) {
            // 811                         ifq_deq_rollback(&ifp->if_snd, m);
            // 812                         ifq_set_oactive(&ifp->if_snd);
            // 813                         break;
            // 814                 }
            // 815                 if (nsegs == 0) {
            // 816                         ifq_deq_commit(&ifp->if_snd, m);
            // 817                         m_freem(m);
            // 818                         ifp->if_oerrors++;
            // 819                         continue;
            // 820                 }
            // 821                 ifq_deq_commit(&ifp->if_snd, m);
            // 822                 if (ifp->if_bpf)
            // 823                         bpf_mtap(ifp->if_bpf, m, BPF_DIRECTION_OUT);
            // 824
            // 825                 index = TX_SKIP(index, nsegs);
            // 826
            // 827                 sc->sc_tx.pidx = (sc->sc_tx.pidx + nsegs) & 0xffff;
            // 828                 cnt++;
            // 829         }

            index = (index + 1) & (registers::TX_DESC_COUNT - 1);

            tx.pidx = (tx.pidx + 1) & 0xffff;
            cnt += 1;
        }

        // 830
        // 831         if (cnt != 0) {
        // 832                 WR4(sc, GENET_TX_DMA_PROD_INDEX(qid), sc->sc_tx.pidx);
        // 833                 ifp->if_timer = 5;
        // 834         }

        Ok(())
    }

    fn rxintr(&self, qid: usize) {
        // TODO
    }

    fn txintr(&self, qid: usize) {
        let Some(tx) = self.tx.as_ref() else {
            return;
        };

        let mut node = MCSNode::new();
        let mut tx = tx.lock(&mut node);

        let base_addr = self.base_addr.as_usize();

        let cidx =
            registers::TX_DMA_BASE.read(registers::tx_dma_cons_index(qid) + base_addr) & 0xffff;
        let total = (cidx - tx.cidx as u32) & 0xffff;

        tx.queued -= total as usize;
    }

    fn intr(&self) {
        let mut val = registers::INTRL2_CPU_STAT.read(self.base_addr.as_usize());
        val &= !registers::INTRL2_CPU_STAT_MASK.read(self.base_addr.as_usize());
        registers::INTRL2_CPU_CLEAR.write(val, self.base_addr.as_usize());

        if val & registers::IRQ_RXDMA_DONE != 0 {
            self.rxintr(DMA_DEFAULT_QUEUE);
        }

        if val & registers::IRQ_TXDMA_DONE != 0 {
            self.txintr(DMA_DEFAULT_QUEUE);
        }
    }
}

impl Mii for GenetInner {
    fn read_reg(&mut self, phy: u32, reg: u32) -> Result<u32, MiiError> {
        let base_addr = self.base_addr.as_usize();

        registers::MDIO_CMD.write(
            registers::MDIO_READ
                | registers::MDIO_START_BUSY
                | shiftin(phy, registers::MDIO_PMD)
                | shiftin(reg, registers::MDIO_REG),
            base_addr,
        );

        for _ in 0..MII_BUSY_RETRY {
            if registers::MDIO_CMD.read(base_addr) & registers::MDIO_START_BUSY == 0 {
                return Ok(registers::MDIO_CMD.read(base_addr) & 0xffff);
            }
            awkernel_lib::delay::wait_microsec(10);
        }

        Err(MiiError::ReadError)
    }

    fn write_reg(&mut self, phy: u32, reg: u32, val: u32) -> Result<(), MiiError> {
        let base_addr = self.base_addr.as_usize();

        registers::MDIO_CMD.write(
            val | registers::MDIO_WRITE
                | registers::MDIO_START_BUSY
                | shiftin(phy, registers::MDIO_PMD)
                | shiftin(reg, registers::MDIO_REG),
            base_addr,
        );

        for _ in 0..MII_BUSY_RETRY {
            if registers::MDIO_CMD.read(base_addr) & registers::MDIO_START_BUSY == 0 {
                return Ok(());
            }
            awkernel_lib::delay::wait_microsec(10);
        }

        Err(MiiError::WriteError)
    }

    fn stat_change(&mut self) -> Result<(), MiiError> {
        self.update_link();
        Ok(())
    }

    fn get_data(&self) -> &MiiData {
        &self.mii_data
    }

    fn get_data_mut(&mut self) -> &mut MiiData {
        &mut self.mii_data
    }
}

pub fn attach(
    base_addr: VirtAddr,
    irqs: &[u16],
    phy_mode: &str,
    phy_id: Option<u32>,
    mac_addr: &Option<[u8; ETHER_ADDR_LEN]>,
) -> Result<(), GenetError> {
    // Check the major version of the Genet controller.
    let (major_ver, minor_ver) = get_version(base_addr);

    if major_ver != registers::REV_MAJOR_V5 {
        log::error!("GENET: unsupported major version {major_ver}");
        return Err(GenetError::InvalidMajorVersion);
    }

    // Get the MAC address.
    let mac_addr = if let Some(mac_addr) = mac_addr {
        mac_addr.clone()
    } else {
        read_mac_addr(base_addr)
    };

    if mac_addr.iter().all(|&b| b == 0) {
        log::error!("GENET: invalid MAC address");
        return Err(GenetError::InvalidMacAddress);
    }

    log::debug!(
        "GENET: mac_addr = {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
        mac_addr[0],
        mac_addr[1],
        mac_addr[2],
        mac_addr[3],
        mac_addr[4],
        mac_addr[5]
    );

    // Get the PHY mode.
    let phy_mode = PhyMode::new(phy_mode);

    let mii_flags = match phy_mode {
        PhyMode::RGMIIId => MiiFlags::RXID | MiiFlags::TXID,
        PhyMode::RGMIIRxId => MiiFlags::RXID,
        PhyMode::RGMIITxId => MiiFlags::TXID,
        PhyMode::RGMII => MiiFlags::empty(),
    };

    let mut genet = GenetInner::new(base_addr, mac_addr, phy_mode, [irqs[0], irqs[1]], mii_flags)?;

    // 992         /* Attach MII driver */
    // 993         ifmedia_init(&mii->mii_media, 0, genet_media_change, genet_media_status);
    // 994         mii->mii_ifp = ifp;
    // 995         mii->mii_readreg = genet_mii_readreg;
    // 996         mii->mii_writereg = genet_mii_writereg;
    // 997         mii->mii_statchg = genet_mii_statchg;
    // 998         mii_attach(&sc->sc_dev, mii, 0xffffffff, sc->sc_phy_id,
    // 999             MII_OFFSET_ANY, mii_flags);

    mii::attach(
        &mut genet,
        |args| Box::new(Ukphy::new(args)),
        0xffffffff,
        phy_id,
        None,
    )
    .or(Err(GenetError::Mii))?;

    if !genet.mii_data.set_current_media(IFM_ETHER | IFM_AUTO) {
        log::error!("GENET: failed to set active media");
        return Err(GenetError::Mii);
    }

    if let Some(current) = genet.get_data().get_media().get_current() {
        log::debug!("GENET: current phy = {}", current.get_instance());
    }

    // Register interrupt handlers.
    for irq in genet.irqs.iter() {
        match awkernel_lib::interrupt::register_handler(
            *irq,
            "genet".into(),
            Box::new(move |irq| {
                awkernel_lib::net::net_interrupt(irq);
            }),
        ) {
            Ok(()) => awkernel_lib::interrupt::enable_irq(*irq),
            Err(e) => log::error!("GENET: failed to register interrupt handler: {e}"),
        }
    }

    let genet = Genet {
        inner: RwLock::new(genet),
    };

    awkernel_lib::net::add_interface(Arc::new(genet), None);

    Ok(())
}

fn get_version(base_addr: VirtAddr) -> (u8, u8) {
    let sys_rev_ctrl = registers::SYS_REV_CTRL.read(base_addr.as_usize());

    (
        ((sys_rev_ctrl >> 24) & 0b1111) as u8,
        ((sys_rev_ctrl >> 16) & 0b1111) as u8,
    )
}

fn read_mac_addr(base_addr: VirtAddr) -> [u8; 6] {
    let maclo = registers::UMAC_MAC0.read(base_addr.as_usize());
    let machi = registers::UMAC_MAC1.read(base_addr.as_usize());

    [
        ((maclo >> 24) & 0xff) as u8,
        ((maclo >> 16) & 0xff) as u8,
        ((maclo >> 8) & 0xff) as u8,
        (maclo & 0xff) as u8,
        ((machi >> 8) & 0xff) as u8,
        (machi & 0xff) as u8,
    ]
}

#[inline(always)]
const fn bit(n: u32) -> u32 {
    1 << n
}

#[inline(always)]
const fn bits(n: u32, m: u32) -> u32 {
    (bit(n - m + 1) - 1) << m
}

#[inline(always)]
const fn lowest_set_bit(mask: u32) -> u32 {
    ((mask - 1) & mask) ^ mask
}

#[inline(always)]
const fn shiftin(x: u32, mask: u32) -> u32 {
    x * lowest_set_bit(mask)
}

// 41 #define __SHIFTOUT(__x, __mask) (((__x) & (__mask)) / __LOWEST_SET_BIT(__mask))

#[inline(always)]
const fn shiftout(x: u32, mask: u32) -> u32 {
    (x & mask) / lowest_set_bit(mask)
}
