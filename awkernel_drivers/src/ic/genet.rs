//! # genet: Broadcom's Genet Ethernet controller.

use awkernel_lib::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr, Addr},
    dma_pool::DMAPool,
    net::{
        ether::ETHER_ADDR_LEN,
        multicast::MulticastAddrs,
        net_device::{
            EtherFrameBuf, EtherFrameRef, NetCapabilities, NetDevError, NetDevice, NetFlags,
        },
    },
    paging::PAGESIZE,
    sync::rwlock::RwLock,
};

use alloc::vec::Vec;

use crate::mii::{self, Mii, MiiData, MiiFlags};

pub const DMA_DEFAULT_QUEUE: usize = 16;
pub const MAX_MDF_FILTER: usize = 17;

pub const TX_BUF_SIZE: usize = 2048;
pub const RX_BUF_SIZE: usize = 2048;
type RxBuffer = [[u8; RX_BUF_SIZE]; registers::DMA_DESC_COUNT];

pub const MII_BUSY_RETRY: i32 = 1000;

mod registers {
    use awkernel_lib::{mmio_r, mmio_rw, mmio_w};

    use super::bits;

    pub const REV_MAJOR_V5: u8 = 6;
    pub const SYS_RBUF_FLUSH_RESET: u32 = 1 << 1;
    pub const RBUF_ALIGN_2B: u32 = 1 << 1;

    mmio_r!(offset 0x000 => pub SYS_REV_CTRL<u32>);
    mmio_rw!(offset 0x008 => pub SYS_RBUF_FLUSH_CTRL<u32>);
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

    mmio_rw!(offset RX_BASE + 0x0004=> pub RX_DESC_ADDRESS_LO<u32>);
    mmio_rw!(offset RX_BASE + 0x0008=> pub RX_DESC_ADDRESS_HI<u32>);
    mmio_rw!(offset RX_BASE + 0x0c00 + 0x00=> pub RX_DMA_WRITE_PTR_LO<u32>);
    mmio_rw!(offset RX_BASE + 0x0c00 + 0x04=> pub RX_DMA_WRITE_PTR_HI<u32>);
    mmio_rw!(offset RX_BASE + 0x0c00 + 0x08=> pub RX_DMA_PROD_INDEX<u32>);
    mmio_rw!(offset RX_BASE + 0x0c00 + 0x0c=> pub RX_DMA_CONS_INDEX<u32>);
    mmio_rw!(offset RX_BASE + 0x0c00 + 0x10=> pub RX_DMA_RING_BUF_SIZE<u32>);
    mmio_rw!(offset RX_BASE + 0x0c00 + 0x14=> pub RX_DMA_START_ADDR_LO<u32>);
    mmio_rw!(offset RX_BASE + 0x0c00 + 0x18=> pub RX_DMA_START_ADDR_HI<u32>);
    mmio_rw!(offset RX_BASE + 0x0c00 + 0x1c=> pub RX_DMA_END_ADDR_LO<u32>);
    mmio_rw!(offset RX_BASE + 0x0c00 + 0x20=> pub RX_DMA_END_ADDR_HI<u32>);
    mmio_rw!(offset RX_BASE + 0x0c00 + 0x28=> pub RX_DMA_XON_XOFF_THRES<u32>);
    mmio_rw!(offset RX_BASE + 0x0c00 + 0x2c=> pub RX_DMA_READ_PTR_LO<u32>);
    mmio_rw!(offset RX_BASE + 0x0c00 + 0x30=> pub RX_DMA_READ_PTR_HI<u32>);

    mmio_rw!(offset TX_BASE + 0x0c00 + 0x00=> pub TX_DMA_READ_PTR_LO<u32>);
    mmio_rw!(offset TX_BASE + 0x0c00 + 0x04=> pub TX_DMA_READ_PTR_HI<u32>);
    mmio_rw!(offset TX_BASE + 0x0c00 + 0x08=> pub TX_DMA_CONS_INDEX<u32>);
    mmio_rw!(offset TX_BASE + 0x0c00 + 0x0c=> pub TX_DMA_PROD_INDEX<u32>);
    mmio_rw!(offset TX_BASE + 0x0c00 + 0x10=> pub TX_DMA_RING_BUF_SIZE<u32>);
    mmio_rw!(offset TX_BASE + 0x0c00 + 0x14=> pub TX_DMA_START_ADDR_LO<u32>);
    mmio_rw!(offset TX_BASE + 0x0c00 + 0x18=> pub TX_DMA_START_ADDR_HI<u32>);
    mmio_rw!(offset TX_BASE + 0x0c00 + 0x1c=> pub TX_DMA_END_ADDR_LO<u32>);
    mmio_rw!(offset TX_BASE + 0x0c00 + 0x20=> pub TX_DMA_END_ADDR_HI<u32>);
    mmio_rw!(offset TX_BASE + 0x0c00 + 0x24=> pub TX_DMA_MBUF_DONE_THRES<u32>);
    mmio_rw!(offset TX_BASE + 0x0c00 + 0x28=> pub TX_DMA_FLOW_PERIOD<u32>);
    mmio_rw!(offset TX_BASE + 0x0c00 + 0x2c=> pub TX_DMA_WRITE_PTR_LO<u32>);
    mmio_rw!(offset TX_BASE + 0x0c00 + 0x30=> pub TX_DMA_WRITE_PTR_HI<u32>);

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

    mmio_rw!(offset 0x808 => pub UMAC_CMD<u32>);
    mmio_r!(offset 0x80c => pub UMAC_MAC0<u32>);
    mmio_r!(offset 0x810 => pub UMAC_MAC1<u32>);
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
        todo!()
    }

    fn down(&self) -> Result<(), NetDevError> {
        todo!()
    }

    fn can_send(&self) -> bool {
        todo!()
    }

    fn interrupt(&self, irq: u16) -> Result<(), NetDevError> {
        todo!()
    }

    fn link_up(&self) -> bool {
        todo!()
    }

    fn link_speed(&self) -> u64 {
        todo!()
    }

    fn full_duplex(&self) -> bool {
        todo!()
    }

    fn poll(&self) -> bool {
        todo!()
    }

    fn poll_mode(&self) -> bool {
        todo!()
    }

    fn poll_in_service(&self) -> Result<(), NetDevError> {
        todo!()
    }

    fn recv(&self, que_id: usize) -> Result<Option<EtherFrameBuf>, NetDevError> {
        todo!()
    }

    fn send(&self, data: EtherFrameRef, que_id: usize) -> Result<(), NetDevError> {
        todo!()
    }

    fn rx_irq_to_que_id(&self, irq: u16) -> Option<usize> {
        todo!()
    }

    fn add_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        todo!()
    }

    fn remove_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        todo!()
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
}

#[derive(Debug)]
struct Tx {
    next: usize,
    queued: usize,
    cidx: usize,
    pidx: usize,
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
        };

        // Soft reset EMAC core
        genet.reset();

        Ok(genet)
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

    fn init(&mut self) {
        todo!()
    }

    fn init_rings(&mut self, qid: usize) -> Result<(), GenetError> {
        let base_addr = self.base_addr.as_usize();

        let tx = Tx {
            next: 0,
            queued: 0,
            cidx: 0,
            pidx: 0,
        };

        registers::TX_SCB_BURST_SIZE.write(0x08, base_addr);

        let offset = qid * registers::DMA_RING_SIZE + base_addr;

        registers::TX_DMA_READ_PTR_LO.write(0, offset);
        registers::TX_DMA_READ_PTR_HI.write(0, offset);
        registers::TX_DMA_CONS_INDEX.write(tx.cidx as u32, offset);
        registers::TX_DMA_PROD_INDEX.write(tx.pidx as u32, offset);
        registers::TX_DMA_RING_BUF_SIZE.write(
            shiftin(
                registers::TX_DESC_COUNT as u32,
                registers::TX_DMA_RING_BUF_SIZE_DESC_COUNT,
            ) | shiftin(
                TX_BUF_SIZE as u32,
                registers::TX_DMA_RING_BUF_SIZE_BUF_LENGTH,
            ),
            offset,
        );
        registers::TX_DMA_START_ADDR_LO.write(0, offset);
        registers::TX_DMA_START_ADDR_HI.write(0, offset);
        registers::TX_DMA_END_ADDR_LO.write(
            registers::TX_DESC_COUNT as u32 * registers::DMA_DESC_SIZE as u32 / 4 - 1,
            offset,
        );
        registers::TX_DMA_END_ADDR_HI.write(0, offset);
        registers::TX_DMA_MBUF_DONE_THRES.write(1, offset);
        registers::TX_DMA_FLOW_PERIOD.write(0, offset);
        registers::TX_DMA_WRITE_PTR_LO.write(0, offset);
        registers::TX_DMA_WRITE_PTR_HI.write(0, offset);

        registers::TX_DMA_RING_CFG.write(1 << qid, base_addr);

        // Enable transmit DMA
        let mut val = registers::TX_DMA_CTRL.read(base_addr);
        val |= registers::TX_DMA_CTRL_EN;
        val |= registers::tx_dma_ctrl_rbuf_en(qid);
        registers::TX_DMA_CTRL.write(val, base_addr);

        // Rx ring
        let mut rx = Rx {
            next: 0,
            cidx: 0,
            pidx: registers::RX_DESC_COUNT,
            buf: DMAPool::new(0, registers::DMA_DESC_COUNT * RX_BUF_SIZE / PAGESIZE)
                .ok_or(GenetError::DMAPoolAllocation)?,
        };

        registers::RX_SCB_BURST_SIZE.write(0x08, base_addr);

        registers::RX_DMA_WRITE_PTR_LO.write(0, offset);
        registers::RX_DMA_WRITE_PTR_HI.write(0, offset);
        registers::RX_DMA_PROD_INDEX.write(rx.pidx as u32, offset);
        registers::RX_DMA_CONS_INDEX.write(rx.cidx as u32, offset);
        registers::RX_DMA_RING_BUF_SIZE.write(
            shiftin(
                registers::RX_DESC_COUNT as u32,
                registers::RX_DMA_RING_BUF_SIZE_DESC_COUNT,
            ) | shiftin(
                RX_BUF_SIZE as u32,
                registers::RX_DMA_RING_BUF_SIZE_BUF_LENGTH,
            ),
            offset,
        );
        registers::RX_DMA_START_ADDR_LO.write(0, offset);
        registers::RX_DMA_START_ADDR_HI.write(0, offset);
        registers::RX_DMA_END_ADDR_LO.write(
            registers::RX_DESC_COUNT as u32 * registers::DMA_DESC_SIZE as u32 / 4 - 1,
            offset,
        );
        registers::RX_DMA_END_ADDR_HI.write(0, offset);
        registers::RX_DMA_XON_XOFF_THRES.write(
            shiftin(5, registers::RX_DMA_XON_XOFF_THRES_LO)
                | shiftin(
                    registers::RX_DESC_COUNT as u32 >> 4,
                    registers::RX_DMA_XON_XOFF_THRES_HI,
                ),
            offset,
        );
        registers::RX_DMA_READ_PTR_LO.write(0, offset);
        registers::RX_DMA_READ_PTR_HI.write(0, offset);

        registers::RX_DMA_RING_CFG.write(1 << qid, base_addr); // enable

        self.fill_rx_ring(qid, &mut rx)?;

        // Enable receive DMA
        let mut val = registers::RX_DMA_CTRL.read(base_addr);
        val |= registers::RX_DMA_CTRL_EN;
        val |= registers::rx_dma_ctrl_rbuf_en(qid);
        registers::RX_DMA_CTRL.write(val, base_addr);

        Ok(())
    }

    fn fill_rx_ring(&mut self, qid: usize, rx: &mut Rx) -> Result<(), GenetError> {
        let mut cidx = rx.cidx;
        let total = (rx.pidx - cidx) & 0xffff;
        assert!(total <= registers::RX_DESC_COUNT);

        let mut index = rx.cidx & (registers::RX_DESC_COUNT - 1);

        let len = rx.buf.as_ref().len();

        if len < RX_BUF_SIZE * registers::DMA_DESC_COUNT {
            return Err(GenetError::InvalidDMAPoolSize);
        }

        let phy_addr = rx.buf.get_phy_addr();
        for _ in 0..total {
            self.setup_rxdesc(index, phy_addr + index * RX_BUF_SIZE);
            cidx = (cidx + 1) & 0xffff;
            index = (index + 1) & (registers::RX_DESC_COUNT - 1);
        }

        if rx.cidx != cidx {
            rx.cidx = cidx;
            registers::RX_DMA_CONS_INDEX.write(
                rx.cidx as u32,
                qid * registers::DMA_RING_SIZE + self.base_addr.as_usize(),
            );
        }

        Ok(())
    }

    fn setup_rxdesc(&mut self, index: usize, addr: PhyAddr) {
        let base_addr = self.base_addr.as_usize() + index * registers::DMA_DESC_SIZE;
        registers::RX_DESC_ADDRESS_LO.write(addr.as_usize() as u32, base_addr);
        registers::RX_DESC_ADDRESS_HI.write((addr.as_usize() >> 32) as u32, base_addr);
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
}

impl Mii for GenetInner {
    fn read(&mut self, phy: u32, reg: u32) -> Option<u32> {
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
                return Some(registers::MDIO_CMD.read(base_addr) & 0xffff);
            }
            awkernel_lib::delay::wait_microsec(10);
        }

        None
    }

    fn write(&mut self, phy: u32, reg: u32, val: u32) {
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
                return;
            }
            awkernel_lib::delay::wait_microsec(10);
        }
    }

    fn mii_data(&self) -> &MiiData {
        &self.mii_data
    }

    fn mii_data_mut(&mut self) -> &mut MiiData {
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

    log::debug!("GENET: major_ver = {major_ver}, minor_ver = {minor_ver}");

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

    mii::attach(&mut genet, 0xffffffff, phy_id, None).or(Err(GenetError::Mii))?;

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
