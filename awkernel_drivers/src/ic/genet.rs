use awkernel_async_lib_verified::ringq::RingQ;
use awkernel_lib::{
    addr::{virt_addr::VirtAddr, Addr},
    dma_pool::DMAPool,
    net::{
        ether::{ETHER_ADDR_LEN, ETHER_BROADCAST_ADDR},
        multicast::MulticastAddrs,
        net_device::{
            self, EtherFrameBuf, EtherFrameRef, LinkStatus, NetCapabilities, NetDevError,
            NetDevice, NetFlags,
        },
    },
    paging::PAGESIZE,
    sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock},
};

use alloc::{boxed::Box, sync::Arc, vec::Vec};

use crate::{
    if_media::{ifm_subtype, IFM_1000_SX, IFM_1000_T, IFM_100_TX, IFM_10_T},
    mii::{mii_mediachg, Mii, MiiDev, MiiError, MiiFlags, MiiPhyMode, MII_OFFSET_ANY, MII_PHY_ANY},
};

const DMA_DESC_COUNT: usize = 256;
const DMA_DESC_SIZE: usize = 12;
const DMA_DEFAULT_QUEUE: u32 = 16;

const TX_DESC_COUNT: usize = DMA_DESC_COUNT;
const RX_DESC_COUNT: usize = DMA_DESC_COUNT;

const MII_BUSY_RETRY: u32 = 1000;

const RX_BUF_SIZE: usize = 2048;
const TX_BUF_SIZE: usize = 2048;

const RECV_QUEUE_SIZE: usize = 32;

type RxBufType = [[u8; RX_BUF_SIZE]; RX_DESC_COUNT];
type TxBufType = [[u8; RX_BUF_SIZE]; RX_DESC_COUNT];

mod registers {
    use awkernel_lib::mmio_rw;

    mmio_rw!(offset 0x000 => pub SYS_REV_CTRL<u32>);
    pub const REV_MAJOR: u32 = 0xf000000;
    pub const REV_MAJOR_SHIFT: u32 = 24;
    pub const REV_MAJOR_V5: u32 = 6;
    pub const REV_MINOR: u32 = 0xf0000;
    pub const REV_MINOR_SHIFT: u32 = 16;
    pub const REV_PHY: u32 = 0xffff;

    mmio_rw!(offset 0x004 => pub SYS_PORT_CTRL<u32>);
    pub const SYS_PORT_MODE_EXT_GPHY: u32 = 3;

    mmio_rw!(offset 0x008 => pub SYS_RBUF_FLUSH_CTRL<u32>);
    pub const SYS_RBUF_FLUSH_RESET: u32 = 1 << 1;

    mmio_rw!(offset 0x08c => pub EXT_RGMII_OOB_CTRL<u32>);
    pub const EXT_RGMII_OOB_ID_MODE_DISABLE: u32 = 1 << 16;
    pub const EXT_RGMII_OOB_RGMII_MODE_EN: u32 = 1 << 6;
    pub const EXT_RGMII_OOB_OOB_DISABLE: u32 = 1 << 5;
    pub const EXT_RGMII_OOB_RGMII_LINK: u32 = 1 << 4;

    mmio_rw!(offset 0x200 => pub INTRL2_CPU_STAT<u32>);
    mmio_rw!(offset 0x208 => pub INTRL2_CPU_CLEAR<u32>);
    mmio_rw!(offset 0x20c => pub INTRL2_CPU_STAT_MASK<u32>);

    mmio_rw!(offset 0x210 => pub INTRL2_CPU_SET_MASK<u32>);
    mmio_rw!(offset 0x214 => pub INTRL2_CPU_CLEAR_MASK<u32>);
    pub const _IRQ_MDIO_ERROR: u32 = 1 << 24;
    pub const _IRQ_MDIO_DONE: u32 = 1 << 23;
    pub const IRQ_TXDMA_DONE: u32 = 1 << 16;
    pub const IRQ_RXDMA_DONE: u32 = 1 << 13;

    mmio_rw!(offset 0x300 => pub RBUF_CTRL<u32>);
    pub const RBUF_ALIGN_2B: u32 = 1 << 1;
    pub const RBUF_64B_EN: u32 = 1;

    mmio_rw!(offset 0x314 => pub RBUF_CHECK_CTRL<u32>);
    pub const RBUF_CHECK_CTRL_EN: u32 = 1;

    mmio_rw!(offset 0x3b4 => pub RBUF_TBUF_SIZE_CTRL<u32>);
    mmio_rw!(offset 0x600 => pub TBUF_CTRL<u32>);

    mmio_rw!(offset 0x808 => pub UMAC_CMD<u32>);
    pub const UMAC_CMD_LCL_LOOP_EN: u32 = 1 << 15;
    pub const UMAC_CMD_SW_RESET: u32 = 1 << 13;
    pub const UMAC_CMD_PROMISC: u32 = 1 << 4;

    pub const UMAC_CMD_SPEED: u32 = 3 << 2;
    pub const UMAC_CMD_SPEED_10: u32 = 0 << 2;
    pub const UMAC_CMD_SPEED_100: u32 = 1 << 2;
    pub const UMAC_CMD_SPEED_1000: u32 = 2 << 2;

    pub const UMAC_CMD_RXEN: u32 = 1 << 1;
    pub const UMAC_CMD_TXEN: u32 = 1;

    mmio_rw!(offset 0x80c => pub UMAC_MAC0<u32>);
    mmio_rw!(offset 0x810 => pub UMAC_MAC1<u32>);

    mmio_rw!(offset 0x814 => pub UMAC_MAX_FRAME_LEN<u32>);

    mmio_rw!(offset 0xd80 => pub UMAC_MIB_CTRL<u32>);
    pub const UMAC_MIB_RESET_TX: u32 = 1 << 2;
    pub const UMAC_MIB_RESET_RUNT: u32 = 1 << 1;
    pub const UMAC_MIB_RESET_RX: u32 = 1;

    mmio_rw!(offset 0xe14 => pub MDIO_CMD<u32>);
    pub const MDIO_START_BUSY: u32 = 1 << 29;
    pub const MDIO_READ_FAILED: u32 = 1 << 28;
    pub const MDIO_READ: u32 = 1 << 27;
    pub const MDIO_WRITE: u32 = 1 << 26;
    pub const MDIO_ADDR_SHIFT: u32 = 21;
    pub const MDIO_REG_SHIFT: u32 = 16;
    pub const MDIO_VAL_MASK: u32 = 0xffff;

    mmio_rw!(offset 0xe50 => pub UMAC_MDF_CTRL<u32>);
    mmio_rw!(offset 0xe54 => pub UMAC_MDF_ADDR0<u32>);
    mmio_rw!(offset 0xe58 => pub UMAC_MDF_ADDR1<u32>);
    pub const MAX_MDF_FILTER: usize = 17;

    #[inline(always)]
    pub fn umac_mdf_offset(n: usize) -> usize {
        n * 0x8
    }

    pub const RX_BASE: usize = 0x2000;
    pub const TX_BASE: usize = 0x4000;

    pub const DMA_RING_SIZE: usize = 0x40;

    #[inline(always)]
    pub fn rx_dma_ringbase(qid: usize) -> usize {
        RX_BASE + 0xc00 + DMA_RING_SIZE * qid
    }

    mmio_rw!(offset 0x00 => pub RX_DMA_WRITE_PTR_LO<u32>);
    mmio_rw!(offset 0x04 => pub RX_DMA_WRITE_PTR_HI<u32>);
    mmio_rw!(offset 0x08 => pub RX_DMA_PROD_INDEX<u32>);
    mmio_rw!(offset 0x0c => pub RX_DMA_CONS_INDEX<u32>);
    pub const RX_DMA_PROD_CONS_MASK: u32 = 0xffff;

    mmio_rw!(offset 0x10 => pub RX_DMA_RING_BUF_SIZE<u32>);
    pub const RX_DMA_RING_BUF_SIZE_DESC_SHIFT: u32 = 16;
    pub const RX_DMA_RING_BUF_SIZE_BUF_LEN_MASK: u32 = 0xffff;

    mmio_rw!(offset 0x14 => pub RX_DMA_START_ADDR_LO<u32>);
    mmio_rw!(offset 0x18 => pub RX_DMA_START_ADDR_HI<u32>);
    mmio_rw!(offset 0x1c => pub RX_DMA_END_ADDR_LO<u32>);
    mmio_rw!(offset 0x20 => pub RX_DMA_END_ADDR_HI<u32>);

    mmio_rw!(offset 0x28 => pub RX_DMA_XON_XOFF_THRES<u32>);
    pub const RX_DMA_XON_XOFF_THRES_LO_SHIFT: u32 = 16;

    mmio_rw!(offset 0x2c => pub RX_DMA_READ_PTR_LO<u32>);
    mmio_rw!(offset 0x30 => pub RX_DMA_READ_PTR_HI<u32>);

    #[inline(always)]
    pub fn tx_dma_ringbase(qid: usize) -> usize {
        TX_BASE + 0xc00 + DMA_RING_SIZE * qid
    }

    mmio_rw!(offset 0x00 => pub TX_DMA_READ_PTR_LO<u32>);
    mmio_rw!(offset 0x04 => pub TX_DMA_READ_PTR_HI<u32>);
    mmio_rw!(offset 0x08 => pub TX_DMA_CONS_INDEX<u32>);

    mmio_rw!(offset 0x0c => pub TX_DMA_PROD_INDEX<u32>);
    pub const TX_DMA_PROD_CONS_MASK: u32 = 0xffff;

    mmio_rw!(offset 0x10 => pub TX_DMA_RING_BUF_SIZE<u32>);
    pub const TX_DMA_RING_BUF_SIZE_DESC_SHIFT: u32 = 16;
    pub const TX_DMA_RING_BUF_SIZE_BUF_LEN_MASK: u32 = 0xffff;

    mmio_rw!(offset 0x14 => pub TX_DMA_START_ADDR_LO<u32>);
    mmio_rw!(offset 0x18 => pub TX_DMA_START_ADDR_HI<u32>);
    mmio_rw!(offset 0x1c => pub TX_DMA_END_ADDR_LO<u32>);
    mmio_rw!(offset 0x20 => pub TX_DMA_END_ADDR_HI<u32>);
    mmio_rw!(offset 0x24 => pub TX_DMA_MBUF_DONE_THRES<u32>);
    mmio_rw!(offset 0x28 => pub TX_DMA_FLOW_PERIOD<u32>);
    mmio_rw!(offset 0x2c => pub TX_DMA_WRITE_PTR_LO<u32>);
    mmio_rw!(offset 0x30 => pub TX_DMA_WRITE_PTR_HI<u32>);

    #[inline(always)]
    pub fn dma_desc_offset(i: usize) -> usize {
        i * super::DMA_DESC_SIZE
    }

    mmio_rw!(offset RX_BASE + 0x04 => pub RX_DESC_ADDRESS_LO<u32>);
    mmio_rw!(offset RX_BASE + 0x08 => pub RX_DESC_ADDRESS_HI<u32>);

    mmio_rw!(offset RX_BASE => pub RX_DESC_STATUS<u32>);
    pub const RX_DESC_STATUS_BUFLEN_MASK: u32 = 0xfff0000;
    pub const RX_DESC_STATUS_BUFLEN_SHIFT: u32 = 16;
    pub const _RX_DESC_STATUS_CKSUM_OK: u32 = 1 << 15;
    pub const RX_DESC_STATUS_EOP: u32 = 1 << 14;
    pub const RX_DESC_STATUS_SOP: u32 = 1 << 13;
    pub const RX_DESC_STATUS_RX_ERROR: u32 = 1 << 2;

    mmio_rw!(offset TX_BASE => pub TX_DESC_STATUS<u32>);
    pub const TX_DESC_STATUS_EOP: u32 = 1 << 14;
    pub const TX_DESC_STATUS_SOP: u32 = 1 << 13;
    pub const TX_DESC_STATUS_CRC: u32 = 1 << 6;
    pub const _TX_DESC_STATUS_CKSUM: u32 = 1 << 4;
    pub const TX_DESC_STATUS_BUFLEN_SHIFT: u32 = 16;
    pub const TX_DESC_STATUS_QTAG_MASK: u32 = 0x1f80;

    mmio_rw!(offset TX_BASE + 0x04 => pub TX_DESC_ADDRESS_LO<u32>);
    mmio_rw!(offset TX_BASE + 0x08 => pub TX_DESC_ADDRESS_HI<u32>);

    mmio_rw!(offset RX_BASE + 0x1040  => pub RX_DMA_RING_CFG<u32>);

    mmio_rw!(offset RX_BASE + 0x1040 + 0x04 => pub RX_DMA_CTRL<u32>);
    pub const RX_DMA_CTRL_EN: u32 = 1;

    #[inline(always)]
    pub fn rx_dma_ctrl_rbuf_en(qid: u32) -> u32 {
        1 << (qid + 1)
    }

    mmio_rw!(offset RX_BASE + 0x1040 + 0x0c => pub RX_SCB_BURST_SIZE<u32>);

    mmio_rw!(offset TX_BASE + 0x1040 => pub TX_DMA_RING_CFG<u32>);

    mmio_rw!(offset TX_BASE + 0x1040 + 0x04 => pub TX_DMA_CTRL<u32>);
    pub const TX_DMA_CTRL_EN: u32 = 1;

    #[inline(always)]
    pub fn tx_dma_ctrl_rbuf_en(qid: u32) -> u32 {
        1 << (qid + 1)
    }

    mmio_rw!(offset TX_BASE + 0x1040 + 0x0c => pub TX_SCB_BURST_SIZE<u32>);
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

pub struct Genet {
    inner: RwLock<GenetInner>,
    mii: RwLock<MiiDev>,
}

impl NetDevice for Genet {
    fn add_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();

        inner.multicast_addrs.add_addr(*addr);
        inner.setup_rxfilter();

        Ok(())
    }

    fn can_send(&self) -> bool {
        if self.mii.read().link_status() != LinkStatus::Up {
            return false;
        }

        let inner = self.inner.read();
        inner.if_flags.contains(NetFlags::RUNNING | NetFlags::UP)
    }

    fn capabilities(&self) -> NetCapabilities {
        NetCapabilities::VLAN_MTU
    }

    fn device_short_name(&self) -> alloc::borrow::Cow<'static, str> {
        "genet".into()
    }

    fn down(&self) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();
        inner.stop();
        Ok(())
    }

    fn flags(&self) -> NetFlags {
        let inner = self.inner.read();
        inner.if_flags
    }

    fn link_speed(&self) -> u64 {
        let mii = self.mii.read();
        mii.link_speed()
    }

    fn link_status(&self) -> net_device::LinkStatus {
        let mii = self.mii.read();
        mii.link_status()
    }

    fn mac_address(&self) -> [u8; 6] {
        let inner = self.inner.read();
        inner.mac_addr
    }

    fn recv(&self, _que_id: usize) -> Result<Option<EtherFrameBuf>, NetDevError> {
        let inner = self.inner.read();

        let Some(rx) = inner.rx.as_ref() else {
            return Ok(None);
        };

        {
            let mut node = MCSNode::new();
            let mut rx = rx.lock(&mut node);

            if let Some(frame) = rx.read_queue.pop() {
                return Ok(Some(frame));
            }
        }

        inner.rx_recv().or(Err(NetDevError::DeviceError))?;

        let mut node = MCSNode::new();
        let mut rx = rx.lock(&mut node);

        if let Some(frame) = rx.read_queue.pop() {
            Ok(Some(frame))
        } else {
            Ok(None)
        }
    }

    fn interrupt(&self, _irq: u16) -> Result<(), NetDevError> {
        let inner = self.inner.read();
        inner.intr();
        Ok(())
    }

    fn send(&self, data: EtherFrameRef, _que_id: usize) -> Result<(), NetDevError> {
        let inner = self.inner.read();
        let frames = [data];
        inner.send(&frames);
        Ok(())
    }

    fn up(&self) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();
        let mut mii_dev = self.mii.write();

        inner.if_flags.insert(NetFlags::UP);
        inner.init(&mut mii_dev).or(Err(NetDevError::DeviceError))
    }

    fn remove_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();

        inner.multicast_addrs.remove_addr(addr);
        inner.setup_rxfilter();

        Ok(())
    }

    fn irqs(&self) -> Vec<u16> {
        let inner = self.inner.read();
        inner.irqs.to_vec()
    }

    fn num_queues(&self) -> usize {
        1
    }

    fn poll(&self) -> bool {
        let inner = self.inner.read();

        if !inner.if_flags.contains(NetFlags::RUNNING | NetFlags::UP)
            || self.mii.read().link_status() != LinkStatus::Up
        {
            return false;
        }

        if let Some(rx) = &inner.rx {
            {
                let mut node = MCSNode::new();
                let rx = rx.lock(&mut node);

                if !rx.read_queue.is_empty() {
                    return true;
                }
            }

            if inner.rx_recv().is_err() {
                return false;
            }

            let mut node = MCSNode::new();
            let rx = rx.lock(&mut node);

            if !rx.read_queue.is_empty() {
                return true;
            }
        }

        false
    }

    fn poll_in_service(&self) -> Result<(), NetDevError> {
        Ok(())
    }

    fn poll_mode(&self) -> bool {
        true
    }

    fn rx_irq_to_que_id(&self, _irq: u16) -> Option<usize> {
        Some(DMA_DEFAULT_QUEUE as usize)
    }

    fn tick(&self) -> Result<(), NetDevError> {
        {
            let mut inner = self.inner.write();
            let mut mii = self.mii.write();

            crate::mii::mii_tick(inner.as_mut(), &mut mii).or(Err(NetDevError::DeviceError))?;
        }

        {
            let inner = self.inner.read();
            inner.rx_recv().or(Err(NetDevError::DeviceError))?;
        }

        Ok(())
    }

    fn tick_msec(&self) -> Option<u64> {
        Some(1000)
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

        awkernel_lib::interrupt::enable_irq(*irq);
    }

    let phy_mode = match phy_mode {
        "rgmii-id" => MiiPhyMode::RgmiiId,
        "rgmii-rxid" => MiiPhyMode::RgmiiRxId,
        "rgmii-txid" => MiiPhyMode::RgmiiTxId,
        _ => MiiPhyMode::Rgmii,
    };

    let mii_flags = match phy_mode {
        MiiPhyMode::RgmiiId => MiiFlags::RX_DELAY | MiiFlags::TX_DELAY,
        MiiPhyMode::RgmiiRxId => MiiFlags::RX_DELAY,
        MiiPhyMode::RgmiiTxId => MiiFlags::TX_DELAY,
        MiiPhyMode::Rgmii => MiiFlags::empty(),
        _ => return Err(GenetError::Mii),
    };

    let mut genet = GenetInner {
        base_addr,
        mac_addr: mac_addr.unwrap_or([0; ETHER_ADDR_LEN]),
        phy_mode,
        irqs: [irqs[0], irqs[1]],
        if_flags: NetFlags::BROADCAST | NetFlags::SIMPLEX | NetFlags::MULTICAST,
        multicast_addrs: MulticastAddrs::new(),
        rx: None,
        tx: None,
    };

    let phy_loc = phy_id.unwrap_or(MII_PHY_ANY);

    let mii = crate::mii::attach(&mut genet, 0xffffffff, phy_loc, MII_OFFSET_ANY, mii_flags)
        .or(Err(GenetError::Mii))?;

    let genet = Genet {
        inner: RwLock::new(genet),
        mii: RwLock::new(mii),
    };

    awkernel_lib::net::add_interface(Arc::new(genet), None);

    Ok(())
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

struct Tx {
    cons_idx: u32,
    prod_idx: u32,
    queued: u32,
    buf: DMAPool<TxBufType>,
}

struct Rx {
    cons_idx: u32,
    buf: DMAPool<RxBufType>,
    read_queue: RingQ<EtherFrameBuf>,
}

struct GenetInner {
    base_addr: VirtAddr,
    mac_addr: [u8; ETHER_ADDR_LEN],
    phy_mode: MiiPhyMode,
    irqs: [u16; 2],
    if_flags: NetFlags,
    multicast_addrs: MulticastAddrs,
    rx: Option<Mutex<Rx>>,
    tx: Option<Mutex<Tx>>,
}

impl Mii for GenetInner {
    fn read_reg(&mut self, phy: u32, reg: u32) -> Result<u32, MiiError> {
        let base = self.base_addr.as_usize();

        registers::MDIO_CMD.write(
            registers::MDIO_READ
                | (phy << registers::MDIO_ADDR_SHIFT)
                | (reg << registers::MDIO_REG_SHIFT),
            base,
        );

        let val = registers::MDIO_CMD.read(base);
        registers::MDIO_CMD.write(val | registers::MDIO_START_BUSY, base);

        for _ in 0..MII_BUSY_RETRY {
            let val = registers::MDIO_CMD.read(base);
            if (val & registers::MDIO_START_BUSY) == 0 {
                if val & registers::MDIO_READ_FAILED != 0 {
                    return Err(MiiError::Read);
                }
                return Ok(val & registers::MDIO_VAL_MASK);
            }
            awkernel_lib::delay::wait_microsec(10);
        }

        Err(MiiError::Read)
    }

    fn write_reg(&mut self, phy: u32, reg: u32, data: u32) -> Result<(), MiiError> {
        let base = self.base_addr.as_usize();

        registers::MDIO_CMD.write(
            registers::MDIO_WRITE
                | (phy << registers::MDIO_ADDR_SHIFT)
                | (reg << registers::MDIO_REG_SHIFT)
                | (data & registers::MDIO_VAL_MASK),
            base,
        );

        let val = registers::MDIO_CMD.read(base);
        registers::MDIO_CMD.write(val | registers::MDIO_START_BUSY, base);

        for _ in 0..MII_BUSY_RETRY {
            let val = registers::MDIO_CMD.read(base);
            if (val & registers::MDIO_START_BUSY) == 0 {
                return Ok(());
            }
            awkernel_lib::delay::wait_microsec(10);
        }

        Err(MiiError::Write)
    }

    fn on_state_change(&mut self, mii_data: &crate::mii::MiiData) {
        let media_status = mii_data.get_media_status();
        let media_active = mii_data.get_media_active();

        let speed =
            if media_status.contains(crate::if_media::IFM_ACTIVE | crate::if_media::IFM_AVALID) {
                match ifm_subtype(&media_active) {
                    IFM_1000_T | IFM_1000_SX => registers::UMAC_CMD_SPEED_1000,
                    IFM_100_TX => registers::UMAC_CMD_SPEED_100,
                    IFM_10_T => registers::UMAC_CMD_SPEED_10,
                    _ => {
                        return;
                    }
                }
            } else {
                return;
            };

        let base = self.base_addr.as_usize();

        let mut val = registers::EXT_RGMII_OOB_CTRL.read(base);
        val &= !registers::EXT_RGMII_OOB_OOB_DISABLE;
        val |= registers::EXT_RGMII_OOB_RGMII_LINK;
        val |= registers::EXT_RGMII_OOB_RGMII_MODE_EN;

        if self.phy_mode == MiiPhyMode::Rgmii {
            val &= !registers::EXT_RGMII_OOB_ID_MODE_DISABLE;
        } else {
            val |= registers::EXT_RGMII_OOB_ID_MODE_DISABLE;
        }

        registers::EXT_RGMII_OOB_CTRL.write(val, base);

        let mut val = registers::UMAC_CMD.read(base);
        val &= !registers::UMAC_CMD_SPEED;
        val |= speed;

        registers::UMAC_CMD.write(val, base);
    }
}

impl GenetInner {
    fn init(&mut self, mii_dev: &mut MiiDev) -> Result<(), GenetError> {
        if self.if_flags.contains(NetFlags::RUNNING) {
            return Ok(());
        }

        let base = self.base_addr.as_usize();

        match self.phy_mode {
            MiiPhyMode::Rgmii
            | MiiPhyMode::RgmiiId
            | MiiPhyMode::RgmiiRxId
            | MiiPhyMode::RgmiiTxId => {
                registers::SYS_PORT_CTRL.write(registers::SYS_PORT_MODE_EXT_GPHY, base);
            }
            _ => {
                registers::SYS_PORT_CTRL.write(0, base);
            }
        }

        self.set_enaddr();

        // Setup RX filter
        self.setup_rxfilter();

        self.init_txring()?;
        self.init_rxring()?;

        self.enable();
        self.enable_offlad();

        mii_mediachg(self, mii_dev).or(Err(GenetError::Mii))?;

        self.if_flags.insert(NetFlags::RUNNING);

        Ok(())
    }

    fn enable_offlad(&mut self) {
        // TODO: Currently offloading is disabled

        let base = self.base_addr.as_usize();

        let mut check_ctrl = registers::RBUF_CHECK_CTRL.read(base);
        let mut buf_ctrl = registers::RBUF_CTRL.read(base);

        check_ctrl &= !registers::RBUF_CHECK_CTRL_EN;
        buf_ctrl &= !registers::RBUF_64B_EN;

        registers::RBUF_CHECK_CTRL.write(check_ctrl, base);
        registers::RBUF_CTRL.write(buf_ctrl, base);

        let mut buf_ctrl = registers::TBUF_CTRL.read(base);

        buf_ctrl &= !registers::RBUF_64B_EN;

        registers::TBUF_CTRL.write(buf_ctrl, base);
    }

    fn send(&self, ether_frames: &[EtherFrameRef]) {
        if !self.if_flags.contains(NetFlags::RUNNING | NetFlags::UP) {
            return;
        }

        let Some(tx) = &self.tx else {
            return;
        };

        let base = self.base_addr.as_usize();

        let cons_idx = registers::TX_DMA_CONS_INDEX
            .read(base + registers::tx_dma_ringbase(DMA_DEFAULT_QUEUE as usize))
            & registers::TX_DMA_PROD_CONS_MASK;

        let mut node = MCSNode::new();
        let mut tx = tx.lock(&mut node);

        let total = (cons_idx - tx.cons_idx) & registers::TX_DMA_PROD_CONS_MASK;
        tx.queued -= total;
        tx.cons_idx = cons_idx;

        let mut index = tx.prod_idx as usize & (TX_DESC_COUNT - 1);

        let mut cnt = 0;
        for frame in ether_frames.iter() {
            if tx.queued >= TX_DESC_COUNT as u32 {
                break;
            }

            let size = frame.data.len();

            let mut length_status = registers::TX_DESC_STATUS_QTAG_MASK
                | registers::TX_DESC_STATUS_SOP
                | registers::TX_DESC_STATUS_EOP
                | registers::TX_DESC_STATUS_CRC;

            length_status |= (size as u32) << registers::TX_DESC_STATUS_BUFLEN_SHIFT;

            let buf = tx.buf.as_mut().get_mut(index).unwrap();
            unsafe { core::ptr::copy_nonoverlapping(frame.data.as_ptr(), buf.as_mut_ptr(), size) };

            let addr = tx.buf.get_phy_addr() + index * TX_BUF_SIZE;
            let addr = addr.as_usize();

            registers::TX_DESC_ADDRESS_LO
                .write(addr as u32, base + registers::dma_desc_offset(index));
            registers::TX_DESC_ADDRESS_HI.write(
                (addr >> 32) as u32,
                base + registers::dma_desc_offset(index),
            );
            registers::TX_DESC_STATUS
                .write(length_status, base + registers::dma_desc_offset(index));

            tx.queued += 1;
            index = (index + 1) & (TX_DESC_COUNT - 1);
            cnt += 1;
        }

        tx.prod_idx += cnt as u32;
        tx.prod_idx &= registers::TX_DMA_PROD_CONS_MASK;

        if cnt > 0 {
            registers::TX_DMA_PROD_INDEX.write(
                tx.prod_idx,
                base + registers::tx_dma_ringbase(DMA_DEFAULT_QUEUE as usize),
            );
        }
    }

    fn intr(&self) {
        let base = self.base_addr.as_usize();

        let mut val = registers::INTRL2_CPU_STAT.read(base);
        val &= !registers::INTRL2_CPU_STAT_MASK.read(base);
        registers::INTRL2_CPU_CLEAR.write(val, base);

        if val & registers::IRQ_RXDMA_DONE != 0 {
            let _ = self.rx_recv();
        }

        if val & registers::IRQ_TXDMA_DONE != 0 {
            self.txintr();
        }
    }

    fn txintr(&self) {
        let Some(tx) = &self.tx else {
            return;
        };

        let base = self.base_addr.as_usize();

        let cons_idx = registers::TX_DMA_CONS_INDEX
            .read(base + registers::tx_dma_ringbase(DMA_DEFAULT_QUEUE as usize))
            & registers::TX_DMA_PROD_CONS_MASK;

        let mut node = MCSNode::new();
        let mut tx = tx.lock(&mut node);

        let total = (cons_idx - tx.cons_idx) & registers::TX_DMA_PROD_CONS_MASK;

        tx.queued -= total;
        tx.cons_idx = cons_idx;
    }

    fn enable(&mut self) {
        let base = self.base_addr.as_usize();

        registers::UMAC_MAX_FRAME_LEN.write(1536, base);

        let mut val = registers::RBUF_CTRL.read(base);
        val |= registers::RBUF_ALIGN_2B;
        registers::RBUF_CTRL.write(val, base);

        registers::RBUF_TBUF_SIZE_CTRL.write(1, base);

        // Enable transmitter and receiver
        let mut val = registers::UMAC_CMD.read(base);
        val |= registers::UMAC_CMD_TXEN;
        val |= registers::UMAC_CMD_RXEN;
        registers::UMAC_CMD.write(val, base);

        // Enable interrupts
        self.enable_intr();
    }

    fn enable_intr(&mut self) {
        let base = self.base_addr.as_usize();
        registers::INTRL2_CPU_CLEAR_MASK
            .write(registers::IRQ_TXDMA_DONE | registers::IRQ_RXDMA_DONE, base);
        registers::INTRL2_CPU_CLEAR.write(!0, base);
    }

    fn set_enaddr(&mut self) {
        let base = self.base_addr.as_usize();

        let val = (self.mac_addr[3] as u32)
            | ((self.mac_addr[2] as u32) << 8)
            | ((self.mac_addr[1] as u32) << 16)
            | ((self.mac_addr[0] as u32) << 24);
        registers::UMAC_MAC0.write(val, base);

        let val = (self.mac_addr[5] as u32) | ((self.mac_addr[4] as u32) << 8);
        registers::UMAC_MAC1.write(val, base);
    }

    fn setup_rxfilter(&mut self) {
        let base = self.base_addr.as_usize();

        let mut cmd = registers::UMAC_CMD.read(base);

        // Count the required number of hardware filters. We need one
        // for each multicast address, plus one for our own address and
        // the broadcast address.
        let n = self.multicast_addrs.len() + 2;

        if n > registers::MAX_MDF_FILTER {
            self.if_flags.insert(NetFlags::ALLMULTI);
        } else {
            self.if_flags.remove(NetFlags::ALLMULTI);
        }

        let mdf_ctrl = if self
            .if_flags
            .intersects(NetFlags::PROMISC | NetFlags::ALLMULTI)
        {
            cmd |= registers::UMAC_CMD_PROMISC;
            0
        } else {
            cmd &= !registers::UMAC_CMD_PROMISC;

            self.setup_rxfilter_mdf(&ETHER_BROADCAST_ADDR, 0);
            self.setup_rxfilter_mdf(&self.mac_addr, 1);
            for (i, ea) in self.multicast_addrs.iter().enumerate() {
                self.setup_rxfilter_mdf(ea, i + 2);
            }

            ((1 << registers::MAX_MDF_FILTER) - 1) & !((1 << (registers::MAX_MDF_FILTER - n)) - 1)
        };

        registers::UMAC_CMD.write(cmd, base);
        registers::UMAC_MDF_CTRL.write(mdf_ctrl, base);
    }

    fn setup_rxfilter_mdf(&self, ea: &[u8; ETHER_ADDR_LEN], n: usize) {
        let base = self.base_addr.as_usize();

        let addr0 = (ea[0] as u32) << 8 | ea[1] as u32;
        let addr1 =
            (ea[2] as u32) << 24 | (ea[3] as u32) << 16 | (ea[4] as u32) << 8 | ea[5] as u32;
        registers::UMAC_MDF_ADDR0.write(addr0, base + registers::umac_mdf_offset(n));
        registers::UMAC_MDF_ADDR1.write(addr1, base + registers::umac_mdf_offset(n));
    }

    fn init_txring(&mut self) -> Result<(), GenetError> {
        let base = self.base_addr.as_usize();
        let qid = DMA_DEFAULT_QUEUE as usize;

        let buf = DMAPool::new(0, core::mem::size_of::<TxBufType>() / PAGESIZE)
            .ok_or(GenetError::DMAPoolAllocation)?;

        let tx = Tx {
            cons_idx: 0,
            prod_idx: 0,
            queued: 0,
            buf,
        };

        registers::TX_SCB_BURST_SIZE.write(0x08, base);

        registers::TX_DMA_READ_PTR_LO.write(0, base + registers::tx_dma_ringbase(qid));
        registers::TX_DMA_READ_PTR_HI.write(0, base + registers::tx_dma_ringbase(qid));
        registers::TX_DMA_CONS_INDEX.write(0, base + registers::tx_dma_ringbase(qid));
        registers::TX_DMA_PROD_INDEX.write(0, base + registers::tx_dma_ringbase(qid));

        registers::TX_DMA_RING_BUF_SIZE.write(
            (DMA_DESC_COUNT as u32) << registers::TX_DMA_RING_BUF_SIZE_DESC_SHIFT
                | (TX_BUF_SIZE as u32 & registers::TX_DMA_RING_BUF_SIZE_BUF_LEN_MASK),
            base + registers::tx_dma_ringbase(qid),
        );

        registers::TX_DMA_START_ADDR_LO.write(0, base + registers::tx_dma_ringbase(qid));
        registers::TX_DMA_START_ADDR_HI.write(0, base + registers::tx_dma_ringbase(qid));

        registers::TX_DMA_END_ADDR_LO.write(
            TX_DESC_COUNT as u32 * DMA_DESC_SIZE as u32 / 4 - 1,
            base + registers::tx_dma_ringbase(qid),
        );

        registers::TX_DMA_END_ADDR_HI.write(0, base + registers::tx_dma_ringbase(qid));
        registers::TX_DMA_MBUF_DONE_THRES.write(1, base + registers::tx_dma_ringbase(qid));
        registers::TX_DMA_FLOW_PERIOD.write(0, base + registers::tx_dma_ringbase(qid));
        registers::TX_DMA_WRITE_PTR_LO.write(0, base + registers::tx_dma_ringbase(qid));
        registers::TX_DMA_WRITE_PTR_HI.write(0, base + registers::tx_dma_ringbase(qid));

        registers::TX_DMA_RING_CFG.write(1 << qid, base);

        let mut val = registers::TX_DMA_CTRL.read(base);
        val |= registers::TX_DMA_CTRL_EN;
        val |= registers::tx_dma_ctrl_rbuf_en(qid as u32);
        registers::TX_DMA_CTRL.write(val, base);

        self.tx = Some(Mutex::new(tx));

        Ok(())
    }

    fn init_rxring(&mut self) -> Result<(), GenetError> {
        use registers::{dma_desc_offset, rx_dma_ringbase};

        let base = self.base_addr.as_usize();
        let qid = DMA_DEFAULT_QUEUE as usize;

        let buf = DMAPool::new(0, core::mem::size_of::<RxBufType>() / PAGESIZE)
            .ok_or(GenetError::DMAPoolAllocation)?;

        let rx = Rx {
            cons_idx: 0,
            buf,
            read_queue: RingQ::new(RECV_QUEUE_SIZE),
        };

        registers::RX_SCB_BURST_SIZE.write(0x08, base);

        registers::RX_DMA_WRITE_PTR_LO.write(0, base + rx_dma_ringbase(qid));
        registers::RX_DMA_WRITE_PTR_HI.write(0, base + rx_dma_ringbase(qid));
        registers::RX_DMA_PROD_INDEX.write(0, base + rx_dma_ringbase(qid));
        registers::RX_DMA_CONS_INDEX.write(0, base + rx_dma_ringbase(qid));

        registers::RX_DMA_RING_BUF_SIZE.write(
            (DMA_DESC_COUNT as u32) << registers::RX_DMA_RING_BUF_SIZE_DESC_SHIFT
                | (RX_BUF_SIZE as u32 & registers::RX_DMA_RING_BUF_SIZE_BUF_LEN_MASK),
            base + rx_dma_ringbase(qid),
        );

        registers::RX_DMA_START_ADDR_LO.write(0, base + rx_dma_ringbase(qid));
        registers::RX_DMA_START_ADDR_HI.write(0, base + rx_dma_ringbase(qid));
        registers::RX_DMA_END_ADDR_LO.write(
            RX_DESC_COUNT as u32 * DMA_DESC_SIZE as u32 / 4 - 1,
            base + rx_dma_ringbase(qid),
        );
        registers::RX_DMA_END_ADDR_HI.write(0, base + rx_dma_ringbase(qid));

        registers::RX_DMA_XON_XOFF_THRES.write(
            (5 << registers::RX_DMA_XON_XOFF_THRES_LO_SHIFT) | (RX_DESC_COUNT as u32 >> 4),
            base + rx_dma_ringbase(qid),
        );
        registers::RX_DMA_READ_PTR_LO.write(0, base + rx_dma_ringbase(qid));
        registers::RX_DMA_READ_PTR_HI.write(0, base + rx_dma_ringbase(qid));

        registers::RX_DMA_RING_CFG.write(1 << qid, base);

        let phy_addr = rx.buf.get_phy_addr().as_usize();
        for i in 0..RX_DESC_COUNT {
            let addr = phy_addr + i * RX_BUF_SIZE;
            registers::RX_DESC_ADDRESS_LO.write(addr as u32, base + dma_desc_offset(i));
            registers::RX_DESC_ADDRESS_HI.write((addr >> 32) as u32, base + dma_desc_offset(i));
        }

        // Enable receive DMA
        let mut val = registers::RX_DMA_CTRL.read(base);
        val |= registers::RX_DMA_CTRL_EN;
        val |= registers::rx_dma_ctrl_rbuf_en(qid as u32);
        registers::RX_DMA_CTRL.write(val, base);

        self.rx = Some(Mutex::new(rx));

        Ok(())
    }

    fn rx_recv(&self) -> Result<(), GenetError> {
        let Some(rx) = &self.rx else {
            return Ok(());
        };

        let mut node = MCSNode::new();
        let mut rx = rx.lock(&mut node);

        if rx.read_queue.len() >= RECV_QUEUE_SIZE {
            return Ok(());
        }

        let base = self.base_addr.as_usize();

        let qid = DMA_DEFAULT_QUEUE as usize;

        let prod_idx = registers::RX_DMA_PROD_INDEX.read(base + registers::rx_dma_ringbase(qid))
            & registers::RX_DMA_PROD_CONS_MASK;
        let total = (prod_idx - rx.cons_idx) & registers::RX_DMA_PROD_CONS_MASK;

        let mut index = rx.cons_idx as usize & (RX_DESC_COUNT - 1);
        for _ in 0..total {
            let status = registers::RX_DESC_STATUS.read(base + registers::dma_desc_offset(index));

            let len = (status & registers::RX_DESC_STATUS_BUFLEN_MASK)
                >> registers::RX_DESC_STATUS_BUFLEN_SHIFT;

            if status
                & (registers::RX_DESC_STATUS_SOP
                    | registers::RX_DESC_STATUS_EOP
                    | registers::RX_DESC_STATUS_RX_ERROR)
                != (registers::RX_DESC_STATUS_SOP | registers::RX_DESC_STATUS_EOP)
            {
                // error
            } else if let Some(buf) = rx.buf.as_ref().get(index) {
                let data = buf[2..len as usize].to_vec();

                let frame = EtherFrameBuf { data, vlan: None };
                let _ = rx.read_queue.push(frame);
            }

            rx.cons_idx = (rx.cons_idx + 1) & registers::RX_DMA_PROD_CONS_MASK;
            index = (index + 1) & (RX_DESC_COUNT - 1);
            registers::RX_DMA_CONS_INDEX.write(rx.cons_idx, base + registers::rx_dma_ringbase(qid));
        }

        Ok(())
    }

    fn disable(&mut self) {
        let base = self.base_addr.as_usize();

        // Stop receiver
        let mut val = registers::UMAC_CMD.read(base);
        val &= !registers::UMAC_CMD_RXEN;
        registers::UMAC_CMD.write(val, base);

        // Stop transmitter
        let mut val = registers::UMAC_CMD.read(base);
        val &= !registers::UMAC_CMD_TXEN;
        registers::UMAC_CMD.write(val, base);
    }

    fn disable_intr(&mut self) {
        let base = self.base_addr.as_usize();

        // Disable interrupts
        registers::INTRL2_CPU_SET_MASK.write(0xffffffff, base);
        registers::INTRL2_CPU_CLEAR_MASK.write(0xffffffff, base);
    }

    fn stop(&mut self) {
        reset(self.base_addr);
        self.disable();
        self.disable_intr();
        dma_disable(self.base_addr);

        self.tx = None;
        self.rx = None;

        self.if_flags.remove(NetFlags::RUNNING | NetFlags::UP);
    }
}
