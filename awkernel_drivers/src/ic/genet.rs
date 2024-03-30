use awkernel_lib::{
    addr::{virt_addr::VirtAddr, Addr},
    net::{
        ether::ETHER_ADDR_LEN,
        net_device::{
            self, EtherFrameBuf, EtherFrameRef, NetCapabilities, NetDevError, NetDevice, NetFlags,
        },
    },
    sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock},
};

use alloc::{boxed::Box, collections::BTreeMap, sync::Arc, vec::Vec};

use crate::{
    if_media::{ifm_subtype, IFM_1000_SX, IFM_1000_T, IFM_100_TX, IFM_10_T},
    mii::{
        Mii, MiiData, MiiDev, MiiError, MiiFlags, MiiPhy, MiiPhyMode, MII_OFFSET_ANY, MII_PHY_ANY,
    },
};

pub const DMA_DEFAULT_QUEUE: u32 = 16;

pub const MII_BUSY_RETRY: u32 = 1000;

mod registers {
    use awkernel_lib::mmio_rw;

    use super::bits;

    mmio_rw!(offset 0x000 => pub SYS_REV_CTRL<u32>);
    pub const REV_MAJOR: u32 = 0xf000000;
    pub const REV_MAJOR_SHIFT: u32 = 24;
    pub const REV_MAJOR_V5: u32 = 6;
    pub const REV_MINOR: u32 = 0xf0000;
    pub const REV_MINOR_SHIFT: u32 = 16;
    pub const REV_PHY: u32 = 0xffff;

    mmio_rw!(offset 0x008 => pub SYS_RBUF_FLUSH_CTRL<u32>);
    pub const SYS_RBUF_FLUSH_RESET: u32 = 1 << 1;

    mmio_rw!(offset 0x08c => pub EXT_RGMII_OOB_CTRL<u32>);
    pub const EXT_RGMII_OOB_ID_MODE_DISABLE: u32 = 1 << 16;
    pub const EXT_RGMII_OOB_RGMII_MODE_EN: u32 = 1 << 6;
    pub const EXT_RGMII_OOB_OOB_DISABLE: u32 = 1 << 5;
    pub const EXT_RGMII_OOB_RGMII_LINK: u32 = 1 << 4;

    mmio_rw!(offset 0x808 => pub UMAC_CMD<u32>);
    pub const UMAC_CMD_LCL_LOOP_EN: u32 = 1 << 15;
    pub const UMAC_CMD_SW_RESET: u32 = 1 << 13;
    pub const UMAC_CMD_PROMISC: u32 = 1 << 4;

    pub const UMAC_CMD_SPEED: u32 = 3 << 2;
    pub const UMAC_CMD_SPEED_10: u32 = 0 << 2;
    pub const UMAC_CMD_SPEED_100: u32 = 1 << 2;
    pub const UMAC_CMD_SPEED_1000: u32 = 2 << 2;

    mmio_rw!(offset 0xd80 => pub UMAC_MIB_CTRL<u32>);
    pub const UMAC_MIB_RESET_TX: u32 = 1 << 2;
    pub const UMAC_MIB_RESET_RUNT: u32 = 1 << 1;
    pub const UMAC_MIB_RESET_RX: u32 = 1;

    mmio_rw!(offset 0xe14 => pub MDIO_CMD<u32>);
    pub const MDIO_START_BUSY: u32 = 1 << 29;
    pub const MDIO_READ_FAILED: u32 = 1 << 28;
    pub const MDIO_READ: u32 = 1 << 27;
    pub const MDIO_WRITE: u32 = 1 << 26;
    pub const MDIO_PMD: u32 = bits(25, 21);
    pub const MDIO_REG: u32 = bits(20, 16);
    pub const MDIO_ADDR_SHIFT: u32 = 21;
    pub const MDIO_REG_SHIFT: u32 = 16;
    pub const MDIO_VAL_MASK: u32 = 0xffff;

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

pub struct Genet {
    inner: RwLock<GenetInner>,
    mii: RwLock<MiiDev>,
}

impl NetDevice for Genet {
    fn add_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        todo!()
    }

    fn can_send(&self) -> bool {
        false
    }

    fn capabilities(&self) -> NetCapabilities {
        NetCapabilities::empty()
    }

    fn device_short_name(&self) -> alloc::borrow::Cow<'static, str> {
        "genet".into()
    }

    fn down(&self) -> Result<(), NetDevError> {
        todo!()
    }

    fn flags(&self) -> NetFlags {
        NetFlags::empty()
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

    fn recv(&self, que_id: usize) -> Result<Option<EtherFrameBuf>, NetDevError> {
        // TODO
        Ok(None)
    }

    fn interrupt(&self, _irq: u16) -> Result<(), NetDevError> {
        // TODO
        Ok(())
    }

    fn send(&self, data: EtherFrameRef, que_id: usize) -> Result<(), NetDevError> {
        // TODO
        Ok(())
    }

    fn up(&self) -> Result<(), NetDevError> {
        // TODO
        Ok(())
    }

    fn remove_multicast_addr(&self, addr: &[u8; 6]) -> Result<(), NetDevError> {
        todo!()
    }

    fn irqs(&self) -> Vec<u16> {
        let inner = self.inner.read();
        inner.irqs.to_vec()
    }

    fn num_queues(&self) -> usize {
        1
    }

    fn poll(&self) -> bool {
        false
    }

    fn poll_in_service(&self) -> Result<(), NetDevError> {
        // TODO
        Ok(())
    }

    fn poll_mode(&self) -> bool {
        false
    }

    fn rx_irq_to_que_id(&self, _irq: u16) -> Option<usize> {
        Some(DMA_DEFAULT_QUEUE as usize)
    }

    fn tick(&self) -> Result<(), NetDevError> {
        let mut inner = self.inner.write();
        let mut mii = self.mii.write();

        crate::mii::mii_tick(inner.as_mut(), &mut mii).or(Err(NetDevError::DeviceError))?;

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
    };

    let mut genet = GenetInner {
        base_addr,
        mac_addr: mac_addr.unwrap_or([0; ETHER_ADDR_LEN]),
        phy_mode,
        irqs: [irqs[0], irqs[1]],
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

struct GenetInner {
    base_addr: VirtAddr,
    mac_addr: [u8; ETHER_ADDR_LEN],
    phy_mode: MiiPhyMode,
    irqs: [u16; 2],
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
        log::debug!("GENET: on_state_change");

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

const fn bits(m: u32, n: u32) -> u32 {
    (1 << (m + 1) - 1) ^ (1 << n) - 1
}
