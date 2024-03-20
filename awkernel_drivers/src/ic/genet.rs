//! # genet: Broadcom's Genet Ethernet controller.

use awkernel_lib::{
    addr::{virt_addr::VirtAddr, Addr},
    net::ether::ETHER_ADDR_LEN,
};

use crate::mii::MiiFlags;

pub const DMA_DEFAULT_QUEUE: usize = 16;

mod registers {
    use awkernel_lib::{mmio_r, mmio_rw, mmio_w};

    pub const REV_MAJOR_V5: u8 = 6;
    pub const SYS_RBUF_FLUSH_RESET: u32 = 1 << 1;

    mmio_r!(offset 0x000 => pub SYS_REV_CTRL<u32>);
    mmio_r!(offset 0x008 => pub SYS_RBUF_FLUSH_CTRL<u32>);

    pub const GENET_RX_BASE: usize = 0x2000;
    pub const GENET_TX_BASE: usize = 0x4000;

    pub const RX_DMA_CTRL_EN: u32 = 1;
    pub fn rx_dma_ctrl_rbuf_en(qid: usize) -> u32 {
        1 << (qid + 1)
    }

    pub const TX_DMA_CTRL_EN: u32 = 1;
    pub fn tx_dma_ctrl_rbuf_en(qid: usize) -> u32 {
        1 << (qid + 1)
    }

    mmio_rw!(offset GENET_RX_BASE + 0x1040 + 0x04 => pub RX_DMA_CTRL<u32>);
    mmio_rw!(offset GENET_TX_BASE + 0x1040 + 0x04 => pub TX_DMA_CTRL<u32>);

    pub const UMAC_CMD_TXEN: u32 = 1;
    pub const UMAC_CMD_RXEN: u32 = 1 << 1;

    mmio_rw!(offset 0x808 => pub UMAC_CMD<u32>);
    mmio_r!(offset 0x80c => pub UMAC_MAC0<u32>);
    mmio_r!(offset 0x810 => pub UMAC_MAC1<u32>);
    mmio_w!(offset 0xb34 => pub UMAC_TX_FLUSH<u32>);
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GenetError {
    InvalidMajorVersion,
    InvalidMacAddress,
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
    base_addr: VirtAddr,
    mac_addr: [u8; ETHER_ADDR_LEN],
    phy_mode: PhyMode,
    irqs: [u16; 2],
}

impl Genet {
    fn new(
        base_addr: VirtAddr,
        mac_addr: [u8; ETHER_ADDR_LEN],
        phy_mode: PhyMode,
        irqs: [u16; 2],
    ) -> Result<Self, GenetError> {
        let mut genet = Self {
            base_addr,
            mac_addr,
            phy_mode,
            irqs,
        };

        genet.reset()?;

        Ok(genet)
    }

    fn reset(&mut self) -> Result<(), GenetError> {
        self.disable_dma();

        // TODO

        Ok(())
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
}

pub fn attach(
    base_addr: VirtAddr,
    irqs: &[u16],
    phy_mode: &str,
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

    let genet = Genet::new(base_addr, mac_addr, phy_mode, [irqs[0], irqs[1]]);

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
