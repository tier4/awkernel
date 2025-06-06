//! This is a skelton of a PCIe device driver.

use alloc::{borrow::Cow, boxed::Box, format, sync::Arc, vec::Vec};
use awkernel_lib::{
    interrupt::IRQ,
    net::{
        ether::ETHER_TYPE_VLAN,
        net_device::{self, LinkStatus, NetDevice},
    },
    sync::rwlock::RwLock,
};
use i225::{igc_get_flash_presence_i225, I225Flash, I225NoFlash};
use igc_api::{igc_set_mac_type, igc_setup_init_funcs};
use igc_defines::*;
use igc_hw::{IgcFcMode, IgcHw, IgcMacType, IgcMediaType, IgcOperations};

use crate::pcie::{PCIeDevice, PCIeDeviceErr, PCIeInfo};

mod i225;
mod igc_api;
mod igc_base;
mod igc_defines;
mod igc_hw;
mod igc_mac;
mod igc_nvm;
mod igc_phy;
mod igc_regs;

const AUTONEG_ADV_DEFAULT: u16 = ADVERTISE_10_HALF
    | ADVERTISE_10_FULL
    | ADVERTISE_100_HALF
    | ADVERTISE_100_FULL
    | ADVERTISE_1000_FULL
    | ADVERTISE_2500_FULL;

const AUTO_ALL_MODES: u8 = 0;

const IGC_FC_PAUSE_TIME: u16 = 0x0680;

const IGC_TXPBSIZE: u32 = 20408;
const IGC_DMCTLX_DCFLUSH_DIS: u32 = 0x80000000; // Disable DMA Coalesce Flush

const IGC_MAX_VECTORS: u16 = 8;

const DEVICE_SHORT_NAME: &str = "igc";

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum IgcDriverErr {
    NoBar0,
    ReadFailure,
    MacInit,
    MasterRequestsPending,
    Reset,
    NVM,
    SwfwSync,
    BlkPhyReset,
    Param,
    Phy,
    Config,
}

/// Check if the device is an Intel I225/I226.
pub fn match_device(vendor: u16, id: u16) -> bool {
    igc_hw::IGC_DEVICES.contains(&(vendor, id))
}

/// Attach the device to the system.
/// This function is also called by `crate::pcie::PCIeInfo::attach`
/// to attach the device to the system.
pub fn attach(mut info: PCIeInfo) -> Result<Arc<dyn PCIeDevice + Sync + Send>, PCIeDeviceErr> {
    // Initialize PCIeInfo

    // Map the memory regions of MMIO.
    if let Err(e) = info.map_bar() {
        log::warn!("Failed to map the memory regions of MMIO: {e:?}");
        return Err(PCIeDeviceErr::PageTableFailure);
    }

    // Read capabilities of PCIe.
    info.read_capability();

    let igc = Igc::new(info)?;

    let result = Arc::new(igc);

    // Add the network interface, if needed.
    awkernel_lib::net::add_interface(result.clone(), None);

    Ok(result)
}

pub struct IgcInner {
    ops: Box<dyn IgcOperations + Sync + Send>,
    info: PCIeInfo,
    hw: IgcHw,
    link_active: bool,
    link_speed: Option<IgcSpeed>,
    link_duplex: Option<IgcDuplex>,
    link_status: LinkStatus,
}

pub struct Igc {
    inner: RwLock<IgcInner>,
}

impl Igc {
    fn new(mut info: PCIeInfo) -> Result<Self, PCIeDeviceErr> {
        use PCIeDeviceErr::InitFailure;

        let mut hw = IgcHw::default();
        hw.device_id = info.id;

        igc_set_mac_type(&mut hw).or(Err(InitFailure))?;

        let (_irqs_queues, _irq_events) = igc_allocate_pci_resources(&mut info)?;

        // TODO:
        // - allocate tx/rx queues.

        let ops = igc_setup_init_funcs(&mut info, &mut hw).or(Err(InitFailure))?;

        hw.mac.autoneg = true;
        hw.phy.autoneg_wait_to_complete = false;
        hw.phy.autoneg_advertised = AUTONEG_ADV_DEFAULT;

        // Copper options.
        if hw.phy.media_type == IgcMediaType::Copper {
            hw.phy.mdix = AUTO_ALL_MODES;
        }

        // Set the max frame size.
        hw.mac.max_frame_size = 9234;

        // TODO: Allocate multicast array memory.

        if ops.check_reset_block(&mut info).is_err() {
            log::info!("PHY reset is blocked due to SOL/IDER session");
        }

        // Disable Energy Efficient Ethernet (EEE).
        hw.dev_spec.eee_disable = true;

        if igc_attach_and_hw_control(ops.as_ref(), &mut info, &mut hw).is_err() {
            let _ = igc_release_hw_control(&mut info);
            return Err(InitFailure);
        }

        let inner = RwLock::new(IgcInner::new(ops, info, hw));

        let igc = Self { inner };
        let mac_addr = igc.mac_address();

        log::info!(
            "{}:{}: MAC = {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}",
            igc.device_short_name(),
            igc.device_name(),
            mac_addr[0],
            mac_addr[1],
            mac_addr[2],
            mac_addr[3],
            mac_addr[4],
            mac_addr[5]
        );

        Ok(igc)
    }
}

impl PCIeDevice for Igc {
    fn device_name(&self) -> Cow<'static, str> {
        "Intel I225/I226 2.5 GbE".into()
    }
}

impl NetDevice for Igc {
    fn add_multicast_addr(&self, _addr: &[u8; 6]) -> Result<(), net_device::NetDevError> {
        todo!("add_multicast_addr")
    }

    fn remove_multicast_addr(&self, _addr: &[u8; 6]) -> Result<(), net_device::NetDevError> {
        todo!("remove_multicast_addr");
    }

    fn can_send(&self) -> bool {
        // TODO
        false
    }

    fn capabilities(&self) -> net_device::NetCapabilities {
        // TODO
        net_device::NetCapabilities::empty()
    }

    fn device_short_name(&self) -> Cow<'static, str> {
        DEVICE_SHORT_NAME.into()
    }

    fn down(&self) -> Result<(), net_device::NetDevError> {
        // TODO
        Ok(())
    }

    fn flags(&self) -> net_device::NetFlags {
        // TODO
        net_device::NetFlags::empty()
    }

    fn interrupt(&self, _irq: u16) -> Result<(), net_device::NetDevError> {
        todo!("interrupt");
    }

    fn irqs(&self) -> Vec<u16> {
        // TODO
        Vec::new()
    }

    fn link_speed(&self) -> u64 {
        let inner = self.inner.read();
        inner.link_speed.map_or(0, |s| s as u64)
    }

    fn link_status(&self) -> net_device::LinkStatus {
        let inner = self.inner.read();
        inner.link_status
    }

    fn mac_address(&self) -> [u8; 6] {
        let inner = self.inner.read();
        inner.hw.mac.addr
    }

    fn num_queues(&self) -> usize {
        // TODO
        1
    }

    fn recv(
        &self,
        _que_id: usize,
    ) -> Result<Option<net_device::EtherFrameBuf>, net_device::NetDevError> {
        // TODO
        Ok(None)
    }

    fn send(
        &self,
        _data: net_device::EtherFrameRef,
        _que_id: usize,
    ) -> Result<(), net_device::NetDevError> {
        // TODO
        Ok(())
    }

    fn up(&self) -> Result<(), net_device::NetDevError> {
        // TODO
        Ok(())
    }

    fn rx_irq_to_que_id(&self, _irq: u16) -> Option<usize> {
        // TODO
        None
    }
}

#[inline(always)]
fn write_flush(info: &PCIeInfo) -> Result<(), IgcDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.read32(igc_regs::IGC_STATUS)
        .ok_or(IgcDriverErr::ReadFailure)?;
    Ok(())
}

#[inline(always)]
fn read_reg(info: &PCIeInfo, offset: usize) -> Result<u32, IgcDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.read32(offset).ok_or(IgcDriverErr::ReadFailure)
}

#[inline(always)]
fn write_reg(info: &PCIeInfo, offset: usize, value: u32) -> Result<(), IgcDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.write32(offset, value);
    Ok(())
}

#[inline(always)]
fn read_reg_array(info: &PCIeInfo, offset: usize, index: usize) -> Result<u32, IgcDriverErr> {
    let bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.read32(offset + (index << 2))
        .ok_or(IgcDriverErr::ReadFailure)
}

#[inline(always)]
fn write_reg_array(
    info: &PCIeInfo,
    offset: usize,
    index: usize,
    value: u32,
) -> Result<(), IgcDriverErr> {
    let mut bar0 = info.get_bar(0).ok_or(IgcDriverErr::NoBar0)?;
    bar0.write32(offset + (index << 2), value);
    Ok(())
}

/// Initialize the DMA Coalescing feature
fn igc_init_dmac(
    info: &mut PCIeInfo,
    hw: &IgcHw,
    pba: u32,
    sc_dmac: u32,
) -> Result<(), IgcDriverErr> {
    use igc_regs::*;

    let reg = !IGC_DMACR_DMAC_EN;

    let max_frame_size = hw.mac.max_frame_size;

    if sc_dmac == 0 {
        // Disabling it
        write_reg(info, IGC_DMACR, reg)?;
        return Ok(());
    } else {
        log::info!("igc: DMA Coalescing enabled");
    }

    // Set starting threshold
    write_reg(info, IGC_DMCTXTH, 0)?;

    let hwm = 64 * pba - max_frame_size / 16;
    let hwm = if hwm < 64 * (pba - 6) {
        64 * (pba - 6)
    } else {
        hwm
    };

    let mut reg = read_reg(info, IGC_FCRTC)?;
    reg &= !IGC_FCRTC_RTH_COAL_MASK;
    reg |= (hwm << IGC_FCRTC_RTH_COAL_SHIFT) & IGC_FCRTC_RTH_COAL_MASK;
    write_reg(info, IGC_FCRTC, reg)?;

    let dmac = pba - max_frame_size / 512;
    let dmac = if dmac < pba - 10 { pba - 10 } else { dmac };
    let mut reg = read_reg(info, IGC_DMACR)?;
    reg &= !IGC_DMACR_DMACTHR_MASK;
    reg |= (dmac << IGC_DMACR_DMACTHR_SHIFT) & IGC_DMACR_DMACTHR_MASK;

    // transition to L0x or L1 if available
    reg |= IGC_DMACR_DMAC_EN | IGC_DMACR_DMAC_LX_MASK;

    // Check if status is 2.5Gb backplane connection
    // before configuration of watchdog timer, which is
    // in msec values in 12.8usec intervals
    // watchdog timer= msec values in 32usec intervals
    // for non 2.5Gb connection
    let status = read_reg(info, IGC_STATUS)?;
    if status & IGC_STATUS_2P5_SKU != 0 && status & IGC_STATUS_2P5_SKU_OVER == 0 {
        reg |= (sc_dmac * 5) >> 6;
    } else {
        reg |= sc_dmac >> 5;
    }

    write_reg(info, IGC_DMACR, reg)?;

    write_reg(info, IGC_DMCRTRH, 0)?;

    // Set the interval before transition
    let mut reg = read_reg(info, IGC_DMCTLX)?;
    reg |= IGC_DMCTLX_DCFLUSH_DIS;

    // in 2.5Gb connection, TTLX unit is 0.4 usec
    // which is 0x4*2 = 0xA. But delay is still 4 usec
    let status = read_reg(info, IGC_STATUS)?;
    if status & IGC_STATUS_2P5_SKU != 0 && status & IGC_STATUS_2P5_SKU_OVER == 0 {
        reg |= 0xA;
    } else {
        reg |= 0x4;
    }

    write_reg(info, IGC_DMCTLX, reg)?;

    // free space in tx packet buffer to wake from DMA coal
    write_reg(
        info,
        IGC_DMCTXTH,
        (IGC_TXPBSIZE - (2 * max_frame_size)) >> 6,
    )?;

    // make low power state decision controlled by DMA coal
    let mut reg = read_reg(info, IGC_PCIEMISC)?;
    reg &= !IGC_PCIEMISC_LX_DECISION;
    write_reg(info, IGC_PCIEMISC, reg)?;

    Ok(())
}

fn igc_reset(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
    sc_fc: IgcFcMode,
    sc_dmac: u32,
) -> Result<(), IgcDriverErr> {
    use igc_regs::*;

    // Let the firmware know the OS is in control
    igc_get_hw_control(info)?;

    // Packet Buffer Allocation (PBA)
    // Writing PBA sets the receive portion of the buffer
    // the remainder is used for the transmit buffer.
    let pba = IGC_PBA_34K;

    // These parameters control the automatic generation (Tx) and
    // response (Rx) to Ethernet PAUSE frames.
    // - High water mark should allow for at least two frames to be
    //   received after sending an XOFF.
    // - Low water mark works best when it is very near the high water mark.
    //   This allows the receiver to restart by sending XON when it has
    //   drained a bit. Here we use an arbitrary value of 1500 which will
    //   restart after one full frame is pulled from the buffer. There
    //   could be several smaller frames in the buffer and if so they will
    //   not trigger the XON until their total number reduces the buffer
    //   by 1500.
    // - The pause time is fairly large at 1000 x 512ns = 512 usec.
    let rx_buffer_size = (pba & 0xffff) << 10;
    hw.fc.high_water = rx_buffer_size - roundup2(hw.mac.max_frame_size, 1024);
    // 16-byte granularity
    hw.fc.low_water = hw.fc.high_water - 16;

    // locally set flow control value?
    if sc_fc != IgcFcMode::None {
        hw.fc.requested_mode = sc_fc;
    } else {
        hw.fc.requested_mode = IgcFcMode::Full;
    }

    hw.fc.pause_time = IGC_FC_PAUSE_TIME;

    hw.fc.send_xon = true;

    // Issue a global reset
    ops.reset_hw(info, hw)?;
    write_reg(info, IGC_WUC, 0)?;

    // and a re-init
    ops.init_hw(info, hw)?;

    // Setup DMA Coalescing
    igc_init_dmac(info, hw, pba, sc_dmac)?;

    write_reg(info, IGC_VET, ETHER_TYPE_VLAN as u32)?;
    ops.get_info(info, hw)?;
    ops.check_for_link(info, hw)?;

    Ok(())
}

/// igc_get_hw_control sets the {CTRL_EXT|FWSM}:DRV_LOAD bit.
/// For ASF and Pass Through versions of f/w this means
/// that the driver is loaded. For AMT version type f/w
/// this means that the network i/f is open.
fn igc_get_hw_control(info: &mut PCIeInfo) -> Result<(), IgcDriverErr> {
    let ctrl_ext = read_reg(info, igc_regs::IGC_CTRL_EXT)?;
    write_reg(
        info,
        igc_regs::IGC_CTRL_EXT,
        ctrl_ext | IGC_CTRL_EXT_DRV_LOAD,
    )
}

/// igc_release_hw_control resets {CTRL_EXT|FWSM}:DRV_LOAD bit.
/// For ASF and Pass Through versions of f/w this means that
/// the driver is no longer loaded. For AMT versions of the
/// f/w this means that the network i/f is closed.
fn igc_release_hw_control(info: &mut PCIeInfo) -> Result<(), IgcDriverErr> {
    let ctrl_ext = read_reg(info, igc_regs::IGC_CTRL_EXT)?;
    write_reg(
        info,
        igc_regs::IGC_CTRL_EXT,
        ctrl_ext & !IGC_CTRL_EXT_DRV_LOAD,
    )
}

fn roundup2<T>(size: T, unit: T) -> T
where
    T: Copy
        + core::ops::Add<Output = T>
        + core::ops::BitAnd<Output = T>
        + core::ops::Sub<Output = T>
        + core::ops::Not<Output = T>
        + From<u8>,
{
    let one = T::from(1);
    (size + unit - one) & !(unit - one)
}

impl IgcInner {
    fn new(ops: Box<dyn IgcOperations + Sync + Send>, info: PCIeInfo, hw: IgcHw) -> Self {
        Self {
            ops,
            info,
            hw,
            link_active: false,
            link_speed: None,
            link_duplex: None,
            link_status: LinkStatus::Down,
        }
    }

    fn igc_update_link_status(
        &mut self,
        ops: &dyn IgcOperations,
        info: &mut PCIeInfo,
        hw: &mut IgcHw,
    ) -> Result<(), IgcDriverErr> {
        if hw.mac.get_link_status {
            ops.check_for_link(info, hw)?;
        }

        self.link_status = if read_reg(info, igc_regs::IGC_STATUS)? & IGC_STATUS_LU != 0 {
            if !self.link_active {
                let (speed, duplex) = ops.get_link_up_info(info, hw)?;
                self.link_speed = Some(speed);
                self.link_duplex = Some(duplex);
                self.link_active = true;
            }

            if self.link_duplex == Some(IgcDuplex::Full) {
                LinkStatus::UpFullDuplex
            } else {
                LinkStatus::UpHalfDuplex
            }
        } else {
            if self.link_active {
                self.link_speed = None;
                self.link_duplex = None;
                self.link_active = false;
            }
            LinkStatus::Down
        };

        Ok(())
    }
}

fn igc_attach_and_hw_control(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), PCIeDeviceErr> {
    use PCIeDeviceErr::InitFailure;

    ops.reset_hw(info, hw).or(Err(InitFailure))?;

    // Make sure we have a good EEPROM before we read from it.
    if ops.validate(info, hw).is_err() {
        // Some PCI-E parts fail the first check due to
        // the link being in sleep state, call it again,
        // if it fails a second time its a real issue.
        ops.validate(info, hw).or(Err(InitFailure))?;
    }

    ops.read_mac_addr(info, hw).or(Err(InitFailure))?;

    if !igc_is_valid_ether_addr(&hw.mac.addr) {
        log::error!("igc: Invalid MAC address read from EEPROM");
        return Err(PCIeDeviceErr::InitFailure);
    }

    // TODO: continue initialization

    Ok(())
}

fn igc_is_valid_ether_addr(addr: &[u8; 6]) -> bool {
    // Check if the address is a multicast address or a zero address.
    !(addr[0] & 1 != 0 || addr.iter().all(|&x| x == 0))
}

/// Allocate PCI resources for the IGC device.
/// This function initialize IRQs for the IGC device,
/// and returns IRQs for the Rx/Tx queues and an IRQ for events.
fn igc_allocate_pci_resources(info: &mut PCIeInfo) -> Result<(Vec<IRQ>, IRQ), PCIeDeviceErr> {
    let bfd = info.get_bfd();
    let segment_number = info.segment_group as usize;

    let msix = info.get_msix_mut().ok_or(PCIeDeviceErr::InitFailure)?;

    let nmsix = msix.get_table_size();

    log::debug!("nmsix = {nmsix}");

    if nmsix <= 1 {
        log::error!("igc: not enough msi-x vectors");
        return Err(PCIeDeviceErr::InitFailure);
    }

    let nmsix = nmsix - 1; // Give one vector to events.

    let nqueues = if nmsix > IGC_MAX_VECTORS {
        IGC_MAX_VECTORS
    } else {
        nmsix
    };

    // Initialize the IRQs for the Rx/Tx queues.
    let mut irqs_queues = Vec::with_capacity(nqueues as usize);

    for q in 0..nqueues {
        let irq_name_rxtx = format!("{DEVICE_SHORT_NAME}-{bfd}-RxTx{q}");
        let mut irq_rxtx = msix
            .register_handler(
                irq_name_rxtx.into(),
                Box::new(move |irq| {
                    awkernel_lib::net::net_interrupt(irq);
                }),
                segment_number,
                awkernel_lib::cpu::raw_cpu_id() as u32,
                q as usize,
            )
            .or(Err(PCIeDeviceErr::InitFailure))?;
        irq_rxtx.enable();
        irqs_queues.push(irq_rxtx);
    }

    // Initialize the IRQs for the events.
    let irq_name_other = format!("{DEVICE_SHORT_NAME}-{bfd}-Other");
    let mut irq_other = msix
        .register_handler(
            irq_name_other.into(),
            Box::new(move |irq| {
                awkernel_lib::net::net_interrupt(irq);
            }),
            segment_number,
            awkernel_lib::cpu::raw_cpu_id() as u32,
            irqs_queues.len(),
        )
        .or(Err(PCIeDeviceErr::InitFailure))?;
    irq_other.enable();

    Ok((irqs_queues, irq_other))
}
