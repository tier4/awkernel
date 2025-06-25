use crate::pcie::PCIeInfo;

use super::{
    igc_defines::{IGC_SWFW_PHY0_SM, IGC_SWFW_PHY1_SM},
    igc_hw::{IgcHw, IgcOperations, IGC_FUNC_1},
    igc_mac::igc_init_rx_addrs_generic,
    igc_phy::igc_power_down_phy_copper,
    igc_regs::*,
    read_reg, write_reg_array, IgcDriverErr,
};

pub(super) const IGC_RAR_ENTRIES_BASE: u16 = 16;

/// Transmit Descriptor - Advanced
pub(super) union IgcAdvTxDesc {
    pub(super) read: TxDescRead,
    pub(super) wb: TxDescWb,
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub(super) struct TxDescRead {
    pub(super) buffer_addr: u64, // Address of descriptor's data buf
    pub(super) cmd_type_len: u32,
    pub(super) olinfo_status: u32,
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub(super) struct TxDescWb {
    pub(super) rsvd: u64, // Reserved
    pub(super) nxtseq_seed: u32,
    pub(super) status: u32,
}

/// Context descriptors
#[derive(Clone, Copy)]
#[repr(C)]
pub(super) struct IgcAdvTxContextDesc {
    pub(super) vlan_macip_lens: u32,
    pub(super) ts: TxContextTS,
    pub(super) type_tucmd_mlhl: u32,
    pub(super) mss_l4len_idx: u32,
}

#[derive(Clone, Copy)]
pub(super) union TxContextTS {
    pub(super) launch_time: u32, // Launch time
    pub(super) seqnum_seed: u32, // Sequence number seed
}

/// Receive Descriptor - Advanced
#[derive(Clone, Copy)]
#[repr(C)]
pub(super) union IgcAdvRxDesc {
    pub(super) read: RxRead,
    pub(super) wb: RxWb, // writeback
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub(super) struct RxRead {
    pub(super) pkt_addr: u64, // Packet buffer address
    pub(super) hdr_addr: u64, // Header buffer address
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub(super) struct RxHsRss {
    pub(super) pkt_info: u16, // Packet type
    pub(super) hdr_info: u16, // Split Header, header buffer len
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub(super) struct RxCsumIp {
    pub(super) ip_id: u16, // IP id
    pub(super) csum: u16,  // Packet checksum
}

#[derive(Clone, Copy)]
pub(super) union RxLoDword {
    pub(super) data: u32,
    pub(super) hs_rss: RxHsRss,
}

#[derive(Clone, Copy)]
pub(super) union RxHiDword {
    pub(super) rss: u32, // RSS hash
    pub(super) csum_ip: RxCsumIp,
}

#[derive(Clone, Copy)]
#[repr(C)]
pub(super) struct RxLower {
    pub(super) lo_dword: RxLoDword,
    pub(super) hi_dword: RxHiDword,
}

#[derive(Debug, Clone, Copy)]
#[repr(C)]
pub(super) struct RxUpper {
    pub(super) status_error: u32, // ext status/error
    pub(super) length: u16,       // Packet length
    pub(super) vlan: u16,         // VLAN tag
}

#[derive(Clone, Copy)]
#[repr(C)]
pub(super) struct RxWb {
    pub(super) lower: RxLower,
    pub(super) upper: RxUpper,
}

/// Acquire access rights to the correct PHY.
pub(super) fn igc_acquire_phy_base(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    let mask = if hw.bus.func == IGC_FUNC_1 {
        IGC_SWFW_PHY1_SM
    } else {
        IGC_SWFW_PHY0_SM
    };
    ops.acquire_swfw_sync(info, hw, mask)
}

/// A wrapper to release access rights to the correct PHY.
pub(super) fn igc_release_phy_base(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    let mask = if hw.bus.func == IGC_FUNC_1 {
        IGC_SWFW_PHY1_SM
    } else {
        IGC_SWFW_PHY0_SM
    };

    ops.release_swfw_sync(info, hw, mask)
}

/// In the case of a PHY power down to save power, or to turn off link during a
/// driver unload, or wake on lan is not enabled, remove the link.
pub(super) fn igc_power_down_phy_copper_base(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    // If the management interface is not enabled, then power down
    if ops.check_reset_block(info).is_ok() {
        igc_power_down_phy_copper(ops, info, hw)?;
    }

    Ok(())
}

/// This inits the hardware readying it for operation.
pub(super) fn igc_init_hw_base(
    ops: &dyn IgcOperations,
    info: &mut PCIeInfo,
    hw: &mut IgcHw,
) -> Result<(), IgcDriverErr> {
    // Setup the receive address
    igc_init_rx_addrs_generic(ops, info, hw, hw.mac.rar_entry_count)?;

    // Zero out the Multicast HASH table
    for i in 0..hw.mac.mta_reg_count {
        write_reg_array(info, IGC_MTA, i as usize, 0)?;
    }

    // Zero out the Unicast HASH table
    for i in 0..hw.mac.uta_reg_count {
        write_reg_array(info, IGC_UTA, i as usize, 0)?;
    }

    // Setup link and flow control
    ops.setup_link(info, hw)?;

    // Clear all of the statistics registers (clear on read).  It is
    // important that we do this after we have tried to establish link
    // because the symbol error count will increment wildly if there
    // is no link.
    igc_clear_hw_cntrs_base_generic(info)?;

    Ok(())
}

/// Clears the base hardware counters by reading the counter registers.
fn igc_clear_hw_cntrs_base_generic(info: &mut PCIeInfo) -> Result<(), IgcDriverErr> {
    read_reg(info, IGC_CRCERRS)?;
    read_reg(info, IGC_MPC)?;
    read_reg(info, IGC_SCC)?;
    read_reg(info, IGC_ECOL)?;
    read_reg(info, IGC_MCC)?;
    read_reg(info, IGC_LATECOL)?;
    read_reg(info, IGC_COLC)?;
    read_reg(info, IGC_RERC)?;
    read_reg(info, IGC_DC)?;
    read_reg(info, IGC_RLEC)?;
    read_reg(info, IGC_XONRXC)?;
    read_reg(info, IGC_XONTXC)?;
    read_reg(info, IGC_XOFFRXC)?;
    read_reg(info, IGC_XOFFTXC)?;
    read_reg(info, IGC_FCRUC)?;
    read_reg(info, IGC_GPRC)?;
    read_reg(info, IGC_BPRC)?;
    read_reg(info, IGC_MPRC)?;
    read_reg(info, IGC_GPTC)?;
    read_reg(info, IGC_GORCL)?;
    read_reg(info, IGC_GORCH)?;
    read_reg(info, IGC_GOTCL)?;
    read_reg(info, IGC_GOTCH)?;
    read_reg(info, IGC_RNBC)?;
    read_reg(info, IGC_RUC)?;
    read_reg(info, IGC_RFC)?;
    read_reg(info, IGC_ROC)?;
    read_reg(info, IGC_RJC)?;
    read_reg(info, IGC_TORL)?;
    read_reg(info, IGC_TORH)?;
    read_reg(info, IGC_TOTL)?;
    read_reg(info, IGC_TOTH)?;
    read_reg(info, IGC_TPR)?;
    read_reg(info, IGC_TPT)?;
    read_reg(info, IGC_MPTC)?;
    read_reg(info, IGC_BPTC)?;
    read_reg(info, IGC_TLPIC)?;
    read_reg(info, IGC_RLPIC)?;
    read_reg(info, IGC_RXDMTC)?;

    Ok(())
}
