// Aquantia Atlantic / Atlantic 2 register definitions.
//
// Based on Linux kernel drivers/net/ethernet/aquantia/atlantic/:
//   hw_atl/hw_atl_llh_internal.h (Atlantic 1)
//   hw_atl2/hw_atl2_llh_internal.h (Atlantic 2)

// ── Firmware / Boot ──────────────────────────────────────────────────────────
/// Firmware boot-complete status. Non-zero once firmware is ready.
pub const MPI_BOOT_COMPLETE: usize = 0x0360;
/// Firmware boot code version register.
pub const MPI_BOOT_CODE: usize = 0x0380;

// ── TX path ──────────────────────────────────────────────────────────────────
/// TX Packet Buffer Enable. Bit 0 = enable.
pub const TPB_TX_BUF_ENABLE: usize = 0x7900;
/// TX DMA ring disable: write bit n to disable ring n.
pub const TDM_RING_DISABLE: usize = 0x7B08;
/// TX DMA ring enable: write bit n to enable ring n.
pub const TDM_RING_ENABLE: usize = 0x7B0C;

/// TX descriptor ring base address (low 32 bits), stride 0x40.
pub fn tx_ring_base_addrl(ring: usize) -> usize {
    0x7C00 + ring * 0x40
}
/// TX descriptor ring base address (high 32 bits), stride 0x40.
pub fn tx_ring_base_addrh(ring: usize) -> usize {
    0x7C04 + ring * 0x40
}
/// TX descriptor ring length (number of descriptors − 1), stride 0x40.
pub fn tx_ring_len(ring: usize) -> usize {
    0x7C08 + ring * 0x40
}
/// TX descriptor ring head pointer (read-only from software), stride 0x40.
pub fn tx_ring_head(ring: usize) -> usize {
    0x7C0C + ring * 0x40
}
/// TX descriptor ring tail pointer (driver writes to post new descriptors).
pub fn tx_ring_tail(ring: usize) -> usize {
    0x7C10 + ring * 0x40
}

// TX descriptor control-word flags
/// Descriptor type = data (bits [18:16] = 0).
pub const TX_DESC_TYPE_DATA: u32 = 0x0 << 16;
/// End-of-Packet flag.
pub const TX_DESC_EOP: u32 = 1 << 22;
/// Auto-append FCS/CRC.
pub const TX_DESC_FCS: u32 = 1 << 23;
/// Request write-back on completion.
pub const TX_DESC_WB: u32 = 1 << 25;

// ── RX path ──────────────────────────────────────────────────────────────────
/// RX Packet Buffer Enable. Bit 0 = enable.
pub const RPB_RX_BUF_ENABLE: usize = 0x5700;
/// RX DMA ring disable: write bit n to disable ring n.
pub const RDM_RING_DISABLE: usize = 0x5A18;
/// RX DMA ring enable: write bit n to enable ring n.
pub const RDM_RING_ENABLE: usize = 0x5A1C;

/// RX descriptor ring base address (low 32 bits), stride 0x20.
pub fn rx_ring_base_addrl(ring: usize) -> usize {
    0x5B00 + ring * 0x20
}
/// RX descriptor ring base address (high 32 bits), stride 0x20.
pub fn rx_ring_base_addrh(ring: usize) -> usize {
    0x5B04 + ring * 0x20
}
/// RX descriptor ring length (number of descriptors − 1), stride 0x20.
pub fn rx_ring_len(ring: usize) -> usize {
    0x5B08 + ring * 0x20
}
/// RX descriptor ring head pointer (hardware advances this; read-only), stride 0x20.
pub fn rx_ring_head(ring: usize) -> usize {
    0x5B0C + ring * 0x20
}
/// RX descriptor ring tail pointer (driver writes to give descriptors to hardware).
pub fn rx_ring_tail(ring: usize) -> usize {
    0x5B10 + ring * 0x20
}

// RX write-back status bits (field at offset 8 of the 16-byte write-back descriptor)
/// Descriptor Done: hardware has written a received packet here.
pub const RX_WB_DD: u16 = 1 << 0;
/// End-of-Packet.
#[allow(dead_code)]
pub const RX_WB_EOP: u16 = 1 << 2;

// ── MAC / L2 filtering ───────────────────────────────────────────────────────
/// L2 unicast filter MAC address low word (bytes 2–5), stride 8.
pub fn mac_filter_addrl(n: usize) -> usize {
    0x5110 + n * 8
}
/// L2 unicast filter MAC address high word (bytes 0–1), stride 8.
pub fn mac_filter_addrh(n: usize) -> usize {
    0x5114 + n * 8
}
/// L2 unicast filter enable register.  Bit n enables filter n.
pub const MAC_FILTER_ENABLE: usize = 0x5100;
/// Enable broadcast reception.
pub const MAC_BCAST_ENABLE: usize = 0x5108;

// ── PHY / link status ────────────────────────────────────────────────────────
/// MAC/PHY status register. Bits [4:0] encode the negotiated speed.
pub const PHY_STATUS: usize = 0x4004;
/// Bit 0 set = 100 Mbps link.
pub const PHY_STATUS_100M: u32 = 1 << 0;
/// Bit 1 set = 1 Gbps link.
pub const PHY_STATUS_1G: u32 = 1 << 1;
/// Bit 2 set = 10 Gbps link.
pub const PHY_STATUS_10G: u32 = 1 << 2;
/// Bit 3 set = 2.5 Gbps link.
pub const PHY_STATUS_2_5G: u32 = 1 << 3;
/// Bit 4 set = 5 Gbps link.
pub const PHY_STATUS_5G: u32 = 1 << 4;

// ── Interrupts (Atlantic 2) ───────────────────────────────────────────────────
/// Interrupt Status register (clear-on-read). Atlantic 2 offset.
pub const ATL2_ITR_STATUS: usize = 0x2090;
/// Interrupt Mask Set register. Atlantic 2 offset.
pub const ATL2_ITR_MASK_SET: usize = 0x2098;
/// Interrupt Mask Clear register. Atlantic 2 offset.
pub const ATL2_ITR_MASK_CLR: usize = 0x20A0;

// Interrupt cause bits (shared between ATL1 and ATL2 for rings 0–7)
/// RX ring 0 interrupt.
pub const ITR_RX0: u32 = 1 << 0;
/// TX ring 0 interrupt.
pub const ITR_TX0: u32 = 1 << 8;
/// Link status change interrupt.
pub const ITR_LSC: u32 = 1 << 16;
