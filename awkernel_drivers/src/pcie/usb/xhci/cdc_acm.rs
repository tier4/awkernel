//! USB CDC-ACM (Abstract Control Model) endpoint discovery.

use super::desc::{self, Descriptor};

/// bInterfaceClass of a CDC Communication interface.
const CLASS_CDC: u8 = 0x02;
/// bInterfaceSubClass of the Abstract Control Model.
const SUBCLASS_ACM: u8 = 0x02;
/// bInterfaceClass of a CDC Data interface.
const CLASS_CDC_DATA: u8 = 0x0A;
/// bInterfaceProtocol 0xFF on an ACM interface means RNDIS (Microsoft's
/// vendor protocol), which does not implement the ACM line-coding requests.
const PROTOCOL_VENDOR: u8 = 0xFF;

/// USB CDC-ACM interface information decoded from the configuration descriptor.
///
/// A CDC-ACM device exposes two interface groups:
///   - Communication interface (bInterfaceClass=0x02, bInterfaceSubClass=0x02) —
///     carries class-specific control requests (SET_LINE_CODING, etc.)
///   - Data interface (bInterfaceClass=0x0A) —
///     carries the Bulk IN/OUT endpoints used for serial data
pub struct CdcAcmInfo {
    /// bConfigurationValue to pass to SET_CONFIGURATION.
    pub config_val: u8,
    /// bInterfaceNumber of the CDC Communication interface.
    /// Used as wIndex in class-specific control requests (§6.2 of USB CDC spec).
    pub ctrl_if_num: u8,
    /// Bulk IN endpoint address on the Data interface (bit 7 = 1, direction = device→host).
    pub bulk_in_addr: u8,
    /// Bulk OUT endpoint address on the Data interface (bit 7 = 0, direction = host→device).
    pub bulk_out_addr: u8,
    /// wMaxPacketSize of the bulk endpoints (typically 64 for FS, up to 512 for HS/SS).
    pub max_pkt: u16,
}

/// Walk a USB configuration descriptor and return CDC-ACM endpoint information.
///
/// Looks for a Communication interface (class=0x02, subclass=0x02, protocol≠0xFF)
/// paired with a Data interface (class=0x0A) that has one Bulk IN and one Bulk OUT
/// endpoint.
/// Returns `None` if the descriptor is malformed or no such pair is present.
pub fn find_cdcacm_endpoints(cfg: &[u8]) -> Option<CdcAcmInfo> {
    let config_val = desc::configuration_value(cfg)?;
    let mut ctrl_if: Option<u8> = None;
    let mut in_data_if = false;
    let mut bulk_in: Option<u8> = None;
    let mut bulk_out: Option<u8> = None;
    let mut max_pkt: u16 = 64;

    for d in desc::descriptors(cfg) {
        match d {
            Descriptor::Interface(iface) => {
                in_data_if = iface.class == CLASS_CDC_DATA;
                if iface.class == CLASS_CDC
                    && iface.subclass == SUBCLASS_ACM
                    && iface.protocol != PROTOCOL_VENDOR
                {
                    ctrl_if = Some(iface.number);
                }
            }
            // Bulk endpoints of interest live only on the Data interface.
            Descriptor::Endpoint(ep) if in_data_if && ep.is_bulk() => {
                max_pkt = ep.max_packet;
                if ep.is_in() {
                    bulk_in = Some(ep.address);
                } else {
                    bulk_out = Some(ep.address);
                }
            }
            _ => {}
        }
    }

    Some(CdcAcmInfo {
        config_val,
        ctrl_if_num: ctrl_if?,
        bulk_in_addr: bulk_in?,
        bulk_out_addr: bulk_out?,
        max_pkt,
    })
}
