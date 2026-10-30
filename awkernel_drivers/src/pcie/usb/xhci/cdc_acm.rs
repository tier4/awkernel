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
    /// wMaxPacketSize of the Bulk OUT endpoint, also used for Bulk IN
    /// (typically 64 for FS, 512 for HS/SS).
    pub max_pkt: u16,
}

/// Walk a USB configuration descriptor and return CDC-ACM endpoint information.
///
/// Takes the first Communication interface (class=0x02, subclass=0x02,
/// protocol≠0xFF) and the Data interface its Union descriptor names (or the
/// next interface number when there is no Union descriptor, the usual layout),
/// so the bulk endpoints of other functions in a composite device (a second ACM
/// port, CDC-ECM/NCM, ...) are never picked up.  Only alternate setting 0 is
/// considered: it is the one active without SET_INTERFACE.
/// Returns `None` if the descriptor is malformed or no such pair is present.
pub fn find_cdcacm_endpoints(cfg: &[u8]) -> Option<CdcAcmInfo> {
    let config_val = desc::configuration_value(cfg)?;

    // Pass 1: the ACM Communication interface.  Its functional descriptors
    // (including Union) follow it up to the next Interface Descriptor.
    let mut ctrl_if: Option<u8> = None;
    let mut union_data_if: Option<u8> = None;
    for d in desc::descriptors(cfg) {
        match d {
            Descriptor::Interface(_) if ctrl_if.is_some() => break,
            Descriptor::Interface(iface) => {
                if iface.alternate == 0
                    && iface.class == CLASS_CDC
                    && iface.subclass == SUBCLASS_ACM
                    && iface.protocol != PROTOCOL_VENDOR
                {
                    ctrl_if = Some(iface.number);
                }
            }
            Descriptor::CdcUnion {
                control,
                subordinate,
            } if ctrl_if == Some(control) => union_data_if = Some(subordinate),
            _ => {}
        }
    }
    let ctrl_if = ctrl_if?;
    let data_if = match union_data_if {
        Some(data_if) => data_if,
        None => ctrl_if.checked_add(1)?,
    };

    // Pass 2: the first Bulk IN and Bulk OUT endpoints of that Data interface.
    let mut in_data_if = false;
    let mut bulk_in: Option<u8> = None;
    let mut bulk_out: Option<(u8, u16)> = None;
    for d in desc::descriptors(cfg) {
        match d {
            Descriptor::Interface(iface) => {
                in_data_if = iface.number == data_if
                    && iface.alternate == 0
                    && iface.class == CLASS_CDC_DATA;
            }
            Descriptor::Endpoint(ep) if in_data_if && ep.is_bulk() => {
                if ep.is_in() {
                    if bulk_in.is_none() {
                        bulk_in = Some(ep.address);
                    }
                } else if bulk_out.is_none() {
                    bulk_out = Some((ep.address, ep.max_packet));
                }
            }
            _ => {}
        }
    }
    let (bulk_out_addr, max_pkt) = bulk_out?;

    Some(CdcAcmInfo {
        config_val,
        ctrl_if_num: ctrl_if,
        bulk_in_addr: bulk_in?,
        bulk_out_addr,
        max_pkt,
    })
}
