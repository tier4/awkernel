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
/// Looks for a Communication interface (class=0x02, subclass=0x02) paired with a Data
/// interface (class=0x0A) that has one Bulk IN and one Bulk OUT endpoint.
/// Returns `None` if no such pair is present in `desc[..len]`.
pub fn find_cdcacm_endpoints(desc: &[u8], len: usize) -> Option<CdcAcmInfo> {
    let config_val  = if len >= 6 { desc[5] } else { 1 };
    let mut ctrl_if: Option<u8> = None;
    let mut in_data_if            = false;
    let mut bulk_in:  Option<u8> = None;
    let mut bulk_out: Option<u8> = None;
    let mut max_pkt: u16         = 64;
    let mut i                    = 0;

    while i < len {
        let blen = desc[i] as usize;
        if blen < 2 || i + blen > len { break; }
        let btype = desc[i + 1];

        match btype {
            // Interface Descriptor (bDescriptorType = 4)
            4 if blen >= 9 => {
                let if_num   = desc[i + 2];
                let if_class = desc[i + 5];
                let if_sub   = desc[i + 6];
                in_data_if   = false;
                if if_class == 0x02 && if_sub == 0x02 {
                    // CDC Abstract Control Model — control interface
                    ctrl_if = Some(if_num);
                } else if if_class == 0x0A {
                    // CDC Data interface — bulk endpoints live here
                    in_data_if = true;
                }
            }
            // Endpoint Descriptor (bDescriptorType = 5) — only on the Data interface
            5 if blen >= 7 && in_data_if => {
                let addr  = desc[i + 2];
                let attrs = desc[i + 3];
                let pkt   = u16::from_le_bytes([desc[i + 4], desc[i + 5]]);
                if attrs & 0x3 == 2 {
                    // Bulk endpoint
                    max_pkt = pkt;
                    if addr & 0x80 != 0 { bulk_in  = Some(addr); }
                    else                { bulk_out = Some(addr); }
                }
            }
            _ => {}
        }
        i += blen;
    }

    match (ctrl_if, bulk_in, bulk_out) {
        (Some(ci), Some(bi), Some(bo)) => Some(CdcAcmInfo {
            config_val,
            ctrl_if_num:  ci,
            bulk_in_addr:  bi,
            bulk_out_addr: bo,
            max_pkt,
        }),
        _ => None,
    }
}
