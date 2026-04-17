/// PL2303 USB-to-serial chip family — Prolific Technology Inc.
///
/// This driver covers all major PL2303 variants (Original, HX, HXD, HXN) using
/// the initialization sequence documented in FreeBSD sys/dev/usb/serial/uplcom.c.

/// Prolific USB Vendor ID.
pub const VID: u16 = 0x067B;

/// Known Prolific PID values.  Non-Prolific OEM entries (IODATA, ELECOM, RATOC …)
/// share the same chip protocol but use a different VID; add them separately.
pub const PIDS: &[u16] = &[
    0x2303, // PL2303 / PL2303HX — the ubiquitous generic USB-RS232 adapter
    0x2304, // PL2303 alternate PID (seen on some I/O DATA USB-RSAQ2)
    0x23A3, // PL2303GC (HXN family)
    0x23B3, // PL2303GB
    0x23C3, // PL2303GT
    0x23D3, // PL2303GL
    0x23E3, // PL2303GE
    0x23F3, // PL2303GS
];

/// Chip variant — determines which initialization path to take.
#[derive(Copy, Clone, PartialEq, Debug)]
pub enum ChipType {
    /// Original PL2303 — legacy device class=0x02, limited baud rate table.
    Original,
    /// PL2303HX / PL2303TA — up to 6 Mbps, bcdDevice=0x0300 or MaxPacketSize0=64.
    Hx,
    /// PL2303HXD / PL2303TB / EA / RA — up to 12 Mbps, bcdDevice=0x0400 or 0x0500.
    Hxd,
    /// PL2303HXN / GC / GB / GT / GL / GE / GS — newest family, different command set.
    /// Identified when reading register 0x8080 fails on a device initially typed as HX.
    Hxn,
}

/// Bulk endpoint configuration decoded from the USB configuration descriptor.
pub struct Pl2303Info {
    pub chip_type: ChipType,
    pub config_val: u8,
    /// bInterfaceNumber of the data interface (used as wIndex in SET_LINE_CODING etc.)
    pub data_iface_no: u8,
    pub bulk_in_addr: u8,  // bit 7 = 1  (device → host)
    pub bulk_out_addr: u8, // bit 7 = 0  (host → device)
    pub max_pkt: u16,
}

/// Return true if `vid:pid` matches any known PL2303 device.
pub fn is_pl2303(vid: u16, pid: u16) -> bool {
    vid == VID && PIDS.contains(&pid)
}

/// Determine the initial chip type from the device descriptor fields.
///
/// This may return `ChipType::Hx` when the device is actually `ChipType::Hxn`
/// — the caller must further probe with a vendor read of register 0x8080.
pub fn detect_chip_type(bcd_device: u16, dev_class: u8, max_pkt0: u8) -> ChipType {
    match bcd_device {
        0x0300          => ChipType::Hx,
        0x0400 | 0x0500 => ChipType::Hxd,
        _ => {
            if dev_class == 0x02    { ChipType::Original }
            else if max_pkt0 == 64 { ChipType::Hx }
            else                   { ChipType::Original }
        }
    }
}

/// Walk the USB configuration descriptor for PL2303 bulk endpoints.
///
/// PL2303 exposes a single interface with up to three endpoints:
///   - Interrupt IN  (status / modem signals — ignored in TX-only mode)
///   - Bulk IN       (RX data, host ← device)
///   - Bulk OUT      (TX data, host → device)
/// Returns `None` if no bulk IN + bulk OUT pair is found.
pub fn find_bulk_endpoints(cfg: &[u8], len: usize) -> Option<Pl2303Info> {
    let config_val    = if len >= 6 { cfg[5] } else { 1 };
    let mut iface_no  = 0u8;
    let mut bulk_in:  Option<u8> = None;
    let mut bulk_out: Option<u8> = None;
    let mut max_pkt: u16         = 64;
    let mut i = 0;

    while i < len {
        let blen = cfg[i] as usize;
        if blen < 2 || i + blen > len { break; }
        let btype = cfg[i + 1];

        match btype {
            4 if blen >= 9 => {
                iface_no = cfg[i + 2];
            }
            5 if blen >= 7 => {
                let addr  = cfg[i + 2];
                let attrs = cfg[i + 3];
                let pkt   = u16::from_le_bytes([cfg[i + 4], cfg[i + 5]]);
                if attrs & 0x3 == 2 {
                    max_pkt = pkt;
                    if addr & 0x80 != 0 { bulk_in  = Some(addr); }
                    else                { bulk_out = Some(addr); }
                }
            }
            _ => {}
        }
        i += blen;
    }

    match (bulk_in, bulk_out) {
        (Some(bi), Some(bo)) => Some(Pl2303Info {
            chip_type:     ChipType::Original, // overwritten by caller after HXN probe
            config_val,
            data_iface_no: iface_no,
            bulk_in_addr:  bi,
            bulk_out_addr: bo,
            max_pkt,
        }),
        _ => None,
    }
}
