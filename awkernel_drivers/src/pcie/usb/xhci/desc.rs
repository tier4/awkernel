//! USB configuration descriptor walking (USB 2.0 spec §9.5, §9.6).
//!
//! The configuration descriptor comes from the device, so every field access is
//! bounds-checked through slice patterns; malformed input ends the walk instead
//! of panicking.
//!
//! WCET contract: no allocation, no panic; a walk visits at most `cfg.len() / 2`
//! descriptors because each one consumes at least two bytes.
//! [`read_configuration`] runs only at enumeration and issues two requests.

use alloc::vec::Vec;

const DT_CONFIGURATION: u8 = 2;
const DT_INTERFACE: u8 = 4;
const DT_ENDPOINT: u8 = 5;
/// CDC class-specific interface descriptor (CDC 1.2 §5.2.3).
const DT_CS_INTERFACE: u8 = 0x24;
/// CDC functional descriptor subtype: Union (CDC 1.2 §5.2.3.2).
const CDC_SUBTYPE_UNION: u8 = 0x06;

/// bmAttributes transfer type: Bulk.
const EP_TYPE_BULK: u8 = 2;
const EP_TYPE_MASK: u8 = 0x3;
/// bEndpointAddress direction bit: device-to-host.
const EP_DIR_IN: u8 = 0x80;
const EP_NUMBER_MASK: u8 = 0x0f;

/// Interface Descriptor fields used by the drivers.
#[derive(Clone, Copy)]
pub struct Interface {
    pub number: u8,
    pub alternate: u8,
    pub class: u8,
    pub subclass: u8,
    pub protocol: u8,
}

/// Endpoint Descriptor fields used by the drivers.
#[derive(Clone, Copy)]
pub struct Endpoint {
    pub address: u8,
    pub attributes: u8,
    pub max_packet: u16,
}

impl Endpoint {
    pub fn is_bulk(&self) -> bool {
        self.attributes & EP_TYPE_MASK == EP_TYPE_BULK
    }

    pub fn is_in(&self) -> bool {
        self.address & EP_DIR_IN != 0
    }
}

/// Endpoint number (1..=15) of an endpoint address; 0 is the control endpoint.
pub fn endpoint_number(address: u8) -> u8 {
    address & EP_NUMBER_MASK
}

pub enum Descriptor {
    Interface(Interface),
    Endpoint(Endpoint),
    /// CDC Union functional descriptor: the controlling interface and its
    /// first subordinate interface.
    CdcUnion {
        control: u8,
        subordinate: u8,
    },
    Other,
}

/// Iterator over the descriptors packed in a configuration descriptor.
pub struct Descriptors<'a> {
    rest: &'a [u8],
}

impl<'a> Iterator for Descriptors<'a> {
    type Item = Descriptor;

    fn next(&mut self) -> Option<Descriptor> {
        let len = usize::from(*self.rest.first()?);
        if len < 2 {
            self.rest = &[];
            return None;
        }
        let Some((desc, rest)) = self.rest.split_at_checked(len) else {
            self.rest = &[];
            return None;
        };
        self.rest = rest;

        Some(match *desc {
            [_, DT_INTERFACE, number, alternate, _, class, subclass, protocol, _, ..] => {
                Descriptor::Interface(Interface {
                    number,
                    alternate,
                    class,
                    subclass,
                    protocol,
                })
            }
            [_, DT_ENDPOINT, address, attributes, lo, hi, _, ..] => {
                Descriptor::Endpoint(Endpoint {
                    address,
                    attributes,
                    max_packet: u16::from_le_bytes([lo, hi]),
                })
            }
            [_, DT_CS_INTERFACE, CDC_SUBTYPE_UNION, control, subordinate, ..] => {
                Descriptor::CdcUnion {
                    control,
                    subordinate,
                }
            }
            _ => Descriptor::Other,
        })
    }
}

/// Walk all descriptors in `cfg` (the full configuration descriptor).
pub fn descriptors(cfg: &[u8]) -> Descriptors<'_> {
    Descriptors { rest: cfg }
}

/// Length of the Configuration Descriptor header, which carries wTotalLength.
pub const CONFIG_HEADER_LEN: u16 = 9;

/// Why [`read_configuration`] failed.
#[derive(Debug, PartialEq)]
pub enum ReadConfigError<E> {
    /// A GET_DESCRIPTOR request failed.
    Transfer(E),
    /// Malformed header, a wTotalLength larger than the buffer, fewer bytes
    /// than wTotalLength, or a different wTotalLength in the second read.
    Invalid,
}

/// Read a whole configuration descriptor (USB 2.0 §9.4.3, §9.6.3).
///
/// `get(len)` issues GET_DESCRIPTOR(Configuration) for `len` bytes and returns
/// the bytes the device actually sent: fewer than `len` if it ended the data
/// stage with a short packet.  The first request reads the header for
/// wTotalLength, the second all wTotalLength bytes, so a function that a
/// composite device places after others (past byte 255, say) is not cut off.
/// `capacity` is the size of the buffer the data stage lands in.  A
/// configuration is never silently truncated: anything shorter or inconsistent
/// is [`ReadConfigError::Invalid`].
pub fn read_configuration<E>(
    capacity: usize,
    mut get: impl FnMut(u16) -> Result<Vec<u8>, E>,
) -> Result<Vec<u8>, ReadConfigError<E>> {
    let header = get(CONFIG_HEADER_LEN).map_err(ReadConfigError::Transfer)?;
    let total = total_length(&header, capacity).ok_or(ReadConfigError::Invalid)?;
    let cfg = get(total).map_err(ReadConfigError::Transfer)?;
    if cfg.len() != usize::from(total) || total_length(&cfg, capacity) != Some(total) {
        return Err(ReadConfigError::Invalid);
    }
    Ok(cfg)
}

/// wTotalLength of the configuration descriptor `cfg` starts with, if the
/// header is well formed and wTotalLength fits `capacity`.
fn total_length(cfg: &[u8], capacity: usize) -> Option<u16> {
    match *cfg {
        [len, DT_CONFIGURATION, lo, hi, ..] if len >= 9 => {
            let total = u16::from_le_bytes([lo, hi]);
            (total >= u16::from(len) && usize::from(total) <= capacity).then_some(total)
        }
        _ => None,
    }
}

/// bConfigurationValue of a configuration descriptor, or `None` if `cfg` does
/// not start with a valid 9-byte Configuration Descriptor.
pub fn configuration_value(cfg: &[u8]) -> Option<u8> {
    match *cfg {
        [len, DT_CONFIGURATION, _, _, _, value, _, _, _, ..] if len >= 9 => Some(value),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A configuration of `total` bytes: a header saying so, then padding.
    fn configuration(total: u16) -> Vec<u8> {
        let [lo, hi] = total.to_le_bytes();
        let mut cfg = vec![9, DT_CONFIGURATION, lo, hi, 1, 1, 0, 0x80, 50];
        cfg.resize(usize::from(total), 0);
        cfg
    }

    /// A device that answers GET_DESCRIPTOR(Configuration) with `cfg`, sends
    /// at most `limit` bytes per request (a short packet beyond that), and
    /// records the requested lengths.
    struct Device {
        cfg: Vec<u8>,
        limit: usize,
        requests: Vec<u16>,
    }

    impl Device {
        fn new(cfg: Vec<u8>) -> Self {
            Self {
                cfg,
                limit: usize::MAX,
                requests: Vec::new(),
            }
        }

        fn get(&mut self, len: u16) -> Result<Vec<u8>, ()> {
            self.requests.push(len);
            let n = usize::from(len).min(self.cfg.len()).min(self.limit);
            Ok(self.cfg[..n].to_vec())
        }
    }

    #[test]
    fn reads_all_bytes_of_a_configuration_longer_than_255_bytes() {
        let mut dev = Device::new(configuration(391));

        let cfg = read_configuration(4096, |len| dev.get(len));

        assert_eq!(cfg, Ok(configuration(391)));
        assert_eq!(dev.requests, [9, 391]);
    }

    /// The device ends the data stage early: the residual of the short packet
    /// makes `get` return fewer bytes than wTotalLength.
    #[test]
    fn rejects_a_short_transfer() {
        let mut dev = Device::new(configuration(391));
        dev.limit = 300;

        let cfg = read_configuration(4096, |len| dev.get(len));

        assert_eq!(cfg, Err(ReadConfigError::Invalid));
        assert_eq!(dev.requests, [9, 391]);
    }

    #[test]
    fn rejects_a_total_length_that_changes_between_reads() {
        let mut replies = [configuration(391), configuration(400)].into_iter();

        let cfg = read_configuration(4096, |len| -> Result<Vec<u8>, ()> {
            let reply = replies.next().unwrap();
            Ok(reply[..usize::from(len)].to_vec())
        });

        assert_eq!(cfg, Err(ReadConfigError::Invalid));
    }

    #[test]
    fn rejects_a_configuration_larger_than_the_buffer() {
        let mut dev = Device::new(configuration(4097));

        let cfg = read_configuration(4096, |len| dev.get(len));

        assert_eq!(cfg, Err(ReadConfigError::Invalid));
        assert_eq!(dev.requests, [9]);
    }

    #[test]
    fn rejects_a_malformed_header() {
        let mut short_total = configuration(9);
        short_total[2] = 8; // wTotalLength shorter than the header
        let mut not_config = configuration(300);
        not_config[1] = DT_INTERFACE;
        let mut short_length = configuration(300);
        short_length[0] = 8; // bLength
        for cfg in [
            short_total,
            not_config,
            short_length,
            vec![9, DT_CONFIGURATION],
        ] {
            let mut dev = Device::new(cfg);

            assert_eq!(
                read_configuration(4096, |len| dev.get(len)),
                Err(ReadConfigError::Invalid)
            );
        }
    }

    #[test]
    fn passes_a_transfer_error_through() {
        let cfg = read_configuration(4096, |_| Err("stall"));

        assert_eq!(cfg, Err(ReadConfigError::Transfer("stall")));
    }
}
