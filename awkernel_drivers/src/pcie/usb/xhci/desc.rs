//! USB configuration descriptor walking (USB 2.0 spec §9.5, §9.6).
//!
//! The configuration descriptor comes from the device, so every field access is
//! bounds-checked through slice patterns; malformed input ends the walk instead
//! of panicking.
//!
//! WCET contract: no allocation, no panic; a walk visits at most `cfg.len() / 2`
//! descriptors because each one consumes at least two bytes.

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

/// wTotalLength of a configuration descriptor (USB 2.0 §9.6.3), the number of
/// bytes to fetch for the whole configuration.
///
/// `cfg` starts with the Configuration Descriptor; `capacity` is the size of the
/// buffer the data stage lands in.  Returns `None` if the header is malformed,
/// if wTotalLength is shorter than the header, or if it exceeds `capacity`, so
/// a configuration is never silently truncated.
pub fn total_length(cfg: &[u8], capacity: usize) -> Option<u16> {
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

    /// Configuration Descriptor header with `wTotalLength = total`.
    fn header(total: u16) -> [u8; 9] {
        let [lo, hi] = total.to_le_bytes();
        [9, DT_CONFIGURATION, lo, hi, 1, 1, 0, 0x80, 50]
    }

    #[test]
    fn total_length_accepts_a_configuration_longer_than_255_bytes() {
        assert_eq!(total_length(&header(300), 4096), Some(300));
        assert_eq!(total_length(&header(4096), 4096), Some(4096));
    }

    #[test]
    fn total_length_rejects_a_configuration_larger_than_the_buffer() {
        assert_eq!(total_length(&header(4097), 4096), None);
    }

    #[test]
    fn total_length_rejects_a_malformed_header() {
        // wTotalLength shorter than the header itself.
        assert_eq!(total_length(&header(8), 4096), None);
        // Not a Configuration Descriptor.
        let mut not_config = header(300);
        not_config[1] = DT_INTERFACE;
        assert_eq!(total_length(&not_config, 4096), None);
        // bLength too short, and a truncated header.
        let mut short = header(300);
        short[0] = 8;
        assert_eq!(total_length(&short, 4096), None);
        assert_eq!(total_length(&[9, DT_CONFIGURATION], 4096), None);
    }
}
