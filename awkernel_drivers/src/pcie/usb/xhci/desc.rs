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
            [_, DT_INTERFACE, number, _, _, class, subclass, protocol, _, ..] => {
                Descriptor::Interface(Interface {
                    number,
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
            _ => Descriptor::Other,
        })
    }
}

/// Walk all descriptors in `cfg` (the full configuration descriptor).
pub fn descriptors(cfg: &[u8]) -> Descriptors<'_> {
    Descriptors { rest: cfg }
}

/// bConfigurationValue of a configuration descriptor, or `None` if `cfg` does
/// not start with a valid 9-byte Configuration Descriptor.
pub fn configuration_value(cfg: &[u8]) -> Option<u8> {
    match *cfg {
        [len, DT_CONFIGURATION, _, _, _, value, _, _, _, ..] if len >= 9 => Some(value),
        _ => None,
    }
}
