//! DMA Remapping Table

pub mod andd;
pub mod atsr;
pub mod device_scope;
pub mod dhrd;
pub mod rhsa;
pub mod rmrr;
pub mod satc;
pub mod sidp;

use core::{marker::PhantomData, mem};

use acpi::{
    sdt::{SdtHeader, Signature},
    AcpiTable,
};

use crate::arch::x86_64::acpi::dmar::dhrd::DmarDrhd;

use self::{andd::DmarAndd, atsr::DmarAtsr, rhsa::DmarRhsa, rmrr::DmarRmrr, satc::DmarSatc};

#[repr(C, packed)]
#[derive(Debug, Clone)]
pub struct Dmar {
    pub header: SdtHeader,
    pub host_address_width: u8,
    pub flags: u8,
    reserved: [u8; 10],
}

#[derive(Clone, Copy, Debug)]
#[repr(C, packed)]
pub struct EntryHeader {
    pub entry_type: u16,
    pub length: u16,
}

unsafe impl AcpiTable for Dmar {
    const SIGNATURE: Signature = Signature::DMAR;

    fn header(&self) -> &SdtHeader {
        &self.header
    }
}

#[derive(Debug)]
pub enum DmarEntry<'a> {
    Drhd(&'a DmarDrhd),
    Rmrr(&'a DmarRmrr),
    Atsr(&'a DmarAtsr),
    Rhsa(&'a DmarRhsa),
    Andd(&'a DmarAndd),
    Satc(&'a DmarSatc),
}

#[derive(Debug)]
pub struct DmarEntryIter<'a> {
    pointer: *const u8,
    /*
     * The iterator can only have at most `u32::MAX` remaining bytes, because the length of the
     * whole SDT can only be at most `u32::MAX`.
     */
    remaining_length: u32,
    _phantom: PhantomData<&'a ()>,
}

impl<'a> Iterator for DmarEntryIter<'a> {
    type Item = DmarEntry<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.remaining_length >= mem::size_of::<Dmar>() as u32 {
            let entry_pointer = self.pointer;
            let header = unsafe { &*(self.pointer as *const EntryHeader) };

            self.pointer = unsafe { self.pointer.offset(header.length as isize) };
            self.remaining_length = self.remaining_length.saturating_sub(header.length as u32);

            macro_rules! construct_entry {
                ($entry_type:expr,
                 $entry_pointer:expr,
                 $(($value:expr => $variant:path as $type:ty)),*
                ) => {
                    match $entry_type {
                        $(
                            $value => {
                                return Some($variant(unsafe {
                                    &*($entry_pointer as *const $type)
                                }))
                            }
                         )*

                        _ => ()
                    }
                }
            }

            #[rustfmt::skip]
            construct_entry!(
                header.entry_type,
                entry_pointer,
                (0x0 => DmarEntry::Drhd as DmarDrhd),
                (0x1 => DmarEntry::Rmrr as DmarRmrr),
                (0x2 => DmarEntry::Atsr as DmarAtsr),
                (0x3 => DmarEntry::Rhsa as DmarRhsa),
                (0x4 => DmarEntry::Andd as DmarAndd),
                (0x5 => DmarEntry::Satc as DmarSatc)
            );
        }

        None
    }
}

impl Dmar {
    pub fn entries(&self) -> DmarEntryIter<'_> {
        DmarEntryIter {
            pointer: unsafe { (self as *const Dmar as *const u8).add(mem::size_of::<Dmar>()) },
            remaining_length: self
                .header
                .length
                .saturating_sub(mem::size_of::<Dmar>() as u32),
            _phantom: PhantomData,
        }
    }
}
