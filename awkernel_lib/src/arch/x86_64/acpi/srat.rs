use core::{marker::PhantomData, mem};

use acpi::{
    sdt::{SdtHeader, Signature},
    AcpiTable,
};

#[repr(C, packed)]
#[derive(Debug, Clone)]
pub struct Srat {
    header: SdtHeader,
    reserved: [u8; 12],
}

#[derive(Debug)]
pub struct SratEntryIter<'a> {
    pointer: *const u8,
    /*
     * The iterator can only have at most `u32::MAX` remaining bytes, because the length of the
     * whole SDT can only be at most `u32::MAX`.
     */
    remaining_length: u32,
    _phantom: PhantomData<&'a ()>,
}

impl<'a> Iterator for SratEntryIter<'a> {
    type Item = SratEntry<'a>;

    fn next(&mut self) -> Option<Self::Item> {
        while self.remaining_length >= mem::size_of::<EntryHeader>() as u32 {
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
                (0x0 => SratEntry::LocalApic as SratLApic),
                (0x1 => SratEntry::MemoryAffinity as SratMemoryAffinity),
                (0x2 => SratEntry::LocalX2Apic as SratX2Apic),
                (0x5 => SratEntry::GenericInitiatorAffinity as SratGenericInitiatorAffinity)
            );
        }

        None
    }
}

#[derive(Clone, Copy, Debug)]
#[repr(C, packed)]
pub struct EntryHeader {
    pub entry_type: u8,
    pub length: u8,
}

#[derive(Debug)]
pub enum SratEntry<'a> {
    LocalApic(&'a SratLApic),
    LocalX2Apic(&'a SratX2Apic),
    MemoryAffinity(&'a SratMemoryAffinity),
    GenericInitiatorAffinity(&'a SratGenericInitiatorAffinity),
}

#[repr(C, packed)]
#[derive(Debug)]
pub struct SratLApic {
    pub header: EntryHeader, // type is 0x0 for this type of structure, length is 16
    pub lo_dm: u8,           // Bits [0:7] of the proximity domain
    pub apic_id: u8,         // Processor's APIC ID
    pub flags: u32,          // Haha the most useless thing ever
    pub sapic_eid: u8,       // The processor's local SAPIC EID. Don't even bother.
    pub hi_dm: [u8; 3],      // Bits [8:31] of the proximity domain
    pub cdm: u32,            // The clock domain which the processor belongs to (more jargon)
}

#[repr(C, packed)]
#[derive(Debug)]
pub struct SratX2Apic {
    pub header: EntryHeader, // type is 0x2 for this type of structure, length is 24
    pub reserved1: [u8; 2],  // Must be zero
    pub domain: u32,         // The proximity domain which the logical processor belongs to
    pub x2apic_id: u32,      // Processor's x2APIC ID
    pub flags: u32,          // Flags
    pub cdm: u32,            // The clock domain which the processor belongs to (more jargon)
    pub reserved2: [u8; 4],  // Reserved.
}

#[repr(C, packed)]
#[derive(Debug)]
pub struct SratMemoryAffinity {
    pub header: EntryHeader, // type is 0x1 for this type of structure, length is 40
    pub domain: u32,         // The domain to which this memory region belongs to
    pub reserved1: [u8; 2],  // Reserved
    pub lo_base: u32,        // Low 32 bits of the base address of the memory range
    pub hi_base: u32,        // High 32 bits of the base address of the memory range
    pub lo_length: u32,      // Low 32 bits of the length of the range
    pub hi_length: u32,      // High 32 bits of the length
    pub reserved2: [u8; 4],  // Reserved
    pub flags: u32,          // Flags
    pub reserved3: [u8; 8],  // Reserved
}

#[repr(C, packed)]
#[derive(Debug)]
pub struct SratGenericInitiatorAffinity {
    pub header: EntryHeader, // type is 0x5 for this type of structure, length is 32
    pub reserved1: u8,       // Reserved
    pub device_handle_type: u8, // The type of device handle
    pub domain: u32,         // The domain to which this initiator belongs to
    pub device_handle: [u8; 16], // The device handle
    pub flags: u32,          // Flags
    pub reserved2: [u8; 4],  // Reserved
}

unsafe impl AcpiTable for Srat {
    const SIGNATURE: Signature = Signature::SRAT;

    fn header(&self) -> &SdtHeader {
        &self.header
    }
}

impl Srat {
    pub fn entries(&self) -> SratEntryIter<'_> {
        SratEntryIter {
            pointer: unsafe { (self as *const Srat as *const u8).add(mem::size_of::<Srat>()) },
            remaining_length: self
                .header
                .length
                .saturating_sub(mem::size_of::<Srat>() as u32),
            _phantom: PhantomData,
        }
    }
}
