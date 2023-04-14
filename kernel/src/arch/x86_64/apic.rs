use awkernel_lib::{
    arch::x86_64::{mmu, page_allocator::PageAllocator},
    delay::wait_forever,
    mmio_r, mmio_rw,
};
use bitflags::bitflags;
use core::{arch::x86_64::__cpuid, fmt::Debug};
use x86_64::{
    registers::model_specific::Msr,
    structures::paging::{OffsetPageTable, PageTableFlags},
};

mmio_r!(offset 0x020 => XAPIC_LOCAL_APIC_ID<u32>);
mmio_r!(offset 0x030 => XAPIC_LOCAL_VERSION<u32>);
mmio_rw!(offset 0x300 => XAPIC_ICR_LOW<u32>);
mmio_rw!(offset 0x310 => XAPIC_ICR_HIGH<u32>);

#[allow(dead_code)]
#[derive(Debug)]
pub struct Xapic {
    is_bsp: bool, // BootStrap Processor?
    apic_base: usize,
}

#[allow(dead_code)]
#[derive(Debug)]
pub struct X2Apic {
    is_bsp: bool, // BootStrap Processor?
}

#[derive(Debug)]
pub enum TypeApic {
    Xapic(Xapic),
    X2Apic(X2Apic),
    Disabled,
}

pub trait Apic {
    fn local_apic_id(&self) -> u32;
    fn local_apic_version(&self) -> u32;
    fn interrupt(
        &self,
        destination: u32,
        dst_shorthand: DestinationShorthand,
        flags: IcrFlags,
        delivery_mode: DeliveryMode,
        vector: u8,
    );
}

const IA32_APIC_BASE_MSR: u32 = 0x1B;

pub fn new(
    page_table: &mut OffsetPageTable<'static>,
    page_allocator: &mut PageAllocator,
) -> TypeApic {
    let cpuid = unsafe { __cpuid(1) };
    if cpuid.ecx & (1 << 21) != 0 {
        log::info!("x2APIC is available.");
    }

    let msr = Msr::new(IA32_APIC_BASE_MSR);
    let value = unsafe { msr.read() };

    let is_bsp = (value & (1 << 8)) != 0;
    let apic_base = (value & 0xFFFF_F000) as usize;

    log::info!("APIC base address = 0x{:x}", apic_base);

    let flags = PageTableFlags::PRESENT
        | PageTableFlags::WRITABLE
        | PageTableFlags::NO_EXECUTE
        | PageTableFlags::NO_CACHE;
    if !unsafe { mmu::map_to(apic_base, apic_base, flags, page_table, page_allocator) } {
        log::error!("Failed to map APIC's memory region.");
        wait_forever();
    }

    match (value >> 10) & 0b11 {
        0b00 => {
            log::info!("Local APIC is disabled.");
            TypeApic::Disabled
        }
        0b01 => {
            log::error!("Invalid APIC configuration.");
            TypeApic::Disabled
        }
        0b10 => {
            log::info!("Local APIC is enabled in xAPIC mode.");
            let xapic = Xapic { is_bsp, apic_base };

            log::info!("Local APIC ID = {:x}", xapic.local_apic_id());

            TypeApic::Xapic(xapic)
        }
        0b11 => {
            log::info!("Local APIC is enabled in x2APIC mode.");
            TypeApic::X2Apic(X2Apic { is_bsp })
        }
        _ => unreachable!(),
    }
}

bitflags! {
    pub struct IcrFlags: u32 {
        const LEVEL_TRIGGER = 1 << 15;       // Trigger Mode
        const ASSERT = 1 << 14;              // Level
        const SEND_PENDING = 1 << 12;        // Delivery Status
        const DESTINATION_LOGICAL = 1 << 11; // Destination Mode
    }
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
pub enum DestinationShorthand {
    NoShorthand = 0,
    DstSelf = 0b01 << 18,
    AllIncludingSelf = 0b10 << 18,
    AllExcludingSelf = 0b11 << 18,
}

#[allow(dead_code)]
#[derive(Debug, Clone, Copy)]
pub enum DeliveryMode {
    Fixed = 0,
    LowestPriority = 0b001 << 8,
    Smi = 0b010 << 8,
    Nmi = 0b100 << 8,
    Init = 0b101 << 8,
    StartUp = 0b110 << 8,
}

impl Apic for Xapic {
    fn local_apic_id(&self) -> u32 {
        let id = XAPIC_LOCAL_APIC_ID.read(self.apic_base);
        (id >> 24) & 0xff
    }

    fn local_apic_version(&self) -> u32 {
        XAPIC_LOCAL_VERSION.read(self.apic_base as _)
    }

    fn interrupt(
        &self,
        destination: u32,
        dst_shorthand: DestinationShorthand,
        flags: IcrFlags,
        delivery_mode: DeliveryMode,
        vector: u8,
    ) {
        let low = XAPIC_ICR_LOW;
        let high = XAPIC_ICR_HIGH;

        let low_bits = low.read(self.apic_base);
        let low_bits = (low_bits & !0x000c_dfff)
            | dst_shorthand as u32
            | flags.bits()
            | delivery_mode as u32
            | vector as u32;

        let high_bits = high.read(self.apic_base) & 0x000f_ffff;
        let high_bits = match dst_shorthand {
            DestinationShorthand::NoShorthand => high_bits | (destination << 24),
            _ => high_bits,
        };

        high.write(high_bits, self.apic_base);
        low.write(low_bits, self.apic_base);

        while (low.read(self.apic_base) & IcrFlags::SEND_PENDING.bits()) != 0 {}
    }
}
