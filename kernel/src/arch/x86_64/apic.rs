use bitflags::bitflags;
use core::{arch::x86_64::__cpuid, fmt::Debug};
use t4os_lib::{mmio_r, mmio_rw};
use x86_64::registers::model_specific::Msr;

mmio_r!(offset 0x020 => xapic_local_apic_id<u32>);
mmio_r!(offset 0x030 => xapic_local_apic_version<u32>);
mmio_rw!(offset 0x300 => xapic_icr_low<u32>);
mmio_rw!(offset 0x310 => xapic_icr_high<u32>);

#[derive(Debug)]
pub struct Xapic {
    is_bsp: bool, // BootStrap Processor?
    apic_base: usize,
}

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

pub fn new(offset: u64) -> TypeApic {
    let cpuid = unsafe { __cpuid(1) };
    if cpuid.ecx & (1 << 21) != 0 {
        log::info!("x2APIC is available.");
    }

    let msr = Msr::new(IA32_APIC_BASE_MSR);
    let value = unsafe { msr.read() };

    let is_bsp = (value & (1 << 8)) != 0;
    let apic_base = (value & 0xFFFF_F000) as u32;

    log::info!("APIC Base Address = {:x}", apic_base);

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
            let offset = (offset + apic_base as u64) as usize;
            let xapic = Xapic {
                is_bsp,
                apic_base: offset,
            };

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

#[derive(Debug, Clone, Copy)]
pub enum DestinationShorthand {
    NoShorthand = 0,
    DstSelf = 0b01 << 18,
    AllIncludingSelf = 0b10 << 18,
    AllExcludingSelf = 0b11 << 18,
}

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
        let id = xapic_local_apic_id(self.apic_base).read();
        (id >> 24) & 0xff
    }

    fn local_apic_version(&self) -> u32 {
        xapic_local_apic_version(self.apic_base as _).read()
    }

    fn interrupt(
        &self,
        destination: u32,
        dst_shorthand: DestinationShorthand,
        flags: IcrFlags,
        delivery_mode: DeliveryMode,
        vector: u8,
    ) {
        let low = xapic_icr_low(self.apic_base);
        let high = xapic_icr_high(self.apic_base);

        let low_bits = low.read();
        let low_bits = (low_bits & !0x000c_dfff)
            | dst_shorthand as u32
            | flags.bits
            | delivery_mode as u32
            | vector as u32;

        let high_bits = high.read() & 0x000f_ffff;
        let high_bits = match dst_shorthand {
            DestinationShorthand::NoShorthand => high_bits | (destination << 24),
            _ => high_bits,
        };

        high.write(high_bits);
        low.write(low_bits);

        while (low.read() & IcrFlags::SEND_PENDING.bits) != 0 {}
    }
}
