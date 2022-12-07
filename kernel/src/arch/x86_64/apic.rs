use core::{arch::x86_64::__cpuid, fmt::Debug};
use x86_64::registers::model_specific::Msr;

use crate::{mmio_r, mmio_rw};

mmio_r!(offset 0x020 => xapic_local_apic_id<u32>);
mmio_r!(offset 0x030 => xapic_local_apic_version<u32>);
mmio_rw!(offset 0x300 => xapic_icr_0<u32>);
mmio_rw!(offset 0x310 => xapic_icr_1<u32>);

#[derive(Debug)]
pub struct XAPIC {
    is_bsp: bool, // BootStrap Processor?
    apic_base: usize,
}

#[derive(Debug)]
pub struct X2APIC {
    is_bsp: bool, // BootStrap Processor?
}

#[derive(Debug)]
pub enum TypeApic {
    XAPIC(XAPIC),
    X2APIC(X2APIC),
    Disabled,
}

pub trait APIC {
    fn local_apic_id(&self) -> u32;
    fn local_apic_version(&self) -> u32;
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

    if is_bsp {
        log::info!("I am a BootStrap processor.");
    }

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
            let xapic = XAPIC {
                is_bsp,
                apic_base: offset,
            };

            log::info!("Local APIC ID = {:x}", xapic.local_apic_id());

            TypeApic::XAPIC(xapic)
        }
        0b11 => {
            log::info!("Local APIC is enabled in x2APIC mode.");
            TypeApic::X2APIC(X2APIC { is_bsp })
        }
        _ => unreachable!(),
    }
}

impl APIC for XAPIC {
    fn local_apic_id(&self) -> u32 {
        let id = xapic_local_apic_id(self.apic_base).read();
        (id >> 24) & 0xff
    }

    fn local_apic_version(&self) -> u32 {
        xapic_local_apic_version(self.apic_base as _).read()
    }
}
