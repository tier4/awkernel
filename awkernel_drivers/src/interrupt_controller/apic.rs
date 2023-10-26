use alloc::boxed::Box;
use awkernel_lib::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr},
    arch::x86_64::page_allocator::PageAllocator,
    delay::wait_forever,
    interrupt::InterruptController,
    memory::Flags,
    paging::PageTable,
};
use core::{arch::x86_64::__cpuid, fmt::Debug};
use x86_64::{registers::model_specific::Msr, structures::paging::PhysFrame};

pub mod registers {
    use awkernel_lib::{mmio_r, mmio_rw, mmio_w};
    use bitflags::bitflags;
    use x86_64::registers::model_specific::Msr;

    pub const IA32_APIC_BASE_MSR: u32 = 0x1B;

    mmio_r!(offset 0x020 => pub(crate) XAPIC_LOCAL_APIC_ID<u32>);
    mmio_r!(offset 0x030 => pub(crate) XAPIC_LOCAL_VERSION<u32>);
    mmio_w!(offset 0x0b0 => pub(crate) XAPIC_EOI<u32>);
    mmio_rw!(offset 0x0f0 => pub(crate) XAPIC_SPURIOUS_INTERRUPT_VECTOR<u32>);
    mmio_rw!(offset 0x300 => pub(crate) XAPIC_ICR_LOW<u32>);
    mmio_rw!(offset 0x310 => pub(crate) XAPIC_ICR_HIGH<u32>);

    bitflags! {
        pub struct IcrFlags: u32 {
            const LEVEL_TRIGGER = 1 << 15;       // Trigger Mode: 0: Edge, 1: Level
            const ASSERT = 1 << 14;              // Level: 0: De-assert, 1: Assert
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

    pub const ENABLE_X2APIC: u64 = 1 << 10;

    pub static X2APIC_LOCAL_APIC_ID: Msr = Msr::new(0x802);
    pub static X2APIC_LOCAL_VERSION: Msr = Msr::new(0x803);
    pub static mut X2APIC_ICR: Msr = Msr::new(0x830);
}

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
        dst_shorthand: registers::DestinationShorthand,
        flags: registers::IcrFlags,
        delivery_mode: registers::DeliveryMode,
        vector: u8,
    );
}

pub fn new<T>(
    page_table: &mut awkernel_lib::arch::x86_64::page_table::PageTable,
    page_allocator: &mut PageAllocator<T>,
) -> TypeApic
where
    T: Iterator<Item = PhysFrame> + Send,
{
    let msr = Msr::new(registers::IA32_APIC_BASE_MSR);

    let cpuid = unsafe { __cpuid(1) };
    if cpuid.ecx & (1 << 21) != 0 {
        log::info!("x2APIC is available.");

        // Enable x2APIC
        // unsafe {
        //     let value = msr.read();
        //     msr.write(value | registers::ENABLE_X2APIC);
        // }
    }

    let value = unsafe { msr.read() };

    let is_bsp = (value & (1 << 8)) != 0;
    let apic_base = (value & 0xFFFF_F000) as usize;

    let phy_base = PhyAddr::new(apic_base);
    let virt_base = VirtAddr::new(apic_base);

    if value & registers::ENABLE_X2APIC == 0 {
        log::info!("APIC base address = 0x{:x}", apic_base);
    }

    let flags = Flags {
        write: true,
        execute: false,
        cache: false,
    };

    if !unsafe {
        page_table
            .map_to(phy_base, virt_base, flags, page_allocator)
            .is_err()
    } {
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
            let x2apic = X2Apic { is_bsp };

            log::info!("Local APIC ID = {:x}", x2apic.local_apic_id());

            TypeApic::X2Apic(x2apic)
        }
        _ => unreachable!(),
    }
}

impl Apic for Xapic {
    fn local_apic_id(&self) -> u32 {
        let id = registers::XAPIC_LOCAL_APIC_ID.read(self.apic_base);
        (id >> 24) & 0xff
    }

    fn local_apic_version(&self) -> u32 {
        registers::XAPIC_LOCAL_VERSION.read(self.apic_base as _)
    }

    fn interrupt(
        &self,
        destination: u32,
        dst_shorthand: registers::DestinationShorthand,
        flags: registers::IcrFlags,
        delivery_mode: registers::DeliveryMode,
        vector: u8,
    ) {
        let low = registers::XAPIC_ICR_LOW;
        let high = registers::XAPIC_ICR_HIGH;

        let low_bits = dst_shorthand as u32 | flags.bits() | delivery_mode as u32 | vector as u32;

        let high_bits = high.read(self.apic_base) & 0x000f_ffff;
        let high_bits = match dst_shorthand {
            registers::DestinationShorthand::NoShorthand => high_bits | (destination << 24),
            _ => high_bits,
        };

        high.write(high_bits, self.apic_base);
        low.write(low_bits, self.apic_base);

        while (low.read(self.apic_base) & registers::IcrFlags::SEND_PENDING.bits()) != 0 {}
    }
}

impl Apic for X2Apic {
    fn local_apic_id(&self) -> u32 {
        let id = unsafe { registers::X2APIC_LOCAL_APIC_ID.read() };
        id as u32
    }

    fn local_apic_version(&self) -> u32 {
        let ver = unsafe { registers::X2APIC_LOCAL_VERSION.read() };
        ver as u32
    }

    fn interrupt(
        &self,
        destination: u32,
        dst_shorthand: registers::DestinationShorthand,
        flags: registers::IcrFlags,
        delivery_mode: registers::DeliveryMode, // Delivery mode is removed
        vector: u8,
    ) {
        let bits = (destination as u64) << 32
            | dst_shorthand as u64
            | flags.bits() as u64
            | delivery_mode as u64
            | vector as u64;

        unsafe { registers::X2APIC_ICR.write(bits) };
    }
}

impl Xapic {
    fn validate_and_convert_irq(&self, irq: u16) -> Option<u8> {
        let lower_bound = 32;
        let upper_bound = u8::MAX as u16;
        if irq < lower_bound || irq > upper_bound {
            log::warn!(
                "XAPIC: Failed to send IRQ #{irq}, because it is smaller than {lower_bound} or greater than {upper_bound}."
            );
            return None;
        }

        Some(irq as u8)
    }
}

impl InterruptController for Xapic {
    fn enable_irq(&mut self, irq: u16) {
        // Set 8th bit of SVR to 1.
        let svr = registers::XAPIC_SPURIOUS_INTERRUPT_VECTOR;
        let mut svr_bits = svr.read(self.apic_base);
        svr_bits |= 1 << 8;
        svr.write(svr_bits, self.apic_base);

        let cpu_id = awkernel_lib::cpu::cpu_id();
        log::info!("XAPIC: IRQ #{irq} has been enabled on CPU#{cpu_id}.");
    }

    fn disable_irq(&mut self, irq: u16) {
        // Set 8th bit of SVR to 0.
        let svr = registers::XAPIC_SPURIOUS_INTERRUPT_VECTOR;
        let mut svr_bits = svr.read(self.apic_base);
        svr_bits &= !(1 << 8);
        svr.write(svr_bits, self.apic_base);

        let cpu_id = awkernel_lib::cpu::cpu_id();
        log::info!("XAPIC: IRQ #{irq} has been disabled on CPU#{cpu_id}.");
    }

    fn pending_irqs(&self) -> Box<dyn Iterator<Item = u16>> {
        unimplemented!("`pending_irqs` is not yet implemented in xAPIC.");
    }

    /// Send an inter-process interrupt to `target` CPU.
    fn send_ipi(&mut self, irq: u16, target: u16) {
        if let Some(vector) = self.validate_and_convert_irq(irq) {
            self.interrupt(
                target as u32,
                registers::DestinationShorthand::NoShorthand,
                registers::IcrFlags::empty(),
                registers::DeliveryMode::Fixed,
                vector,
            );
        }
    }

    /// Send an inter-process interrupt to all CPUs.
    fn send_ipi_broadcast(&mut self, irq: u16) {
        if let Some(vector) = self.validate_and_convert_irq(irq) {
            self.interrupt(
                0,
                registers::DestinationShorthand::AllIncludingSelf,
                registers::IcrFlags::empty(),
                registers::DeliveryMode::Fixed,
                vector,
            )
        }
    }

    /// Send an inter-process interrupt to all CPUs except the sender CPU.
    fn send_ipi_broadcast_without_self(&mut self, irq: u16) {
        if let Some(vector) = self.validate_and_convert_irq(irq) {
            self.interrupt(
                0,
                registers::DestinationShorthand::AllExcludingSelf,
                registers::IcrFlags::empty(),
                registers::DeliveryMode::Fixed,
                vector,
            )
        }
    }

    /// Initialization for non-primary core.
    fn init_non_primary(&mut self) {
        // Nothing to do.
    }

    fn eoi(&mut self) {
        registers::XAPIC_EOI.write(0, self.apic_base);
    }
}

impl InterruptController for X2Apic {
    fn disable_irq(&mut self, _irq: u16) {
        todo!()
    }

    fn enable_irq(&mut self, _irq: u16) {
        todo!()
    }

    fn pending_irqs(&self) -> Box<dyn Iterator<Item = u16>> {
        todo!()
    }

    fn send_ipi(&mut self, _irq: u16, _target: u16) {
        todo!()
    }

    fn send_ipi_broadcast(&mut self, _irq: u16) {
        todo!()
    }

    fn send_ipi_broadcast_without_self(&mut self, _irq: u16) {
        todo!()
    }

    fn init_non_primary(&mut self) {}
}
