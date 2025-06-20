//! # XAPIC and x2APIC driver for x86_64 architecture.

use alloc::boxed::Box;
use awkernel_lib::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr},
    arch::x86_64::{interrupt_remap, page_allocator::VecPageAllocator},
    delay::wait_forever,
    interrupt::{InterruptController, IRQ},
    paging::{Flags, PageTable},
    timer::Timer,
};
use core::{arch::x86_64::__cpuid, fmt::Debug, ptr::write_volatile, time::Duration};
use x86_64::registers::model_specific::Msr;

const TIMER_IRQ: u8 = 253;

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
    mmio_rw!(offset 0x320 => pub(crate) XAPIC_LVT_TIMER<u32>);
    mmio_rw!(offset 0x380 => pub(crate) XAPIC_TIMER_INITIAL_COUNT<u32>);
    mmio_rw!(offset 0x390 => pub(crate) XAPIC_TIMER_CURRENT_COUNT<u32>);
    mmio_rw!(offset 0x3e0 => pub(crate) XAPIC_TIMER_DIV<u32>);

    pub const LVT_TIMER_PERIODIC: u32 = 1 << 17;

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
    pub static mut X2APIC_EOI: Msr = Msr::new(0x80B);
    pub static mut X2APIC_SPURIOUS_INTERRUPT_VECTOR: Msr = Msr::new(0x80F);
    pub static mut X2APIC_ICR: Msr = Msr::new(0x830);
    pub static mut X2APIC_LVT_TIMER: Msr = Msr::new(0x832);
    pub static mut X2APIC_TIMER_INITIAL_COUNT: Msr = Msr::new(0x838);
    pub static mut X2APIC_TIMER_CURRENT_COUNT: Msr = Msr::new(0x839);
    pub static mut X2APIC_TIMER_DIV: Msr = Msr::new(0x83E);
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
    fn validate_and_convert_irq(&self, irq: u16) -> Option<u8> {
        let lower_bound = 32;
        let upper_bound = u8::MAX as u16;
        if irq < lower_bound || irq > upper_bound {
            log::warn!(
                "Failed to send IRQ #{irq}, because it is smaller than {lower_bound} or greater than {upper_bound}."
            );
            return None;
        }

        Some(irq as u8)
    }

    fn write_timer_div(&mut self, div: u32);

    fn read_current_timer_count(&self) -> u32;

    fn write_timer_initial_count(&mut self, _count: u32);

    fn create_timer(&self, timer_div: u32, clock_per_ms: u64) -> Box<dyn Timer + Send + Sync>;
}

pub fn new(
    page_table: &mut awkernel_lib::arch::x86_64::page_table::PageTable,
    page_allocator: &mut VecPageAllocator,
) -> TypeApic {
    let mut msr = Msr::new(registers::IA32_APIC_BASE_MSR);

    let cpuid = unsafe { __cpuid(1) };

    // 1 << 21: x2APIC
    // 1 << 31: Hypervisor present
    if cpuid.ecx & (1 << 21) != 0 && cpuid.ecx & (1 << 31) == 0 {
        log::info!("x2APIC is available.");

        // Enable x2APIC
        unsafe {
            let value = msr.read();
            msr.write(value | registers::ENABLE_X2APIC);
        }
    }

    let value = unsafe { msr.read() };

    let is_bsp = (value & (1 << 8)) != 0;
    let apic_base = (value & 0xFFFF_F000) as usize;

    let phy_base = PhyAddr::new(apic_base);
    let virt_base = VirtAddr::new(apic_base);

    if value & registers::ENABLE_X2APIC == 0 {
        log::info!("APIC base address = 0x{apic_base:x}");
    }

    let flags = Flags {
        write: true,
        execute: false,
        cache: false,
        write_through: false,
        device: true,
    };

    if unsafe {
        page_table
            .map_to(virt_base, phy_base, flags, page_allocator)
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

    fn write_timer_div(&mut self, div: u32) {
        registers::XAPIC_TIMER_DIV.write(div, self.apic_base);
    }

    fn read_current_timer_count(&self) -> u32 {
        registers::XAPIC_TIMER_CURRENT_COUNT.read(self.apic_base)
    }

    fn write_timer_initial_count(&mut self, count: u32) {
        registers::XAPIC_TIMER_INITIAL_COUNT.write(count, self.apic_base);
    }

    fn create_timer(&self, timer_div: u32, clock_per_ms: u64) -> Box<dyn Timer + Send + Sync> {
        Box::new(TimerXapic {
            apic_base: self.apic_base,
            timer_div,
            clock_per_ms,
        })
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

    fn write_timer_div(&mut self, div: u32) {
        unsafe { registers::X2APIC_TIMER_DIV.write(div as u64) };
    }

    fn read_current_timer_count(&self) -> u32 {
        unsafe { registers::X2APIC_TIMER_CURRENT_COUNT.read() as u32 }
    }

    fn write_timer_initial_count(&mut self, count: u32) {
        unsafe { registers::X2APIC_TIMER_INITIAL_COUNT.write(count as u64) };
    }

    fn create_timer(&self, timer_div: u32, clock_per_ms: u64) -> Box<dyn Timer + Send + Sync> {
        Box::new(TimerX2apic {
            timer_div,
            clock_per_ms,
        })
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
    fn send_ipi(&mut self, irq: u16, cpu_id: u32) {
        let Some(dst) = awkernel_lib::arch::x86_64::cpu::cpu_id_to_raw_cpu_id(cpu_id as usize)
        else {
            return;
        };

        if let Some(vector) = self.validate_and_convert_irq(irq) {
            self.interrupt(
                dst as u32,
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

    fn irq_range(&self) -> (u16, u16) {
        // IRQ255 is used for preemption
        (32, 255)
    }

    fn irq_range_for_pnp(&self) -> (u16, u16) {
        // IRQ255 is used for preemption
        // IRQ254 is used for wakeup
        // IRQ253 is used for local timer
        (64, 253)
    }

    fn set_pcie_msi(
        &self,
        _segment_number: usize,
        target: u32,
        irq: u16,
        message_data: &mut u32,
        message_address: &mut u32,
        message_address_upper: Option<&mut u32>,
    ) -> Result<IRQ, &'static str> {
        const IS_EDGE_TRIGGER: bool = false;

        unsafe {
            write_volatile(
                message_data,
                (irq as u32) & 0xFF | if IS_EDGE_TRIGGER { 0 } else { 1 << 15 },
            );

            write_volatile(message_address, 0xfee0_0000 | ((target & 0xFF) << 12));

            if let Some(message_address_upper) = message_address_upper {
                write_volatile(message_address_upper, 0);
            }
        }

        Ok(IRQ::Basic(irq))
    }
}

impl InterruptController for X2Apic {
    fn enable_irq(&mut self, irq: u16) {
        // Enable x2APIC
        let mut msr = Msr::new(registers::IA32_APIC_BASE_MSR);
        unsafe {
            let value = msr.read();
            msr.write(value | registers::ENABLE_X2APIC);
        }

        // Set 8th bit of SVR to 1.
        unsafe {
            let mut svr_bits = registers::X2APIC_SPURIOUS_INTERRUPT_VECTOR.read();
            svr_bits |= 1 << 8;
            registers::X2APIC_SPURIOUS_INTERRUPT_VECTOR.write(svr_bits);
        }

        let cpu_id = awkernel_lib::cpu::cpu_id();
        log::info!("x2APIC: IRQ #{irq} has been enabled on CPU#{cpu_id}.");
    }

    fn disable_irq(&mut self, irq: u16) {
        // Set 8th bit of SVR to 0.
        let mut svr_bits = unsafe { registers::X2APIC_SPURIOUS_INTERRUPT_VECTOR.read() };
        svr_bits &= !(1 << 8);
        unsafe { registers::X2APIC_SPURIOUS_INTERRUPT_VECTOR.write(svr_bits) };

        let cpu_id = awkernel_lib::cpu::cpu_id();
        log::info!("x2APIC: IRQ #{irq} has been disabled on CPU#{cpu_id}.");
    }

    fn pending_irqs(&self) -> Box<dyn Iterator<Item = u16>> {
        unimplemented!("`pending_irqs` is not yet implemented in x2APIC.");
    }

    fn send_ipi(&mut self, irq: u16, cpu_id: u32) {
        let Some(dst) = awkernel_lib::arch::x86_64::cpu::cpu_id_to_raw_cpu_id(cpu_id as usize)
        else {
            return;
        };

        if let Some(vector) = self.validate_and_convert_irq(irq) {
            self.interrupt(
                dst as u32,
                registers::DestinationShorthand::NoShorthand,
                registers::IcrFlags::empty(),
                registers::DeliveryMode::Fixed,
                vector,
            );
        }
    }

    fn send_ipi_broadcast(&mut self, irq: u16) {
        if let Some(vector) = self.validate_and_convert_irq(irq) {
            self.interrupt(
                0xFFFF_FFFF,
                registers::DestinationShorthand::AllIncludingSelf,
                registers::IcrFlags::empty(),
                registers::DeliveryMode::Fixed,
                vector,
            )
        }
    }

    fn send_ipi_broadcast_without_self(&mut self, irq: u16) {
        if let Some(vector) = self.validate_and_convert_irq(irq) {
            self.interrupt(
                0xFFFF_FFFF,
                registers::DestinationShorthand::AllExcludingSelf,
                registers::IcrFlags::empty(),
                registers::DeliveryMode::Fixed,
                vector,
            )
        }
    }

    fn irq_range(&self) -> (u16, u16) {
        // IRQ255 is used for preemption
        (32, 255)
    }

    fn irq_range_for_pnp(&self) -> (u16, u16) {
        // IRQ255 is used for preemption
        // IRQ254 is used for wakeup
        // IRQ253 is used for local timer
        (64, 253)
    }

    fn init_non_primary(&mut self) {
        // Nothing to do.
    }

    fn eoi(&mut self) {
        unsafe { registers::X2APIC_EOI.write(0) };
    }

    fn set_pcie_msi(
        &self,
        segment_number: usize,
        target: u32,
        irq: u16,
        message_data: &mut u32,
        message_address: &mut u32,
        message_address_upper: Option<&mut u32>,
    ) -> Result<IRQ, &'static str> {
        assert!(irq < 256);

        let remap_info = interrupt_remap::allocate_remapping_entry(
            segment_number,
            target,
            irq as u8,
            false,
            false,
        )
        .ok_or("Failed to allocate an Interrupt Remapping Table Entry.")?;

        // See
        // Intel® Virtualization Technology for Directed I/O Architecture Specification, Rev. 4.1
        // Figure 5-4. MSI-X Programming

        let interrupt_index = remap_info.get_entry_id() as u32;

        let val_lower = 0xfee << 20
            | 1 << 4 // Interrupt Remappable Format
            | (interrupt_index & 0b0111_1111_1111_1111) << 5
            | (interrupt_index & 0b1000_0000_0000_0000) << 2;

        unsafe {
            write_volatile(message_data, 0);
            write_volatile(message_address, val_lower);
            if let Some(addr_upper) = message_address_upper {
                write_volatile(addr_upper, 0);
            }
        }

        Ok(IRQ::X86InterruptRemap { irq, remap_info })
    }
}

pub struct TimerXapic {
    apic_base: usize,
    timer_div: u32,
    clock_per_ms: u64,
}

impl awkernel_lib::timer::Timer for TimerXapic {
    fn irq_id(&self) -> u16 {
        TIMER_IRQ as u16
    }

    fn reset(&self, dur: Duration) {
        let ns = dur.as_nanos();

        let initial_count = (self.clock_per_ms as u128) * ns / 1_000_000;
        let initial_count = if initial_count > 0xFFFF_FFFF {
            0xFFFF_FFFF
        } else {
            initial_count as u32
        };

        if initial_count == 0 {
            log::warn!("TimerXapic::reset(): initial_count is 0");
        }

        registers::XAPIC_LVT_TIMER.write(
            TIMER_IRQ as u32 | registers::LVT_TIMER_PERIODIC,
            self.apic_base,
        );
        registers::XAPIC_TIMER_DIV.write(self.timer_div, self.apic_base);
        registers::XAPIC_TIMER_INITIAL_COUNT.write(initial_count, self.apic_base);
    }

    fn disable(&self) {
        registers::XAPIC_LVT_TIMER.write(0, self.apic_base);
    }
}

pub struct TimerX2apic {
    timer_div: u32,
    clock_per_ms: u64,
}

impl awkernel_lib::timer::Timer for TimerX2apic {
    fn irq_id(&self) -> u16 {
        TIMER_IRQ as u16
    }

    fn reset(&self, dur: Duration) {
        let ns = dur.as_nanos();

        let initial_count = (self.clock_per_ms as u128) * ns / 1_000_000;
        let initial_count = if initial_count > 0xFFFF_FFFF {
            0xFFFF_FFFF
        } else {
            initial_count as u64
        };

        if initial_count == 0 {
            log::warn!("TimerXapic::reset(): initial_count is 0");
        }

        unsafe {
            registers::X2APIC_LVT_TIMER
                .write(TIMER_IRQ as u64 | registers::LVT_TIMER_PERIODIC as u64);
            registers::X2APIC_TIMER_DIV.write(self.timer_div as u64);
            registers::X2APIC_TIMER_INITIAL_COUNT.write(initial_count);
        }
    }

    fn disable(&self) {
        unsafe {
            registers::X2APIC_LVT_TIMER.write(0);
        }
    }
}
