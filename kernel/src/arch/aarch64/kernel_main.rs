//! # Boot process
//!
//! 1. The entrypoint, `_start` in `kernel/asm/aarch64/boot.S`, is called.
//! 2. [`kernel_main`] is called.
//! 3. For the primary CPU, [`primary_cpu`] is called and some initializations are performed.
//! 4. For non-primary CPUs, [`non_primary_cpu`] is called.

use super::bsp::DeviceTreeRef;
use crate::{
    arch::aarch64::bsp::SoC,
    config::{BACKUP_HEAP_SIZE, DMA_SIZE, HEAP_START},
    kernel_info::KernelInfo,
};
use awkernel_aarch64::{dsb_ish, dsb_ishst, dsb_sy, isb, tlbi_vmalle1is};
use awkernel_lib::{
    console::{unsafe_print_hex_u32, unsafe_puts},
    delay::wait_forever,
    dma_pool, heap,
};
use core::{
    arch::asm,
    ptr::{addr_of, addr_of_mut, read_volatile, write_volatile},
    sync::atomic::{AtomicBool, Ordering},
};

static mut CPU_READY: usize = 0;
static PRIMARY_INITIALIZED_1: AtomicBool = AtomicBool::new(false);
static PRIMARY_INITIALIZED_2: AtomicBool = AtomicBool::new(false);

static mut TTBR0_EL1: usize = 0;

/// The entry point from `boot.S`.
#[no_mangle]
pub unsafe extern "C" fn kernel_main(device_tree_base: usize) -> ! {
    awkernel_aarch64::init_cpacr_el1(); // Enable floating point numbers.

    awkernel_lib::delay::wait_millisec(10);

    if awkernel_lib::cpu::cpu_id() == 0 {
        primary_cpu(device_tree_base);
    } else {
        let cpu_id = awkernel_lib::cpu::cpu_id();

        while read_volatile(addr_of!(CPU_READY)) != cpu_id {}
        non_primary_cpu();
    }

    wait_forever();
}

/// 1. Initialize the device (UART, etc.).
/// 2. Initialize the virtual memory.
/// 3. Enable MMU.
/// 4. Start non-primary CPUs.
/// 5. Enable heap allocator.
/// 6. Board specific initialization (Interrupt controller, etc).
unsafe fn primary_cpu(device_tree_base: usize) {
    #[cfg(not(feature = "raspi5"))]
    let device_tree = load_device_tree(device_tree_base);
    #[cfg(not(feature = "raspi5"))]
    let mut initializer = super::bsp::SoCInitializer::new(device_tree, device_tree_base);
    #[cfg(feature = "raspi5")]
    let mut initializer = super::bsp::SoCInitializer::new(device_tree_base);

    // 1. Initialize device (UART, etc.).
    if initializer.init_device().is_err() {
        wait_forever();
    }

    match awkernel_aarch64::get_current_el() {
        0 => unsafe_puts("EL0\r\n"),
        1 => unsafe_puts("EL1\r\n"),
        2 => unsafe_puts("EL2\r\n"),
        3 => unsafe_puts("EL3\r\n"),
        _ => unsafe_puts("EL other\r\n"),
    }

    unsafe_puts("Device Tree: 0x");
    unsafe_print_hex_u32(device_tree_base as u32);
    unsafe_puts("\r\n");

    // 2. Initialize the virtual memory.
    let vm = match initializer.init_virtual_memory() {
        Ok(vm) => vm,
        Err(msg) => {
            unsafe_puts("failed to initialize the virtual memory\r\n");
            unsafe_puts(msg);
            unsafe_puts("\r\n");
            wait_forever();
        }
    };

    let Some(ttbr0) = vm.get_ttbr0_addr() else {
        unsafe_puts("failed to get TTBR0_EL0\r\n");
        wait_forever();
    };

    write_volatile(addr_of_mut!(TTBR0_EL1), ttbr0);

    dsb_sy();

    // Invalidate all TLB
    dsb_ishst();
    tlbi_vmalle1is();
    dsb_ish();
    isb();

    // 3. Enable MMU.
    super::vm::enable(ttbr0);

    // 4. Start non-primary CPUs.
    let cpu_ready = read_volatile(addr_of!(CPU_READY));
    write_volatile(addr_of_mut!(CPU_READY), cpu_ready + 1);
    super::vm::flush_cache();

    unsafe_puts("The virtual memory has been successfully enabled.\r\n");

    awkernel_lib::arch::aarch64::init_primary(); // Initialize timer.

    awkernel_lib::delay::wait_sec(3);

    // 5. Enable heap allocator.
    let backup_start = HEAP_START;
    let backup_size = BACKUP_HEAP_SIZE;
    let primary_start = HEAP_START + BACKUP_HEAP_SIZE;
    let primary_size = vm.get_heap_size().unwrap() - BACKUP_HEAP_SIZE;

    heap::init_primary(primary_start, primary_size);
    heap::init_backup(backup_start, backup_size);

    log::info!("Waking non-primary CPUs up.");
    PRIMARY_INITIALIZED_1.store(true, Ordering::SeqCst);

    heap::TALLOC.use_primary_then_backup(); // use backup allocator

    for i in 0..initializer.get_segment_count() {
        if let Some(dma_pool) = initializer.get_dma_pool(i) {
            dma_pool::init_dma_pool(i, dma_pool, DMA_SIZE);
        }
    }

    // 6. Board specific initialization (Interrupt controller, PCIe, etc).
    if let Err(msg) = initializer.init() {
        unsafe_puts("failed init()\r\n");
        unsafe_puts(msg);
        unsafe_puts("\r\n");
        wait_forever();
    }

    log::info!(
        "Primary heap: 0x{:016x} - {:016x} ({}[MiB])",
        primary_start,
        primary_start + primary_size,
        primary_size >> 20
    );

    log::info!(
        "Backup heap : 0x{:016x} - {:016x} ({}[MiB])",
        backup_start,
        backup_start + backup_size,
        backup_size >> 20
    );

    if awkernel_aarch64::spsel::get() & 1 == 0 {
        log::info!("Use SP_EL0.");
    } else {
        log::info!("Use SP_ELx.");
    }

    // log::info!("{device_tree}");

    #[cfg(feature = "raspi")]
    if let Some(framebuffer) = awkernel_drivers::ic::rpi::lfb::get_framebuffer_info() {
        use embedded_graphics::{
            mono_font::{ascii::FONT_10X20, MonoTextStyle},
            prelude::*,
            text::{Alignment, Text},
        };
        use embedded_graphics_core::pixelcolor::Rgb888;

        let character_style = MonoTextStyle::new(&FONT_10X20, Rgb888::new(255, 255, 255));

        let text = "Welcome to Autoware Kernel v0.1";
        let _ = Text::with_alignment(
            text,
            framebuffer.bounding_box().center() + Point::new(0, 15),
            character_style,
            Alignment::Center,
        )
        .draw(framebuffer);
    }

    PRIMARY_INITIALIZED_2.store(true, Ordering::SeqCst);

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: 0,
    };

    crate::main::<()>(kernel_info);
}

/// 1. Enable the virtual memory.
/// 2. Wait until the primary CPU is enabled.
/// 3. Initialization for non-primary CPUs.
unsafe fn non_primary_cpu() {
    let mut ttbr0;

    // flush TLB
    asm!(
        "
        dsb     sy

        dsb     ishst
        tlbi    vmalle1is
        dsb     ish
        isb

        ldr     {ttbr0}, [{ttbr0_addr}]
        isb
        ",
        ttbr0 = out(reg) ttbr0,
        ttbr0_addr = in(reg) addr_of!(TTBR0_EL1),
    );

    let cpu_ready = read_volatile(addr_of!(CPU_READY));

    super::vm::enable(ttbr0);
    write_volatile(addr_of_mut!(CPU_READY), cpu_ready + 1);
    super::vm::flush_cache();

    // 2. Wait until the primary CPU is enabled.
    while !PRIMARY_INITIALIZED_1.load(Ordering::SeqCst) {
        awkernel_lib::delay::wait_millisec(1);
    }

    // 3. Initialization for non-primary CPUs.
    unsafe { awkernel_lib::arch::aarch64::init_non_primary() }; // Initialize timer.

    awkernel_lib::interrupt::init_non_primary(); // Initialize the interrupt controller.

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: awkernel_lib::cpu::cpu_id(),
    };

    heap::TALLOC.use_primary_then_backup(); // use backup allocator

    // 3. Wait again
    while !PRIMARY_INITIALIZED_2.load(Ordering::SeqCst) {
        awkernel_lib::delay::wait_millisec(1);
    }

    crate::main::<()>(kernel_info);
}

unsafe fn load_device_tree(device_tree_base: usize) -> DeviceTreeRef {
    if let Ok(tree) = awkernel_lib::device_tree::from_address(device_tree_base) {
        tree
    } else {
        wait_forever();
    }
}
