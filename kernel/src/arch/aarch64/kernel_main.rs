use super::{
    bsp::raspi,
    cpu,
    driver::uart::{DevUART, Uart},
    mmu, serial,
};
use crate::{
    config::{BACKUP_HEAP_SIZE, HEAP_SIZE, HEAP_START},
    heap,
    kernel_info::KernelInfo,
};
use awkernel_lib::delay::wait_forever;
use core::{
    ptr::{read_volatile, write_volatile},
    sync::atomic::{AtomicBool, Ordering},
};

static mut PRIMARY_READY: bool = false;
static PRIMARY_INITIALIZED: AtomicBool = AtomicBool::new(false);

/// Entry point from assembly code.
#[no_mangle]
pub unsafe extern "C" fn kernel_main() -> ! {
    awkernel_aarch64::init_cpacr_el1(); // Enable floating point numbers.

    if cpu::core_pos() == 0 {
        raspi::start_non_primary(); // Wake non-primary CPUs up.
        primary_cpu();
    } else {
        while !unsafe { read_volatile(&PRIMARY_READY) } {}
        non_primary_cpu();
    }

    wait_forever();
}

unsafe fn primary_cpu() {
    DevUART::init(serial::UART_CLOCK, serial::UART_BAUD);

    match awkernel_aarch64::get_current_el() {
        0 => DevUART::unsafe_puts("EL0\n"),
        1 => DevUART::unsafe_puts("EL1\n"),
        2 => DevUART::unsafe_puts("EL2\n"),
        3 => DevUART::unsafe_puts("EL3\n"),
        _ => (),
    }

    // Initialize MMU.
    mmu::init_memory_map();
    if mmu::init().is_none() {
        DevUART::unsafe_puts("Failed to init MMU.\n");
        wait_forever();
    }

    // Start non-primary CPUs.
    write_volatile(&mut PRIMARY_READY, true);

    // Enable MMU.
    mmu::enable();

    awkernel_lib::arch::aarch64::init_primary(); // Initialize timer.

    let backup_start = HEAP_START as usize;
    let backup_size = BACKUP_HEAP_SIZE as usize;
    let primary_start = (HEAP_START + BACKUP_HEAP_SIZE) as usize;
    let primary_size = HEAP_SIZE as usize;

    heap::init(primary_start, primary_size, backup_start, backup_size); // Enable heap allocator.
    serial::init(); // Enable serial port.

    PRIMARY_INITIALIZED.store(true, Ordering::SeqCst);

    log::info!("Waking non-primary CPUs up.");

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: 0,
    };
    crate::heap::TALLOC.use_primary(); // use primary allocator in userland
    crate::main::<()>(kernel_info);
}

unsafe fn non_primary_cpu() {
    mmu::enable();

    while !PRIMARY_INITIALIZED.load(Ordering::SeqCst) {
        core::hint::spin_loop();
    }

    unsafe { awkernel_lib::arch::aarch64::init_non_primary() }; // Initialize timer.

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: cpu::core_pos(),
    };

    awkernel_aarch64::init_cpacr_el1(); // Enable floating point numbers.
    crate::heap::TALLOC.use_primary(); // use primary allocator in userland
    crate::main::<()>(kernel_info);
}
