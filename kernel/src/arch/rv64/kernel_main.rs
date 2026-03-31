use super::console;
use crate::{
    config::{BACKUP_HEAP_SIZE, HEAP_START},
    kernel_info::KernelInfo,
};
use awkernel_lib::{cpu, heap};
use core::{
    arch::global_asm,
    fmt::Write,
    sync::atomic::{AtomicBool, Ordering},
};
use ns16550a::Uart;

const UART_BASE: usize = 0x1000_0000;

const HEAP_SIZE: usize = 1024 * 1024 * 512;

static PRIMARY_INITIALIZED: AtomicBool = AtomicBool::new(false);
pub(super) static NUM_CPUS: core::sync::atomic::AtomicUsize =
    core::sync::atomic::AtomicUsize::new(4);

global_asm!(include_str!("boot.S"));

/// M-mode software interrupt (IPI) handler called from assembly
///
/// # Safety
///
/// This function is called from the M-mode trap handler in boot.S
#[no_mangle]
pub unsafe extern "C" fn riscv_handle_ipi() {
    // Handle all pending interrupts, including IPI preemption
    awkernel_lib::interrupt::handle_irqs(true);
}

/// M-mode timer interrupt handler called from assembly
///
/// # Safety
///
/// This function is called from the M-mode trap handler in boot.S
#[no_mangle]
pub unsafe extern "C" fn riscv_handle_timer() {
    // Timer interrupt is already disabled in assembly by setting mtimecmp to max
    // Handle any pending interrupts (the timer handler will be invoked if registered)
    awkernel_lib::interrupt::handle_irqs(true);
}

/// Initialize and register the RISC-V ACLINT timer.
///
/// # Safety
///
/// Must be called after heap initialization on the primary hart.
unsafe fn init_timer() {
    use super::timer::RiscvTimer;
    use alloc::boxed::Box;

    const TIMER_IRQ: u16 = 5;
    let timer = Box::new(RiscvTimer::new(TIMER_IRQ));
    awkernel_lib::timer::register_timer(timer);
}

#[no_mangle]
pub unsafe extern "C" fn kernel_main() {
    unsafe { crate::config::init() };

    let hartid: usize = cpu::cpu_id();
    if hartid == 0 {
        primary_hart(hartid);
    } else {
        non_primary_hart(hartid);
    }
}

unsafe fn primary_hart(hartid: usize) {
    super::console::init_port(UART_BASE);

    // Initialize memory management (page allocator)
    awkernel_lib::arch::rv64::init_page_allocator();

    // Initialize virtual memory system
    awkernel_lib::arch::rv64::init_kernel_space();

    // Activate virtual memory (enable MMU and page tables)
    awkernel_lib::arch::rv64::activate_kernel_space();

    // setup the VM
    let backup_start = HEAP_START;
    let backup_size = BACKUP_HEAP_SIZE;
    let primary_start = HEAP_START + BACKUP_HEAP_SIZE;
    let primary_size = HEAP_SIZE;

    // enable heap allocator
    heap::init_primary(primary_start, primary_size);
    heap::init_backup(backup_start, backup_size);
    heap::TALLOC.use_primary_then_backup();

    // initialize serial device and dump booting logo
    let mut port = Uart::new(UART_BASE);
    port.init(
        ns16550a::WordLength::EIGHT,
        ns16550a::StopBits::ONE,
        ns16550a::ParityBit::DISABLE,
        ns16550a::ParitySelect::EVEN,
        ns16550a::StickParity::DISABLE,
        ns16550a::Break::DISABLE,
        ns16550a::DMAMode::MODE0,
        ns16550a::Divisor::BAUD115200,
    );

    let _ = port.write_str("\r\nAwkernel is booting\r\n\r\n");

    // initialize console driver to which log messages are dumped
    console::init(UART_BASE);

    // Initialize architecture-specific features (delay/uptime counters)
    awkernel_lib::arch::rv64::init_primary();

    // Initialize and register the RISC-V timer
    init_timer();

    // Enable machine software interrupts for IPIs
    core::arch::asm!("csrrs t0, mie, {}", in(reg) 1 << 3);

    log::info!("AWkernel RV64 timer initialized");

    // wake up another harts
    NUM_CPUS.store(4, Ordering::Release); // TODO: detect from device tree
    PRIMARY_INITIALIZED.store(true, Ordering::SeqCst);

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: hartid,
        num_cpu: NUM_CPUS.load(Ordering::Acquire),
    };

    crate::main::<()>(kernel_info);
}

unsafe fn non_primary_hart(hartid: usize) {
    while !PRIMARY_INITIALIZED.load(Ordering::SeqCst) {
        core::hint::spin_loop();
    }

    awkernel_lib::arch::rv64::init_non_primary();
    heap::TALLOC.use_primary_then_backup();

    let num_cpu = NUM_CPUS.load(Ordering::Acquire);

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: hartid,
        num_cpu,
    };

    crate::main::<()>(kernel_info);
}
