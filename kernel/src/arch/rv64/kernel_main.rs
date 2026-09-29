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

#[no_mangle]
pub unsafe extern "C" fn riscv_handle_ipi() {
    awkernel_lib::interrupt::handle_irqs(true);
}

#[no_mangle]
pub unsafe extern "C" fn riscv_handle_timer() {
    awkernel_lib::interrupt::handle_irqs(true);
}

unsafe fn init_interrupt_controller() {
    use super::interrupt_controller::RiscvPlic;
    use alloc::boxed::Box;

    const PLIC_BASE: usize = 0x0c000000;
    const NUM_SOURCES: u16 = 128;
    let plic = Box::new(RiscvPlic::new(PLIC_BASE, NUM_SOURCES));
    awkernel_lib::interrupt::register_interrupt_controller(plic);

    core::arch::asm!("csrrs t0, mie, {}", in(reg) 1 << 3);
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

    awkernel_lib::arch::rv64::init_page_allocator();
    awkernel_lib::arch::rv64::init_kernel_space();
    awkernel_lib::arch::rv64::activate_kernel_space();

    let backup_start = HEAP_START;
    let backup_size = BACKUP_HEAP_SIZE;
    let primary_start = HEAP_START + BACKUP_HEAP_SIZE;
    let primary_size = HEAP_SIZE;

    heap::init_primary(primary_start, primary_size);
    heap::init_backup(backup_start, backup_size);
    heap::TALLOC.use_primary_then_backup();

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

    console::init(UART_BASE);

    init_interrupt_controller();

    log::info!("AWkernel RV64 PLIC interrupt controller initialized");

    NUM_CPUS.store(4, Ordering::Release);
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

    awkernel_lib::interrupt::init_non_primary();
    heap::TALLOC.use_primary_then_backup();

    let num_cpu = NUM_CPUS.load(Ordering::Acquire);

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: hartid,
        num_cpu,
    };

    crate::main::<()>(kernel_info);
}
