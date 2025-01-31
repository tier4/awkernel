use super::console;
use crate::{
    config::{BACKUP_HEAP_SIZE, HEAP_START},
    kernel_info::KernelInfo,
};
use awkernel_lib::{cpu, heap};
use core::{
    arch::global_asm,
    fmt::Write,
    //    mem::MaybeUninit,
    sync::atomic::{AtomicBool, Ordering},
};
use ns16550a::Uart;

const UART_BASE: usize = 0x1000_0000;

const HEAP_SIZE: usize = 1024 * 1024 * 512;

// TODO: set initial stack 4MB for each CPU on 0x8040_0000. see boot.S
// const MAX_HARTS: usize = 8;
// const INITIAL_STACK: usize = 0x8040_0000;
// const INITIAL_STACK_SIZE: usize = 0x0040_0000;
// #[repr(align(4096))]
// struct InitialStack([MaybeUninit<u8>; INITIAL_STACK_SIZE * MAX_HARTS]);
// #[no_mangle]
// static INITIAL_STACK: InitialStack = unsafe { MaybeUninit::uninit().assume_init() };

static PRIMARY_INITIALIZED: AtomicBool = AtomicBool::new(false);

global_asm!(include_str!("boot.S"));

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
    // setup interrupt; TODO;

    super::console::init_port(UART_BASE);

    // setup the VM
    let backup_start = HEAP_START;
    let backup_size = BACKUP_HEAP_SIZE;
    let primary_start = HEAP_START + BACKUP_HEAP_SIZE;
    let primary_size = HEAP_SIZE;

    // enable heap allocator
    heap::init_primary(primary_start, primary_size);
    heap::init_backup(backup_start, backup_size);
    heap::TALLOC.use_primary_then_backup(); // use backup allocator

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

    let _ = port.write_str("\r\nautoware kernel is booting\r\n\r\n");

    // initialize console driver to which log messages are dumped
    console::init(UART_BASE);

    // switch to S-Mode; TODO;
    // * currntly this impl. holds both kernel and userland
    // * in M-Mode, which is the highest priority.

    // wake up another harts
    PRIMARY_INITIALIZED.store(true, Ordering::SeqCst);

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: hartid,
        num_cpu: 4, // TODO: get the number of CPUs
    };

    crate::main::<()>(kernel_info);
}

unsafe fn non_primary_hart(hartid: usize) {
    while !PRIMARY_INITIALIZED.load(Ordering::SeqCst) {
        core::hint::spin_loop();
    }

    heap::TALLOC.use_primary_then_backup(); // use backup allocator

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: hartid,
        num_cpu: 4, // TODO: get the number of CPUs
    };

    crate::main::<()>(kernel_info);
}
