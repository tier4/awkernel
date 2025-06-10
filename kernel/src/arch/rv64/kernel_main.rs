use super::console;
use crate::{config::BACKUP_HEAP_SIZE, kernel_info::KernelInfo};
use awkernel_lib::{cpu, heap};
use core::{
    arch::global_asm,
    sync::atomic::{AtomicBool, Ordering},
};

const UART_BASE: usize = 0x1000_0000;

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

// Simple UART functions for early debugging
unsafe fn simple_uart_init() {
    // Basic 16550 UART initialization
    let uart_base = UART_BASE as *mut u8;

    // Disable interrupts
    uart_base.add(1).write_volatile(0x00);

    // Enable DLAB to set baud rate
    uart_base.add(3).write_volatile(0x80);

    // Set baud rate divisor (115200 baud)
    uart_base.add(0).write_volatile(0x03); // Low byte
    uart_base.add(1).write_volatile(0x00); // High byte

    // 8 bits, no parity, one stop bit
    uart_base.add(3).write_volatile(0x03);

    // Enable FIFO, clear TX/RX queues
    uart_base.add(2).write_volatile(0xC7);

    // Enable interrupts, RTS/DTR set
    uart_base.add(4).write_volatile(0x0B);
}

unsafe fn simple_uart_write_str(s: &str) {
    let uart_base = UART_BASE as *mut u8;

    for byte in s.bytes() {
        // Wait for transmit holding register to be empty
        while uart_base.add(5).read_volatile() & 0x20 == 0 {}

        // Write the byte
        uart_base.add(0).write_volatile(byte);
    }
}

/// Initialize UART for early debugging and console output.
unsafe fn init_uart() {
    simple_uart_init();
    simple_uart_write_str("\r\n=== AWkernel RV64 Starting ===\r\n");

    super::console::init_port(UART_BASE);
    simple_uart_write_str("Console port initialized\r\n");

    // Initialize full UART driver
    let mut port = ns16550a::Uart::new(UART_BASE);
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

    use core::fmt::Write;
    let _ = port.write_str("UART driver initialized\r\n");
}

/// Initialize memory management including page allocator and virtual memory.
unsafe fn init_memory_management() {
    simple_uart_write_str("Initializing page allocator...\r\n");
    awkernel_lib::arch::rv64::init_page_allocator();

    simple_uart_write_str("Initializing kernel space...\r\n");
    awkernel_lib::arch::rv64::init_kernel_space();

    simple_uart_write_str("Activating kernel space...\r\n");
    awkernel_lib::arch::rv64::activate_kernel_space();

    simple_uart_write_str("Virtual memory system initialized\r\n");
}

/// Setup dynamic heap allocation based on available memory.
unsafe fn init_heap_allocation() {
    simple_uart_write_str("Setting up heap allocation...\r\n");

    extern "C" {
        fn ekernel();
    }

    let heap_start = (ekernel as usize + 0xfff) & !0xfff; // Align to 4K
    let backup_size = BACKUP_HEAP_SIZE;
    let total_heap_size = awkernel_lib::arch::rv64::get_heap_size();

    if total_heap_size <= backup_size {
        // Use minimal heap if not enough memory
        simple_uart_write_str("Using minimal heap configuration\\r\\n");
        let primary_size = 64 * 1024 * 1024; // 64MB minimum
        heap::init_primary(heap_start + backup_size, primary_size);
        heap::init_backup(heap_start, backup_size);
    } else {
        // Use dynamic calculation
        simple_uart_write_str("Using dynamic heap configuration\\r\\n");
        let primary_size = total_heap_size - backup_size;
        heap::init_primary(heap_start + backup_size, primary_size);
        heap::init_backup(heap_start, backup_size);
    }

    heap::TALLOC.use_primary_then_backup();
    simple_uart_write_str("Heap allocation complete\\r\\n");
}

/// Initialize timer and interrupt controller for RV64.
unsafe fn init_timer_and_interrupts() {
    use super::interrupt_controller::RiscvPlic;
    use super::timer::RiscvTimer;
    use alloc::boxed::Box;

    simple_uart_write_str("Initializing RISC-V interrupt controller...\\r\\n");

    // RISC-V PLIC (Platform-Level Interrupt Controller) base address
    // This should match the device tree or platform specification
    const PLIC_BASE: usize = 0x0c000000;
    const NUM_SOURCES: u16 = 128; // Typical PLIC configuration
    const TIMER_IRQ: u16 = 5; // Machine timer interrupt is typically IRQ 5 for PLIC

    // Initialize and register interrupt controller
    let plic = Box::new(RiscvPlic::new(PLIC_BASE, NUM_SOURCES));
    awkernel_lib::interrupt::register_interrupt_controller(plic);

    simple_uart_write_str("Initializing RISC-V timer...\\r\\n");

    // Initialize and register timer
    let timer = Box::new(RiscvTimer::new(TIMER_IRQ));
    awkernel_lib::timer::register_timer(timer);

    simple_uart_write_str("Timer and interrupt controller initialized\\r\\n");
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

/// Primary CPU initialization sequence.
/// 1. Initialize UART for early debugging
/// 2. Initialize memory management (page allocator and virtual memory)
/// 3. Setup dynamic heap allocation
/// 4. Initialize architecture-specific features
/// 5. Initialize console driver
/// 6. Initialize timer and interrupt controller
/// 7. Wake up secondary CPUs
/// 8. Start the kernel main function
unsafe fn primary_hart(hartid: usize) {
    // 1. Initialize UART for early debugging
    init_uart();

    // 2. Initialize memory management
    init_memory_management();

    // 3. Setup dynamic heap allocation
    init_heap_allocation();

    // 4. Initialize architecture-specific features
    awkernel_lib::arch::rv64::init_primary();

    // 5. Initialize console driver
    console::init(UART_BASE);

    // 6. Initialize timer and interrupt controller
    init_timer_and_interrupts();

    log::info!("AWkernel RV64 primary CPU initialization complete");

    // 7. Wake up secondary CPUs
    PRIMARY_INITIALIZED.store(true, Ordering::SeqCst);

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: hartid,
        num_cpu: 4, // TODO: get the number of CPUs from device tree
    };

    crate::main::<()>(kernel_info);
}

/// Secondary CPU initialization sequence.
/// 1. Wait for primary CPU to complete initialization
/// 2. Initialize architecture-specific features for non-primary CPUs
/// 3. Setup heap allocator usage
/// 4. Start the kernel main function
unsafe fn non_primary_hart(hartid: usize) {
    // 1. Wait for primary CPU to complete initialization
    while !PRIMARY_INITIALIZED.load(Ordering::SeqCst) {
        core::hint::spin_loop();
    }

    // 2. Initialize architecture-specific features for non-primary CPUs
    awkernel_lib::arch::rv64::init_non_primary();
    awkernel_lib::interrupt::init_non_primary();

    // 3. Setup heap allocator usage
    heap::TALLOC.use_primary_then_backup();

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: hartid,
        num_cpu: 4, // TODO: get the number of CPUs from device tree
    };

    crate::main::<()>(kernel_info);
}
