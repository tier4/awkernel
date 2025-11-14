use super::console;
use crate::{config::BACKUP_HEAP_SIZE, kernel_info::KernelInfo};
use awkernel_lib::{cpu, heap};
use core::{
    arch::global_asm,
    sync::atomic::{AtomicBool, Ordering},
};

const UART_BASE: usize = 0x1000_0000;

extern "C" {
    static dtb_ptr: usize;
}

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

/// Write to UART during early boot for debugging
///
/// # Safety
///
/// UART must be initialized before calling this function
#[inline]
unsafe fn uart_debug_puts(s: &str) {
    let uart_base = UART_BASE as *mut u8;
    const LSR: usize = 5;
    const THR: usize = 0;

    for byte in s.bytes() {
        while uart_base.add(LSR).read_volatile() & 0x20 == 0 {
            core::hint::spin_loop();
        }
        uart_base.add(THR).write_volatile(byte);
    }
}

fn register_boot_dtb_pointer() {
    unsafe {
        let addr = dtb_ptr;
        if addr != 0 {
            awkernel_lib::arch::rv64::set_boot_dtb_ptr(addr);
        }
    }
}

/// Initialize UART for early debugging and console output.
///
/// # Safety
///
/// Must be called during early boot on the primary hart.
unsafe fn init_uart() {
    let uart_base = UART_BASE as *mut u8;

    // 16550 UART register offsets
    const IER: usize = 1;
    const FCR: usize = 2;
    const LCR: usize = 3;
    const MCR: usize = 4;
    const LSR: usize = 5;
    const THR: usize = 0;

    // Initialize 16550 UART for early debugging
    uart_base.add(IER).write_volatile(0x00); // Disable interrupts
    uart_base.add(LCR).write_volatile(0x80); // Enable DLAB
    uart_base.add(THR).write_volatile(0x03); // Baud rate divisor low
    uart_base.add(IER).write_volatile(0x00); // Baud rate divisor high
    uart_base.add(LCR).write_volatile(0x03); // 8N1
    uart_base.add(FCR).write_volatile(0xC7); // Enable FIFO
    uart_base.add(MCR).write_volatile(0x0B); // RTS/DTR

    // Helper to write strings during early boot
    let uart_puts = |s: &str| {
        for byte in s.bytes() {
            while uart_base.add(LSR).read_volatile() & 0x20 == 0 {
                core::hint::spin_loop();
            }
            uart_base.add(THR).write_volatile(byte);
        }
    };

    uart_puts("\r\n=== AWkernel RV64 Starting ===\r\n");

    super::console::init_port(UART_BASE);
    uart_puts("Console port initialized\r\n");

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
///
/// # Safety
///
/// Must be called after heap initialization on the primary hart.
unsafe fn init_memory_management() {
    uart_debug_puts("Initializing page allocator...\r\n");
    awkernel_lib::arch::rv64::init_page_allocator();

    uart_debug_puts("Initializing kernel space...\r\n");
    awkernel_lib::arch::rv64::init_kernel_space();

    uart_debug_puts("Activating kernel space...\r\n");
    awkernel_lib::arch::rv64::activate_kernel_space();

    uart_debug_puts("Virtual memory system initialized\r\n");
}

/// Setup dynamic heap allocation based on available memory.
///
/// # Safety
///
/// Must be called before memory management initialization on the primary hart.
unsafe fn init_heap_allocation() {
    uart_debug_puts("Setting up heap allocation...\r\n");

    extern "C" {
        fn ekernel();
    }

    let heap_start = (ekernel as usize + 0xfff) & !0xfff; // Align to 4K
    let backup_size = BACKUP_HEAP_SIZE;
    let total_heap_size = awkernel_lib::arch::rv64::get_heap_size();

    if total_heap_size <= backup_size {
        // Use minimal heap if not enough memory
        uart_debug_puts("Using minimal heap configuration\r\n");
        let primary_size = 64 * 1024 * 1024; // 64MB minimum
        heap::init_primary(heap_start + backup_size, primary_size);
        heap::init_backup(heap_start, backup_size);
    } else {
        // Use dynamic calculation
        uart_debug_puts("Using dynamic heap configuration\r\n");
        let primary_size = total_heap_size - backup_size;
        heap::init_primary(heap_start + backup_size, primary_size);
        heap::init_backup(heap_start, backup_size);
    }

    heap::TALLOC.use_primary_then_backup();
    uart_debug_puts("Heap allocation complete\r\n");
}

/// Initialize timer and interrupt controller for RV64.
///
/// # Safety
///
/// Must be called after heap and memory management initialization on the primary hart.
unsafe fn init_timer_and_interrupts() {
    use super::interrupt_controller::RiscvPlic;
    use super::timer::RiscvTimer;
    use alloc::boxed::Box;

    uart_debug_puts("Initializing RISC-V interrupt controller...\r\n");

    // RISC-V PLIC (Platform-Level Interrupt Controller) base address
    // This should match the device tree or platform specification
    const PLIC_BASE: usize = 0x0c000000;
    const NUM_SOURCES: u16 = 128; // Typical PLIC configuration
    const TIMER_IRQ: u16 = 5; // Machine timer interrupt is typically IRQ 5 for PLIC

    // Initialize and register interrupt controller
    let plic = Box::new(RiscvPlic::new(PLIC_BASE, NUM_SOURCES));
    awkernel_lib::interrupt::register_interrupt_controller(plic);

    uart_debug_puts("Initializing RISC-V timer...\r\n");

    // Initialize and register timer
    let timer = Box::new(RiscvTimer::new(TIMER_IRQ));
    awkernel_lib::timer::register_timer(timer);

    uart_debug_puts("Timer and interrupt controller initialized\r\n");
}

#[no_mangle]
pub unsafe extern "C" fn kernel_main() {
    unsafe { crate::config::init() };

    register_boot_dtb_pointer();

    let hartid: usize = cpu::cpu_id();
    if hartid == 0 {
        primary_hart(hartid);
    } else {
        non_primary_hart(hartid);
    }
}

/// Primary CPU initialization sequence.
/// 1. Initialize UART for early debugging
/// 2. Setup heap allocation FIRST (required for page tables)
/// 3. Initialize memory management (page allocator and virtual memory)
/// 4. Initialize architecture-specific features
/// 5. Initialize console driver
/// 6. Initialize timer and interrupt controller
/// 7. Detect CPU count from device tree
/// 8. Wake up secondary CPUs
/// 9. Start the kernel main function
///
/// # Safety
///
/// Must be called exactly once by the primary hart during boot.
unsafe fn primary_hart(hartid: usize) {
    // 1. Initialize UART for early debugging
    init_uart();

    // 2. Setup heap allocation FIRST - page tables need this!
    init_heap_allocation();

    // 3. Initialize memory management (now that heap exists)
    init_memory_management();

    // 4. Initialize architecture-specific features
    awkernel_lib::arch::rv64::init_primary();

    // 5. Initialize console driver
    console::init(UART_BASE);

    // 6. Initialize timer and interrupt controller
    init_timer_and_interrupts();

    // Enable software interrupts for IPIs on primary hart
    unsafe {
        core::arch::asm!("csrrs t0, mie, {}", in(reg) 1 << 3);
    }

    log::info!("AWkernel RV64 primary CPU initialization complete");

    // 7. Detect CPU count from device tree and store it
    let num_cpu = awkernel_lib::arch::rv64::detect_cpu_count();
    NUM_CPUS.store(num_cpu, Ordering::Release);

    // 8. Wake up secondary CPUs
    PRIMARY_INITIALIZED.store(true, Ordering::SeqCst);

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: hartid,
        num_cpu,
    };

    // 9. Start the kernel main function
    crate::main::<()>(kernel_info);
}

/// Secondary CPU initialization sequence.
/// 1. Wait for primary CPU to complete initialization
/// 2. Initialize architecture-specific features for non-primary CPUs
/// 3. Setup heap allocator usage
/// 4. Get CPU count from primary hart
/// 5. Start the kernel main function
///
/// # Safety
///
/// Must be called by non-primary harts during boot.
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

    // 4. Get CPU count detected by primary hart
    let num_cpu = NUM_CPUS.load(Ordering::Acquire);

    let kernel_info = KernelInfo {
        info: (),
        cpu_id: hartid,
        num_cpu,
    };

    // 5. Start the kernel main function
    crate::main::<()>(kernel_info);
}
