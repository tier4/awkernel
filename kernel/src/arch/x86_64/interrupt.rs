use awkernel_lib::delay::wait_forever;
use x86_64::structures::idt::{InterruptDescriptorTable, InterruptStackFrame, PageFaultErrorCode};

static mut IDT: InterruptDescriptorTable = InterruptDescriptorTable::new();

pub unsafe fn init() {
    IDT.alignment_check.set_handler_fn(alignment_check);
    IDT.bound_range_exceeded
        .set_handler_fn(bound_range_exceeded);
    IDT.breakpoint.set_handler_fn(breakpoint);
    IDT.debug.set_handler_fn(debug);
    IDT.device_not_available
        .set_handler_fn(device_not_available);
    IDT.divide_error.set_handler_fn(divide_error);
    IDT.double_fault.set_handler_fn(double_fault);
    IDT.general_protection_fault
        .set_handler_fn(general_protection_fault);
    IDT.invalid_opcode.set_handler_fn(invalid_opcode);
    IDT.invalid_tss.set_handler_fn(invalid_tss);
    IDT.machine_check.set_handler_fn(machine_check);
    IDT.non_maskable_interrupt
        .set_handler_fn(non_maskable_interrupt);
    IDT.overflow.set_handler_fn(overflow);
    IDT.page_fault.set_handler_fn(page_fault);
    IDT.security_exception.set_handler_fn(security_exception);
    IDT.segment_not_present.set_handler_fn(segment_not_present);
    IDT.simd_floating_point.set_handler_fn(simd_floating_point);
    IDT.stack_segment_fault.set_handler_fn(stack_segment_fault);
    IDT.virtualization.set_handler_fn(virtualization);
    IDT.vmm_communication_exception
        .set_handler_fn(vmm_communication_exception);
    IDT.x87_floating_point.set_handler_fn(x87_floating_point);

    IDT.load();
}

extern "x86-interrupt" fn alignment_check(stack_frame: InterruptStackFrame, error: u64) {
    log::debug!(
        "alignment check: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn bound_range_exceeded(stack_frame: InterruptStackFrame) {
    log::debug!("bound range exceeded: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn breakpoint(stack_frame: InterruptStackFrame) {
    log::debug!("breakpoint: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn debug(stack_frame: InterruptStackFrame) {
    log::debug!("debug: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn device_not_available(stack_frame: InterruptStackFrame) {
    log::debug!("device not available: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn divide_error(stack_frame: InterruptStackFrame) {
    log::debug!("divide error: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn double_fault(stack_frame: InterruptStackFrame, error: u64) -> ! {
    log::debug!(
        "double fault: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
    wait_forever()
}

extern "x86-interrupt" fn general_protection_fault(stack_frame: InterruptStackFrame, error: u64) {
    log::debug!(
        "general protection fault: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn invalid_opcode(stack_frame: InterruptStackFrame) {
    log::debug!("invalid opcode: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn invalid_tss(stack_frame: InterruptStackFrame, error: u64) {
    log::debug!(
        "invalid tss: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn machine_check(stack_frame: InterruptStackFrame) -> ! {
    log::debug!("machine check: stack_frame = {:?}", stack_frame,);
    wait_forever()
}

extern "x86-interrupt" fn non_maskable_interrupt(stack_frame: InterruptStackFrame) {
    log::debug!("non maskable interrupt: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn overflow(stack_frame: InterruptStackFrame) {
    log::debug!("overflow: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn page_fault(stack_frame: InterruptStackFrame, error: PageFaultErrorCode) {
    let addr = x86_64::registers::control::Cr2::read();

    log::debug!(
        "page fault: addr = {:?}, stack_frame = {:?}, error = {:b}",
        addr,
        stack_frame,
        error.bits()
    );
}

extern "x86-interrupt" fn security_exception(stack_frame: InterruptStackFrame, error: u64) {
    log::debug!(
        "security exception: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn segment_not_present(stack_frame: InterruptStackFrame, error: u64) {
    log::debug!(
        "segment not present: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn simd_floating_point(stack_frame: InterruptStackFrame) {
    log::debug!("simd floating point: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn stack_segment_fault(stack_frame: InterruptStackFrame, error: u64) {
    log::debug!(
        "stack segment fault: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn virtualization(stack_frame: InterruptStackFrame) {
    log::debug!("virtualization: stack_frame = {:?}", stack_frame,);
}

extern "x86-interrupt" fn vmm_communication_exception(
    stack_frame: InterruptStackFrame,
    error: u64,
) {
    log::debug!(
        "vmm communication exception: stack_frame = {:?}, error = {error}",
        stack_frame,
    );
}

extern "x86-interrupt" fn x87_floating_point(stack_frame: InterruptStackFrame) {
    log::debug!("x87 floating point: stack_frame = {:?}", stack_frame,);
}
