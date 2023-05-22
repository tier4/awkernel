use awkernel_lib::context::ArchContext;
use core::{
    alloc::{GlobalAlloc, Layout},
    ptr::null_mut,
};

const PAGE_SIZE: usize = 4096;

pub struct WorkerThreadContext {
    cpu_ctx: ArchContext,
    stack_mem: *mut u8,
}

impl WorkerThreadContext {
    pub fn new() -> Self {
        WorkerThreadContext {
            cpu_ctx: ArchContext::default(),
            stack_mem: null_mut(),
        }
    }

    pub fn with_stack(size: usize) -> Result<Self, &'static str> {
        let Ok(layout) = Layout::from_size_align(size, PAGE_SIZE) else {
            return Err("failed to allocate stack memory.")
        };

        let stack_mem = unsafe { awkernel_lib::heap::TALLOC.alloc(layout) };

        Ok(WorkerThreadContext {
            cpu_ctx: ArchContext::default(),
            stack_mem,
        })
    }

    pub fn with_context_and_stack(
        ctx: &ArchContext,
        stack_size: usize,
    ) -> Result<Self, &'static str> {
        let Ok(layout) = Layout::from_size_align(stack_size, PAGE_SIZE) else {
            return Err("failed to allocate stack memory.")
        };

        let stack_mem = unsafe { awkernel_lib::heap::TALLOC.alloc(layout) };

        Ok(WorkerThreadContext {
            cpu_ctx: *ctx,
            stack_mem,
        })
    }
}
