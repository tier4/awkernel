use awkernel_lib::context::ArchContext;
use core::{
    alloc::{GlobalAlloc, Layout},
    ptr::null_mut,
};

const PAGE_SIZE: usize = 4096;

pub struct WorkerThreadContext {
    cpu_ctx: ArchContext,
    stack_mem: *mut u8,
    stack_size: usize,
}

impl WorkerThreadContext {
    pub fn new() -> Self {
        WorkerThreadContext {
            cpu_ctx: ArchContext::default(),
            stack_mem: null_mut(),
            stack_size: 0,
        }
    }

    pub fn with_stack(size: usize) -> Result<Self, &'static str> {
        let Ok(layout) = Layout::from_size_align(size, PAGE_SIZE) else {
            return Err("failed to allocate stack memory.")
        };

        let stack_mem = unsafe {
            let _config = awkernel_lib::heap::TALLOC.save();
            awkernel_lib::heap::TALLOC.use_primary();
            awkernel_lib::heap::TALLOC.alloc(layout)
        };

        Ok(WorkerThreadContext {
            cpu_ctx: ArchContext::default(),
            stack_mem,
            stack_size: size,
        })
    }

    pub fn with_context_and_stack(
        ctx: &ArchContext,
        stack_size: usize,
    ) -> Result<Self, &'static str> {
        let Ok(layout) = Layout::from_size_align(stack_size, PAGE_SIZE) else {
            return Err("failed to allocate stack memory.")
        };

        let stack_mem = unsafe {
            let _config = awkernel_lib::heap::TALLOC.save();
            awkernel_lib::heap::TALLOC.use_primary();
            awkernel_lib::heap::TALLOC.alloc(layout)
        };

        Ok(WorkerThreadContext {
            cpu_ctx: *ctx,
            stack_mem,
            stack_size,
        })
    }

    pub fn stack_start(&self) -> *mut () {
        let ptr = unsafe { self.stack_mem.add(self.stack_size) };
        ptr as _
    }
}

impl Drop for WorkerThreadContext {
    fn drop(&mut self) {
        if !self.stack_mem.is_null() {
            let layout = Layout::from_size_align(self.stack_size, PAGE_SIZE).unwrap();
            unsafe { awkernel_lib::heap::TALLOC.dealloc(self.stack_mem, layout) };
        }
    }
}
