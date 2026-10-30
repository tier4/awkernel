use core::ptr::{read_volatile, write_volatile};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    InvalidPriority,
    InvalidSource,
    InvalidContext,
    InternalError,
    NotImplemented,
    Other,
}

impl Error {
    /// Returns a string slice describing the error.
    pub const fn description(&self) -> &'static str {
        match self {
            Error::InvalidPriority => "Invalid priority",
            Error::InvalidSource => "Invalid source",
            Error::InvalidContext => "Invalid context",
            Error::InternalError => "Internal error",
            Error::NotImplemented => "Not implemented",
            Error::Other => "Other error",
        }
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}", self.description())
    }
}

impl core::error::Error for Error {}

pub type Result<T> = core::result::Result<T, Error>;

pub struct Plic {
    pub(crate) base_addr: usize,
    pub(crate) max_priority: u32,
    pub(crate) num_sources: u16,
    pub(crate) num_contexts: u16,
}

impl Plic {
    const PRIORITIES_BASE: usize = 0x0000;

    const PENDING_BASE: usize = 0x1000;

    const ENABLES_OFFSET: usize = 0x2000;
    const ENABLES_SEPARATION: usize = 0x80;

    const THRESHOLDS_OFFSET: usize = 0x20_0000;
    const THRESHOLDS_SEPARATION: usize = 0x1000;

    const CLAIMS_OFFSET: usize = 0x20_0004;
    const CLAIMS_SEPARATION: usize = 0x1000;

    #[inline]
    const fn check_priority(&self, priority: u32) -> Result<()> {
        match priority <= self.max_priority {
            true => Ok(()),
            false => Err(Error::InvalidPriority),
        }
    }

    #[inline]
    const fn check_source(&self, source: u16) -> Result<()> {
        match source > 0 && source <= self.num_sources {
            true => Ok(()),
            false => Err(Error::InvalidSource),
        }
    }

    #[inline]
    const fn check_context(&self, context_id: u16) -> Result<()> {
        match context_id < self.num_contexts {
            true => Ok(()),
            false => Err(Error::InvalidContext),
        }
    }

    #[inline]
    const fn priority(&self, source: u16) -> *mut u32 {
        (self.base_addr + Self::PRIORITIES_BASE + source as usize * 4) as _
    }

    #[inline]
    const fn pending(&self, source: u16) -> *const u32 {
        (self.base_addr + Self::PENDING_BASE + (source as usize / 32) * 4) as _
    }

    #[inline]
    const fn enable(&self, context_id: u16, source: u16) -> *mut u32 {
        let context_id = context_id as usize;
        let reg_index = source as usize / 32;
        let base = self.base_addr + Self::ENABLES_OFFSET + context_id * Self::ENABLES_SEPARATION;
        (base + reg_index * 4) as _
    }

    #[inline]
    const fn threshold(&self, context_id: u16) -> *mut u32 {
        let context_id = context_id as usize;
        (self.base_addr + Self::THRESHOLDS_OFFSET + context_id * Self::THRESHOLDS_SEPARATION) as _
    }

    #[inline]
    const fn claim_complete(&self, context_id: u16) -> *mut u32 {
        let context_id = context_id as usize;
        (self.base_addr + Self::CLAIMS_OFFSET + context_id * Self::CLAIMS_SEPARATION) as _
    }

    /// Get the priority of a given interrupt source.
    ///
    /// If the source is out of range, this function will return an error.
    pub fn get_priority(&self, source: u16) -> Result<u32> {
        self.check_source(source)?;
        let reg = self.priority(source);
        // Safety: source is in range
        let priority = unsafe { read_volatile(reg) };
        Ok(priority)
    }

    /// Set the priority of a given interrupt source.
    ///
    /// If the source or priority is out of range, this function will return an error.
    pub fn set_priority(&self, source: u16, priority: u32) -> Result<()> {
        self.check_source(source)?;
        self.check_priority(priority)?;
        let reg = self.priority(source);
        // Safety: source and priority are in range
        unsafe { write_volatile(reg, priority) };
        Ok(())
    }

    /// Check if a given interrupt source is pending.
    ///
    /// If the source is out of range, this function will return an error.
    pub fn is_pending(&self, source: u16) -> Result<bool> {
        self.check_source(source)?;
        let reg = self.pending(source);
        let mask = 1 << (source % 32);
        // Safety: source is in range
        let pending = unsafe { read_volatile(reg) } & mask != 0;
        Ok(pending)
    }

    /// Enable an interrupt for a given context.
    ///
    /// If the context_id or source is out of range, this function will return an error.
    pub fn enable_interrupt(&self, context_id: u16, source: u16) -> Result<()> {
        self.check_context(context_id)?;
        self.check_source(source)?;
        let enables_reg = self.enable(context_id, source);
        let mask = 1 << (source % 32);
        // Safety: context and source are in range
        unsafe {
            let current = read_volatile(enables_reg);
            write_volatile(enables_reg, current | mask);
        }
        Ok(())
    }

    /// Disable an interrupt for a given context.
    ///
    /// If context_id or source is out of range, this function will return an error.
    pub fn disable_interrupt(&self, context_id: u16, source: u16) -> Result<()> {
        self.check_context(context_id)?;
        self.check_source(source)?;
        let enables_reg = self.enable(context_id, source);
        let mask = !(1 << (source % 32));
        // Safety: context and source are in range
        unsafe {
            let current = read_volatile(enables_reg);
            write_volatile(enables_reg, current & mask);
        }
        Ok(())
    }

    /// Get the threshold for a given context.
    ///
    /// If the context_id is out of range, this function will return an error.
    pub fn get_threshold(&self, context_id: u16) -> Result<u32> {
        self.check_context(context_id)?;
        let reg = self.threshold(context_id);
        // Safety: context_id is in range
        let threshold = unsafe { read_volatile(reg) };
        Ok(threshold)
    }

    /// Set the threshold for a given context.
    ///
    /// If the context_id or threshold is out of range, this function will return an error
    pub fn set_threshold(&self, context_id: u16, threshold: u32) -> Result<()> {
        self.check_context(context_id)?;
        self.check_priority(threshold)?;
        let reg = self.threshold(context_id);
        // Safety: context_id is in range
        unsafe { write_volatile(reg, threshold) };
        Ok(())
    }

    /// Claim an interrupt for a given context.
    ///
    /// If context_id is out of range, this function will return an error.
    /// If no pending interrupt is available, it will return `Ok(None)`.
    /// If a pending interrupt is claimed, it is completed and returned as `Ok(Some(irq))`.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the context_id is valid.
    pub unsafe fn claim_interrupt_unchecked(&self, context_id: u16) -> Option<u16> {
        let claim_reg = self.claim_complete(context_id);
        // Safety: context is in range
        let irq = unsafe { read_volatile(claim_reg) };
        match irq {
            0 => None,
            _ => {
                // Safety: context is in range and irq is a valid interrupt source
                unsafe {
                    if let Err(e) = clear_ext_interrupt(irq as u16) {
                        log::warn!("Failed to clear external interrupt {}: {:?}", irq, e);
                    }
                    write_volatile(claim_reg, irq); // Complete the interrupt
                }
                Some(irq as u16)
            }
        }
    }

    /// Claim an interrupt for a given context.
    ///
    /// If context_id is out of range, this function will return an error.
    /// If no pending interrupt is available, it will return `Ok(None)`.
    /// If a pending interrupt is claimed, it is completed and returned as `Ok(Some(irq))`.
    pub fn claim_interrupt(&self, context_id: u16) -> Result<Option<u16>> {
        self.check_context(context_id)?;
        // Safety: context is in range
        let irq = unsafe { self.claim_interrupt_unchecked(context_id) };
        Ok(irq)
    }
}

extern "Rust" {
    fn __awkernel_plic_clear_ext_interrupt(irq: u16) -> Result<()>;
}

#[inline]
fn clear_ext_interrupt(irq: u16) -> Result<()> {
    unsafe { __awkernel_plic_clear_ext_interrupt(irq) }
}

#[linkage = "weak"]
#[export_name = "__awkernel_plic_clear_ext_interrupt"]
extern "Rust" fn default_clear_ext_interrupt() -> Result<()> {
    Err(Error::NotImplemented)
}
