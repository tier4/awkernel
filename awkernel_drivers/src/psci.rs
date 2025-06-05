use core::arch::global_asm;

/// PSCI which uses the hypervisor call.
pub struct PSCIHvc;

/// PSCI which uses the secure monitor call.
pub struct PSCISmc;

pub trait PSCI {
    fn cpu_on(&self, affinity: Affinity, entry_point_address: usize) -> Result<(), PSCIResult>;
}

const CPU_ON: u32 = 0xC400_0003;

#[derive(Debug, Clone, Copy)]
pub struct Affinity(u64);

impl Affinity {
    pub fn new(aff0: u64, aff1: u64, aff2: u64, aff3: u64) -> Self {
        let aff =
            aff0 & 0xff | ((aff1 & 0xff) << 8) | ((aff2 & 0xff) << 16) | ((aff3 & 0xff) << 32);
        Affinity(aff)
    }
}

global_asm!(
    "
.global __arg4_hvc
__arg4_hvc:
    hvc #0
    ret

.global __arg4_smc
__arg4_smc:
    smc #0
    ret
"
);

extern "C" {
    fn __arg4_hvc(arg0: u64, arg1: u64, arg2: u64, arg3: u64) -> i64;
    fn __arg4_smc(arg0: u64, arg1: u64, arg2: u64, arg3: u64) -> i64;
}

#[derive(Debug, Clone)]
pub enum PSCIResult {
    NotSupported = -1,
    InvalidParameters = -2,
    Denied = -3,
    AlreadyOn = -4,
    OnPending = -5,
    InternalFailure = -6,
    NotPresent = -7,
    Disabled = -8,
    InvalidAddress = -9,
}

impl From<i64> for PSCIResult {
    fn from(value: i64) -> Self {
        match value {
            -1 => PSCIResult::NotSupported,
            -2 => PSCIResult::InvalidParameters,
            -3 => PSCIResult::Denied,
            -4 => PSCIResult::AlreadyOn,
            -5 => PSCIResult::OnPending,
            -6 => PSCIResult::InternalFailure,
            -7 => PSCIResult::NotPresent,
            -8 => PSCIResult::Disabled,
            -9 => PSCIResult::InvalidAddress,
            _ => PSCIResult::InternalFailure,
        }
    }
}

impl PSCI for PSCIHvc {
    fn cpu_on(&self, affinity: Affinity, entry_point_address: usize) -> Result<(), PSCIResult> {
        let result =
            unsafe { __arg4_hvc(CPU_ON as u64, affinity.0, entry_point_address as u64, 0) };

        if result == 0 {
            Ok(())
        } else {
            Err(PSCIResult::from(result))
        }
    }
}

impl PSCI for PSCISmc {
    fn cpu_on(&self, affinity: Affinity, entry_point_address: usize) -> Result<(), PSCIResult> {
        let result =
            unsafe { __arg4_hvc(CPU_ON as u64, affinity.0, entry_point_address as u64, 0) };

        if result == 0 {
            Ok(())
        } else {
            Err(PSCIResult::from(result))
        }
    }
}

pub fn new(method: &str) -> Result<&dyn PSCI, PSCIResult> {
    match method {
        "hvc" => Ok(&PSCIHvc),
        "smc" => Ok(&PSCISmc),
        _ => Err(PSCIResult::InvalidParameters),
    }
}
