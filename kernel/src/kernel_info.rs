use core::fmt::Debug;

pub struct KernelInfo<T: Debug> {
    #[allow(dead_code)]
    pub info: T,
    pub cpu_id: usize,
    pub num_cpu: usize,
}
