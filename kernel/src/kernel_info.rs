use core::fmt::Debug;

#[derive(Debug)]
pub struct KernelInfo<T: Debug> {
    pub info: T,
    pub cpu_id: usize,
}
