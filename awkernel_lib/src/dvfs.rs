pub trait Dvfs {
    /// Set the frequency of the current CPU.
    fn set_freq(&self, freq: u64);

    /// Get the frequency of the current CPU.
    fn get_freq(&self) -> u64;
}
