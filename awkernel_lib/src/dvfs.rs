pub trait Dvfs {
    /// Fix the frequency of the current CPU.
    fn fix_freq(freq: u64);

    /// Get the maximum frequency of the current CPU.
    fn get_max_freq() -> u64;

    /// Get the frequency of the current CPU.
    fn get_curr_freq() -> u64;
}
