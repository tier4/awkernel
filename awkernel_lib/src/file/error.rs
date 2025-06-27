/// Trait that should be implemented by errors returned from the user supplied storage.
pub trait IoError: core::fmt::Debug {
    fn is_interrupted(&self) -> bool;
    fn new_unexpected_eof_error() -> Self;
    fn new_write_zero_error() -> Self;
}
