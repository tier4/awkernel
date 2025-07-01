/// Trait that should be implemented by errors returned from the user supplied storage.
pub trait IoError: core::fmt::Debug + Clone + Send + Sync + 'static {
    fn is_interrupted(&self) -> bool;
    fn new_unexpected_eof_error() -> Self;
    fn new_write_zero_error() -> Self;
}

impl IoError for () {
    fn is_interrupted(&self) -> bool {
        false
    }

    fn new_unexpected_eof_error() -> Self {
        // empty
    }

    fn new_write_zero_error() -> Self {
        // empty
    }
}
