use core::fmt::Debug;

#[derive(Debug)]
pub struct BoardInfo<T: Debug> {
    pub info: T,
}
