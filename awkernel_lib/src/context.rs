pub trait Context: Default {
    fn set_jump(&mut self);
    fn long_jump(&self) -> !;
}
