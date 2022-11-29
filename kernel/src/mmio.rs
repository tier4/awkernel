use core::{
    ops::{BitAnd, BitOr, Not},
    ptr::{read_volatile, write_volatile},
};

pub struct ReadWrite<T>(*mut T);

#[macro_export]
macro_rules! mmio_rw {
    ($addr:expr => $func_name:ident<$ty:ty>) => {
        fn $func_name() -> crate::mmio::ReadWrite<$ty> {
            crate::mmio::ReadWrite::new($addr)
        }
    };
    ($addr:expr => $visibility:vis $func_name:ident<$ty:ty>) => {
        $visibility fn $func_name() -> crate::mmio::ReadWrite<$ty> {
            crate::mmio::ReadWrite::new($addr)
        }
    };
}

#[macro_export]
macro_rules! mmio_rw_base {
    ($addr:expr => $func_name:ident<$ty:ty>) => {
        fn $func_name(&self) -> crate::mmio::ReadWrite<$ty> {
            crate::mmio::ReadWrite::new(self.base + $addr)
        }
    };
    ($addr:expr => $visibility:vis $func_name:ident<$ty:ty>) => {
        $visibility fn $func_name(&self) -> crate::mmio::ReadWrite<$ty> {
            crate::mmio::ReadWrite::new(self.base + $addr)
        }
    };
}

#[macro_export]
macro_rules! mmio_r {
    ($addr:expr => $func_name:ident<$ty:ty>) => {
        fn $func_name() -> crate::mmio::ReadOnly<$ty> {
            crate::mmio::ReadOnly::new($addr)
        }
    };
    ($addr:expr => $visibility:vis $func_name:ident<$ty:ty>) => {
        $visibility fn $func_name() -> crate::mmio::ReadOnly<$ty> {
            crate::mmio::ReadOnly::new($addr)
        }
    };
}

#[macro_export]
macro_rules! mmio_w {
    ($addr:expr => $func_name:ident<$ty:ty>) => {
        fn $func_name() -> crate::mmio::WriteOnly<$ty> {
            crate::mmio::WriteOnly::new($addr)
        }
    };
    ($addr:expr => $visibility:vis $func_name:ident<$ty:ty>) => {
        $visibility fn $func_name() -> crate::mmio::WriteOnly<$ty> {
            crate::mmio::WriteOnly::new($addr)
        }
    };
}

impl<T: Not<Output = T> + BitOr<Output = T> + BitAnd<Output = T>> ReadWrite<T> {
    pub fn new(addr: usize) -> Self {
        ReadWrite(addr as *mut T)
    }

    pub fn write(&self, n: T) {
        unsafe { write_volatile(self.0, n) };
    }

    pub fn read(&self) -> T {
        unsafe { read_volatile(self.0) }
    }

    pub fn setbits(&self, mask: T) {
        let old = self.read();
        self.write(old | mask);
    }

    pub fn clrbits(&self, mask: T) {
        let old = self.read();
        self.write(old & !mask);
    }
}

pub struct ReadOnly<T>(*const T);

impl<T: Not<Output = T> + BitOr<Output = T> + BitAnd<Output = T>> ReadOnly<T> {
    pub fn new(addr: usize) -> Self {
        ReadOnly(addr as *const T)
    }

    pub fn read(&self) -> T {
        unsafe { read_volatile(self.0) }
    }
}

pub struct WriteOnly<T>(*mut T);

impl<T: Not<Output = T> + BitOr<Output = T> + BitAnd<Output = T>> WriteOnly<T> {
    pub fn new(addr: usize) -> Self {
        WriteOnly(addr as *mut T)
    }

    pub fn write(&self, n: T) {
        unsafe { write_volatile(self.0, n) };
    }
}
