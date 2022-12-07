use core::{
    ops::{BitAnd, BitOr, Not},
    ptr::{read_volatile, write_volatile},
};

#[derive(Debug)]
pub struct ReadWrite<T>(*mut T);

#[macro_export]
macro_rules! mmio_rw {
    ($addr:expr => $func_name:ident<$ty:ty>) => {
        fn $func_name() -> $crate::mmio::ReadWrite<$ty> {
            $crate::mmio::ReadWrite::new($addr)
        }
    };
    ($addr:expr => $visibility:vis $func_name:ident<$ty:ty>) => {
        $visibility fn $func_name() -> $crate::mmio::ReadWrite<$ty> {
            $crate::mmio::ReadWrite::new($addr)
        }
    };
    (offset $addr:expr => $func_name:ident<$ty:ty>) => {
        fn $func_name(base: usize) -> $crate::mmio::ReadWrite<$ty> {
            $crate::mmio::ReadWrite::new($addr + base)
        }
    };
    (offset $addr:expr => $visibility:vis $func_name:ident<$ty:ty>) => {
        $visibility fn $func_name(base: usize) -> $crate::mmio::ReadWrite<$ty> {
            $crate::mmio::ReadWrite::new($addr + usize)
        }
    };
}

/// ```
/// // Read only MMIO.
/// mmio_r!(0x100, mmio_1st<u32>);
/// let val = mmio_1st().read(); // Read from 0x100
///
/// mmio_r!(0x200, pub mmio_2nd<u32>);
/// let val = mmio_2nd().read(); // Read from 0x200
///
/// mmio_r1!(offset 0x300, mmio_3rd<u32>);
/// let val = mmio_3rd(0x4000).read(); // Read from 0x4000 + 0x300.
/// ```
#[macro_export]
macro_rules! mmio_r {
    ($addr:expr => $func_name:ident<$ty:ty>) => {
        fn $func_name() -> $crate::mmio::ReadOnly<$ty> {
            $crate::mmio::ReadOnly::new($addr)
        }
    };
    ($addr:expr => $visibility:vis $func_name:ident<$ty:ty>) => {
        $visibility fn $func_name() -> $crate::mmio::ReadOnly<$ty> {
            $crate::mmio::ReadOnly::new($addr)
        }
    };
    (offset $addr:expr => $func_name:ident<$ty:ty>) => {
        fn $func_name(base: usize) -> $crate::mmio::ReadOnly<$ty> {
            $crate::mmio::ReadOnly::new($addr + base)
        }
    };
    (offset $addr:expr => $visibility:vis $func_name:ident<$ty:ty>) => {
        $visibility fn $func_name(base: usize) -> $crate::mmio::ReadOnly<$ty> {
            $crate::mmio::ReadOnly::new($addr + base)
        }
    };
}

#[macro_export]
macro_rules! mmio_w {
    ($addr:expr => $func_name:ident<$ty:ty>) => {
        fn $func_name() -> $crate::mmio::WriteOnly<$ty> {
            $crate::mmio::WriteOnly::new($addr)
        }
    };
    ($addr:expr => $visibility:vis $func_name:ident<$ty:ty>) => {
        $visibility fn $func_name() -> $crate::mmio::WriteOnly<$ty> {
            $crate::mmio::WriteOnly::new($addr)
        }
    };
    (offset $addr:expr => $func_name:ident<$ty:ty>) => {
        fn $func_name(base: usize) -> $crate::mmio::WriteOnly<$ty> {
            $crate::mmio::WriteOnly::new($addr + base)
        }
    };
    (offset $addr:expr => $visibility:vis $func_name:ident<$ty:ty>) => {
        $visibility fn $func_name(base) -> $crate::mmio::WriteOnly<$ty> {
            $crate::mmio::WriteOnly::new($addr + usize)
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
