fn main() {
    // `awkernel.ld` is provided by the kernel crate's build script.
    println!("cargo:rustc-link-arg-bins=-Tawkernel.ld");
}
