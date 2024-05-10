fn main() {
    println!("cargo::rustc-check-cfg=cfg(loom)");
    println!("cargo::rustc-check-cfg=cfg(std)");
}
