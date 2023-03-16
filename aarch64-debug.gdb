set disassemble-next-line on
set confirm off
set arch aarch64
add-symbol-file target/aarch64-kernel/debug/awkernel
target remote localhost:1234