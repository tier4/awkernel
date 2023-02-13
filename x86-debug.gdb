set disassemble-next-line on
set confirm off
set arch  i386:x86-64:intel
add-symbol-file kernel-x86_64.elf
target remote localhost:1234