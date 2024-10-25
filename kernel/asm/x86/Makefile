ASM_FILE_X86=mpboot.S
ASM_OBJ_X86=mpboot.o
ASM_ELF_X86=mpboot.elf
ASM_IMG_X86=mpboot.img

all: $(ASM_IMG_X86)

$(ASM_OBJ_X86): $(ASM_FILE_X86)
	gcc -m32 -fno-pie -nostdlib -c $< -o $@

# See kernel::arch::x86_64::kernel_main::NON_PRIMARY_START
$(ASM_ELF_X86): $(ASM_OBJ_X86)
	$(LD) -m elf_i386 -N -e _start_cpu -Ttext 0 $< -o $@

%.img: %.elf
	rust-objcopy -O binary $< $@

clean:
	rm -f *.o *.img *.elf
