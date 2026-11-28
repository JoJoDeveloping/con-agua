/* Minimal static ELF linker script for Linux RV64 (`-DCA_NOLIBC` cross-builds).
 * Overrides Debian riscv64-unknown-elf-gcc's default bare-metal picolibc.ld. */
OUTPUT_ARCH(riscv)
ENTRY(_start)

PHDRS {
  text PT_LOAD FLAGS(5); /* R | X */
  data PT_LOAD FLAGS(6); /* R | W */
}

SECTIONS {
  . = 0x400000;
  .text : ALIGN(4096) {
    *(.text .text.*)
  } :text
  .rodata : ALIGN(4096) {
    *(.rodata .rodata.* .srodata .srodata.*)
  } :text
  . = ALIGN(4096);
  .data : {
    *(.data .data.* .sdata .sdata.*)
  } :data
  .bss : {
    *(.bss .bss.* .sbss .sbss.* COMMON)
  } :data
  /DISCARD/ : {
    *(.comment .eh_frame .eh_frame_hdr)
  }
}
