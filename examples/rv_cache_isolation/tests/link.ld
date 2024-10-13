OUTPUT_ARCH("riscv")
ENTRY(_start)

_ADDRESS_WIDTH = 12; /* 256kiB of memory, 64kiB of stack */
_MEMSIZE = (1 << _ADDRESS_WIDTH) * 4;
_START0 = 0x0000;
_START1 = 0x4000;
_ENCLAVE0 = 0x0100;
_ENCLAVE1 = 0x4100;
_ENCLAVE2 = 0x8000;
_ENCLAVE3 = 0xC000;
_BOOTLOADER_LENGTH = 0x100;
/* _MIN_STACK_SIZE = (1 << _ADDRESS_WIDTH); */
/* _fstack = _MEMSIZE - 4; */

MEMORY {
  bootloader0 (rx) : ORIGIN = _START0, LENGTH = _BOOTLOADER_LENGTH 
  enclave0(rx) : ORIGIN = _ENCLAVE0, LENGTH = _MEMSIZE - _BOOTLOADER_LENGTH
  bootloader1 (rx) : ORIGIN = _START1, LENGTH = _BOOTLOADER_LENGTH 
  enclave1(rx) : ORIGIN = _ENCLAVE1, LENGTH = _MEMSIZE  - _BOOTLOADER_LENGTH
  enclave2(rx) : ORIGIN = _ENCLAVE2, LENGTH = _MEMSIZE 
  enclave3(rx) : ORIGIN = _ENCLAVE3, LENGTH = _MEMSIZE 
}

SECTIONS
{
   . = 0x00000000;
   .text.init0 : { *(.text.init0) } > bootloader0
   .text.init1 : { *(.text.init1) } > bootloader1
   .text.enclave0 : { *(.text.enclave0) } > enclave0


   .text :  { *(.text) } > enclave0
   .data : { *(.data) } > enclave0
   .bss : { *(.bss) } > enclave0
   _end = .;
   
  /*
  .text.init : { *(.text.init) } > bram
  .text : { *(.text) } > bram
  .data : { *(.data) } > bram
  */
/*   .bss : { *(.bss) } > bram */
}
