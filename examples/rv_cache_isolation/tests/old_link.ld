OUTPUT_ARCH("riscv")
ENTRY(_start)

_ADDRESS_WIDTH = 12; /* 256kiB of memory, 64kiB of stack */

_MEMSIZE = (1 << _ADDRESS_WIDTH) * 4;
_MIN_STACK_SIZE = (1 << _ADDRESS_WIDTH);
_fstack = _MEMSIZE - 4;

MEMORY {
  /*
  mem0_init (rx) : ORIGIN = 0x0, LENGTH = 0x1000
  mem0_bootloader (rx) : ORIGIN = 0x1000, LENGTH = 0x2000
  mem0_start (rx) : ORIGIN + 0x2000, LENGTH = _MEMSIZE - _MIN_STACK_SIZE - 0x2000

  mem1 (rx) : ORIGIN = _ORIGIN1;
  */

  bram (rx) : ORIGIN = 0x0, LENGTH = _MEMSIZE - _MIN_STACK_SIZE
}

SECTIONS
{
  . = 0x00000000;
  .text.init : { *(.text.init) } > bram
  .text : { *(.text) } > bram
  .data : { *(.data) } > bram
  .bss : { *(.bss) } > bram
  _end = .;
}
