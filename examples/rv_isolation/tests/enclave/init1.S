.section ".text.init"
#  .text
#  .align 6
  .globl _start1
  .extern stack_ptr1
  .extern save_enclave_state1
  .extern bootloader1
  .extern call_main1
_start0:
  li  x1, 0
  li  x2, 0
  li  x3, 0
  li  x4, 0
  li  x5, 0
  li  x6, 0
  li  x7, 0
  li  x8, 0
  li  x9, 0
  li  x10,0
  li  x11,0
  li  x12,0
  li  x13,0
  li  x14,0
  li  x15,0
#ifndef RV32E
  li  x16,0
  li  x17,0
  li  x18,0
  li  x19,0
  li  x20,0
  li  x21,0
  li  x22,0
  li  x23,0
  li  x24,0
  li  x27,0
  li  x28,0
  li  x29,0
  li  x30,0
  li  x31,0
#endif
  la sp, stack_ptr1
  la a0, call_main1  # Save address of call_main in a0
  call save_enclave_state1
  call bootloader1
spin:
  j spin




