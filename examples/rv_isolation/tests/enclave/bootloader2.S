#include "defs.h"


.section ".text.bootloader"
  .extern _GLBL2
  .global bootloader2
/* if a2 = 0, do lookup; if a2 = 1, do add. 
   - return to enclave config in a1 
 */
/* No state saved between entries to enclave 2, stack pointer constant */
bootloader2:
  la sp, stack_ptr2 
  la t0, _GLBL2
  sw a1,0(t0)   # save destination enclave config in _GLBL2
  bnez a2,call_add_password
  beq a2,x0,call_lookup
  j clear_state

call_lookup:
  mv a0,a3 # id
  mv a1,a4 # secret key
  call lookup
  j clear_state

call_add_password:
  mv a0,a3 # id 
  mv a1,a4 # password
  mv a2,a5 # secret key
  call add_password
  j clear_state

clear_state:
  la t0,_GLBL2
  lw x12,0(t0)

  li  x1, 0
  li  x2, 0
  li  x3, 0
  li  x4, 0
  li  x5, 0
  li  x6, 0
  li  x7, 0
  li  x8, 0
  li  x9, 0
  #li  x10,0
  #li  x11,0
  #li  x12,0
  li  x13,0
  li  x14,0
  li  x15,0
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
  /* li t0,0x1000  *//* TODO: remove this... temp */
  SET_ENCLAVE(12)
spin:
  j spin

