#include "defs.h"

.section ".text.bootloader"
  .extern _GLBL0
  .global bootloader0
bootloader0:
  la t0,_GLBL0   # Load address of _GLBL0 (old stack pointer) into register t0
  lw sp,0(t0)    # Set stack pointer with value stored at _GLBL0
  lw   s0, 4(t0)  # Save frame pointer to global location _GLBL0+4
  lw   s2, 8(t0)  # Save remaining callee saved registers
  lw   s3, 12(t0) 
  lw   s4, 16(t0) 
  lw   s5, 20(t0) 
  lw   s6, 24(t0) 
  lw   s7, 28(t0) 
  lw   s8, 32(t0) 
  lw   s9, 36(t0) 
  lw   s10, 40(t0) 
  lw   s11, 44(t0) 
  lw x6,0(sp)    # Load function address pointer to by sp 
  addi sp,sp,4   # Increment stack pointer
  jalr x6        # Call function, and save return address in ra
  li x10, 0      
  call exit0     # exit with arg 0
  ret
1:
  j 1b           # spin 

.section ".text"
  .global save_enclave_state0
save_enclave_state0:
  addi sp,sp,-4   # Decrement stack pointer
  sw   a0,0(sp)   # save contents of a0 (next pc) onto the stack
  la   t0,_GLBL0  # sp address
  sw   sp, 0(t0)  # Save stack pointer to global location _GLBL0
  sw   s0, 4(t0)  # Save frame pointer to global location _GLBL0+4
  sw   s2, 8(t0)  # Save remaining callee saved registers
  sw   s3, 12(t0) 
  sw   s4, 16(t0) 
  sw   s5, 20(t0) 
  sw   s6, 24(t0) 
  sw   s7, 28(t0) 
  sw   s8, 32(t0) 
  sw   s9, 36(t0) 
  sw   s10, 40(t0) 
  sw   s11, 44(t0) 
  # TODO: reset some registers to 0 b/c secrecy!
  ret

  .global call_main0
call_main0:
  addi sp, sp,-4
  sw   ra,0(sp)
  call main0
  lw   ra,0(sp)
  addi sp,sp,4
  ret

  .globl _lookup
  .type  _lookup,%function
_lookup:
  addi sp,sp,-4
  sw ra,0(sp)
  mv a3,a0  # Argument 0: id
  mv a4,a1  # Argument 1: secret_key
  li a0,2   # Switch to enclave 2 with no permissions
  li a1, 0x71c # Ask to switch back to enclave 0 with all permissions
  li a2,_FN_LOOKUP_CODE   # Function code for lookup
  call set_enclave
  lw ra,0(sp)
  addi sp,sp,4
  ret

  .globl _add_password
  .type  _add_password,%function
_add_password:
  addi sp,sp,-4
  sw ra,0(sp)
  mv a3,a0  # Argument 0: id 
  mv a4,a1  # Argument 1: password
  mv a5,a2  # Argument 2: secret key
  li a0,2 
  li a1, 0x71c
  li a2,_FN_ADD_PASSWORD_CODE
  call set_enclave
  lw ra,0(sp)
  addi sp,sp,4
  ret

# TODO: does not follow RISC-V conventions oops. Need to save nore regusters,
set_enclave: # arg: a0 := enclave_id; a1 := enclave_to_return_to 
             # a2 := func_code; a3-a7 := arguments
  addi sp, sp,-4
  sw   ra,0(sp)
  la t0, set_enclave_ret
# save_enclave_state
  addi sp,sp,-4   # Decrement stack pointer
  sw   t0,0(sp)   # save contents of a0 (next pc) onto the stack
  la   t0,_GLBL0  # sp address
  sw   sp, 0(t0)  # Save stack pointer to global location _GLBL0
  sw   s0, 4(t0)  # Save frame pointer to global location _GLBL0+4
  sw   s1, 8(t0)  # Save remaining callee saved registers
  sw   s2, 12(t0) 
  sw   s3, 16(t0) 
  sw   s4, 20(t0) 
  sw   s5, 24(t0) 
  sw   s6, 28(t0) 
  sw   s7, 32(t0) 
  sw   s8, 36(t0) 
  sw   s9, 40(t0) 
  sw   s10, 44(t0) 
  sw   s11, 48(t0) 
  SET_ENCLAVE(10) # set enclave to config in a0
set_enclave_ret:
  lw   ra,0(sp)
  addi sp,sp,4
  ret

