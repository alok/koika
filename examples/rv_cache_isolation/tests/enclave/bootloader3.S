.section ".text.bootloader"
  .extern _GLBL3
  .global bootloader3
bootloader3:
1:
  j 1b
/*
  la t0,_GLBL3   # Load address of _GLBL0 (old stack pointer) into register t0
  lw sp,0(t0)    # Set stack pointer with value stored at _GLBL0
  lw x6,0(sp)    # Load function address pointer to by sp 
  addi sp,sp,4   # Increment stack pointer
  jalr x6        # Call function, and save return address in ra
  li x10, 0      
  call exit3     # exit with arg 0
  ret
1:
  j 1b           # spin 

.section ".text"
  .global save_enclave_state3
save_enclave_state3:
  addi sp,sp,-4   # Decrement stack pointer
  sw   a0,0(sp)   # save contents of a0 (next pc) onto the stack
  la   t0,_GLBL3  # sp address
  sw   sp, 0(t0)  # Save stack pointer to global location _GLBL0
  ret

  .global call_main3
call_main3:
  addi sp, sp,-4
  sw   ra,0(sp)
  call main3
  lw   ra,0(sp)
  addi sp,sp,4
  ret

*/
