.section .data.stacks

.globl stack_base2, stack_ptr2, persistent_base2, persistent_ptr2 

stack_base2:
  .skip (0x1000)
stack_ptr2:
persistent_base2:
  .skip(0x1000)
persistent_ptr2:
