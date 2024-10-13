#define _ADDRESS_WIDTH  12 /* 16kiB of memory, 4kiB of stack */
#define _MEMSIZE  ((1 << _ADDRESS_WIDTH) * 4)
#define _START0  0x0000
#define _START1  0x4000
#define _ENCLAVE0  0x0100 /* TODO */
#define _ENCLAVE1  0x4100 /* TODO */
#define _ENCLAVE2  0x8000
#define _ENCLAVE3  0xC000
#define _SHARED01  0x01000000
#define _SHARED02  0x01008000
#define _SHARED03  0x01010000
#define _SHARED12  0x01018000
#define _SHARED13  0x01020000
#define _SHARED23  0x01028000

#define _INIT_LENGTH  0x100
#define _MIN_STACK_SIZE  (1 << _ADDRESS_WIDTH) 
#define _ENCLAVE_SIZE (0x3000)
#define _SHARED_REGION_SIZE 0x00008000

/* _fstack  _MEMSIZE - 4 */

