.PHONY: all clean

BUILD_DIR := _build
elf2hex := ../elf2hex/elf2hex

default: all

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

RISCVCC32 ?= riscv-none-embed-gcc
RISCVCC32_ARGS := -g -mstrict-align -nostartfiles -static -march=rv32i -mabi=ilp32
RISCVOBJDUMP32 ?= riscv-none-embed-objdump
RISCVOBJDUMP32_ARGS := --disassemble --source --full-contents
RISCVOBJCOPY32 ?= riscv-none-embed-objcopy

cc := $(RISCVCC32) $(RISCVCC32_ARGS)
objdump := $(RISCVOBJDUMP32) $(RISCVOBJDUMP32_ARGS)
objcopy := $(RISCVOBJCOPY32)

# Source files
ENCLAVE0_SRC := init0.S bootloader0.S enclave0.c stack0.S mmio0.c
ENCLAVE1_SRC := init1.S bootloader1.S enclave1.c stack1.S mmio1.c
ENCLAVE2_SRC := bootloader2.S enclave2.c stack2.S mmio2.c
ENCLAVE3_SRC := bootloader3.S enclave3.c stack3.S mmio3.c
ENCLAVE_SRC := $(ENCLAVE0_SRC) $(ENCLAVE1_SRC) $(ENCLAVE2_SRC) $(ENCLAVE3_SRC)

# Object files
OBJ_ALL := $(addprefix $(BUILD_DIR)/, $(notdir $(patsubst %.S,%.o,$(patsubst %.c,%.o,$(ENCLAVE_SRC))))) 

#$(ENCLAVE_SRC:%.c=%.o) $(ENCLAVE_SRC:%.S=%.o))
#$(addprefix $(BUILD_DIR)/, $(notdir $(ENCLAVE_SRC:.c=.o) $(ENCLAVE_SRC:.S=.o)))

$(BUILD_DIR)/%.o: %.S | $(BUILD_DIR)
	$(cc)  -c $< -o $@

$(BUILD_DIR)/%.o: %.c | $(BUILD_DIR)
	$(cc) -c $< -o $@

$(BUILD_DIR)/%.vmh: $(BUILD_DIR)/%.rv32 $(elf2hex)
	$(elf2hex) $< 0 256K 4 $@

$(elf2hex):
	$(MAKE) -C elf2hex

# Linker scripts
ENCLAVE_LD := $(BUILD_DIR)/link.ld
$(ENCLAVE_LD) : link.ld.in | $(BUILD_DIR)
	$(RISCVCC32) -E -x c -I $(CURDIR) $< | grep -v "^#" > $@


# ELF files
ENCLAVE_ELF := $(BUILD_DIR)/enclave.rv32
ENCLAVE_DUMP:= $(BUILD_DIR)/enclave.dump
ENCLAVE_VMH := $(BUILD_DIR)/enclave.vmh

$(ENCLAVE_ELF) : $(ENCLAVE_LD) $(OBJ_ALL) | $(BUILD_DIR)
	riscv-none-embed-ld -T $(ENCLAVE_LD) -o $@ $(OBJ_ALL)

$(BUILD_DIR)/%.dump: $(BUILD_DIR)/%.rv32 | $(BUILD_DIR)
	$(objdump) $< > $@

# BINARY files
#ENCLAVE_BIN := $(BUILD_DIR)/enclave.rv32 
#ENCLAVE0_BIN := $(BUILD_DIR)/enclave0.bin
#ENCLAVE1_BIN := $(BUILD_DIR)/enclave1.bin

#$(ENCLAVE_BIN) : $(ENCLAVE_ELF) | $(BUILD_DIR)
#	$(objcopy) -O binary --only-section=.text0 --only-section=.text1 --only-section=.data0 --only-section=.data1 --only-section=.rodata0 --only-section=.rodata1 --only-section=.bss0 --only-section=.bss1 $< $@
	
#	text --only-section=.rodata --only-section=srodata* --only-section=.data --only-section=.sdata --only-section=.bss --only-section=.sbss $< $@	
#test:
#	echo $(OBJ_ALL)
all: $(ENCLAVE_ELF) $(ENCLAVE_DUMP) $(ENCLAVE_VMH)

clean: 
	rm -rf $(BUILD_DIR)
