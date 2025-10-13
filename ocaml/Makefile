ROOT := $(shell while [ ! -e dune-project ] && [ "$$PWD" != "/" ]; do cd ..; done; pwd)
include $(ROOT)/etc/common.mk

.PHONY: build
build:
	@$(call emph-print,== <{ build(OCaml-lib / cuttlec) }> ==)
	dune build cuttlec.exe @../install

.PHONY: clean
clean:
	@$(call emph-print,== <{ clean($(SUBDIR)) }> ==)
	rm -rf $(patsubst $(ROOT)%,$(BUILD_DIR)%,$(shell pwd))

.PHONY: help
help::
	@echo ""
	@echo "build         - build cuttlec / ocaml lib"
	@echo "clean         - clean build files"