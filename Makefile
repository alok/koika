ROOT := $(shell while [ ! -e dune-project ] && [ "$$PWD" != "/" ]; do cd ..; done; pwd)
include $(ROOT)/etc/common.mk

# building coq without subdirectories (i.e. without the big proofs)
.PHONY: coq
coq: configure
	@$(call emph-print,== <{ build(coq) }> ==)
	dune build @@coq/all

# building coq library and proofs (i.e. all subdirectories)
.PHONY: coq-all
coq-all: configure
	@$(call emph-print,== <{ build(coq) }> ==)
	dune build @coq/all

CHECKED_MODULES ?= OneRuleAtATime CompilerCorrectness/Correctness

# TODO: fails
.PHONY: coq-check
coq-check: coq-all
	coqchk --output-context -R $(BUILD_DIR)/coq Koika $(patsubst %,$(BUILD_DIR)/coq/%.vo,$(CHECKED_MODULES))

.PHONY: ocaml
ocaml: configure
	$(verbose)$(MAKE) -C ocaml build

####################
# Examples & tests #
####################

.PHONY: configure
configure:
	$(verbose)$(MAKE) -C tests dune.inc
	$(verbose)$(MAKE) -C examples dune.inc

.PHONY: examples
examples: configure
	$(verbose)$(MAKE) -C examples all

.PHONY: tests
tests: configure
	$(verbose)$(MAKE) -C tests all


#################
# Whole project #
#################

readme:
	@$(call emph-print,== <{ update(README.rst) }> ==)
	@if command -v python &> /dev/null; \
		then python ./etc/readme/update.py README.rst; \
		else echo "python not available - skipping readme update"; fi

package:
	@$(call emph-print,== <{ package() }> ==)
	$(verbose)etc/package.sh

dune-all: coq ocaml
	@printf "\n== Completing full build =="
	dune build @all

all: coq ocaml examples tests readme;

clean-%: FORCE %/
	$(verbose)$(MAKE) -C $* clean

clean: clean-tests clean-examples
	@$(call emph-print,== <{ clean() }> ==)
	dune clean
	rm -f koika-*.tar.gz

.PHONY: readme package dune-all all clean

help-%: FORCE
	$(verbose)$(MAKE) -C $* help

help::
	@echo "help-<subdir> - help page for subdir"
	@echo
	@echo "all           - build everythin: coq + ocaml + examples + test + .."
	@echo "coq           - build coq files"
	@echo "coq-all       - build coq files + proofs"
	@echo "coq-check     - check axiomatic dependencies of important theorems"
	@echo "examples      - build all examples"
	@echo "tests         - build all tests"
	@echo "clean         - clean build files"
	@echo "package       - create a .tar.gz-file of the current state"
	@echo "configure     - create **/dune.inc files"

.SUFFIXES:

# Running two copies of dune in parallel isn't safe, and dune is already
# handling most of the parallelism for us
.NOTPARALLEL:

.SUFFIXES:
