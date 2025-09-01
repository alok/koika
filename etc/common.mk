# check makefile version
# (https://github.com/mit-plv/koika/issues/18)
ifeq ($(filter output-sync,$(value .FEATURES)),)
	$(info You have Make version $(MAKE_VERSION).)
	$(error Unsupported version of Make. Please use GNU Make >= 4.0)
endif

# check if terminal supports color + define color variables
# TODO test colors without direnv
ifneq ($(COLORS_TESTED),y)
	COLORS_TESTED := y
	COLORS_SUPPORTED := $(shell tput colors &>/dev/null && echo -n 'y' || echo -n 'n')
	export COLORS_SUPPORTED
endif
ifeq ($(COLORS_SUPPORTED), y)
	BLACK   = $(shell tput setaf 0)
	RED     = $(shell tput setaf 1)
	GREEN   = $(shell tput setaf 2)
	YELLOW  = $(shell tput setaf 3)
	BLUE    = $(shell tput setaf 4)
	MAGENTA = $(shell tput setaf 5)
	CYAN    = $(shell tput setaf 6)
	RESET   = $(shell tput sgr0)
	DIM     = $(shell tput dim)
	BOLD    = $(shell tput bold)
else
	BLACK   =
	RED     =
	GREEN   =
	YELLOW  =
	BLUE    =
	MAGENTA =
	CYAN    =
	RESET   =
endif

# center = center() { printf "%*s%s\n" $$(( ( $$(tput cols) - $${\#*} ) / 2 )) "" "$$*" }; center

emph-print  = printf '%s\n' '$(BOLD)$(YELLOW)$(1)$(RESET)'
emph2-print = printf '%s\n' '$(BLUE)$(1)$(RESET)'
err-print   = printf '%s\n' '$(RED)$(1)$(RESET)'
dim-print   = printf '%s\n' '$(DIM)$(1)$(RESET)'

# Disable built-in rules
MAKEFLAGS += --no-print-directory --no-builtin-rules
export MAKEFLAGS

verbose := $(if $(V),,@)

ROOT := $(shell while [ ! -e dune-project ] && [ "$$PWD" != "/" ]; do cd ..; done; pwd)

BUILD_DIR := $(ROOT)/_build/default

SUBDIR := $(patsubst $(ROOT)%,%,$(shell pwd))

.PHONY: help
help::
	@$(call emph-print,== <{ help($(SUBDIR)) }> ==)
	@$(call dim-print,Please specify one of the following targets:)
	@echo ""
	@echo "help          - this help page"

.PHONY: FORCE
FORCE:

.DEFAULT_GOAL := help