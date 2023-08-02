all:
	@dune build _build/default/refinedc.install --display short
.PHONY: all

all_with_examples: generate_all
	@dune build --display short
.PHONY: all_with_examples

install:
	@dune install
.PHONY: install

uninstall:
	@dune uninstall
.PHONY: uninstall

C_SRC = $(wildcard examples/*.c) $(wildcard examples/VerifyThis2021/*.c) $(wildcard tutorial/*.c) $(wildcard tutorial/VerifyThis/*.c) $(wildcard linux/casestudies/*.c) $(wildcard linux/pkvm/*.c) $(wildcard examples/scheduler/src/fdsched.c)

%.c.gen: %.c phony
	@dune exec -- refinedc check $<
.PHONY: phony

generate_all: $(addsuffix .gen, $(C_SRC))
.PHONY: generate_all

check_generate_all: generate_all
	git diff --exit-code
.PHONY: check_generate_all

clean_generated:
	@for FILE in ${C_SRC} ; do dune exec -- refinedc clean --soft $$FILE ; done
	@rm -f $(addsuffix .gen, $(C_SRC))
.PHONY: clean_generated

clean: clean_generated
	@dune clean
.PHONY: clean

# We cannot use builddep-pins as a dependency of builddep-opamfiles because the CI removes all pins.
builddep-pins:
	@opam pin add -n -y cerberus-lib "git+https://github.com/rems-project/cerberus.git#57c0e80af140651aad72e3514133229425aeb102"
	@opam pin add -n -y cerberus "git+https://github.com/rems-project/cerberus.git#57c0e80af140651aad72e3514133229425aeb102"
.PHONY: builddep-pins

builddep-opamfiles: builddep/refinedc-builddep.opam
	@true
.PHONY: builddep-opamfiles

# see https://stackoverflow.com/a/649462 for defining multiline strings in Makefiles
define BUILDDEP_OPAM_BODY
opam-version: "2.0"
name: "refinedc-builddep"
synopsis: "---"
description: """
---
"""
license: "BSD-3-Clause"
maintainer: ["Michael Sammler <msammler@mpi-sws.org>"
             "Rodolphe Lepigre <lepigre@mpi-sws.org>"]
authors: ["Michael Sammler" "Rodolphe Lepigre"]
homepage: "https://plv.mpi-sws.org/refinedc"
bug-reports: "https://gitlab.mpi-sws.org/iris/refinedc/issues"
dev-repo: "git+https://gitlab.mpi-sws.org/iris/refinedc.git"
depends: [
endef
export BUILDDEP_OPAM_BODY

# Create a virtual Opam package with the same deps as RefinedC, but no
# build.
builddep/refinedc-builddep.opam: refinedc.opam coq-lithium.opam Makefile
	@echo "# Creating builddep package."
	@mkdir -p builddep
	@echo "$$BUILDDEP_OPAM_BODY" > $@
	@opam show -f depends: ./coq-lithium.opam >> $@
	@opam show -f depends: ./refinedc.opam | sed 's/"coq-lithium".*//g' >> $@
	@echo "]" >> $@

# Install the virtual Opam package to ensure that:
#  1) dependencies of RefinedC are installed,
#  2) they will remain satisfied even if other packages are updated/installed,
#  3) we do not have to pin the RefinedC package itself (which takes time).
# Note: We also need to install cerberus to make sure that new pins are propagated correctly.
builddep: builddep/refinedc-builddep.opam builddep-pins
	@echo "# Installing package $<."
	@opam install $(OPAMFLAGS) $< cerberus
.PHONY: builddep

DUNE_FILES = $(shell find theories/ -type f -name 'dune')

# Currently, we don't need to do anything special before building RefinedC in opam.
prepare-install-refinedc:
	@true
.PHONY: prepare-install-refinedc

# FIXME
#TUTORIAL_SRC = \
#	theories/examples/tutorial/t3_list.c \
#	theories/examples/tutorial/t4_alloc.c \
#	theories/examples/tutorial/t5_main.c \
#	theories/examples/spinlock/spinlock.c
#
#theories/examples/tutorial/tutorial: $(TUTORIAL_SRC)
#	clang -fdouble-square-bracket-attributes -Wno-unknown-attributes -g -O0 $^ -o $@
