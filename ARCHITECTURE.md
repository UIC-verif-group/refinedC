# Architecture

This document describes the source-code layout of RefinedC. This is
the right place to get an overview over the structure of this
repository.

Note: This document is based on the advice described in
https://matklad.github.io//2021/02/06/ARCHITECTURE.md.html

## Bird's eye view

```
├── theories                      Coq source code of RefinedC.
│   ├── lang                      Caesium formalization of C and Iris instantiation.
│   ├── lithium                   Lithium definition and interpreter.
│   └── typing                    RefinedC type system.

├── frontend                      Source code of the frontend.

├── include                       RefinedC extra include directory.

├── examples                      Examples of verified C code.
├── tutorial                      Stem of a tutorial (needs more work).
├── linux                         Examples based on Linux code

└── tools                         Scripts and stuff.
```

## RefinedC Coq code (`theories/`)

The main RefinedC development is contained in the `theories/` folder
and consists of Caesium in `theories/lang`, Lithium in
`theories/lithium` and the RefinedC type system in `theories/typing`.

**Architecture invariant:** Files in `theories/lang` must not depend
on files in `theories/lithium` or `theories/typing`. Files in
`theories/lithium` must not depend on files in `theories/typing` or
`theories/lang` with the exception of `theories/lang/base.v`.

## Frontend (`frontend/`)

The frontend directory contains the OCaml implementation of the
frontend that parses C code and converts to Caesium code and proofs
about the Caesium code.

## include files (`include/`)

RefinedC provides some include files that define macros to be used as
annotations. These live in `include/`.

## Examples (`examples/`, `tutorial/`, `linux/`)

The `examples/`, `tutorial/` and `linux/` directories contain many
examples of code verified using RefinedC. `tutorial/` contains the
start of a tutorial for RefinedC. `linux/` contains examples derived
from Linux code and thus all files in this directory are licensed
under GPL-2.0. `examples/` contains various other examples.

## tools (`tools/`)

The `tools/` directory contains some scripts necessary for the
RefinedC infrastructure.
