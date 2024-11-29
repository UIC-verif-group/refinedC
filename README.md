# RefinedC verification framework ([webpage](https://plv.mpi-sws.org/refinedc/))

This repository contains the source code of **RefinedC**: a foundational
verification framework targeted at idiomatic C code. Thanks to its frontend
(written in OCaml), RefinedC automatically translates annotated C source code
into a deep embedding of our **Caesium** C semantics (in Coq), together with
corresponding function specs expressed using ownership and refinement types.
After this generation step, the RefinedC automation (built using our logic
programming framework called **Lithium**) takes over to prove user-defined
function specs (which can encode full functional correctness), possibly
leaving some (pure) side-conditions for the user to prove. To resolve such
side-conditions, the user can either extend the RefinedC automation or write
interactive Coq proofs. The RefinedC type system itself is also extensible to
allow expert users to add support for specific programming idioms through new
typing rules. Such additions must be proven sound against the semantic model
of RefinedC, which is encoded in [Iris](https://gitlab.mpi-sws.org/iris/iris)
(a modern framework for higher-order, concurrent separation logic).

## Documentation

The following files contain documentation about RefinedC:

- [ANNOTATIONS.md](ANNOTATIONS.md): Describes the annotation syntax
  accepted by the RefinedC frontend
- [FAQ.md](FAQ.md): Describes solutions to frequently asked questions
- [ARCHITECTURE.md](ARCHITECTURE.md): Gives an high-level overview of
  the layout of this repository.
- [DEVELOPERS.md](DEVELOPERS.md): Information for RefinedC developers.

There is a work in progress tutorial in [tutorial/](tutorial/) which
is also available in a standalone repository here:
https://gitlab.mpi-sws.org/msammler/refinedc-tutorial

## Installing RefinedC

RefinedC is known to compile with Coq 8.20.0, on 64-bits Linux machines. It
also possibly works on MacOS. In any case, we strongly advise you to rely on
[opam](https://opam.ocaml.org/doc/Install.html) to install dependencies.

Note that if you want to develop RefinedC or build the examples
shipped with RefinedC, you should install RefinedC according to the
instructions in [DEVELOPERS.md](DEVELOPERS.md).

### tl;dr

Assuming an appropriate [opam](https://opam.ocaml.org/doc/Install.html) switch
(OCaml version 4.14.0 at least), run the following commands.
```bash
sudo apt-get install libmpfr-dev # Implicit Cerberus dependency.
opam repo add coq-released "https://coq.inria.fr/opam/released"
opam repo add iris-dev "https://gitlab.mpi-sws.org/iris/opam.git"
opam update
opam pin add -n -y cerberus-lib "git+https://github.com/rems-project/cerberus.git#57c0e80af140651aad72e3514133229425aeb102"
opam pin add -n -y cerberus "git+https://github.com/rems-project/cerberus.git#57c0e80af140651aad72e3514133229425aeb102"
opam pin add refinedc "git+https://gitlab.mpi-sws.org/iris/refinedc.git"
```

If the `refinedc` command it not in the `PATH` and you installed
`refinedc` in an opam switch, try `eval $(opam env)` in the directory
where you created the switch.

### System dependencies

In order to install RefinedC you will need to make sure that you have the GNU
MPFR library on your system (`libmpfr-dev` package on Debian). It is required
by [Cerberus](https://github.com/rems-project/cerberus), which we use or our
frontend (but the dependency is implicit).

The frontend also requires a C compiler (accessible through `cc`). A standard
GCC or Clang installation should do the trick.

### Setting up [opam](https://opam.ocaml.org/doc/Install.html)

First, make sure that the OCaml package manager `opam` is installed. To do so
you can check if the following command succeeds.
```bash
opam --version
```
If you already have `opam` version 2.1.0 or higher, then you can skip to the
next section.

Otherwise, install `opam` using your usual package manager (checking that a
recent enough version is available), or run the following command (taken from
the [official installation guide](https://opam.ocaml.org/doc/Install.html)).
```bash
sh <(curl -sL https://raw.githubusercontent.com/ocaml/opam/master/shell/install.sh)
```
You can use the `BINDIR` environment variable to choose where the binary is
installed. There is a reasonable default but it needs root privileges.

### Setting up an [opam](https://opam.ocaml.org) switch (optional)

If you are an OCaml user and if you know what you are doing, it is perfectly
fine to install RefinedC in any "opam switch" you like (provided the OCaml
version is 4.14.0 or higher) and you can skip this section.

In the following instructions we are going to create an "opam switch" (i.e., a
fresh OCaml environment) in which RefinedC can be installed and used. Creating
a new switch is a good way to make sure that other OCaml projects are not at
all impacted, even if they have conflicting dependencies. It makes sense to
follow these steps even if you are a practiced OCamler.

The "opam swith" we are going to create will be tied to a particular directory
of your system, and the corresponding OCaml environment (including `refinedc`)
will only be accessible form a shell when working under this directory. If you
are not quite sure what to do, simply create a new directory under which all
of you RefinedC will be placed. And then create the new switch in that folder.
```bash
mkdir refinedc-projects
opam switch create refinedc-projects ocaml-variants.4.14.0+options ocaml-option-flambda
```
You should then have an appropriate OCaml environment (with version 4.14.0) in
the `refinedc-projects` directory (or whatever you named it). In the following
we will assume that everything you do will be under that directory, so do not
forget to move into it.
```bash
cd refinedc-projects
```

### Installing RefiendC and its dependencies

RefinedC requires Coq, Iris, as well as a number of OCaml dependencies. These
dependencies can be made available to opam by running the following commands.
```bash
opam repo add coq-released "https://coq.inria.fr/opam/released"
opam repo add iris-dev "https://gitlab.mpi-sws.org/iris/opam.git"
opam update
opam pin add -n -y cerberus-lib "git+https://github.com/rems-project/cerberus.git#57c0e80af140651aad72e3514133229425aeb102"
opam pin add -n -y cerberus "git+https://github.com/rems-project/cerberus.git#57c0e80af140651aad72e3514133229425aeb102"
```
You can then finally install RefinedC with the following command, or rather
decide to install it from a local clone to have access to various examples.
```bash
opam pin add refinedc "git+https://gitlab.mpi-sws.org/iris/refinedc.git"
```

To install RefinedC from a local clone you can run the following commands.
```bash
git clone "https://gitlab.mpi-sws.org/iris/refinedc.git"
opam pin add refinedc refinedc
```
You can then start checking annotated C files in the repository using, for
example, the following command.
```bash
cd refinedc
refinedc check examples/queue.c
```

## Verifying a program from scratch using RefinedC

In this section we will see how one can create a new RefinedC project and
verify a first (trivial) program example. It is assumed that RefinedC has
been installed following the above instructions.

### Source project setup

In the following, we will assume that the user's code lives in a directory
`c_example` with the following structure.
```
├── Makefile
└── src
    └── example.c
```
File `Makefile`:
```make
all: src/example
.PHONY: all

src/example: src/example.c
	gcc -Wno-attributes -o $@ $<

clean:
	rm -f src/example
.PHONY: clean
```
File `src/example.c`:
```c
#include <assert.h>

unsigned int add3(unsigned int x, unsigned int y, unsigned int z){
  unsigned int r = x + y;
  return r + z;
}

int main(){
  unsigned int a;

  a = add3(1, 2, 3);
  assert(a == 6u);

  a = add3(a, a, a);
  assert(a == 18u);

  return 0;
}
```
Of course, bigger projects, with more source files and more complex directory
structure will work just as well, but we start simple so that you can see how
things work more easily.

### RefinedC project creation

The first step for verifying a C program using RefinedC is to set up a new
RefinedC project. To do so, you must run the following command at the root of
the source tree (i.e., exactly where you would typically run `git init`).
```bash
cd c_example
refinedc init
```
If all goes well, `refinedc init` will report that a RefinedC project has been
initialized in your `c_example` directory, and it should also give the logical
Coq directory (i.e., the module path) that will be used as a prefix for every
Coq module of your project. Its default value is based on the name of the
project directory, but this behaviour can be overridden. (Note that you can
use `refinedc init --help` to see what options are available.)

After having successfully initialised the RefinedC project, your `c_example`
directory should contain the following.
```
├── _CoqProject       ← Coq project file, maintained by RefinedC.
├── dune-project      ← Dune project file, used by RefinedC internally.
├── Makefile
├── rc-project.toml   ← RefinedC project configuration
└── src
    └── example.c
```
The generated files should not be edited directly, to the exception of the
project configuration file `rc-project.toml`, which is used to configure
certain things like C preprocessor options or Coq dependencies. For now, you
don't need to worry about it.

### Running RefinedC

We are now ready to actually run RefinedC on our C source file. So, go ahead
and run the following command.
```bash
refinedc check src/example.c
```
If everything goes well, this command will generate the necessary Coq files,
and then automatically run Coq to check them. Let us have a look to the files
contained in our project folder to see what happened.
```
├── _build                             ← Dune build directory.
├── _CoqProject
├── dune-project
├── Makefile
├── rc-project.toml
└── src
    ├── example.c
    └── proofs                         ← Coq files for all C files in [src].
        └── example                    ← Coq files for [src/example.c].
            ├── dune                   ← Generated dune file.
            ├── generated_code.v       ← Generated code file.
            ├── generated_proof_add3.v ← Generated proof file for [add3].
            ├── generated_proof_main.v ← Generated proof file for [main].
            ├── generated_spec.v       ← Generated specification file.
            └── proof_files            ← Internally used file.
```
You can see that a whole bunch of files have been generated inside a new
directory `src/proofs/example`. This directory gathers all Coq files that
are specific to the `src/example.c` file. It contains generated files, but
the user can also write their own Coq source files there. Note that we use
the convention that generated Coq files are prefixed with `generated_`. Note
also that Coq compilation does not directly happen in the source directory,
but in the `_build` directory, which is automatically created by calling the
`dune` build system (used by RefinedC internally).

You might now wonder: what have we proved about our program? And the answer
is: nothing. Indeed, RefinedC checks function specifications, but such specs
must be provided by the user. So far we have not given any RefinedC spec for
our two functions `add3` and `main`. In fact, if you edit the proof file at
`src/proofs/example/generated_proof_add3.v` you will see that it only holds
a comment saying that the function has no spec. And similarly, if you look at
the file `src/proofs/example/generated_spec.v` you will see that none of our
functions have a specification (they have been skipped).

### A spec for `add3`

Let us now do some actual RefinedC verification and give a specification to
our `add3` function. Specifications are given as attributes attached to the
function definitions (or prototypes). The valid attributes and the RefinedC
syntax are documented in [ANNOTATIONS.md](ANNOTATIONS.md), you can consult it
later if you want to learn more. For now, we will introduce what we need en
passant.

In RefinedC, a function specification is given by a type. And as one might
expect, the type of a function is specified by giving a type for each of the
arguments and a type for the return value. The C type of the arguments and
the return type of `add3` are all `unsigned int`. The corresponding RefinedC
type is `int<u32>`, so you can edit `src/example.c` as follows.
```c
[[rc::args("int<u32>", "int<u32>", "int<u32>")]]
[[rc::returns("int<u32>")]]
unsigned int add3(unsigned int x, unsigned int y, unsigned int z){
  unsigned int r = x + y;
  return r + z;
}
```
Here, the `rc::args` annotation gives the type for each function argument (in
order), and the `rc::returns` annotation gives the type of the return value.

Let us now see what happens if we run RefinedC again.
```bash
refinedc check src/example.c
```
This time the system actually attempts to prove something, but it fails with
two error messages of the following form (abbreviated).
```
Cannot solve sidecondition in function "add3" !
```
Next to the messages, Coq goals are shown to tell us what it is that could not
be proved. In our case, both goals are of the form `_ + _ ≤ max_int u32`. That
explains the error: the additions in our `add3` function can overflow (which
leads to undefined behaviour in RefinedC).

To solve this problem we need to extend the function specification using two
pre-conditions. However, these preconditions need to mention the actual value
of the function arguments, which is not yet available in the specification. To
this aim we must use refinement types of the form `n @ int<u32>`, Intuitively
corresponding to a singleton (integer) type with value `n`.
```
[[rc::parameters("nx : nat", "ny : nat", "nz : nat")]]
[[rc::args("nx @ int<u32>", "ny @ int<u32>", "nz @ int<u32>")]]
[[rc::requires("{nx + ny ≤ max_int u32}", "{(nx + ny) + nz ≤ max_int u32}")]]
[[rc::returns("int<u32>")]]
unsigned int add3(unsigned int x, unsigned int y, unsigned int z){
  unsigned int r = x + y;
  return r + z;
}
```
Note that the `rc::parameters` annotation is used to introduced universally
quantified variables in the specifications. Here all such variables are given
the Coq type `nat`, and the pre-conditions given with `rc::requires` are
expressed as Coq propositions (wrapped in braces to escape to Coq syntax).
After this modification, the specification is successfully checked by calling
RefinedC.
```bash
refinedc check src/example.c
```

### Verifying `main`

Let us now turn to the `main` function, whose specification should be fairly
trivial: it take no arguments and returns an integer which happens to always
be `0`. This can be expressed using the following RefinedC spec.
```c
[[rc::returns("{0} @ int<i32>")]]
int main(){
  unsigned int a;

  a = add3(1, 2, 3);
  assert(a == 6u);

  a = add3(a, a, a);
  assert(a == 18u);

  return 0;
}
```
One important thing that this spec implies is that the evaluation of `main`
does not fail. In particular, RefinedC needs to check that the assertions will
never fail. Let us check if it is able to do so.
```bash
refinedc check src/example.c
```

Not quite! And the reason is that the specification of `add3` is too weak: it
only says that its return value is an unsigned integer. In particular, its
return value is not linked to its arguments in any way. Hence, it is not very
surprising that RefinedC cannot establish that the result of `add3(1, 2, 3)`
is equal to `6u`.

To fix this, we can change the return type of `add3` to be the following.
```c
[[rc::returns("{nx + ny + nz} @ int<u32>")]]
```
With this modification, the verification finally goes through.
```bash
refinedc check src/example.c
```
Congratulations, you have verified your first C program using RefinedC!
