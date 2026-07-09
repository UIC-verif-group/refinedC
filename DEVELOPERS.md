# Information for RefinedC developers

## Installation for development

Assumes a working install of `opam` with at least version 2.0.0 (see
https://opam.ocaml.org/doc/Install.html for installation
instructions), run the following commands in a fresh checkout of
RefinedC to get at working setup suitable for development of RefinedC
and building the examples in this repository:

```
opam switch create . ocaml-variants.4.14.2+options ocaml-option-flambda --no-install
sudo apt-get install libmpfr-dev # Implicit Cerberus dependency.
opam repo add coq-released "https://coq.inria.fr/opam/released"
opam repo add iris-dev "https://gitlab.mpi-sws.org/iris/opam.git"
make builddep
```

To build the files in this repository you also need to make sure that
your shell contains the correct opam environment, e.g. by running:
```
eval $(opam env)
```

## Updating dependencies

To upgrade the Iris dependency after the version has been updated in
`refinedc.opam`, run
```
opam update && make builddep && make clean
```

## make targets

The Makefile provides the following targets:

- `make all` or `make` builds the RefinedC type system without the examples
- `make all_with_examples` builds everything including examples
- `make generate_all` uses the frontend to regenerate the Caesium code
  for all examples
- `make clean` remove .vo files and other build artifacts

## Running RefinedC on examples in this repository

The `refinedc` program form the repository can be called using `dune` with the
following command.
```bash
dune exec -- refinedc
```
Note however that the command will not build the generated Coq code since this
would require invoking dune recursively under a dune environment, which is not
supported. The build is disabled in `rc-project.toml` with `no-build = true`.

To fully check an example in the repository you can use one of the following
two (equivalent) methods:
```bash
# With the build script.
./build.sh examples/queue.c

# Manually.
dune exec -- refinedc check examples/queue.c
cd examples/proofs/queue
dune build
cd -
```

To generate the Coq code for all the examples of the repository you can run
`make generate_all`. You can also force the generation of all the generated
code using `make -B generate_all`.

## Emacs setup

The following elisp function enables direct execution of the `build.sh` script in this repo from emacs.
It searches for a `build.sh` file in parent directories of the current file and executes it with the name
of the current file. A similar functionallity should be easy to add to other editors as well.
This script binds `build` to the keys `C-c c`. Use at your own risk!

```elisp
(setq build-file-name "build.sh")
(defun build ()
  "Search in the current and parent directories for a file with the name of variable `build-file-name' and execute the first file it find."
  (interactive)
  (save-some-buffers t) ; save all buffers
  (let ((buildfile (locate-dominating-file default-directory build-file-name)))
    (unless buildfile (error "No build file found!"))
    (let ((default-directory buildfile))
      (compile (concat buildfile build-file-name " " (buffer-file-name))))
    (select-window (get-buffer-window "*compilation*"))))
(global-set-key (kbd "C-c c") 'build)
```
