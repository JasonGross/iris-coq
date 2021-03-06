# IRIS COQ DEVELOPMENT

This is the Coq development of the [Iris Project](http://iris-project.org),
which includes [MoSeL](http://iris-project.org/mosel/), a general proof mode
for carrying out separation logic proofs in Coq.

A LaTeX version of the core logic definitions and some derived forms is
available in [docs/iris.tex](docs/iris.tex).  A compiled PDF version of this
document is [available online](http://plv.mpi-sws.org/iris/appendix-3.1.pdf).

## Building Iris

### Prerequisites

This version is known to compile with:

 - Coq 8.7.1 / 8.7.2 / 8.8.0 / 8.8.1
 - A development version of [std++](https://gitlab.mpi-sws.org/robbertkrebbers/coq-stdpp)

For a version compatible with Coq 8.6, have a look at the
[iris-3.1 branch](https://gitlab.mpi-sws.org/FP/iris-coq/tree/iris-3.1).
If you need to work with Coq 8.5, please check out the
[iris-3.0 branch](https://gitlab.mpi-sws.org/FP/iris-coq/tree/iris-3.0).

### Working *with* Iris

To use Iris in your own proofs, we recommend you install Iris via opam (1.2.2 or
newer).  To obtain the latest stable release, you have to add the Coq opam
repository:

    opam repo add coq-released https://coq.inria.fr/opam/released

To obtain a development version, also add the Iris opam repository:

    opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git

Either way, you can now do `opam install coq-iris`.  To fetch updates later, run
`opam update && opam upgrade`.  However, notice that we do not guarnatee
backwards-compatibility, so upgrading Iris may break your Iris-using
developments.

### Working *on* Iris

To work on Iris itself, you need to install its build-dependencies.  Again we
recommend you do that with opam (1.2.2 or newer).  This requires the following
two repositories:

    opam repo add coq-released https://coq.inria.fr/opam/released
    opam repo add iris-dev https://gitlab.mpi-sws.org/FP/opam-dev.git

Once you got opam set up, run `make build-dep` to install the right versions
of the dependencies.

Run `make -jN` to build the full development, where `N` is the number of your
CPU cores.

To update Iris, do `git pull`.  After an update, the development may fail to
compile because of outdated dependencies.  To fix that, please run `opam update`
followed by `make build-dep`.

## Directory Structure

* The folder [algebra](theories/algebra) contains the COFE and CMRA
  constructions as well as the solver for recursive domain equations.
* The folder [base_logic](theories/base_logic) defines the Iris base logic and
  the primitive connectives.  It also contains derived constructions that are
  entirely independent of the choice of resources.
  * The subfolder [lib](theories/base_logic/lib) contains some generally useful
    derived constructions.  Most importantly, it defines composeable
    dynamic resources and ownership of them; the other constructions depend
    on this setup.
* The folder [program_logic](theories/program_logic) specializes the base logic
  to build Iris, the program logic.   This includes weakest preconditions that
  are defined for any language satisfying some generic axioms, and some derived
  constructions that work for any such language.
* The folder [bi](theories/bi) contains the BI++ laws, as well as derived
  connectives, laws and constructions that are applicable for general BIS.
* The folder [proofmode](theories/proofmode) contains
  [MoSeL](http://iris-project.org/mosel/), which extends Coq with contexts for
  intuitionistic and spatial BI++ assertions. It also contains tactics for
  interactive proofs. Documentation can be found in
  [ProofMode.md](ProofMode.md).
* The folder [heap_lang](theories/heap_lang) defines the ML-like concurrent heap
  language
  * The subfolder [lib](theories/heap_lang/lib) contains a few derived
    constructions within this language, e.g., parallel composition.
    For more examples of using Iris and heap_lang, have a look at the
    [Iris Examples](https://gitlab.mpi-sws.org/FP/iris-examples).
* The folder [tests](theories/tests) contains modules we use to test our
  infrastructure. Users of the Iris Coq library should *not* depend on these
  modules; they may change or disappear without any notice.

## Case Studies

The following is a (probably incomplete) list of case studies that use Iris, and
that should be compatible with this version:

* [Iris Examples](https://gitlab.mpi-sws.org/FP/iris-examples) is where we
  collect miscellaneous case studies that do not have their own repository.
* [LambdaRust](https://gitlab.mpi-sws.org/FP/LambdaRust-coq/) is a Coq
  formalization of the core Rust type system.
* [iGPS](https://gitlab.mpi-sws.org/FP/sra-gps/tree/gen_proofmode_WIP) is a
  logic for release-acquire memory.
* [Iris Atomic](https://gitlab.mpi-sws.org/FP/iris-atomic/) is an experimental
  formalization of logically atomic triples in Iris.

## Notes for Iris Developers

* Information on how to set up your editor for unicode input and output is
  collected in [Editor.md](Editor.md).
* The Iris Proof Mode (IPM) / MoSeL is documented at [ProofMode.md](ProofMode.md).
* Naming conventions are documented at [Naming.md](Naming.md).

### How to update the std++ dependency

* Do the change in std++, push it.
* Wait for CI to publish a new std++ version on the opam archive, then run
  `opam update iris-dev`.
* In Iris, change the `opam` file to depend on the new version.
* Run `make build-dep` (in Iris) to install the new version of std++.
  You may have to do `make clean` as Coq will likely complain about .vo file
  mismatches.

### How to write/update test cases

The files in `tests/` are test cases.  Each of the `.v` files comes with a
matching `.ref` file containing the expected output of `coqc`.  Adding `Show.`
in selected places in the proofs makes `coqc` print the current goal state.
This is used to make sure the proof mode prints goals and reduces terms the way
we expect it to.  You can run `MAKE_REF=1 make` to re-generate all the `.ref` files;
this is useful after adding or removing `Show.` from a test.  If you do this,
make sure to check the diff for any unexpected changes in the output!
