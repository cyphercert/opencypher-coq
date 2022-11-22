![Build Status](https://github.com/cyphercert/opencypher-coq/actions/workflows/docker-action.yml/badge.svg?branch=master)
# opencypher-coq
A Coq formalizaton of "Formalizing openCypher Graph Queries in Relational Algebra" [Marton-al:ADBIS17]

## Building 
You must have `opam` [installed](https://opam.ocaml.org/doc/Install.html).

For an easy start run in the project root:
```console
$ ./make_switch.sh
```
This will create a local `opam` switch, configure repositories, and install all the dependencies.

To generate all the necessary configuration files and build all the theories you can simply run `make` (or more specifically `make build`).

Note that this will create all the build artefacts right in the `src` next to the theories sources. To clean up the auxilliary files and the build artefacts run `make clean`.

## IDE support

Note that some IDEs require to be configured to work with the local `coq` installation. For example, to be able to use it with `VSCoq` plugin you have to set `Coq: Bin Path` setting. You can look up the path with `where coqtop` command when the local switch is active.