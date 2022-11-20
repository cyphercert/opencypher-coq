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

This project supports two build systems:
- `dune`

    After you setup the switch, run the following command to build the project:
    ```console
    $ dune build
    ```

- `coq_makefile`

    You can simply run `make` (or more specifically `make build`) to generate all the necessary configuration files and build all the theories. 
    
    Note that this will create all the build artefacts right in the `src` next to the theories sources. To clean up the auxilliary files and the build artefacts run `make clean`.

## IDE support

If you have chosen to use `dune` as a primary build system, to enable interactive development in an IDE you can generate a `_CoqProject` file with:
```console
$ make _CoqProject.dune
$ cp _CoqProject.dune _CoqProject
```

Note that this `_CoqProject` file is incompatible with `_CoqProject` file for `coq_makefile`.

Note that some IDEs require to be configured to work with the local `coq` installation. For example, to be able to use it with `VSCoq` plugin you have to set `Coq: Bin Path` setting. You can look up the path with `where coqtop` command when the local switch is active.