#!/usr/bin/env bash
git clone https://github.com/shananton/qcert.git
git checkout compile-with-coq8.13

opam repo add coq-released https://coq.inria.fr/opam/released
opam install . --deps-only

make
