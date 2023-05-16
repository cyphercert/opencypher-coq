#!/usr/bin/env bash
opam switch create ./ --yes --no-install --deps-only 4.12.0
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install . --deps-only --yes