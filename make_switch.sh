#!/usr/bin/env bash
opam switch create opencypher-qcert 4.11.2
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq=8.12.2 coq-qcert=2.1.0 coq-relation-algebra coq-hahn
