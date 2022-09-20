#!/usr/bin/env bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add coq-released-hahn https://github.com/vafeiadis/hahn.git
opam install coq-relation-algebra coq-hahn
