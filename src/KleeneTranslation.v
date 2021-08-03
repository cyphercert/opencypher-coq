From Coq Require Import BinNums.
From Coq Require Import BinInt.
From Coq Require Import List.

From OpencypherCoq Require Import Cypher.
From RelationAlgebra Require Import syntax matrix bmx ordinal.
Import ListNotations.

From RelationAlgebra Require Import kleene boolean sups matrix.
From OpencypherCoq Require Import PropertyGraph.
Import PropertyGraph.

Definition get_labels_matrices (n : nat) (vlab : vertex -> list label) : list (label * (ord n -> ord n -> boolean)) := .
Definition get_types_matrices (n : nat) (elab : edge -> label) (st : edge -> vertex * vertex) : list (label * (ord n -> ord n -> boolean)) := .

Definition labels := get_labels_matrices 




































Fixpoint get_current_label (n : nat) (cur : )

Fixpoint get_labels (n : nat) (vlab : vertex -> list label) : list (label * (ord n -> ord n -> boolean)) :=
    let a := [] in 



Definition ord0 {n}: ord (S n) := @Ord (S n) 0 eq_refl.

Print ord_lt.

Open Scope positive_scope.

Definition var := nat.
Definition s (_ : var) : positive := 1.
Definition t (_ : var) : po

Definition f' (_ : positive) :

Definition example_bmx (i j : ord 1) : bool := true.

Definition var_assignment (v : var) :

Definition e := eval 1 1.


(*

(10) ----> (7)

*)
