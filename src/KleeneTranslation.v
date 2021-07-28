From Coq Require Import BinNums.
From Coq Require Import BinInt.
From RelationAlgebra Require Import syntax matrix bmx ordinal.

Open Scope positive_scope.

Definition var := nat.
Definition s (_ : var) : positive := 1.
Definition t (_ : var) : positive := 1.

Definition expr1 : expr s t _ _ := e_zer 1 1.

Compute monoid.ob bmx.

Definition f' (_ : positive) :

Definition example_bmx (i j : ord 1) : bool := true.

Definition var_assignment (v : var) :

Definition e := eval 1 1.


(*

(10) ----> (7)

*)
