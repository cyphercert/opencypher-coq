Require Import BinNums.
Require Import BinInt.
Require Import List.

(* Require Import Cypher. *)
(* From RelationAlgebra Require Import syntax matrix bmx ordinal. *)
(* Import ListNotations. *)

(* From RelationAlgebra Require Import kleene boolean sups matrix. *)
(* From OpencypherCoq Require Import PropertyGraph. *)
(* Import PropertyGraph. *)

(* TODO: find a standard function of boolean (in)equality on nat *)
Definition nat_eq (x y : nat) := true.
Definition nat_neq (x y : nat) := false.

(* TODO: remove *)
Definition vertex := Z.
Definition label := Z.
Definition ord (n : nat) := nat.

Definition label_neq (x y : label) := false.

Fixpoint list_unique (l : list label) :=
  match l with
  | nil => nil
  | cons h l =>
    h :: filter (fun x => label_neq x h)
      (list_unique l)
  end.

(* TODO: use definition from RelationAlgebra *)
Definition eq_ord {n} (x y : ord n) := true.

Definition list_in (lbl : label) (lbls : list label) : bool := 
  false.

Definition get_labels_matrices
           (n : nat) 
           (n2v : nat -> vertex)
           (vlab : vertex -> list label)
  : list (label * (ord n -> ord n -> bool)) :=
  let labels :=
      list_unique
        (concat
           (map (fun i => vlab (n2v i)) (seq 0 n) ))
  in
  map
    (fun lbl =>
       let mtx (x y : ord n) :=
           if eq_ord x y
           then
             (* TODO: List.In in boolean form *)
             list_in lbl (vlab (n2v x))
           else false
       in
       (lbl, mtx)
    )
    labels
.

Definition get_types_matrices
           (n : nat)
           (edges : list edge)
           (elab : edge -> label)
           (st : edge -> vertex * vertex)
  : list (label * (ord n -> ord n -> boolean)) :=
  let labels :=
      list_unique
        (concat
           (map (fun edge => elab edge) edges ))
  in
  map
    (fun lbl =>
       let mtx (x y : ord n) :=

       in
       (lbl, mtx)
    )
    labels
.

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
