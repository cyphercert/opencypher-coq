Require Import PropertyGraph.

Import PropertyGraph.
From RelationAlgebra Require Import syntax matrix bmx ordinal.
From RelationAlgebra Require Import monoid boolean prop sups bmx.
Require Import List.
Import ListNotations.
Require Import String.
Require Import Utils.
Require Import BinNums.
Require Import BinInt.
Require Import Notations.
Require Import Ltac.
Require Import Logic.
Require Import Basics.
Set Implicit Arguments.

Local Open Scope nat_scope.

Fixpoint list_of_label_to_elabel (l : list label) : list Label :=
  match l with
  | nil => nil
  | a :: m => elabel a :: list_of_label_to_elabel m
  end.

(*Definition pg_extract_lmatrices (n : nat) (vlab : vertex -> list label) (lbl : Label) :
    ord n -> ord n -> bool := 
  fun (x y : ord n) => 
      if eqb_ord x y then Utils.list_inb lbl (list_of_label_to_elabel (vlab x)) 
      else false.
*)
Print mx.

Search mx.
Print bmx.
Lemma temp (AA: bmx 0 0) : False.
Definition pg_extract_lmatrices (n : nat) (vlab : vertex -> list label) (lbl : Label) :
    bmx n n :=
  fun x y =>
      if eqb_ord x y then sup (fun i => Label_eqb lbl i) (list_of_label_to_elabel (vlab x))
                     else false.

Definition pg_extract_tmatrices (n : nat) (edges : list edge) (elab : edge -> label)
  (st : edge -> vertex * vertex) (lbl : Label) : bmx n n :=
  fun x y => sup (fun edge => andb (andb 
                 (eqb_ord (ord (fst (st edge))) x) 
                 (eqb_ord (ord (snd (st edge))) y)) 
                 (Label_eqb (elabel (elab edge)) lbl)) edges.


Search monoid.mor.
Print monoid.str.
Print mx.
Print eval.
Print monoid.ofbool.
Print monoid.one.
Print monoid.mor.
Search lattice.ops.
(* Deinition pg_extract_matrices (g : PropertyGraph.t) :=
  let n := List.length g.(vertices) in
  (get_labels_matrices n g.(vlab)) ++ (get_types_matrices n g.(edges) g.(elab) g.(st)). *)
