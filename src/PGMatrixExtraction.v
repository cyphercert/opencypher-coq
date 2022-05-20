Require Import PropertyGraph.

Import PropertyGraph.

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
From RelationAlgebra Require Import syntax matrix bmx ordinal.
From RelationAlgebra Require Import monoid boolean prop sups bmx.

Local Open Scope nat_scope.

Fixpoint list_of_label_to_vlabel (l : list label) : list Label :=
  match l with
  | nil => nil
  | a :: m => vlabel a :: list_of_label_to_vlabel m
  end.

(*Definition pg_extract_lmatrices (n : nat) (vlab : vertex -> list label) (lbl : Label) :
    ord n -> ord n -> bool := 
  fun (x y : ord n) => 
      if eqb_ord x y then Utils.list_inb lbl (list_of_label_to_elabel (vlab x)) 
      else false.
 *)

Definition pg_extract_lmatrices (n : nat) (vlab : vertex -> list label) (lbl : Label) :
    bmx n n :=
  fun x y =>
      if eqb_ord x y then sup (fun i => Label_eqb lbl i) (list_of_label_to_vlabel (vlab x))
                     else false.

Definition ord_to_nat (n : nat) (o : ord n) : nat :=
  match o with
  | Ord k _ => k
  end.

Definition pg_extract_tmatrices (n : nat) (edges : list edge) (elab : edge -> label)
  (st : edge -> vertex * vertex) (lbl : Label) : bmx n n :=
  fun x y => sup (fun edge => andb (andb
                  (Nat.eqb (fst (st edge)) (ord_to_nat n x))
                  (Nat.eqb (snd (st edge)) (ord_to_nat n y)))
                 (Label_eqb (elabel (elab edge)) lbl)) edges.

(* Deinition pg_extract_matrices (g : PropertyGraph.t) :=
  let n := List.length g.(vertices) in
  (get_labels_matrices n g.(vlab)) ++ (get_types_matrices n g.(edges) g.(elab) g.(st)). *)
