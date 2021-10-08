Require Import PropertyGraph.
Import PropertyGraph.
From RelationAlgebra Require Import syntax matrix bmx ordinal.
Require Import List.
Import ListNotations.
Require Import String.
Require Import Bool.
Require Import Utils.
Require Import BinNums.
Require Import BinInt.
Require Import Notations.
Require Import Ltac.
Require Import Logic.
Require Import Basics.

Set Implicit Arguments.

Inductive Label :=
| vlabel (l : label)
| elabel (l : label)
.

Definition pg_extract_lmatrices (n : nat) (vlab : vertex -> list label) : 
  list (Label * (ord n -> ord n -> bool)) :=
  let labels := list_unique (List.concat (map (fun i => vlab i) (List.seq 0 n))) in
  map (fun lbl => let mtx (x y : ord n) := 
    if eqb_ord x y then Utils.list_inb lbl (vlab x) else false in (vlabel lbl, mtx)) labels.

Definition ord_to_nat (n : nat) (o : ord n) : nat :=
  match o with 
  | Ord k _ => k
  end.

Definition pg_extract_tmatrices (n : nat) (edges : list edge) (elab : edge -> label)
  (st : edge -> vertex * vertex) : list (Label * (ord n -> ord n -> bool)) :=
  let labels := list_unique (map (fun edge => elab edge) edges) in
  map (fun lbl => 
    let mtx (x y : ord n) := Utils.list_inb_b 
      true 
      (map (fun edge => 
        andb 
          (andb 
            (Nat.eqb (fst (st edge)) (ord_to_nat n x)) 
            (Nat.eqb (snd (st edge)) (ord_to_nat n y))) 
          (String.eqb (elab edge) lbl)) edges) in (elabel lbl, mtx)) labels.

(* Definition pg_extract_matrices (g : PropertyGraph.t) := 
  let n := List.length g.(vertices) in
  (get_labels_matrices n g.(vlab)) ++ (get_types_matrices n g.(edges) g.(elab) g.(st)). *)