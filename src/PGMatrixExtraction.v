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
(** To work properly with the graph we should transfer it to the adjacency matrix. *)
(** Adjacency matrix has type bmx, matrix of booleans, which is implemented in RelationAlgebra library *)
(** (see http://perso.ens-lyon.fr/damien.pous/ra/html/RelationAlgebra.bmx.html ) **)

Local Open Scope nat_scope.

(** Building adjacency matrix for current property graph **)

(** Adjacency matrix for verteces **)
Definition pg_extract_lmatrices (n : nat) (vlab : vertex -> list label) (lbl : Label) :
    bmx n n :=
  fun x y =>
      if eqb_ord x y then sup (fun i => Label_eqb lbl i) (map vlabel (vlab x))
                     else false.

Definition ord_to_nat (n : nat) (o : ord n) : nat :=
  match o with
  | Ord k _ => k
  end.

(** Adjacency matrix for edges **)
Definition pg_extract_tmatrices (n : nat) (edges : list edge) (elab : edge -> label)
  (st : edge -> vertex * vertex) (lbl : Label) : bmx n n :=
  fun x y => sup (fun edge => andb (andb
                  (Nat.eqb (fst (st edge)) (ord_to_nat n x))
                  (Nat.eqb (snd (st edge)) (ord_to_nat n y)))
                 (Label_eqb (elabel (elab edge)) lbl)) edges.
