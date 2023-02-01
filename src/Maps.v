From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
From Coq Require Import Classes.EquivDec.
From hahn Require Import HahnBase.

Require Import Utils.
(**From Coq Require Import omega.Omega.**)

(* ################################################################# *)
(**maps**)

Definition total_map (A : Type) := string -> A.
Definition total_map_nat (A : Type) := nat -> A.


Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_empty_nat {A : Type} (v : A) : total_map_nat A :=
  (fun _ => v).


Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if x ==b x' then v else m x'.

Definition t_update_nat {A : Type} (m : total_map_nat A)
                    (x : nat) (v : A) :=
  fun x' => if x ==b x' then v else m x'.


Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Notation "'_' '!!->' v" := (t_empty_nat v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).
Notation "x '!!->' v ';' m" := (t_update_nat m x v)
                              (at level 100, v at next level, right associativity).

(* ################################################################# *)
(** lemmas about total maps **)

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof. intros A x v. unfold t_empty. reflexivity. Qed.

Lemma t_apply_empty_nat : forall (A : Type) (x : nat) (v : A),
    (_ !!-> v) x = v.
Proof. intros A x v. unfold t_empty. reflexivity. Qed.

(** ----- **)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros A m x v. unfold t_update.
  rewrite equiv_decb_true; reflexivity.
Qed.

Lemma t_update_eq_nat : forall (A : Type) (m : total_map_nat A) x v,
    (x !!-> v ; m) x = v.
Proof.
  intros A m x v. unfold t_update_nat.
  rewrite equiv_decb_true; reflexivity.
Qed.

(** ----- **)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H. unfold t_update.
  rewrite equiv_decb_false. reflexivity. apply H.
Qed.

Theorem t_update_neq_nat : forall (A : Type) (m : total_map_nat A) x1 x2 v,
    x1 <> x2 ->
    (x1 !!-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H. unfold t_update_nat.
  rewrite equiv_decb_false. reflexivity. apply H.
Qed.

(** ----- **)

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2.
  apply functional_extensionality. intros x'.
  unfold t_update. destruct (x ==b x'); reflexivity.
Qed.

Lemma t_update_shadow_nat : forall (A : Type) (m : total_map_nat A) x v1 v2,
    (x !!-> v2 ; x !!-> v1 ; m) = (x !!-> v2 ; m).
Proof.
  intros A m x v1 v2.
  apply functional_extensionality. intros x'.
  unfold t_update_nat. destruct (x ==b x'); reflexivity.
Qed.

(** ----- **)

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros A m x.
  extensionality x'.
  unfold t_update. destruct (equiv_decbP x x') as [Heq | Hneq].
  + rewrite Heq. reflexivity.
  + reflexivity.
Qed.

Theorem t_update_same_nat : forall (A : Type) (m : total_map_nat A) x,
    (x !!-> m x ; m) = m.
Proof.
  intros A m x.
  extensionality x'.
  unfold t_update_nat. destruct (equiv_decbP x x') as [Heq | Hneq].
  + rewrite Heq. reflexivity.
  + reflexivity.
Qed.

(** ----- **)

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 H.
  extensionality x'.
  unfold t_update. destruct (equiv_decbP x1 x').
  + destruct (equiv_decbP x2 x').
    * rewrite<-e in e0. rewrite e0 in H. destruct H. reflexivity.
    * reflexivity.
  + destruct (equiv_decbP x2 x').
    * reflexivity.
    * reflexivity.
Qed.


Theorem t_update_permute_nat : forall (A : Type) (m : total_map_nat A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !!-> v1 ; x2 !!-> v2 ; m)
    =
    (x2 !!-> v2 ; x1 !!-> v1 ; m).
Proof.
  intros A m v1 v2 x1 x2 H.
  extensionality x'.
  unfold t_update_nat. destruct (equiv_decbP x1 x').
  + destruct (equiv_decbP x2 x').
    * rewrite<-e in e0. rewrite e0 in H. destruct H. reflexivity.
    * reflexivity.
  + destruct (equiv_decbP x2 x').
    * reflexivity.
    * reflexivity.
Qed.


(* ################################################################# *)
(** * Partial maps *)

Definition partial_map (A : Type) := total_map (option A).
(* Definition partial_map_nat (A : Type) := total_map_nat (option A). *)

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Example examplepmap :=
  ("a" |-> true ; "b" |-> false).


Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

Lemma add_none: forall (A : Type) (h : partial_map A) n m, h n = None -> h = (n !-> None; n !-> Some m; h).
Proof.
  intros A h n m H.
  extensionality x.
  unfold t_update. destruct (equiv_decbP n x) as [Heq | Hneq].
  - rewrite <- Heq. apply H.
  - reflexivity.
Qed.

Lemma add_swap: forall (A : Type) (h : partial_map A) n m k l,
    n <> m -> (n |-> k; m |-> l; h) = (m |-> l; n |-> k; h).
Proof.
  intros A h n m k l H.
  extensionality x. unfold update. unfold t_update.
  destruct (equiv_decbP n x) as [Heq | Hneq], (equiv_decbP m x) as [Heq' | Hneq'];
  try reflexivity.
  exfalso. apply H. rewrite Heq. rewrite <- Heq'. reflexivity.
Qed.

Definition disjoint {A : Type} (m1 m2 : partial_map A) : Prop := 
  forall k, m1 k = None \/ m2 k = None.

Definition join {A : Type} (m1 m2 : partial_map A) : partial_map A :=
  fun k =>
    match m1 k with
    | Some val => Some val
    | None     => m2 k
    end.

Lemma join_comm (A : Type) (m1 m2 : partial_map A) (Hdisj : disjoint m1 m2) :
  (join m1 m2) = (join m2 m1).
Proof.
  extensionality k.
  unfold join.
  destruct Hdisj with k; desf.
Qed.

Lemma join_assoc (A : Type) (m1 m2 m3 : partial_map A) :
  join m1 (join m2 m3) = join (join m1 m2) m3.
Proof.
  extensionality k.
  unfold join.
  desf.
Qed.

Lemma join_empty_r (A : Type) (m : partial_map A) :
  join m empty = m.
Proof.
  extensionality k.
  unfold join, empty, t_empty.
  desf.
Qed.

Lemma join_empty_l (A : Type) (m : partial_map A) :
  join empty m = m.
Proof.
  extensionality k.
  unfold join, empty, t_empty.
  desf.
Qed.

Lemma empty_disjoint_l (A : Type) (m : partial_map A) :
  disjoint empty m.
Proof.
  unfold disjoint, empty, t_empty.
  intros k. now left.
Qed.

Lemma empty_disjoint_r (A : Type) (m : partial_map A) :
  disjoint m empty.
Proof.
  unfold disjoint, empty, t_empty.
  intros k. now right.
Qed.

Lemma disjoint_comm (A : Type) (m1 m2 : partial_map A) (Hdisj : disjoint m1 m2) :
  disjoint m2 m1.
Proof.
  unfold disjoint in *.
  intros k.
  destruct Hdisj with k; auto.
Qed.

Lemma disjoint_comm_iff (A : Type) (m1 m2 : partial_map A) :
  disjoint m1 m2 <-> disjoint m2 m1.
Proof.
  split; apply disjoint_comm.
Qed.