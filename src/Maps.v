From Coq Require Import Arith.Arith.
From Coq Require Import Bool.Bool.
Require Export Coq.Strings.String.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lists.List.
(**From Coq Require Import omega.Omega.**)

(**strings**)

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof. intros s. unfold eqb_string. destruct (string_dec s s) as [|Hs].
  - reflexivity.
  - destruct Hs. reflexivity.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [|Hs].
   - subst. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. rewrite H in Hs. destruct Hs. reflexivity.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.

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
  fun x' => if eqb_string x x' then v else m x'.

Definition t_update_nat {A : Type} (m : total_map_nat A)
                    (x : nat) (v : A) :=
  fun x' => if x =? x' then v else m x'.


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
Proof.
  intros A x v.
  unfold t_empty. reflexivity.
Qed.

Lemma t_apply_empty_nat : forall (A : Type) (x : nat) (v : A),
    (_ !!-> v) x = v.
Proof.
  intros A x v.
  unfold t_empty. reflexivity.
Qed.

(** ----- **)

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros A m x v.
  unfold t_update. rewrite<-eqb_string_refl. reflexivity.
Qed.

Lemma t_update_eq_nat : forall (A : Type) (m : total_map_nat A) x v,
    (x !!-> v ; m) x = v.
Proof.
  intros A m x v.
  unfold t_update_nat.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(** ----- **)

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H.
  unfold t_update. rewrite false_eqb_string. reflexivity. apply H.
Qed.

Theorem t_update_neq_nat : forall (A : Type) (m : total_map_nat A) x1 x2 v,
    x1 <> x2 ->
    (x1 !!-> v ; m) x2 = m x2.
Proof.
  intros A m x1 x2 v H.
  unfold t_update_nat.
  remember (x1 =? x2) as c eqn:EP.
  symmetry in EP.
  unfold eqb in EP.
  destruct c.
  - apply Nat.eqb_eq in EP. apply H in EP. inversion EP.
  - reflexivity.
Qed.

(** ----- **)

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros A m x v1 v2.
  apply functional_extensionality. intros x0.
  unfold t_update. destruct (eqb_string x x0).
  - reflexivity.
  - reflexivity.
Qed.

Lemma t_update_shadow_nat : forall (A : Type) (m : total_map_nat A) x v1 v2,
    (x !!-> v2 ; x !!-> v1 ; m) = (x !!-> v2 ; m).
Proof.
  intros A m x v1 v2.
  apply functional_extensionality. intros x0.
  unfold t_update_nat.
  remember (x =? x0) as c eqn:EP.
  destruct c.
  - reflexivity.
  - reflexivity.
Qed.

(** ----- **)

Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  intros x y. apply iff_reflect. split.
  + apply eqb_string_true_iff.
  + apply eqb_string_true_iff.
Qed.

(** ----- **)

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros A m x.
  apply functional_extensionality. intros x0.
  unfold t_update. destruct (eqb_stringP x x0).
  + rewrite e. reflexivity.
  + reflexivity.
Qed.

Theorem t_update_same_nat : forall (A : Type) (m : total_map_nat A) x,
    (x !!-> m x ; m) = m.
Proof.
  intros A m x.
  apply functional_extensionality. intros x0.
  unfold t_update_nat. remember (x =? x0) as c eqn:EP.
  destruct c.
  + symmetry in EP. apply Nat.eqb_eq in EP. rewrite EP. reflexivity.
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
  apply functional_extensionality. intros x0.
  unfold t_update. destruct (eqb_stringP x1 x0).
  + destruct (eqb_stringP x2 x0).
    * rewrite<-e in e0. rewrite e0 in H. destruct H. reflexivity.
    * reflexivity.
  + destruct (eqb_stringP x2 x0).
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
  apply functional_extensionality. intros x0.
  unfold t_update_nat.
  remember (x1 =? x0) as c1 eqn:EP1. symmetry in EP1.
  remember (x2 =? x0) as c2 eqn:EP2. symmetry in EP2.
  destruct c1.
  + destruct c2.
    * apply Nat.eqb_eq in EP1. apply Nat.eqb_eq in EP2.
      rewrite<-EP1 in EP2. apply H in EP2. inversion EP2.
    * reflexivity.
  + destruct c2.
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
  apply functional_extensionality. intros x.
  unfold t_update. destruct (eqb_string n x) eqn:E.
  - apply eqb_string_true_iff in E. rewrite<-E. apply H.
  - reflexivity.
Qed.

Lemma add_swap: forall (A : Type) (h : partial_map A) n m k l,
    n <> m -> (n |-> k; m |-> l; h) = (m |-> l; n |-> k; h).
Proof.
  intros A h n m k l H.
  apply functional_extensionality. intros x.
  destruct (eqb_string n x) eqn:E1, (eqb_string m x) eqn:E2.
  - apply eqb_string_true_iff  in E1. apply eqb_string_true_iff  in E2.
    rewrite<-E2 in E1. apply H in E1. inversion E1.
  - apply eqb_string_true_iff  in E1. rewrite E1. rewrite update_eq.
    rewrite update_neq. rewrite update_eq. reflexivity.
    apply eqb_string_false_iff in E2. apply E2.
  - apply eqb_string_true_iff  in E2. rewrite E2. rewrite update_eq.
    rewrite update_neq. rewrite update_eq. reflexivity.
    apply eqb_string_false_iff  in E1. apply E1.
  - apply eqb_string_false_iff in E1. apply eqb_string_false_iff in E2.
    repeat(rewrite update_neq); try(reflexivity); try(assumption).
Qed.
