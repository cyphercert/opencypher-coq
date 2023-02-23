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

Module TotalMap.
  Definition t (A B : Type) `{EqDec A eq} := A -> B.

  Section ops.
    Context {A B : Type}.
    Context `{EqDec A eq}.

    Definition empty (v : B) : t A B :=
      fun _ => v.

    Definition update (m : t A B) (x : A) (v : B) :=
      fun x' => if x ==b x' then v else m x'.
  End ops.

  Module Notations.
    Notation "'_' '!->' v" := (TotalMap.empty v)
      (at level 100, right associativity).

    Notation "x '!->' v ';' m" := (TotalMap.update m x v)
      (at level 100, v at next level, right associativity).
  End Notations.

  Import Notations.

  (* ################################################################# *)
  (** lemmas about total maps **)

  Section lemmas.
    Context (A B : Type).
    Context `{EqDec A eq}.
    Implicit Types m : t A B.

    Lemma apply_empty (x : A) (v : B) :
        (_ !-> v) x = v.
    Proof using. unfold empty. reflexivity. Qed.

    Lemma update_eq m x v :
        (x !-> v ; m) x = v.
    Proof using.
      unfold update.
      now rewrite equiv_decb_true.
    Qed.

    Theorem update_neq m x1 x2 v
      (Hneq : x1 <> x2) :
        (x1 !-> v ; m) x2 = m x2.
    Proof using.
      unfold update.
      now rewrite equiv_decb_false.
    Qed.

    Lemma update_shadow m x v1 v2 :
        (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
    Proof using.
      extensionality x'. unfold update.
      now destruct (x ==b x').
    Qed.

    Theorem update_same m x :
      (x !-> m x ; m) = m.
    Proof using.
      extensionality x'. unfold update.
      destruct (equiv_decbP x x') as [Heq | Hneq].
      { now rewrite Heq. }
      reflexivity.
    Qed.

    Theorem update_permute m v1 v2 x1 x2
      (Hneq : x2 <> x1) :
        (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
    Proof using.
      extensionality x'. unfold update.
      destruct (equiv_decbP x1 x'), (equiv_decbP x2 x').
      all: try reflexivity.
      congruence.
    Qed.
  End lemmas.
End TotalMap.

(* ################################################################# *)
(** * Partial maps *)

Module PartialMap.
  Definition t (A B : Type) `{EqDec A eq} := TotalMap.t A (option B).

  Import TotalMap.Notations.

  Section ops.
    Context {A B : Type}.
    Context `{EqDec A eq}.
    
    Definition empty : t A B :=
      (_ !-> None).

    Definition update (m : t A B) (x : A) (v : B) :=
      (x !-> Some v ; m).
  End ops.

  Module Notations.
    Notation "x '|->' v ';' m" := (update m x v)
      (at level 100, v at next level, right associativity).

    Notation "x '|->' v" := (update empty x v)
      (at level 100).
  End Notations.

  Import Notations.

  Section lemmas.
    Context (A B : Type).
    Context `{EqDec A eq}.
    Implicit Types m : t A B.

    Lemma apply_empty (x : A) :
        (empty : t A B) x = None.
    Proof using.
      unfold empty.
      now rewrite TotalMap.apply_empty.
    Qed.

    Lemma update_eq m x v :
        (x |-> v ; m) x = Some v.
    Proof using.
      unfold update.
      now rewrite TotalMap.update_eq.
    Qed.

    Theorem update_neq m x1 x2 v
      (Hneq : x2 <> x1) :
        (x2 |-> v ; m) x1 = m x1.
    Proof using.
      unfold update.
      now rewrite TotalMap.update_neq.
    Qed.

    Lemma update_shadow m x v1 v2 :
      (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
    Proof using.
      unfold update.
      now rewrite TotalMap.update_shadow.
    Qed.

    Theorem update_same m x v
      (Heq : m x = Some v) :
        (x |-> v ; m) = m.
    Proof using.
      unfold update. rewrite <- Heq.
      apply TotalMap.update_same.
    Qed.

    Theorem update_permute m x1 x2 v1 v2
      (Hneq : x2 <> x1) :
        (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
    Proof using.
      unfold update.
      now apply TotalMap.update_permute.
    Qed.

    Lemma add_none m x v
      (Hnone : m x = None) :
        m = (x !-> None; x !-> Some v; m).
    Proof using.
      extensionality x'.
      unfold TotalMap.update.
      destruct (equiv_decbP x x') as [Heq | Hneq].
      { now rewrite <- Heq. }
      reflexivity.
    Qed.
  End lemmas.

  Section join.
    Context {A B : Type}.
    Context `{EqDec A eq}.

    Definition in_dom (x : A) (m : t A B) :=
      exists v, m x = Some v.

    Definition disjoint (m1 m2 : t A B) : Prop := 
      forall k, m1 k = None \/ m2 k = None.

    Definition join (m1 m2 : t A B) : t A B :=
      fun k =>
        match m1 k with
        | Some val => Some val
        | None     => m2 k
        end.
  End join.

  Section join_lemmas.
    Context (A B : Type).
    Context `{EqDec A eq}.

    Lemma not_in_dom_iff (m : t A B) (x : A) :
      ~ in_dom x m <-> m x = None.
    Proof using.
      unfold in_dom.
      destruct (m x).
      all: split; ins.
      { exfalso; eauto. }
      intro; desf.
    Qed.

    Lemma disjoint_iff (m1 m2 : t A B) :
      disjoint m1 m2 <-> (forall k, ~ in_dom k m1 \/ ~ in_dom k m2).
    Proof using.
      unfold disjoint.
      setoid_rewrite not_in_dom_iff.
      reflexivity.
    Qed.

    Lemma join_comm (m1 m2 : t A B) (Hdisj : disjoint m1 m2) :
      (join m1 m2) = (join m2 m1).
    Proof using.
      extensionality k.
      unfold join.
      destruct Hdisj with k; desf.
    Qed.

    Lemma join_assoc (m1 m2 m3 : t A B) :
      join m1 (join m2 m3) = join (join m1 m2) m3.
    Proof using.
      extensionality k.
      unfold join.
      desf.
    Qed.

    Lemma join_empty_r (m : t A B) :
      join m empty = m.
    Proof using.
      extensionality k.
      unfold join, empty, TotalMap.empty.
      desf.
    Qed.

    Lemma join_empty_l (m : t A B) :
      join empty m = m.
    Proof using.
      extensionality k.
      unfold join, empty, TotalMap.empty.
      desf.
    Qed.

    Lemma empty_disjoint_l (m : t A B) :
      disjoint empty m.
    Proof using.
      unfold join, empty, TotalMap.empty.
      intros k. now left.
    Qed.

    Lemma empty_disjoint_r (m : t A B) :
      disjoint m empty.
    Proof using.
      unfold disjoint, empty, TotalMap.empty.
      intros k. now right.
    Qed.

    Lemma disjoint_symm (m1 m2 : t A B)
      (Hdisj : disjoint m1 m2) :
        disjoint m2 m1.
    Proof using.
      unfold disjoint in *.
      intros k.
      destruct Hdisj with k; auto.
    Qed.

    Lemma disjoint_symm_iff (m1 m2 : t A B) :
      disjoint m1 m2 <-> disjoint m2 m1.
    Proof using.
      split; apply disjoint_symm.
    Qed.
  End join_lemmas.
End PartialMap.