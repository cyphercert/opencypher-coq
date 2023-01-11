Require Import List.
Require Import String.
Require Import List.
Require Import Bool.
Require Import BinNums.
From Coq Require Export Classes.EquivDec.
Import ListNotations.

Fixpoint list_inb {A : Type} `{EqDec A eq} (e : A) (l : list A) : bool :=
  match l with 
  | [] => false 
  | h :: tl => if (e ==b h) then true else list_inb e tl
  end.

Fixpoint list_inb_b (e : bool) (l : list bool) : bool :=
  match l with 
  | [] => false 
  | h :: tl => if (Bool.eqb e h) then true else list_inb_b e tl
  end.

Definition option_bind {A B : Type} (f : A -> option B) (x : option A) : option B :=
  match x with
  | Some x' => f x'
  | None => None
  end.

Infix ">>=" := option_bind (at level 58, left associativity).

#[global]
Program Instance int_eq_eqdec : EqDec Z eq := BinInt.Z.eq_dec.

#[global]
Program Instance string_eqdec : EqDec string eq := String.string_dec.

Lemma equiv_decb_true : forall {A : Type} `{EqDec A eq} (a b : A),
  a = b -> a ==b b = true.
Proof.
  intros A ? ? a b Heq.
  unfold equiv_decb.
  destruct (a == b) as [Heq' | Hneq'].
  - reflexivity.
  - exfalso. apply Hneq'. apply Heq.
Qed.

Lemma equiv_decb_false : forall {A : Type} `{EqDec A eq} (a b : A),
  a <> b -> a ==b b = false.
Proof.
  intros A ? ? a b Hneq.
  unfold equiv_decb.
  destruct (a == b) as [Heq' | Hneq'].
  - exfalso. apply Hneq. apply Heq'.
  - reflexivity.
Qed.

Lemma equiv_decb_true' : forall {A : Type} `{EqDec A eq} (a b : A),
  a ==b b = true -> a = b.
Proof.
  intros A ? ? a b H.
  unfold equiv_decb in H.
  destruct (a == b) as [Heq' | Hneq'].
  - apply Heq'.
  - discriminate H.
Qed.

Lemma equiv_decb_false' : forall {A : Type} `{EqDec A eq} (a b : A),
  a ==b b = false -> a <> b.
Proof.
  intros A ? ? a b H.
  unfold equiv_decb in H.
  destruct (a == b) as [Heq' | Hneq'].
  - discriminate H.
  - apply Hneq'.
Qed.

Lemma equiv_decbP : forall {A : Type} `{EqDec A eq} (x y : A),
  reflect (x = y) (x ==b y).
Proof.
  intros A ? ? x y. unfold equiv_decb.
  destruct (x == y) as [Heq | Hneq].
  + apply ReflectT. apply Heq.
  + apply ReflectF. apply Hneq.
Qed.