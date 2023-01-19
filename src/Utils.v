Require Import List.
Require Import String.
Require Import List.
Require Import Bool.
Require Import BinNums.
From hahn Require Import HahnBase.
From Coq Require Export Classes.EquivDec.
From Coq Require Export Classes.RelationClasses.
Import ListNotations.

Definition coerce_sumbool {A B : Prop} (x : {A} + {B}) : bool :=
  if x then true else false.

Coercion coerce_sumbool : sumbool >-> bool.

Definition option_bind {A B : Type} (x : option A) (f : A -> option B) : option B :=
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

Lemma equiv_decb_true_iff : forall {A : Type} `{EqDec A eq} (a b : A),
  (a ==b b) = true <-> a = b.
Proof.
  intros. split.
  apply equiv_decb_true'.
  apply equiv_decb_true.
Qed.

Lemma equiv_decbP : forall {A : Type} `{EqDec A eq} (x y : A),
  reflect (x = y) (x ==b y).
Proof.
  intros A ? ? x y. unfold equiv_decb.
  destruct (x == y) as [Heq | Hneq].
  + apply ReflectT. apply Heq.
  + apply ReflectF. apply Hneq.
Qed.

#[global]
Instance neq_symmetric {A : Type} : Symmetric (fun (x y : A) => ~(x = y)).
Proof.
  intros x y Hneq Heq.
  apply Hneq. symmetry. apply Heq.
Qed.

Fixpoint In_dec {A : Type} `{EqDec A eq} (a : A) (xs : list A) : {In a xs} + {~ In a xs}.
  refine (match xs with
          | nil => right _
          | x :: xs => if (a == x) then left _ else
            match In_dec _ _ _ a xs with
            | left p => left _
            | right np => right _
            end
          end).
  all: unfold equiv, complement in *.
  all: simpl in *; subst.
  all: auto.
  intros contra. desf.
Defined.

Definition In_decb {A : Type} `{EqDec A eq} (a : A) (xs : list A) : bool := In_dec a xs.

Lemma In_decb_true_iff : forall {A : Type} `{EqDec A eq} (a : A) (xs : list A),
  In_decb a xs = true <-> In a xs.
Proof.
  intros. unfold In_decb.
  destruct (In_dec a xs) as [HIn | HIn].
  all: split; auto.
  ins.
Qed.

Fixpoint fold_option {A : Type} (xs : list (option A)) : option (list A) :=
  match xs with
  | nil => Some nil
  | x :: xs => x >>= fun x' => fold_option xs >>= fun xs' => Some (x' :: xs')
  end.

Lemma fold_option_some {A : Type} (xs : list (option A))
                       (Hsome : forall a, In a xs -> exists a', a = Some a') :
  exists xs', fold_option xs = Some xs'.
Proof.
  induction xs as [| x xs]. { now eexists. }

  destruct Hsome with x. { now left. }
  destruct IHxs as [? IHxs]. { intros. apply Hsome. now right. }

  subst. simpl. rewrite IHxs. simpl. now eexists.
Qed.

Lemma fold_option_In {A : Type} (xs : list (option A)) (xs' : list A) (a' : A) 
                     (H : fold_option xs = Some xs') :
  In (Some a') xs <-> In a' xs'.
Proof.
  generalize dependent xs'.
  induction xs as [| x xs]; ins.
  { inv H. }
  split.
  all: destruct xs' as [|x' xs']; try easy.
  all: unfold option_bind in *; desf.
  all: intros [Hx | Hx]; subst; auto.
  { inv Hx. now left. }
  { right. now apply IHxs. }
  apply IHxs in Hx; auto.
Qed.

Lemma fold_option_none {A : Type} (xs : list (option A))
                       (Hnone : In None xs) :
  fold_option xs = None.
Proof.
  induction xs as [| x xs], Hnone; subst; auto.
  simpl. rewrite (IHxs H). now destruct x.
Qed.

Section filter_map.
  Variable A B : Type.
  Variable f : A -> option B.

  Fixpoint filter_map (xs : list A) : list B :=
    match xs with
    | nil => nil
    | x :: xs =>
      match f x with
      | Some y => y :: filter_map xs
      | None => filter_map xs
      end
    end.
End filter_map.

Arguments filter_map {A B} f xs.