Require Export List.
Require Export String.
(* We don't import Bool because of notation conflicts with RelationAlgebra*)
(* Require Import Bool. *)
Require Export List.
Require Export BinNums.
From hahn Require Export HahnBase.
From Coq Require Export Classes.EquivDec.
From Coq Require Export Classes.RelationClasses.
From Coq Require Export Logic.FunctionalExtensionality.
Export ListNotations.

#[global]
Open Scope string_scope.

(* To override notation from Classes.EquivDec *)
Notation "x <> y" := (not (eq x y)).

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

#[global]
Program Instance nat_eqdec : EqDec nat eq := PeanoNat.Nat.eq_dec.

Lemma equiv_decb_true : forall {A : Type} `{EqDec A eq} (a b : A),
  a = b -> a ==b b = true.
Proof using.
  intros A ? ? a b Heq.
  unfold equiv_decb.
  destruct (a == b) as [Heq' | Hneq'].
  - reflexivity.
  - exfalso. apply Hneq'. apply Heq.
Qed.

Lemma equiv_decb_false : forall {A : Type} `{EqDec A eq} (a b : A),
  a <> b -> a ==b b = false.
Proof using.
  intros A ? ? a b Hneq.
  unfold equiv_decb.
  destruct (a == b) as [Heq' | Hneq'].
  - exfalso. apply Hneq. apply Heq'.
  - reflexivity.
Qed.

Lemma equiv_decb_true' : forall {A : Type} `{EqDec A eq} (a b : A),
  a ==b b = true -> a = b.
Proof using.
  intros A ? ? a b H.
  unfold equiv_decb in H.
  destruct (a == b) as [Heq' | Hneq'].
  - apply Heq'.
  - discriminate H.
Qed.

Lemma equiv_decb_false' : forall {A : Type} `{EqDec A eq} (a b : A),
  a ==b b = false -> a <> b.
Proof using.
  intros A ? ? a b H.
  unfold equiv_decb in H.
  destruct (a == b) as [Heq' | Hneq'].
  - discriminate H.
  - apply Hneq'.
Qed.

Lemma equiv_decb_true_iff : forall {A : Type} `{EqDec A eq} (a b : A),
  (a ==b b) = true <-> a = b.
Proof using.
  intros. split.
  apply equiv_decb_true'.
  apply equiv_decb_true.
Qed.

Lemma equiv_decbP : forall {A : Type} `{EqDec A eq} (x y : A),
  Bool.reflect (x = y) (x ==b y).
Proof using.
  intros A ? ? x y. unfold equiv_decb.
  destruct (x == y) as [Heq | Hneq].
  + apply Bool.ReflectT. apply Heq.
  + apply Bool.ReflectF. apply Hneq.
Qed.

#[global]
Instance neq_symmetric {A : Type} : Symmetric (fun (x y : A) => ~(x = y)).
Proof using.
  intros x y Hneq Heq.
  apply Hneq. symmetry. apply Heq.
Qed.

#[global]
Instance unequiv_symmetric {A : Type} : Symmetric (fun (x y : A) => x =/= y).
Proof using.
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

Theorem In_decbP {A : Type} `{EqDec A eq} (a : A) (xs : list A) :
  Bool.reflect (In a xs) (In_decb a xs).
Proof using.
  unfold In_decb.
  destruct (In_dec a xs).
  { now apply Bool.ReflectT. }
  { now apply Bool.ReflectF. }
Qed.

Lemma In_decb_true_iff : forall {A : Type} `{EqDec A eq} (a : A) (xs : list A),
  In_decb a xs = true <-> In a xs.
Proof using.
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

Lemma fold_option_some (A : Type) (xs : list (option A))
                       (Hsome : forall a, In a xs -> exists a', a = Some a') :
  exists xs', fold_option xs = Some xs'.
Proof using.
  induction xs as [| x xs]. { now eexists. }

  destruct Hsome with x. { now left. }
  destruct IHxs as [? IHxs]. { intros. apply Hsome. now right. }

  subst. simpl. rewrite IHxs. simpl. now eexists.
Qed.

Lemma fold_option_some_inv {A : Type} (xs : list (option A)) (xs' : list A) (a : option A)
                           (Hres : fold_option xs = Some xs') (HIn : In a xs) :
  exists a', a = Some a'.
Proof using.
  generalize dependent xs'.
  induction xs as [| x xs]; ins.
  simpls. unfold option_bind in *.
  desf. { now eexists. }

  eapply IHxs; eauto.
Qed.

Lemma fold_option_In {A : Type} (xs : list (option A)) (xs' : list A) (a' : A) 
                     (H : fold_option xs = Some xs') :
  In (Some a') xs <-> In a' xs'.
Proof using.
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
Proof using.
  induction xs as [| x xs], Hnone; subst; auto.
  simpl. rewrite (IHxs H). now destruct x.
Qed.

Lemma option_map_some (A B : Type) (f : A -> B) (a : option A) (y : B)
                      (Hres : option_map f a = Some y) :
  exists x, f x = y /\ a = Some x.
Proof using.
  destruct a as [x |]; [exists x | inv Hres].
  split; simpls; desf.
Qed.

Definition concat_option {A : Type} (xs : list (option (list A))) : option (list A) :=
  option_map (@List.concat A) (fold_option xs).

Theorem in_concat_option_iff {A : Type} (a : A)
  (xs : list (option (list A)))
  (ys : list A)
  (Hres : concat_option xs = Some ys) :
    In a ys <-> exists x, In (Some x) xs /\ In a x.
Proof using.
  unfold concat_option in Hres.
  destruct (fold_option xs) eqn:Hfold; try discriminate.
  simpls. desf.
  rewrite in_concat.
  setoid_rewrite fold_option_In; eauto.
  split; ins; desf; eauto.
Qed.

Theorem concat_option_some_inv {A : Type}
  (xs : list (option (list A)))
  (ys : list A) (x : option (list A))
  (HIn : In x xs)
  (Hres : concat_option xs = Some ys) :
    exists y, x = Some y.
Proof using.
  unfold concat_option.
  edestruct option_map_some; eauto. desc.
  eapply fold_option_some_inv; eauto.
Qed.

Theorem concat_option_some_inv_cons {A : Type}
  (xs : list (option (list A)))
  (ys : list A) (x : option (list A))
  (Hres : concat_option (x :: xs) = Some ys) :
    exists (y ys' : list A), x = Some y /\
      ys = app y ys' /\
      concat_option xs = Some ys'.
Proof using.
  unfold concat_option in *.
  edestruct option_map_some; eauto. desc.
  clear Hres. simpls.
  unfold option_bind in *. desf.
  do 2 eexists. splits; eauto.
  { now rewrite concat_cons. }
  reflexivity.
Qed.

Ltac apply_concat_option_some_inv_cons :=
  match goal with
  | [ H : concat_option (?x :: ?xs) = Some ?ys |- _ ] =>
    apply concat_option_some_inv_cons in H; desc
  end.

Theorem concat_option_nil (A : Type) : @concat_option A [] = Some [].
Proof using. reflexivity. Qed.

Theorem concat_option_some (A : Type) (xs : list (option (list A)))
                           (Hsome : forall x, In x xs -> exists x', x = Some x') :
  exists xs', concat_option xs = Some xs'.
Proof using.
  unfold concat_option.
  edestruct fold_option_some as [? Hfold]; eauto.
  rewrite Hfold. simpl. eauto.
Qed.

Definition concat_option_map {A B : Type}
  (f : A -> option (list B))
  (xs : list A) : option (list B) :=
    concat_option (map f xs).

Theorem in_concat_option_map_iff {A B : Type}
  (f : A -> option (list B))
  (xs : list A) (ys : list B) (b : B)
  (Hres : concat_option_map f xs = Some ys) :
    In b ys <-> exists x y, In x xs /\ In b y /\ f x = Some y.
Proof using.
  unfold concat_option_map in *.
  rewrite in_concat_option_iff; eauto.
  setoid_rewrite in_map_iff.
  split; ins; desf; eauto.
Qed.

Theorem concat_option_map_some_inv {A B : Type}
  (f : A -> option (list B))
  (xs : list A) (ys : list B)
  (x : A) (HIn : In x xs)
  (Hres : concat_option_map f xs = Some ys) :
    exists y, f x = Some y.
Proof using.
  unfold concat_option_map in Hres.
  eapply concat_option_some_inv; eauto.
  now apply in_map.
Qed.

Theorem concat_option_map_some (A B : Type)
  (f : A -> option (list B)) (xs : list A)
  (Hsome : forall x, In x xs -> exists y, f x = Some y) :
    exists xs', concat_option_map f xs = Some xs'.
Proof using.
  unfold concat_option_map.
  eapply concat_option_some; eauto.
  intros ? HIn.
  rewrite in_map_iff in HIn. desf.
  now apply Hsome.
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

Lemma filter_map_In {A B : Type} (f : A -> option B) (xs : list A) (y : B) :
  In y (filter_map f xs) <-> exists x, f x = Some y /\ In x xs.
Proof using.
  unfold filter_map.
  induction xs as [| x xs IHxs ]; simpls.
  { split; ins; desf. }

  split; ins.
  - desf; simpls; desf.
    all: try (eexists; split; eauto; now left).
    all: try match goal with
         | [ H : In _ _, IH : In _ _ -> _ |- _ ] => apply IH in H
         end; desf; eauto.

  - desf; simpls.
    all: try now left.
    all: try right.
    all: match goal with
         | [ IH : _ -> In _ _  |- _ ] => apply IH
         end.
    all: eexists; split; eauto.
Qed.

Lemma NoDup_cons_l (A : Type) (x : A) (xs : list A) (Hdup : NoDup (x :: xs)) :
  ~ In x xs.
Proof using.
  apply NoDup_cons_iff in Hdup. desf.
Qed.

Lemma NoDup_cons_r (A : Type) (x : A) (xs : list A) (Hdup : NoDup (x :: xs)) :
  NoDup xs.
Proof using.
  apply NoDup_cons_iff in Hdup. desf.
Qed.

Lemma NoDup_cons_contra (A : Type) (x : A) (xs : list A)
                        (Hdup : NoDup (x :: xs)) (HIn : In x xs) : False.
Proof using.
  eapply NoDup_cons_l; eassumption.
Qed.

Ltac normalize_bool :=
  repeat match goal with
  | [ H : negb _ = true |- _ ] => rewrite Bool.negb_true_iff in H
  | [ H : negb _ <> true |- _ ] => rewrite Bool.negb_true_iff in H
  | [ H : _ = false |- _ ] => rewrite <- Bool.not_true_iff_false in H
  | [ H : _ <> false |- _ ] => rewrite -> Bool.not_false_iff_true in H
  | [ H : (In_decb _ _) = true |- _ ] => rewrite -> In_decb_true_iff in H
  | [ H : (In_decb _ _) <> true |- _ ] => rewrite -> In_decb_true_iff in H
  end.

Ltac inj_subst :=
  repeat match goal with
  | [ H : Some ?x = Some ?y |- _ ] =>
      injection H as H; try subst y; try subst x
  end.

Tactic Notation "gen_dep" ident(a) :=
  generalize dependent a.

Tactic Notation "gen_dep" ident(a) ident(b) :=
  generalize dependent a; gen_dep b.

Tactic Notation "gen_dep" ident(a) ident(b) ident(c) :=
  generalize dependent a; gen_dep b c.

Tactic Notation "gen_dep" ident(a) ident(b) ident(c) ident(d) :=
  generalize dependent a; gen_dep b c d.

Tactic Notation "gen_dep" ident(a) ident(b) ident(c) ident(d) ident(e) :=
  generalize dependent a; gen_dep b c d e.

Tactic Notation "gen_dep" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) :=
  generalize dependent a; gen_dep b c d e f.

Tactic Notation "gen_dep" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) :=
  generalize dependent a; gen_dep b c d e f g.

Tactic Notation "gen_dep" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) ident(h) :=
  generalize dependent a; gen_dep b c d e f g h.

Tactic Notation "gen_dep" ident(a) ident(b) ident(c) ident(d) ident(e) ident(f) ident(g) ident(h) ident(i) :=
  generalize dependent a; gen_dep b c d e f g h i.

Fixpoint tails {A : Type} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: xs => (x :: xs) :: tails xs
  end.

Theorem tails_hd {A : Type} (xs : list A) :
  tails xs = xs :: tl (tails xs).
Proof using. now destruct xs. Qed.

Theorem map_tl {A B : Type} (f : A -> B) (xs : list A) :
  map f (tl xs) = tl (map f xs).
Proof using. now destruct xs. Qed.
