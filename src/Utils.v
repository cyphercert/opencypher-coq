Require Import PropertyGraph.
Import PropertyGraph.
Require Import List.
Import ListNotations.

(** To create a common adjacency matrix that will store both vertex labels and edge vertex it is necessary to create generic types*)

Inductive Label :=
| vlabel (l : label)
| elabel (l : label)
.

(** Functions for translation to the generic type and vice versa **)

Fixpoint list_unique (l : list label) : list label :=
  match l with
  | [] => []
  | h :: tl => h :: filter (fun x => negb (String.eqb x h)) (list_unique tl)
  end.

(*Fixpoint list_ord_nat (l : list nat) : list ord nat :=
  match l with
  | [] => []
  | h :: tl => Some h :: list_ord_nat tl
  end.*)

<<<<<<< Updated upstream
Fixpoint list_inb_b (e : bool) (l : list bool) : bool :=
  match l with 
  | [] => false 
  | h :: tl => if (Bool.eqb e h) then true else list_inb_b e tl
=======
#[global]
Program Instance int_eq_eqdec : EqDec Z eq := BinInt.Z.eq_dec.

#[global]
Program Instance string_eqdec : EqDec string eq := String.string_dec.

#[global]
Program Instance nat_eqdec : EqDec nat eq := PeanoNat.Nat.eq_dec.

#[global]
Instance option_eqdec {A : Type} `{eq_dec : EqDec A eq} : EqDec (option A) eq.
Proof using.
  unfold EqDec, equiv, complement in *.
  intros [x|] [y|].
  all: try now left.
  all: try now right.
  all: specialize (eq_dec x y); destruct eq_dec.
  { subst. now left. }
  right. now inversion 1.
Qed.

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
>>>>>>> Stashed changes
  end.

Definition Label_eqb (a : Label) (b : Label) : bool := 
  match a with 
  | vlabel a' => match b with 
                 | vlabel b' => String.eqb a' b'
                 | elabel b' => false
                 end
  | elabel a' => match b with 
                 | vlabel b' => false
                 | elabel b' => String.eqb a' b'
                 end
  end.

<<<<<<< Updated upstream
Fixpoint list_inb (e : Label) (l : list Label) : bool :=
  match l with 
  | [] => false 
  | h :: tl => if (Label_eqb e h) then true else list_inb e tl
=======
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
  | [ H : (_ ==b _) = true |- _ ] => rewrite -> equiv_decb_true_iff in H
  | [ H : (_ ==b _) <> true |- _ ] => rewrite -> equiv_decb_true_iff in H
>>>>>>> Stashed changes
  end.
