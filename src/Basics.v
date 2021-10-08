Require Import String.
From hahn Require Import Hahn.
Require Import List.
Import ListNotations.

Set Implicit Arguments.

Section Aux.
Variable T : eqType.

Fixpoint list_eqb (l l' : list T) : bool :=
  match l, l' with
  | [], [] => true
  | a::l, b::l' =>
    eq_op a b && (list_eqb l l')
  | _, _ => false
  end.

Lemma list_eqP : Equality.axiom list_eqb.
Proof using T.
  red. induction x.
  { ins. destruct y; constructor; desf. }
  ins. desf.
  { constructor. desf. }
  destruct (eq_op a s) eqn:HH; subst; ins.
  2: { constructor. intros AA. inv AA. rewrite beq_refl in HH. inv HH. }
  specialize (IHx l).
  apply Bool.reflect_iff in IHx.
  apply Bool.iff_reflect.
  etransitivity; eauto.
  split; intros AA; desf.
  apply hahn__beq_rewrite in HH. desf.
Qed.

Canonical Structure list_eqMixin := EqMixin list_eqP.
Canonical Structure list_eqType := Eval hnf in EqType (list T) list_eqMixin.

Fixpoint list_inb {T : eqType} x (l : list T) : bool :=
  match l with
  | [] => false
  | a::l => eq_op x a || list_inb x l
  end.
End Aux.