Require Import Utils.
From RelationAlgebra Require Export ordinal lattice level sups comparisons.

Open Scope ltb_scope.

Section index_of.
  Context {A : Type}.
  Context `{EqDec A eq}.
  Context (a : A).

  Fixpoint index_of (xs : list A) : option (ord (length xs)) :=
    match xs with
    | [] => None
    | x :: xs =>
      if a ==b x then Some ord0
      else option_map ordS (index_of xs)
    end.

  Lemma In_index_of xs (HIn : In a xs) :
    exists i, index_of xs = Some i.
  Proof using.
    induction xs as [| x xs IHxs ]. { inv HIn. }
    simpls. case equiv_decbP; ins; subst.
    { now eexists. }
    desf. destruct IHxs as [? IH]; auto.
    rewrite IH. now eexists.
  Qed.

  Lemma index_of_nth xs i
    (Hindex : index_of xs = Some i) :
      nth_error xs i = Some a.
  Proof using.
    gen_dep i.
    induction xs as [| x xs IHxs ]; ins.
    unfold option_map in *.
    destruct (equiv_decbP a x); desf.
    simpls. auto.
  Qed.

  Lemma index_of_In xs i
    (Hindex : index_of xs = Some i) :
      In a xs.
  Proof using.
    eapply nth_error_In, index_of_nth, Hindex.
  Qed.

  Lemma index_of_In_iff xs :
    In a xs <-> exists i, index_of xs = Some i.
  Proof using.
    split; ins.
    { now apply In_index_of. }
    { desf. eauto using index_of_In. }
  Qed.
End index_of.

(* TODO: prove that nat is a lattice *)

Canonical Structure nat_lattice_ops: lattice.ops := {|
  leq := fun i j => i <= j;
  weq := eq;
  cup := max;
  cap := min;
  bot := 0;
  neg := id; (* this is a stub *)
  top := 1; (* this is a stub *)
|}.

Theorem ltb_succ (x y : nat) : x <= y <-> x < S y.
Proof.
  split; ins; gen_dep y.
  all: induction x; ins; destruct y; simpls; auto.
  destruct x; auto.
Qed.

Theorem leb_refl (n : nat) : n <= n.
Proof. induction n; auto. Qed.

Theorem leb_trans (x y z : nat)
  (H1 : x <= y) (H2 : y <= z) : x <= z.
Proof.
  gen_dep y x.
  induction z; ins; destruct y, x; simpls.
  eauto.
Qed.

Theorem leb_antisym (x y : nat)
  (H1 : x <= y) (H2 : y <= x) : x = y.
Proof.
  gen_dep x.
  induction y; ins; destruct x; simpls.
  f_equal. eauto.
Qed.

Theorem max_leb (x y z : nat)
  (H1 : x <= z) (H2 : y <= z) : max x y <= z.
Proof.
  gen_dep x y.
  induction z; ins; destruct x, y; simpls.
  auto.
Qed.

Theorem max_leb_l (x y z : nat)
  (H : max x y <= z) : x <= z.
Proof.
  gen_dep x y.
  induction z; ins; destruct x, y; simpls.
  eauto.
Qed.

Theorem max_leb_r (x y z : nat)
  (H : max x y <= z) : y <= z.
Proof.
  gen_dep x y.
  induction z; ins; destruct x, y; simpls.
  eauto.
Qed.

Theorem max_leb_iff (x y z : nat) :
  max x y <= z <-> x <= z /\ y <= z.
Proof.
  split; ins.
  { split; eauto using max_leb_l, max_leb_r. }
  { desf. eauto using max_leb. }
Qed.

Theorem leb_min (x y z : nat)
  (H1 : z <= x) (H2 : z <= y) : z <= min x y.
Proof.
  gen_dep x y.
  induction z; ins; destruct x, y; simpls.
  auto.
Qed.

Theorem leb_min_l (x y z : nat)
  (H : z <= min x y) : z <= x.
Proof.
  gen_dep x y.
  induction z; ins; destruct x, y; simpls.
  eauto.
Qed.

Theorem leb_min_r (x y z : nat)
  (H : z <= min x y) : z <= y.
Proof.
  gen_dep x y.
  induction z; ins; destruct x, y; simpls.
  eauto.
Qed.

Theorem leb_min_iff (x y z : nat) :
  z <= min x y <-> z <= x /\ z <= y.
Proof.
  split; ins.
  { split; eauto using leb_min_l, leb_min_r. }
  { desf. eauto using leb_min. }
Qed.

Theorem min_leb_l (x y : nat) : min x y <= x.
Proof.
  gen_dep y; induction x; ins; destruct y; simpls.
Qed.

Theorem min_leb_r (x y : nat) : min x y <= y.
Proof.
  gen_dep y; induction x; ins; destruct y; simpls.
Qed.

Theorem leb_max_l (x y : nat) : x <= max x y.
Proof.
  gen_dep y; induction x; ins; destruct y; simpls.
  apply leb_refl.
Qed.

Theorem leb_max_r (x y : nat) : y <= max x y.
Proof.
  gen_dep y; induction x; ins; destruct y; simpls.
  apply leb_refl.
Qed.

Theorem zro_leb (x : nat) : 0 <= x.
Proof. induction x; auto. Qed.

Theorem min_leb_max (x y : nat) : min x y <= max x y.
Proof.
  gen_dep y; induction x; ins; destruct y; simpls.
Qed.

Theorem max_comm (x y : nat) : max x y = max y x.
Proof.
  gen_dep y; induction x; ins; destruct y; simpls.
  f_equal. eauto.
Qed.

Theorem max_assoc (x y z : nat) : max x (max y z) = max (max x y) z.
Proof.
  gen_dep y z; induction x; ins; destruct y, z; simpls.
  f_equal. eauto.
Qed.

Theorem max_idemp (x : nat) : max x x = x.
Proof.
  induction x; ins; simpls.
  f_equal. eauto.
Qed.

Theorem min_comm (x y : nat) : min x y = min y x.
Proof.
  gen_dep y; induction x; ins; destruct y; simpls.
  f_equal. eauto.
Qed.

Theorem min_assoc (x y z : nat) : min x (min y z) = min (min x y) z.
Proof.
  gen_dep y z; induction x; ins; destruct y, z; simpls.
  f_equal. eauto.
Qed.

Theorem min_idemp (x : nat) : min x x = x.
Proof.
  induction x; ins; simpls.
  f_equal. eauto.
Qed.

Theorem max_min_distr (x y z : nat) : max (min x y) (min x z) = min x (max y z).
Proof.
  gen_dep y z; induction x; ins; destruct y, z; simpls.
  f_equal. eauto.
Qed.

Theorem min_max_cancel (x y : nat) : min x (max x y) = x.
Proof.
  gen_dep y; induction x; ins; destruct y; simpls.
  all: f_equal; eauto.
  { apply min_idemp. }
Qed.

Theorem min_max_distr (x y z : nat) : min (max x y) (max x z) = max x (min y z).
Proof.
  gen_dep y z; induction x; ins; destruct y, z; simpls.
  all: f_equal.
  { apply min_idemp. }
  { apply min_max_cancel. }
  { rewrite min_comm. apply min_max_cancel. }
  eauto.
Qed.

Theorem leb_max_eq_l_iff (x y : nat) :
  max x y = x <-> y <= x.
Proof.
  split; ins.
  { gen_dep y. induction x; intros [|y]; ins.
    desf; auto. }
  apply leb_antisym.
  { eapply max_leb; auto using leb_refl. }
  { eapply leb_max_l. }
Qed.

Theorem leb_max_eq_r_iff (x y : nat) :
  max x y = y <-> x <= y.
Proof.
  rewrite max_comm. apply leb_max_eq_l_iff.
Qed.

Theorem leb_min_eq_l_iff (x y : nat) :
  min x y = x <-> x <= y.
Proof.
  split; ins.
  { gen_dep y. induction x; intros [|y]; ins.
    desf; auto. }
  apply leb_antisym.
  { eapply min_leb_l. }
  { eapply leb_min; auto using leb_refl. }
Qed.

Theorem leb_min_eq_r_iff (x y : nat) :
  min x y = y <-> y <= x.
Proof.
  rewrite min_comm. apply leb_min_eq_l_iff.
Qed.

#[global]
Instance nat_lattice_laws: lattice.laws (CUP + CAP + BOT) nat_lattice_ops.
Proof.
  constructor; ins.
  { constructor.
    { unfold Reflexive. apply leb_refl. }
    { unfold Transitive. apply leb_trans. } }
  { simpls. intros.
    split.
    { ins; subst. split; apply leb_refl. }
    { intros []. now apply leb_antisym. } }
  { apply max_leb_iff. }
  { apply leb_min_iff. }
  { right. apply zro_leb. }
  { rewrite min_max_distr. apply leb_refl. }
Qed.

Theorem eqb_eq_iff (A: cmpType) (x y : A) : eqb x y <-> x = y.
Proof.
  split; ins.
  { apply eqb_eq. auto. }
  { subst. apply eqb_refl. }
Qed.