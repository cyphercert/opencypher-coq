Require Import String.
Require Import List.
Require Import BinNums.
Require Import BinInt.
Import ListNotations.
Require Import Cypher.
Import PropertyGraph.
Require Import KleeneTranslation.
Require Import PGMatrixExtraction.
Require Import Utils.
Require Import Lia.

From RelationAlgebra Require Import syntax matrix bmx ordinal.
From RelationAlgebra Require Import monoid boolean prop sups
  bmx rewriting sums.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

From hahn Require Import HahnBase.

Definition eval_graph g :=
    let size := Datatypes.length(PropertyGraph.vertices g) in
    let size_pos := Pos.of_nat (Datatypes.length(PropertyGraph.vertices g))
    in
    let adj_m := e_var2matrix_real g in
    @eval Label (fun _ => size_pos) (fun _ => size_pos) bmx
      (fun _ => size) adj_m size_pos size_pos.

Theorem pattern_associativity g v t1 t2 t3 :
    let pattern_1 :=
      Pattern.mk v (Pattern.Node (Pattern.Node t1 t2) t3)
    in
    let pattern_2 :=
      Pattern.mk v (Pattern.Node t1 (Pattern.Node t2 t3))
    in
    let size_pos :=
      Pos.of_nat (Datatypes.length(PropertyGraph.vertices g)) in
    let p1_m := pattern_to_matrix size_pos pattern_1 in
    let p2_m := pattern_to_matrix size_pos pattern_2 in
    eval_graph g p1_m ≡ eval_graph g p2_m.
Proof.
  unfold eval_graph. simpl.
  set (Datatypes.length (PropertyGraph.vertices g)) as n.
  intros oa ob.
  remember (mx_dot bool_ops bool_tt n n n) as MXDOT.
  assert (forall a b c,
             MXDOT (MXDOT a b) c ≡
             MXDOT a (MXDOT b c))
    as MXDOT_ASSOC.
  { intros a b c. subst MXDOT.
    rewrite mx_dotA with (M:=a) (N:=b) (P:=c).
    reflexivity. }
  assert (forall X a b (EQ : a ≡ b), MXDOT X a ≡ MXDOT X b)
    as MXDOT_MORPH_R.
  { intros X a b EQ.
    subst MXDOT.
    admit. }
  remember
    (MXDOT
       (eval (e_var2matrix_real g)
          (labels_to_expr
             (Pos.of_nat n)
             (Pattern.vlabels v)))) as VEVAL.
  enough (forall a b (EQ : a ≡ b), VEVAL a ≡ VEVAL b) as MORPH.
  { apply MORPH. apply MXDOT_ASSOC. }
  intros a b EQ.
  subst VEVAL. now apply MXDOT_MORPH_R.
Admitted.
