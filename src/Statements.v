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

Require Import HahnBase.

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
    subst MXDOT. Print eq_refl.
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

Lemma edge_pattern_to_matrix_insert_tree_r x tl tr :
  edge_pattern_to_matrix x (Pattern.Node tl tr) =
  edge_pattern_to_matrix x (Pattern.insert_tree_r tr tl).
Proof.
  generalize dependent tr.
  induction tl; ins.
  rewrite <- IHtl2.
Admitted.

Lemma edge_pattern_to_matrix_tree_normalization t x :
  edge_pattern_to_matrix x t = edge_pattern_to_matrix x (Pattern.tree_normalize t).
Proof.
    induction t; ins.
    rewrite <- edge_pattern_to_matrix_insert_tree_r. ins.
    now rewrite <- IHt2, <- IHt1.
Qed.

Theorem pattern_normalization_eq g v t :
    let p  := Pattern.mk v t in
    let np := Pattern.normalize p in
    let size_pos :=
      Pos.of_nat (Datatypes.length(PropertyGraph.vertices g)) in
    let p1_m := pattern_to_matrix size_pos p  in
    let p2_m := pattern_to_matrix size_pos np in
    eval_graph g p1_m ≡ eval_graph g p2_m.
Proof.
    unfold eval_graph. simpl.
    set (Datatypes.length (PropertyGraph.vertices g)) as n.
    intros oa ob.
    remember (mx_dot bool_ops bool_tt n n n) as MXDOT.
    enough (edge_pattern_to_matrix (Pos.of_nat n) t =
            edge_pattern_to_matrix (Pos.of_nat n) (Pattern.tree_normalize t)) as AA.
    { rewrite AA. reflexivity. }
    apply edge_pattern_to_matrix_tree_normalization.
Qed.
