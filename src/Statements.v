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

Lemma edge_pattern_to_matrix_tree_normalization (t1 t2: Pattern.tree) (g: PropertyGraph.t):
  let n :=  (Datatypes.length (PropertyGraph.vertices g)) in
   (@eval Label (fun _ => (Pos.of_nat n)) (fun _ => (Pos.of_nat n)) bmx
                                        (fun _ => n) (e_var2matrix_real g) (Pos.of_nat n) (Pos.of_nat n)
                                        (edge_pattern_to_matrix (Pos.of_nat n) (Pattern.insert_tree_r t2 t1))
       )
    ≡  mx_dot bool_ops bool_tt n n n (@eval Label (fun _ => (Pos.of_nat n)) (fun _ => (Pos.of_nat n)) bmx
                                        (fun _ => n) (e_var2matrix_real g) (Pos.of_nat n) (Pos.of_nat n)
                                        (edge_pattern_to_matrix (Pos.of_nat n) t1))
                                       (@eval Label (fun _ => (Pos.of_nat n)) (fun _ => (Pos.of_nat n)) bmx
                                        (fun _ => n) (e_var2matrix_real g) (Pos.of_nat n) (Pos.of_nat n)
                                        (edge_pattern_to_matrix (Pos.of_nat n) t2)) .
Proof.
    intros n.
    induction t1. simpl. reflexivity.
    ins.
    remember (@eval Label (fun _ => (Pos.of_nat n)) (fun _ => (Pos.of_nat n)) bmx
                (fun _ => n) (e_var2matrix_real g) (Pos.of_nat n) (Pos.of_nat n)) as EVAL.
    remember (mx_dot bool_ops bool_tt n n n) as MXDOT.

    assert (forall a, EVAL (edge_pattern_to_matrix (Pos.of_nat n) (Pattern.insert_tree_r t2 t1_2)) a =
                       MXDOT
             (EVAL (edge_pattern_to_matrix (Pos.of_nat n) t1_2))
             (EVAL (edge_pattern_to_matrix (Pos.of_nat n) t2)) a) as IH1.
    {intros. apply functional_extensionality. apply IHt1_2. }

     assert (forall a, EVAL (edge_pattern_to_matrix (Pos.of_nat n) (Pattern.insert_tree_r t2 t1_1)) a =
                       MXDOT
             (EVAL (edge_pattern_to_matrix (Pos.of_nat n) t1_1))
             (EVAL (edge_pattern_to_matrix (Pos.of_nat n) t2)) a) as IH2.
    {intros. apply functional_extensionality. apply IHt1_1. }
    apply  functional_extensionality in IH1. apply functional_extensionality in IH2. rewrite IH1.
    assert (forall a b c,
             MXDOT (MXDOT a b) c ≡
             MXDOT a (MXDOT b c))
    as MXDOT_ASSOC.
  { intros x y z. subst MXDOT.
     rewrite mx_dotA with (M:=x) (N:=y) (P:=z).
     reflexivity.}
  simpl.


    (*induction t; ins.
    rewrite <- edge_pattern_to_matrix_insert_tree_r. ins.
    now rewrite <- IHt2, <- IHt1.*)
Admitted.

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
    subst MXDOT. unfold mx_dot.
    (* apply sup_weq'. *)
    admit. }
  remember
    (MXDOT
       (eval (e_var2matrix_real g)
          (labels_to_expr
             (Pos.of_nat n)
             (Pattern.vlabels v)))) as VEVAL.
  assert (forall a b (EQ : a ≡ b), VEVAL a ≡ VEVAL b) as MORPH.
  { intros a b EQ.
    subst VEVAL. now apply MXDOT_MORPH_R. }
  apply MORPH. induction t; ins.
  rewrite edge_pattern_to_matrix_tree_normalization with
    (t2 := Pattern.tree_normalize t2 ) (t1 := Pattern.tree_normalize t1) (g := g).
  do 2 match goal with
    | H : forall a a0 : ord n, ?A a a0 = ?B a a0 |- _ =>
        assert (A = B) as AA by (do 2 (apply functional_extensionality; intros); apply H);
        clear H; rename AA into H
    end.
  now rewrite IHt1, IHt2.
Admitted.
