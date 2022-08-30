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
From RelationAlgebra Require Import monoid boolean prop sups bmx rewriting sums.
Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope nat_scope.

Definition eval_graph g :=
    let size := Datatypes.length(PropertyGraph.vertices g) in
    let size_pos := Pos.of_nat (Datatypes.length(PropertyGraph.vertices g)) in
    let adj_m := e_var2matrix_real g in
    @eval Label (fun _ => size_pos) (fun _ => size_pos) bmx
      (fun _ => size) adj_m size_pos size_pos.

Theorem pattern_associativity g v p1 p2 p3 :
    let pattern_1 :=
      Pattern.mk v (Pattern.Node (Pattern.Node (Pattern.Leaf p1) (Pattern.Leaf p2))
                                 (Pattern.Leaf p3))
    in
    let pattern_2 :=
      Pattern.mk v (Pattern.Node (Pattern.Leaf p1)
                                 (Pattern.Node (Pattern.Leaf p2) (Pattern.Leaf p3)))
    in
    let size_pos := Pos.of_nat (Datatypes.length(PropertyGraph.vertices g)) in
    let p1_m := pattern_to_matrix size_pos pattern_1 in
    let p2_m := pattern_to_matrix size_pos pattern_2 in
    eval_graph g p1_m = eval_graph g p2_m .
Proof.
  unfold eval_graph. (*assert (H: p1_m = p2_m).
  Focus 2. rewrite H. reflexivity.*)
  unfold pattern_to_matrix.
  (*assert (H: edge_pattern_to_matrix size_pos (Pattern.ledges pattern_1) = edge_pattern_to_matrix size_pos (Pattern.ledges pattern_2)).
  Focus 2. rewrite H. simpl. reflexivity.*)
  unfold edge_pattern_to_matrix. simpl. destruct (Pattern.edir p1); destruct (Pattern.edir p2); destruct (Pattern.edir p3).
 (* remember (e_dot (k_edges size_pos (Pattern.elabels p1) false (Pattern.enum p1))
              (labels_to_expr size_pos (Pattern.vlabels (Pattern.evertex p1)))) as M.
  remember (e_dot (k_edges size_pos (Pattern.elabels p2) false (Pattern.enum p2))
              (labels_to_expr size_pos (Pattern.vlabels (Pattern.evertex p2)))) as N.
  remember (e_dot (k_edges size_pos (Pattern.elabels p3) false (Pattern.enum p3))
              (labels_to_expr size_pos (Pattern.vlabels (Pattern.evertex p3)))) as P.*)
  eapply mx_dotA.
  remember (mx_dot bool_ops bool_tt) as bmx_dot.
  remember (eval adj_m (labels_to_expr (Pattern.vlabels v))) as a.
  remember (bmx_dot (eval adj_m (k_edges size_pos (Pattern.elabels p1) false (Pattern.enum p1)))
             (eval adj_m (labels_to_expr size_pos (Pattern.vlabels (Pattern.evertex p1))))) as b.
  remember (bmx_dot (eval adj_m (k_edges size_pos (Pattern.elabels p2) false (Pattern.enum p2)))
              (eval adj_m (labels_to_expr size_pos (Pattern.vlabels (Pattern.evertex p2))))) as c.
  remember  (bmx_dot (eval adj_m (k_edges size_pos (Pattern.elabels p3) false (Pattern.enum p3)))
               (eval adj_m (labels_to_expr size_pos (Pattern.vlabels (Pattern.evertex p3))))) as d.
  Print mx_dotA. rewrite Heqbmx_dot. (* unfold mx_dot.
  setoid_rewrite dotxsum. rewrite sup_swap.
  apply sup_weq; trivial. intro. rewrite dotsumx.
  apply sup_weq; trivial. intro. apply dotA.*)
  apply mx_dotA with (M:=b) (N:=c) (P:=d).

  remember (mx_dot bool_ops bool_tt size size size (eval adj_m (labels_to_expr size_pos (Pattern.vlabels v)))) as m.
  remember (mx_dot bool_ops bool_tt size size size
          (mx_dot bool_ops bool_tt size size size
             (eval adj_m (k_edges size_pos (Pattern.elabels p1) false (Pattern.enum p1)))
             (eval adj_m (labels_to_expr size_pos (Pattern.vlabels (Pattern.evertex p1)))))) as n.
  remember (mx_dot bool_ops bool_tt size size size
             (eval adj_m (k_edges size_pos (Pattern.elabels p2) false (Pattern.enum p2)))
             (eval adj_m (labels_to_expr size_pos (Pattern.vlabels (Pattern.evertex p2))))) as p.
  remember (mx_dot bool_ops bool_tt size size size
          (eval adj_m (k_edges size_pos (Pattern.elabels p3) false (Pattern.enum p3)))
          (eval adj_m (labels_to_expr size_pos (Pattern.vlabels (Pattern.evertex p3))))) as q.
  Type mx_dot. rewrite mx_dotA.
Admitted.
