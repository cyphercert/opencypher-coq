Require Import String.
Require Import List.
Require Import Bool.
Require Import BinNums.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.
From hahn Require Import HahnBase.
From Coq Require Import Classes.EquivDec.
From Coq Require Import Classes.RelationClasses.

Require Import Cypher.
Require Import Semantics.
Require Import PropertyGraph.
Require Import ExecutionPlan.
Require Import Maps.
Require Import Utils.

Import PropertyGraph.
Import ExecutionPlan.
Import FilterMode.
Import ExpandMode.

Section translate_pattern.
  Import Pattern.

  Definition translate_pvertex pv plan : ExecutionPlan.t :=
    match vlabel pv with
    | Some l => FilterByLabel Vertices (vname pv) l plan
    | None => plan
    end.

  Definition translate_pedge pe plan : ExecutionPlan.t :=
    match elabel pe with
    | Some l => FilterByLabel Edges (ename pe) l plan
    | None => plan
    end.

  Fixpoint translate_pattern (pi : Pattern.t) : ExecutionPlan.t :=
    match pi with
    | Pattern.start pv => 
        translate_pvertex pv (ScanVertices (vname pv))
    | Pattern.hop pi pe pv =>
      let plan := translate_pattern pi in
      let plan :=
        if (In_decb (vname pv) (dom_vertices pi)) then
          Expand Into (vname (last pi)) (ename pe) (vname pv) (edir pe) plan
        else
          Expand All (vname (last pi)) (ename pe) (vname pv) (edir pe) plan
      in translate_pvertex pv (translate_pedge pe plan)
    end.
End translate_pattern.

Ltac normilize_bool :=
  repeat match goal with
  | [ H : negb _ = true |- _ ] => rewrite negb_true_iff in H
  | [ H : negb _ <> true |- _ ] => rewrite negb_true_iff in H
  | [ H : _ = false |- _ ] => rewrite <- not_true_iff_false in H
  | [ H : _ <> false |- _ ] => rewrite -> not_false_iff_true in H
  | [ H : (In_decb _ _) = true |- _ ] => rewrite -> In_decb_true_iff in H
  | [ H : (In_decb _ _) <> true |- _ ] => rewrite -> In_decb_true_iff in H
  end.

Theorem translate_pattern__type_of pi n (Hwf : Pattern.wf pi) :
  (In n (Pattern.dom_edges pi) <-> type_of (translate_pattern pi) n = Some Value.GEdgeT) /\
  (In n (Pattern.dom_vertices pi) <-> type_of (translate_pattern pi) n = Some Value.GVertexT).
Proof.
  all: induction pi; simpls.
  all: unfold Pattern.wf in *.
  all: unfold translate_pvertex.
  all: unfold translate_pedge.

  { do 2 split; ins; desf; simpls.
    all: autounfold with unfold_pat in *.
    all: desf; simpls.
    all: eauto with pattern_wf_db.
    all: unfold complement, equiv in *; contradiction. }

  split.
  all: desf; simpls.
  all: normilize_bool.
  all: split; ins; desf.

  all: try now apply update_eq.
  all: try rewrite update_neq.
  all: try now apply update_eq.
  all: try rewrite update_neq.
  all: try (apply IHpi; [ split | ]; now eauto with pattern_wf_db).

  all: try now (intros ?; exfalso; subst; eauto with pattern_wf_db).
  all: try now (intros ?; exfalso; subst; simple eapply NoDup_cons_l; eassumption).

  all: autounfold with unfold_pat in *.
  all: desf; simpls.
  all: try now (left; eauto with pattern_wf_db).
  all: right; apply IHpi; [ split | ]; now eauto with pattern_wf_db.
Qed.

Corollary translate_pattern__type_of_GVertexT pi n (Hwf : Pattern.wf pi) :
  (In n (Pattern.dom_vertices pi) <-> type_of (translate_pattern pi) n = Some Value.GVertexT).
Proof. edestruct translate_pattern__type_of; eassumption. Qed.

Corollary translate_pattern__type_of_GEdgeT pi n (Hwf : Pattern.wf pi) :
  (In n (Pattern.dom_edges pi) <-> type_of (translate_pattern pi) n = Some Value.GEdgeT).
Proof. edestruct translate_pattern__type_of; eassumption. Qed.

Corollary translate_pattern__type_of_None pi n (Hwf : Pattern.wf pi)
  (HIn_vertices : ~ In n (Pattern.dom_vertices pi))
  (HIn_edges    : ~ In n (Pattern.dom_edges pi)) :
    type_of (translate_pattern pi) n = None.
Proof.
  edestruct type_of_types as [H | [H | H]].
  - eapply translate_pattern__type_of_GVertexT in H; try eassumption.
    apply HIn_vertices in H. contradiction.
  - eapply translate_pattern__type_of_GEdgeT in H; try eassumption.
    apply HIn_edges in H. contradiction.
  - assumption.
Qed.

Corollary translate_pattern__type_of_None_iff pi n (Hwf : Pattern.wf pi) :
  ~ In n (Pattern.dom_vertices pi) /\ ~ In n (Pattern.dom_edges pi) <->
    type_of (translate_pattern pi) n = None.
Proof.
  split.
  { intros [? ?]. apply translate_pattern__type_of_None; assumption. }
  ins. split.
  all: intros contra.
  1: apply translate_pattern__type_of_GVertexT in contra; try assumption.
  2: apply translate_pattern__type_of_GEdgeT   in contra; try assumption.
  all: congruence.
Qed.

Theorem translate_pattern_wf pi (Hwf : Pattern.wf pi) :
  ExecutionPlan.wf (translate_pattern pi).
Proof.
  induction pi; simpls.
  2: assert (Pattern.wf pi) by (eapply Pattern.hop_wf; eassumption).
  all: unfold translate_pvertex, translate_pedge.
  all: desf; simpls; splits; auto.
  all: normilize_bool.
  all: try apply translate_pattern__type_of_GVertexT; try assumption.
  all: try apply translate_pattern__type_of_None; try assumption.
  all: eauto with pattern_wf_db.

  all: autounfold with unfold_pat in *.
  all: desf.
  all: unfold complement, equiv in *.
  all: try contradiction.
  all: try apply translate_pattern__type_of_GVertexT; try assumption.
  all: try (exfalso; simple eapply Pattern.wf__pe_neq_pv; eassumption).
  all: try (exfalso; simple eapply Pattern.wf__pv_neq_pe; eassumption).
Qed.

Module EvalQueryImpl (S : ExecutionPlan.Spec).
  Module EvalPlanImpl := EvalPlan S.
  Import S.
  Import EvalPlanImpl.

  Definition eval_pattern (graph : PropertyGraph.t) (pi : Pattern.t) : option BindingTable.t :=
    let plan := translate_pattern pi in
      EvalPlanImpl.eval graph plan.
  
  Theorem eval_pattern__wf graph pi
    (Hwf_g : PropertyGraph.wf graph) (Hwf : Pattern.wf pi) :
      exists table', eval_pattern graph pi = Some table'.
  Proof.
    eapply eval_wf; eauto.
    now apply translate_pattern_wf.
  Qed.
End EvalQueryImpl.
