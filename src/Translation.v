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

Import PartialMap.Notations.
Import TotalMap.Notations.
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

Ltac desf_translate_pvertex_pedge :=
  unfold translate_pvertex, translate_pedge in *;
  desf; simpls;
  normalize_bool.

Lemma type_of__rcd__pattern__cases pi r :
  Rcd.type_of r = PatternT.type_of pi <->
    (forall n, Rcd.type_of r n = Some Value.GVertexT <->
      PatternT.type_of pi n = Some Value.GVertexT) /\
    (forall n, Rcd.type_of r n = Some Value.GEdgeT <->
      PatternT.type_of pi n = Some Value.GEdgeT) /\
    (forall n, Rcd.type_of r n = None <->
      PatternT.type_of pi n = None).
Proof.
  split.
  { intros Heq; rewrite Heq.
    splits; ins; auto. }
  intros [Hv [He Hn]].
  extensionality k.
  edestruct PatternT.type_of__types as [Heq | [Heq | Heq]].
  all: erewrite Heq.
  { rewrite Hv; auto. }
  { rewrite He; auto. }
  { rewrite Hn; auto. }
Qed.

Theorem type_of__translate_pattern pi (Hwf : Pattern.wf pi) :
  type_of (translate_pattern pi) = PatternT.type_of pi.
Proof.
  all: induction pi; simpls.
  all: desf_translate_pvertex_pedge.
  all: assert (Hwf': Pattern.wf pi) by (eauto with pattern_wf_db).
  all: extensionality n.
  all: desf_unfold_pat.
  all: try (exfalso; eapply Pattern.wf__pv_neq_pe; now eauto).
  all: rewrite IHpi; auto.
  all: rewrite <- PatternT.In_dom_vertices__iff; auto.
Qed.

Corollary translate_pattern__type_of_GVertexT pi n (Hwf : Pattern.wf pi) :
  (In n (Pattern.dom_vertices pi) <-> type_of (translate_pattern pi) n = Some Value.GVertexT).
Proof.
  rewrite type_of__translate_pattern; auto.
  now rewrite PatternT.In_dom_vertices__iff.
Qed.

Corollary translate_pattern__type_of_GEdgeT pi n (Hwf : Pattern.wf pi) :
  (In n (Pattern.dom_edges pi) <-> type_of (translate_pattern pi) n = Some Value.GEdgeT).
Proof. 
  rewrite type_of__translate_pattern; auto.
  now rewrite PatternT.In_dom_edges__iff.
Qed.

Theorem translate_pattern__type_of__types pi n :
  type_of (translate_pattern pi) n = Some Value.GVertexT \/
  type_of (translate_pattern pi) n = Some Value.GEdgeT \/
  type_of (translate_pattern pi) n = None.
Proof.
  edestruct type_of_types as [H | [H | H]]; eauto.
Qed.

Corollary translate_pattern__type_of_None pi n (Hwf : Pattern.wf pi)
  (HIn_vertices : ~ In n (Pattern.dom_vertices pi))
  (HIn_edges    : ~ In n (Pattern.dom_edges pi)) :
    type_of (translate_pattern pi) n = None.
Proof.
  edestruct translate_pattern__type_of__types as [H | [H | H]]; eauto.
  1: eapply translate_pattern__type_of_GVertexT in H; try eassumption.
  2: eapply translate_pattern__type_of_GEdgeT in H; try eassumption.
  all: congruence.
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
  all: normalize_bool.
  all: try apply translate_pattern__type_of_GVertexT; try assumption.
  all: try apply translate_pattern__type_of_None; try assumption.
  all: eauto with pattern_wf_db.

  all: desf_unfold_pat.
  all: try contradiction.
  all: try apply translate_pattern__type_of_GVertexT; try assumption.
  all: try intro; exfalso.
  all: try (eapply Pattern.wf__pv_neq_pe; now eauto).
  all: try (eapply Pattern.wf__last_neq_pe; now eauto).
Qed.

Module EvalQueryImpl (S : ExecutionPlan.Spec) : EvalQuery.Spec.
  Module EvalPlanImpl := EvalPlan S.
  Import S.
  Import EvalPlanImpl.

  Definition eval_match_clause (graph : PropertyGraph.t) (pi : Pattern.t) : option BindingTable.t :=
    let plan := translate_pattern pi in
      EvalPlanImpl.eval graph plan.
  
  Theorem match_clause_wf graph pi
    (Hwf_g : PropertyGraph.wf graph) (Hwf : Pattern.wf pi) :
      exists table', eval_match_clause graph pi = Some table'.
  Proof.
    eapply eval_wf; eauto.
    now apply translate_pattern_wf.
  Qed.

  Theorem match_clause_type_of graph pi table'
    (Hres : eval_match_clause graph pi = Some table') :
    BindingTable.of_type table' (type_of (translate_pattern pi)).
  Proof.
    eapply eval_type_of; eassumption.
  Qed.

  Ltac desf_match_result Hres :=
    unfold eval_match_clause in Hres; simpls;
    desf_translate_pvertex_pedge;
    unfold option_bind in *; desf.

  Theorem match_clause_reduce graph pi pe pv table'
    (Hres : eval_match_clause graph (Pattern.hop pi pe pv) = Some table') :
      exists table, eval_match_clause graph pi = Some table.
  Proof.
    desf_match_result Hres.
    all: eauto.
  Qed.

  Theorem match_clause_type graph pi table' r'
    (Hres : eval_match_clause graph pi = Some table')
    (Hwf : Pattern.wf pi)
    (HIn : In r' table') :
      Rcd.type_of r' = PatternT.type_of pi.
  Proof.
    unfold eval_match_clause in Hres.
    apply eval_type_of in Hres.
    rewrite type_of__translate_pattern in Hres; auto.
  Qed.

  Lemma matches_pattern_type_start r' pv v
    (Htype : Rcd.type_of r' = PatternT.type_of (Pattern.start pv))
    (Hval : r' (Pattern.vname pv) = Some (Value.GVertex v)) :
      r' = (Pattern.vname pv |-> Value.GVertex v).
  Proof.
    extensionality k; simpls.
    apply (f_equal (fun f => f k)) in Htype.
    desf_unfold_pat.
    now apply Rcd.type_of_None.
  Qed.

  Lemma matches_pattern_type_start' r' pv v
    (Hval : r' = (Pattern.vname pv |-> Value.GVertex v)) :
      Rcd.type_of r' = PatternT.type_of (Pattern.start pv).
  Proof.
    extensionality k.
    subst. simpl.
    now rewrite Rcd.type_of_singleton.
  Qed.

  Definition expansion_of_by_hop' graph r' r mode v_from e v_to pi pe pv :=
    expansion_of' graph r' r mode v_from e v_to
      (Pattern.vname (Pattern.last pi)) (Pattern.ename pe) (Pattern.vname pv) (Pattern.edir pe).

  Definition expansion_of_by_hop graph r' r mode pi pe pv :=
    expansion_of graph r' r mode
      (Pattern.vname (Pattern.last pi)) (Pattern.ename pe) (Pattern.vname pv) (Pattern.edir pe).

  Lemma matches_pattern_type_exclude_All pi pe pv r'
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (Htype : Rcd.type_of r' = PatternT.type_of (Pattern.hop pi pe pv))
    (HIn : ~ In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      Rcd.type_of (Pattern.ename pe !-> None; Pattern.vname pv !-> None; r') =
        PatternT.type_of pi.
  Proof.
    assert (Hwf': Pattern.wf pi) by (eauto with pattern_wf_db).
    repeat rewrite Rcd.type_of_t_update; simpls.
    rewrite Htype; clear Htype; unfold PartialMap.update.
    extensionality k.
    desf_unfold_pat.
    { erewrite <- PatternT.wf__type_of_pe; eauto. }
    { erewrite <- PatternT.wf__type_of_pv__None; eauto. }
  Qed.

  Lemma matches_pattern_type_exclude_Into pi pe pv r'
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (Htype : Rcd.type_of r' = PatternT.type_of (Pattern.hop pi pe pv))
    (HIn : In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      Rcd.type_of (Pattern.ename pe !-> None; r') = PatternT.type_of pi.
  Proof.
    assert (Hwf': Pattern.wf pi) by (eauto with pattern_wf_db).
    rewrite Rcd.type_of_t_update; simpls.
    rewrite Htype; clear Htype; unfold PartialMap.update.
    extensionality k.
    desf_unfold_pat.
    { erewrite <- PatternT.wf__type_of_pe; eauto. }
    { erewrite <- PatternT.wf__type_of_pv__Some; eauto. }
  Qed.

  Lemma matches_hop_All graph path e v pi pe pv r'
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (Htype : Rcd.type_of r' = PatternT.type_of (Pattern.hop pi pe pv))
    (Hmatch : Path.matches graph r' (Path.hop path e v) (Pattern.hop pi pe pv))
    (HIn : ~ In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      exists r, << Hexp : expansion_of_by_hop graph r' r All pi pe pv >> /\
                << Hmatch' : Path.matches graph r path pi >> /\
                << Htype' : Rcd.type_of r = PatternT.type_of pi >>.
  Proof.
    exists (Pattern.ename pe !-> None; Pattern.vname pv !-> None; r').
    inv Hmatch.
    destruct Hpe, Hpv.
    splits.
    { unfold expansion_of_by_hop, expansion_of, expansion_of'.
      do 3 eexists. splits; eauto.
      all: try extensionality k.
      all: desf_unfold_pat.
      all: try (exfalso; eapply Pattern.wf__pe_neq_last; now eauto).
      { exfalso. apply HIn. rewrite e0. apply Pattern.last__dom_vertices. }
      eauto using Path.matches_last. }
    { apply Path.matches_exclude. apply Path.matches_exclude.
      all: eauto with pattern_wf_db. }
    { apply matches_pattern_type_exclude_All; eauto. }
  Qed.

  Lemma matches_hop_Into graph path e v pi pe pv r'
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (Htype : Rcd.type_of r' = PatternT.type_of (Pattern.hop pi pe pv))
    (Hmatch : Path.matches graph r' (Path.hop path e v) (Pattern.hop pi pe pv))
    (HIn : In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      exists r, << Hexp : expansion_of_by_hop graph r' r Into pi pe pv >> /\
                << Hmatch' : Path.matches graph r path pi >> /\
                << Hdom' : Rcd.type_of r = PatternT.type_of pi >>.
  Proof.
    exists (Pattern.ename pe !-> None; r').
    inv Hmatch.
    destruct Hpe, Hpv.
    eauto.
    splits.
    { unfold expansion_of_by_hop, expansion_of, expansion_of'.
      do 3 eexists. splits; eauto.
      
      all: try extensionality k.
      all: desf_unfold_pat.
      all: try (exfalso; eapply Pattern.wf__pe_neq_last; now eauto).
      all: try (exfalso; eapply Pattern.wf__pe_neq_pv; now eauto).
      eauto using Path.matches_last. }
    { apply Path.matches_exclude.
      all: eauto with pattern_wf_db. }
    { eapply matches_pattern_type_exclude_Into; eauto. }
  Qed.

  Theorem match_clause_spec graph path pi table' r'
    (Hres : eval_match_clause graph pi = Some table')
    (Hwf : Pattern.wf pi)
    (Htype : Rcd.type_of r' = PatternT.type_of pi)
    (Hmatch : Path.matches graph r' path pi) :
      In r' table'.
  Proof.
    gen_dep Htype Hres r' table' path.
    induction pi; ins.
    all: destruct path; inv Hmatch.
    all: destruct Hpv.
    all: try destruct Hpe.

    { all: desf_match_result Hres.
      1: eapply filter_vertices_by_label_spec; try eassumption.
      all: auto.
      all: assert (r' = (Pattern.vname pv |-> Value.GVertex v))
            by (eauto using matches_pattern_type_start); subst.
      all: eauto using scan_vertices_spec. }

    all: desf_match_result Hres.
    all: repeat match goal with
         | [H : filter_by_label Vertices _ _ _ _ = _ |- _ ] =>
            eapply filter_vertices_by_label_spec; try eassumption; clear H
         | [H : filter_by_label Edges _ _ _ _ = _ |- _ ] =>
            eapply filter_edges_by_label_spec; try eassumption; clear H
         end.
    all: auto.
    all: match goal with 
         | [H : expand Into _ _ _ _ _ _ = _ |- _ ] =>
            apply matches_hop_Into in Hmatch; eauto
         | [H : expand All _ _ _ _ _ _ = _ |- _ ] =>
            apply matches_hop_All in Hmatch; eauto
         end.
    all: desf.
    all: match goal with
         | [H : expand _ _ _ _ _ _ _ = _ |- _ ] =>
            eapply expand_spec; eauto
         end.
    all: eapply IHpi.
    all: eauto with pattern_wf_db.
  Qed.

  Lemma matches_pattern_type_hop graph mode r r' pi pe pv
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (Htype : Rcd.type_of r = PatternT.type_of pi)
    (Hexp : expansion_of_by_hop graph r' r mode pi pe pv) :
      Rcd.type_of r' = PatternT.type_of (Pattern.hop pi pe pv).
  Proof.
    unfold expansion_of_by_hop, expansion_of, expansion_of' in Hexp.
    unfold Rcd.matches_pattern_dom, PartialMap.in_dom in *.
    ins; desf; desf.
    all: repeat rewrite Rcd.type_of_update; simpls.
    all: rewrite <- Htype.
    { reflexivity. }

    extensionality k.
    desf_unfold_pat.
    { exfalso; eapply Pattern.wf__pv_neq_pe; eauto. }
    now rewrite Hval_to.
  Qed.

  Lemma matches_expansion_of graph mode r r' path v_from e v_to pi pe pv
    (Hg_wf : PropertyGraph.wf graph)
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (Hdom : Path.matches graph r path pi)
    (Hvlabel : forall l : label, Pattern.vlabel pv = Some l -> In l (vlabels graph v_to))
    (Helabel : forall l : label, Pattern.elabel pe = Some l -> elabel graph e = l)
    (Hexp : expansion_of_by_hop' graph r' r mode v_from e v_to pi pe pv) :
      Path.matches graph r' (Path.hop path e v_to) (Pattern.hop pi pe pv).
  Proof.
    apply Path.matches_cons.
    all: unfold expansion_of_by_hop', expansion_of', expansion_of in Hexp.
    all: desf; desf.
    all: try apply Path.matches_exclude.
    all: try apply Path.matches_exclude.
    all: eauto using Path.matches_in_dom_contra.
    all: try apply Path.Build_matches_pedge.
    all: try apply Path.Build_matches_pvertex.
    all: auto.

    all: assert (Path.last path = v_from)
          by (erewrite Path.matches_last in Hval_from; eauto;
            injection Hval_from; trivial).
    all: subst; auto.

    all: desf_unfold_pat.
    all: try (exfalso; eapply Pattern.wf__pv_neq_pe; now eauto).

    all: unfold Path.matches_direction in Hdir.
    all: desf; desf.
    all: edestruct ends_In; eauto.
  Qed.

  Theorem match_clause_spec' graph pi table' r'
    (Hres : eval_match_clause graph pi = Some table')
    (Hg_wf : PropertyGraph.wf graph)
    (Hwf : Pattern.wf pi)
    (HIn : In r' table') :
      exists path, Path.matches graph r' path pi /\
        Rcd.type_of r' = PatternT.type_of pi.
  Proof.
    gen_dep Hres r' table'.
    induction pi; ins.
    all: desf_match_result Hres.
    all: repeat match goal with
         | [H : filter_by_label Vertices _ _ _ _ = _ |- _ ] =>
            eapply filter_vertices_by_label_spec' in H; try eassumption; desf
         | [H : filter_by_label Edges _ _ _ _ = _ |- _ ] =>
            eapply filter_edges_by_label_spec' in H; try eassumption; desf
         end.
    all: try match goal with
          | [H : scan_vertices _ _ = _ |- _ ] =>
             eapply scan_vertices_spec' in H; try eassumption; desf
          end.
    all: repeat match goal with
         | [H : expand _ _ _ _ _ _ _ = _ |- _ ] =>
            eapply expand_spec' in H; try eassumption; desf
         end.
    all: try edestruct IHpi as [path [? ?]];
            eauto with pattern_wf_db.
    all: unfold expansion_of_by_hop, expansion_of in *; desf.
    1-2: eexists (Path.start _); splits.
    5-12: eexists (Path.hop path _ _); splits.

    all: try eapply matches_expansion_of; eauto.
    all: try eapply matches_pattern_type_hop.
    all: try unfold expansion_of_by_hop, expansion_of.
    all: eauto using matches_pattern_type_start'.

    all: try eapply Path.matches_nil, Path.Build_matches_pvertex; eauto.
    all: try rewrite PartialMap.update_eq.
    all: auto.

    all: ins.
    all: try unfold expansion_of' in *; desf.
    all: desf_unfold_pat.
  Qed.
End EvalQueryImpl.
