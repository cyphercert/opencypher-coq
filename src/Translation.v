Require Import Utils.
Require Import Maps.
Require Import PropertyGraph.
Require Import Cypher.
Require Import BindingTable.
Require Import Semantics.
Require Import ExecutionPlan.

Import PartialMap.Notations.
Import TotalMap.Notations.
Import PropertyGraph.
Import ExecutionPlan.
Import FilterMode.
Import ExpandMode.
Import MatchMode.
Import UpdateNotations.

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

  Fixpoint translate_pattern' (pi : Pattern.t) : ExecutionPlan.t :=
    match pi with
    | Pattern.start pv => 
        translate_pvertex pv (ScanVertices (vname pv))
    | Pattern.hop pi pe pv =>
      let mode := 
        if ((PatternT.type_of Full pi (vname pv)) == (Some Value.GVertexT))
        then Into else All
      in
      let plan := translate_pattern' pi in
      let plan :=
        Expand mode (vname (last pi)) (ename pe) (vname pv)
               (edir pe) plan
      in translate_pvertex pv (translate_pedge pe plan)
    end.

  Definition translate_pattern (pi : Pattern.t) : ExecutionPlan.t :=
    ReturnAll (translate_pattern' pi).
End translate_pattern.

Ltac desf_translate_pvertex_pedge :=
  unfold translate_pvertex, translate_pedge in *;
  desf; simpls;
  normalize_bool.

Lemma translate_pvertex_type pv plan :
  type_of (translate_pvertex pv plan) = type_of plan.
Proof using. desf_translate_pvertex_pedge. Qed.

Lemma translate_pedge_type pe plan :
  type_of (translate_pedge pe plan) = type_of plan.
Proof using. desf_translate_pvertex_pedge. Qed.

Theorem translate_pattern'_type pi (Hwf : PatternT.wfT pi) :
  type_of (translate_pattern' pi) = PatternT.type_of Full pi.
Proof using.
  all: induction pi; simpls.
  all: rewrite translate_pvertex_type.
  all: try rewrite translate_pedge_type.
  { reflexivity. }
  inv Hwf. desf.
  all: simpl.
  all: repeat f_equal.
  all: auto.
Qed.

Theorem translate_pattern_type pi (Hwf : PatternT.wfT pi) :
  type_of (translate_pattern pi) = PatternT.type_of Explicit pi.
Proof using.
  unfold translate_pattern. simpls.
  rewrite translate_pattern'_type; auto.
  now rewrite PatternT.explicit_projT_type_of.
Qed.

Theorem translate_pattern'_wf pi (Hwf : PatternT.wfT pi) :
  ExecutionPlan.wf (translate_pattern' pi).
Proof using.
  induction pi; simpls.
  all: inv Hwf.
  all: unfold translate_pvertex, translate_pedge.
  all: desf; simpls; splits; auto.
  all: normalize_bool.
  all: desf_unfold_pat.
  all: try contradiction.
  all: try congruence.
  all: try rewrite translate_pattern'_type; auto.
  all: try apply PatternT.last__dom_vertices.
  all: intros contra; eapply PatternT.last_neq_pe; eauto.
Qed.

Theorem translate_pattern_wf pi (Hwf : PatternT.wfT pi) :
  ExecutionPlan.wf (translate_pattern pi).
Proof using.
  unfold translate_pattern. simpls.
  now apply translate_pattern'_wf.
Qed.

Module EvalQueryImpl (S : ExecutionPlan.Spec) : EvalQuery.Spec.
  Module EvalPlanImpl := EvalPlan S.
  Import S.
  Import EvalPlanImpl.

  Definition eval_match_clause (graph : PropertyGraph.t) (pi : Pattern.t) : option BindingTable.t :=
    let plan := translate_pattern pi in
      EvalPlanImpl.eval graph plan.
  
  Theorem match_clause_wf graph pi
    (Hwf_g : PropertyGraph.wf graph) (Hwf : PatternT.wfT pi) :
      exists table', eval_match_clause graph pi = Some table'.
  Proof using.
    eapply eval_wf; eauto.
    now apply translate_pattern_wf.
  Qed.

  Theorem match_clause_type graph pi table'
    (Hres : eval_match_clause graph pi = Some table')
    (Hwf : PatternT.wfT pi) :
      BindingTable.of_type table' (PatternT.type_of Explicit pi).
  Proof using.
    unfold eval_match_clause in Hres.
    apply eval_type_of in Hres.
    now rewrite translate_pattern_type in Hres.
  Qed.

  Ltac desf_match_result Hres :=
    unfold eval_match_clause in Hres; simpls;
    desf_translate_pvertex_pedge;
    unfold option_bind in *; desf.

  Theorem eval_translate_pattern'_reduce graph pi pe pv table'
    (Hres : eval graph (translate_pattern' (Pattern.hop pi pe pv)) = Some table') :
      exists table, eval graph (translate_pattern' pi) = Some table.
  Proof using.
    desf_match_result Hres.
    all: eauto.
  Qed.

  Definition expansion_of_by_hop' graph r' r mode v_from e v_to pi pe pv :=
    expansion_of' graph r' r mode v_from e v_to
      (Pattern.vname (Pattern.last pi)) (Pattern.ename pe) (Pattern.vname pv) (Pattern.edir pe).

  Definition expansion_of_by_hop graph r' r mode pi pe pv :=
    expansion_of graph r' r mode
      (Pattern.vname (Pattern.last pi)) (Pattern.ename pe) (Pattern.vname pv) (Pattern.edir pe).

  Lemma matches_hop_All graph path e v pi pe pv r'
    (Hwf : PatternT.wfT (Pattern.hop pi pe pv))
    (Hmatch : Path.matches Full graph r' (Path.hop path e v) (Pattern.hop pi pe pv))
    (HIn : PatternT.type_of Full pi (Pattern.vname pv) = None) :
      exists r, << Hexp : expansion_of_by_hop graph r' r All pi pe pv >> /\
                << Hmatch' : Path.matches Full graph r path pi >>.
  Proof using.
    inv Hmatch. inv Hwf.
    exists r.
    destruct Hpe, Hpv.
    unfold update_with_mode_hop, update_with_mode_start in *.
    unfold expansion_of_by_hop, expansion_of, expansion_of'.
    splits; auto.
    do 3 eexists. splits; eauto.
    { eauto using Path.matches_full_last. }
    all: erewrite <- Path.matches_not_in_dom_iff; eauto.
  Qed.

  Lemma matches_hop_Into graph path e v pi pe pv r'
    (Hwf : PatternT.wfT (Pattern.hop pi pe pv))
    (Hmatch : Path.matches Full graph r' (Path.hop path e v) (Pattern.hop pi pe pv))
    (HIn : PatternT.type_of Full pi (Pattern.vname pv) = Some Value.GVertexT) :
      exists r, << Hexp : expansion_of_by_hop graph r' r Into pi pe pv >> /\
                << Hmatch' : Path.matches Full graph r path pi >>.
  Proof using.
    inv Hmatch. inv Hwf.
    exists r.
    desf.
    { eapply Path.matches_in_dom_vertex with (r' := r) in Htype_pv;
        eauto; desf. }
    destruct Hpe, Hpv.
    unfold update_with_mode_hop, update_with_mode_start in *.
    unfold expansion_of_by_hop, expansion_of, expansion_of'.
    splits; auto.
    do 3 eexists. splits; eauto.
    { eauto using Path.matches_full_last. }
    { erewrite <- Path.matches_not_in_dom_iff; eauto. }
  Qed.

  Lemma eval_translate_pattern'_spec graph path pi table' r'
    (Hres : eval graph (translate_pattern' pi) = Some table')
    (Hwf : PatternT.wfT pi)
    (Hmatch : Path.matches Full graph r' path pi) :
      In r' table'.
  Proof using.
    gen_dep Hres r' table' path.
    induction pi; ins.
    all: inv Hwf.
    all: destruct path; inv Hmatch.
    all: destruct Hpv.
    all: try destruct Hpe.

    { all: desf_match_result Hres.
      1: eapply filter_vertices_by_label_spec; eauto.
      { apply PartialMap.update_eq. }
      all: eauto using scan_vertices_spec. }

    desf; simpls.

    all: desf_match_result Hres.
    
    all: repeat match goal with
         | [H : filter_by_label Vertices _ _ _ _ = _ |- _ ] =>
            eapply filter_vertices_by_label_spec; eauto; clear H
         | [H : filter_by_label Edges _ _ _ _ = _ |- _ ] =>
            eapply filter_edges_by_label_spec; eauto; clear H
         end.

    all: try apply PartialMap.update_eq.
    all: try (rewrite PartialMap.update_neq; auto).
    all: try apply PartialMap.update_eq.
    
    all: match goal with 
         | [H : expand Into _ _ _ _ _ _ = _ |- _ ] =>
            apply matches_hop_Into in Hmatch; eauto
         | [H : expand All _ _ _ _ _ _ = _ |- _ ] =>
            apply matches_hop_All in Hmatch; eauto
         end.
    all: desf.
    all: eapply expand_spec; eauto.
  Qed.

  Theorem match_clause_spec graph path pi table' r'
    (Hres : eval_match_clause graph pi = Some table')
    (Hg_wf : PropertyGraph.wf graph)
    (Hwf : PatternT.wfT pi)
    (Hmatch : Path.matches Explicit graph r' path pi) :
      In r' table'.
  Proof using.
    desf_match_result Hres.
    assert (Hmatch' := Hmatch).
    eapply Path.matches_explicit_exists_proj in Hmatch' as [r ?]; auto.
    erewrite Path.matches_both_modes with (r := r'); eauto.
    eapply return_all_spec; eauto.
    eapply eval_translate_pattern'_spec; eauto.
  Qed.

  Lemma matches_expansion_of graph mode r r' path v_from e v_to pi pe pv
    (Hg_wf : PropertyGraph.wf graph)
    (Hwf : PatternT.wfT (Pattern.hop pi pe pv))
    (Hdom : Path.matches Full graph r path pi)
    (Hvlabel : forall l : label, Pattern.vlabel pv = Some l -> In l (vlabels graph v_to))
    (Helabel : forall l : label, Pattern.elabel pe = Some l -> elabel graph e = l)
    (Hexp : expansion_of_by_hop' graph r' r mode v_from e v_to pi pe pv) :
      Path.matches Full graph r' (Path.hop path e v_to) (Pattern.hop pi pe pv).
  Proof using.
    inv Hwf.
    unfold expansion_of_by_hop', expansion_of', expansion_of in Hexp.
    desf; desf.
    all: lift_to_update_with_mode.
    all: apply Path.matches_cons; simpls; auto.
    all: try constructor; auto.

    all: assert (Path.last path = v_from)
          by (erewrite Path.matches_full_last in Hval_from; eauto;
            injection Hval_from; trivial).
    all: subst; auto.

    all: unfold Path.matches_direction in Hdir.
    all: desf; desf.
    all: edestruct ends_In; eauto.
  Qed.

  Lemma eval_translate_pattern'_spec' graph pi table' r'
    (Hres : eval graph (translate_pattern' pi) = Some table')
    (Hg_wf : PropertyGraph.wf graph)
    (Hwf : PatternT.wfT pi)
    (HIn : In r' table') :
      exists path, Path.matches Full graph r' path pi.
  Proof using.
    gen_dep Hres r' table'.
    induction pi; ins.
    all: inv Hwf.
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
    all: try edestruct IHpi as [path ?]; eauto.

    all: unfold expansion_of_by_hop, expansion_of in *; desf.
    1-2: eexists (Path.start _).
    all: try eexists (Path.hop path _ _).

    1-2: lift_to_update_with_mode.
    1-2: do 2 constructor; auto.

    all: try eapply matches_expansion_of; eauto.
    all: try unfold expansion_of_by_hop, expansion_of, expansion_of' in *.
    all: ins; desf_unfold_pat.
  Qed.

  Theorem match_clause_spec' graph pi table' r'
    (Hres : eval_match_clause graph pi = Some table')
    (Hg_wf : PropertyGraph.wf graph)
    (Hwf : PatternT.wfT pi)
    (HIn : In r' table') :
      exists path, Path.matches Explicit graph r' path pi.
  Proof using.
    desf_match_result Hres.
    eapply return_all_spec' in HIn; eauto; desf.
    edestruct eval_translate_pattern'_spec'; eauto.
    eexists.
    eapply Path.matches_explicit_proj; eauto.
  Qed.
End EvalQueryImpl.
