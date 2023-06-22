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

  Definition translate_props (mode : FilterMode.t) (n : Name.t) props plan :=
    fold_right (fun '(k, v) => FilterByProperty mode n k v) plan props.

  Definition translate_pvertex pv plan : ExecutionPlan.t :=
    let plan := match vlabel pv with
                | Some l => FilterByLabel Vertices (vname pv) l plan
                | None => plan
                end
    in translate_props Vertices (vname pv) (vprops pv) plan.

  Definition translate_pedge pe plan : ExecutionPlan.t :=
    let plan := match elabel pe with
                | Some l => FilterByLabel Edges (ename pe) l plan
                | None => plan
                end
    in translate_props Edges (ename pe) (eprops pe) plan.

  Fixpoint translate_pattern' (pi : Pattern.t) : ExecutionPlan.t :=
    match pi with
    | Pattern.start pv => 
        translate_pvertex pv (ScanVertices (vname pv))
    | Pattern.hop pi pe pv =>
      let mode := 
        if ((PatternT.type_of Full pi (vname pv)) ==b (Some Value.GVertexT))
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

Lemma translate_props_type mode n props plan :
  type_of (translate_props mode n props plan) = type_of plan.
Proof using.
  induction props as [| [k v] props]; simpls.
Qed.

Ltac desf_translate_pvertex_pedge :=
  unfold translate_pvertex, translate_pedge in *;
  desf; simpls;
  normalize_bool.

Lemma translate_pvertex_type pv plan :
  type_of (translate_pvertex pv plan) = type_of plan.
Proof using.
  desf_translate_pvertex_pedge.
  all: now rewrite translate_props_type.
Qed.

Lemma translate_pedge_type pe plan :
  type_of (translate_pedge pe plan) = type_of plan.
Proof using.
  desf_translate_pvertex_pedge.
  all: now rewrite translate_props_type.
Qed.

Theorem translate_pattern'_type pi (Hwf : PatternT.wfT pi) :
  type_of (translate_pattern' pi) = PatternT.type_of Full pi.
Proof using.
  all: induction pi; simpls.
  all: rewrite translate_pvertex_type.
  all: try rewrite translate_pedge_type.
  { reflexivity. }
  inv Hwf. desf.
  all: unfold_update_with_mode; simpl.
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

Lemma translate_props_wf mode n props plan
  (Htype : match mode with
           | Vertices => type_of plan n = Some Value.GVertexT
           | Edges => type_of plan n = Some Value.GEdgeT
           end)
  (Hwf : ExecutionPlan.wf plan) :
    ExecutionPlan.wf (translate_props mode n props plan).
Proof using.
  destruct mode.
  all: induction props as [| [k v] props]; simpls.
  all: unnw; intuition.
  all: now rewrite translate_props_type.
Qed.

Lemma translate_pvertex_wf pv plan
  (Htype : type_of plan (Pattern.vname pv) = Some Value.GVertexT)
  (Hwf : ExecutionPlan.wf plan) :
    ExecutionPlan.wf (translate_pvertex pv plan).
Proof using.
  unfold translate_pvertex; desf.
  all: apply translate_props_wf; simpls.
Qed.

Lemma translate_pedge_wf pe plan
  (Htype : type_of plan (Pattern.ename pe) = Some Value.GEdgeT)
  (Hwf : ExecutionPlan.wf plan) :
    ExecutionPlan.wf (translate_pedge pe plan).
Proof using.
  unfold translate_pedge; desf.
  all: apply translate_props_wf; simpls.
Qed.

Theorem translate_pattern'_wf pi (Hwf : PatternT.wfT pi) :
  ExecutionPlan.wf (translate_pattern' pi).
Proof using.
  induction pi; simpls.
  { apply translate_pvertex_wf; simpls.
    apply PartialMap.update_eq. }
  inv Hwf.
  apply translate_pvertex_wf.
  { rewrite translate_pedge_type.
    case equiv_decbP; intros Heq; simpls.
    all: rewrite translate_pattern'_type by assumption.
    all: apply PartialMap.update_eq. }
  apply translate_pedge_wf.
  { simpls. rewrite PartialMap.update_neq by assumption.
    now rewrite PartialMap.update_eq. }
  simpls.
  case equiv_decbP; intros Heq; unnw.
  all: rewrite translate_pattern'_type by assumption.
  all: splits; auto.
  all: try apply PatternT.last__dom_vertices.
  all: try now (intros contra; eapply PatternT.last_neq_pe; eauto).
  desf.
Qed.

Theorem translate_pattern_wf pi (Hwf : PatternT.wfT pi) :
  ExecutionPlan.wf (translate_pattern pi).
Proof using.
  unfold translate_pattern. simpls.
  now apply translate_pattern'_wf.
Qed.

Module EvalPvertexPedge (S : ExecutionPlan.Spec).
  Module EvalPlanImpl := EvalPlan S.
  Import S.
  Import EvalPlanImpl.

  Lemma eval_translate_props_reduce graph mode n props plan table'
    (Hres : eval graph (translate_props mode n props plan) = Some table') :
      exists table, eval graph plan = Some table.
  Proof using.
    gen_dep table'.
    induction props as [| [k v] props]; intros.
    { eauto 2. }
    simpl in Hres.
    eval_operation_reduce in Hres.
    eauto using IHprops.
  Qed.

  Lemma eval_translate_pvertex_reduce graph pv plan table'
    (Hres : eval graph (translate_pvertex pv plan) = Some table') :
      exists table, eval graph plan = Some table.
  Proof.
    unfold translate_pvertex in *.
    apply eval_translate_props_reduce in Hres as [table'' Hres].
    desf; simpls.
    1: eval_operation_reduce in Hres.
    all: eauto 2.
  Qed.

  Lemma eval_translate_pedge_reduce graph pe plan table'
    (Hres : eval graph (translate_pedge pe plan) = Some table') :
      exists table, eval graph plan = Some table.
  Proof.
    unfold translate_pedge in *.
    apply eval_translate_props_reduce in Hres as [table'' Hres].
    desf; simpls.
    1: eval_operation_reduce in Hres.
    all: eauto 2.
  Qed.


  Lemma eval_translate_props_spec graph mode n props plan table table' r
    (Hres : eval graph plan = Some table)
    (Hres' : eval graph (translate_props mode n props plan) = Some table')
    (HIn : In r table)
    (H : match mode with
         | Vertices => exists v,
             << Hval : r n = Some (Value.GVertex v) >> /\
             << Hprops : Forall (fun '(k, val) => get_vprop graph k v = Some val) props >>
         | Edges => exists e,
             << Hval : r n = Some (Value.GEdge e) >> /\
             << Hprops : Forall (fun '(k, val) => get_eprop graph k e = Some val) props >>
         end) :
      In r table'.
  Proof using.
    gen_dep table'.
    induction props as [| [k val] props]; ins.
    { congruence. }

    destruct mode; desc.
    all: assert (Hprop := Hprops).
    all: apply Forall_inv in Hprop.
    all: apply Forall_inv_tail in Hprops.

    all: eval_operation_reduce in Hres'.
    { eauto using filter_vertices_by_property_spec. }
    { eauto using filter_edges_by_property_spec. }
  Qed.

  Lemma eval_translate_pvertex_spec graph pv plan table table' r v
    (Hres : eval graph plan = Some table)
    (Hres' : eval graph (translate_pvertex pv plan) = Some table')
    (HIn : In r table)
    (Hval : r (Pattern.vname pv) = Some (Value.GVertex v))
    (Hprops : Forall (fun '(k, val) => get_vprop graph k v = Some val)
                     (Pattern.vprops pv))
    (Hlabel : match Pattern.vlabel pv with
              | Some l => In l (vlabels graph v)
              | None => True
              end) :
      In r table'.
  Proof.
    unfold translate_pvertex in *. simpls.
    assert (Hres_filter := Hres').
    apply eval_translate_props_reduce in Hres_filter as [table'' Hres_filter].
    eapply eval_translate_props_spec; eauto.
    2: { simpl. eauto. }

    destruct (Pattern.vlabel pv).
    2: { congruence. }

    simpl in Hres_filter.
    eval_operation_reduce in Hres_filter.
    eapply filter_vertices_by_label_spec; eauto.
    assert (table = table0) by congruence.
    now subst.
  Qed.

  Lemma eval_translate_pedge_spec graph pe plan table table' r e
    (Hres : eval graph plan = Some table)
    (Hres' : eval graph (translate_pedge pe plan) = Some table')
    (HIn : In r table)
    (Hval : r (Pattern.ename pe) = Some (Value.GEdge e))
    (Hprops : Forall (fun '(k, val) => get_eprop graph k e = Some val)
                     (Pattern.eprops pe))
    (Hlabel : match Pattern.elabel pe with
              | Some l => elabel graph e = l
              | None => True
              end) :
      In r table'.
  Proof.
    unfold translate_pedge in *. simpls.
    assert (Hres_filter := Hres').
    apply eval_translate_props_reduce in Hres_filter as [table'' Hres_filter].
    eapply eval_translate_props_spec; eauto.
    2: { simpl. eauto. }

    destruct (Pattern.elabel pe).
    2: { congruence. }

    simpl in Hres_filter.
    eval_operation_reduce in Hres_filter.
    eapply filter_edges_by_label_spec; eauto.
    assert (table = table0) by congruence.
    now subst.
  Qed.


  Lemma eval_translate_props_spec' graph mode n props plan table table' r
    (Hres : eval graph plan = Some table)
    (Hres' : eval graph (translate_props mode n props plan) = Some table')
    (HIn : In r table') :
      In r table /\ (props = [] \/
        match mode with
        | Vertices => exists v,
            << Hval : r n = Some (Value.GVertex v) >> /\
            << Hprops : Forall (fun '(k, val) => get_vprop graph k v = Some val) props >>
        | Edges => exists e,
            << Hval : r n = Some (Value.GEdge e) >> /\
            << Hprops : Forall (fun '(k, val) => get_eprop graph k e = Some val) props >>
        end).
  Proof.
    gen_dep table'.
    induction props as [| [k val] props]; ins.
    { split.
      { congruence. }
      now left. }
    eval_operation_reduce in Hres' eqn:Hres_filter.
    destruct mode;
    [ eapply filter_vertices_by_property_spec' in Hres_filter |
      eapply filter_edges_by_property_spec' in Hres_filter ]; eauto.
    all: desc; unnw.
    all: edestruct IHprops; eauto 1; desf.
    all: eauto 10 using Forall_cons.
  Qed.

  Lemma eval_translate_pvertex_spec' graph pv plan table table' r
    (Hres : eval graph plan = Some table)
    (Hres' : eval graph (translate_pvertex pv plan) = Some table')
    (HIn : In r table') :
      << HIn : In r table >> /\
      forall v, r (Pattern.vname pv) = Some (Value.GVertex v) ->
        << Hlabel : match Pattern.vlabel pv with
                    | Some l => In l (vlabels graph v)
                    | None => True
                    end >> /\
        << Hprops : Forall (fun '(k, val) => get_vprop graph k v = Some val)
                          (Pattern.vprops pv) >>.
  Proof.
    unfold translate_pvertex in *.
    assert (Hres'' := Hres').
    eapply eval_translate_props_reduce in Hres'' as [table'' Hres'']; eauto.
    eapply eval_translate_props_spec' in Hres'; eauto.
    all: desf; simpls.
    all: try eval_operation_reduce in Hres'' eqn:Hres_filter.
    all: try (eapply filter_vertices_by_label_spec' in Hres_filter; eauto).
    all: desf; unnw; intuition.
    all: try assert (v = v0) by congruence; subst.
    all: auto.
    all: now rewrite Hres'0.
  Qed.

  Lemma eval_translate_pedge_spec' graph pe plan table table' r
    (Hres : eval graph plan = Some table)
    (Hres' : eval graph (translate_pedge pe plan) = Some table')
    (HIn : In r table') :
      << HIn : In r table >> /\
      forall e, r (Pattern.ename pe) = Some (Value.GEdge e) ->
        << Hlabel : match Pattern.elabel pe with
                    | Some l => elabel graph e = l
                    | None => True
                    end >> /\
        << Hprops : Forall (fun '(k, val) => get_eprop graph k e = Some val)
                          (Pattern.eprops pe) >>.
  Proof.
    unfold translate_pedge in *.
    assert (Hres'' := Hres').
    eapply eval_translate_props_reduce in Hres'' as [table'' Hres'']; eauto.
    eapply eval_translate_props_spec' in Hres'; eauto.
    all: desf; simpls.
    all: try eval_operation_reduce in Hres'' eqn:Hres_filter.
    all: try (eapply filter_edges_by_label_spec' in Hres_filter; eauto).
    all: desf; unnw; intuition.
    all: try assert (e = e0) by congruence; subst.
    all: auto.
    all: now rewrite Hres'0.
  Qed.
End EvalPvertexPedge.

Module EvalQueryImpl (S : ExecutionPlan.Spec) : EvalQuery.Spec.
  Module EvalPvertexPedgeImpl := EvalPvertexPedge S.
  Import S.
  Import EvalPvertexPedgeImpl.
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
    { now rewrite translate_pattern_type in Hres. }
    auto using translate_pattern_wf.
  Qed.

  Theorem eval_translate_pattern'_reduce graph pi pe pv table'
    (Hres : eval graph (translate_pattern' (Pattern.hop pi pe pv)) = Some table') :
      exists table, eval graph (translate_pattern' pi) = Some table.
  Proof using.
    simpls.
    apply eval_translate_pvertex_reduce in Hres as [table'' Hres].
    apply eval_translate_pedge_reduce in Hres as [table Hres].
    simpls. eval_operation_reduce in Hres. eauto 2.
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

    all: assert (Hres' := Hres).
    all: apply eval_translate_pvertex_reduce in Hres' as [table Hres'].
    all: eapply eval_translate_pvertex_spec; eauto.
    all: try apply PartialMap.update_eq.
    all: try now (desf; auto).
    { eauto using scan_vertices_spec. }

    assert (Hres'' := Hres').
    apply eval_translate_pedge_reduce in Hres'' as [table'' Hres''].

    eapply eval_translate_pedge_spec; eauto.
    2: { unfold update_with_mode_hop.
         rewrite PartialMap.update_neq by assumption.
         apply PartialMap.update_eq. }
    2: { desf; auto. }

    simpl in Hres''.
    eval_operation_reduce in Hres'' eqn:Hres_expand.
    eapply expand_spec; eauto.

    case equiv_decbP; intros Heq.
    1: eapply matches_hop_Into in Hmatch; eauto.
    2: eapply matches_hop_All in Hmatch; eauto.
    3: now desf.

    all: desc; unfold expansion_of_by_hop in *.
    all: assert (r = r0) by eauto using Path.matches_two_records.
    all: now subst.
  Qed.

  Theorem match_clause_spec graph path pi table' r'
    (Hres : eval_match_clause graph pi = Some table')
    (Hg_wf : PropertyGraph.wf graph)
    (Hwf : PatternT.wfT pi)
    (Hmatch : Path.matches Explicit graph r' path pi) :
      In r' table'.
  Proof using.
    unfold eval_match_clause, translate_pattern in *; simpls.
    eval_operation_reduce in Hres eqn:Hres_return.
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
    (Hvprops : Forall (fun '(k, val) => get_vprop graph k v_to = Some val) (Pattern.vprops pv))
    (Heprops : Forall (fun '(k, val) => get_eprop graph k e = Some val) (Pattern.eprops pe))
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
    
    all: assert (Hres' := Hres).
    all: apply eval_translate_pvertex_reduce in Hres' as [table'' Hres'].
    all: eapply eval_translate_pvertex_spec' in Hres; eauto.
    all: desc.
    
    { eapply scan_vertices_spec' in Hres'.
      2: eassumption.
      desc. subst.
      edestruct Hres0.
      { apply PartialMap.update_eq. }
      exists (Path.start v).
      lift_to_update_with_mode.
      do 2 constructor; auto.
      ins. desf. }

    assert (Hres'' := Hres').
    eapply eval_translate_pedge_reduce in Hres'' as [table''' Hres''].
    eapply eval_translate_pedge_spec' in Hres'; eauto; desc.
    simpl in Hres''.
    eval_operation_reduce in Hres'' eqn:Hres_expand.
    eapply expand_spec' in Hres_expand; eauto; desc.
    unfold expansion_of_by_hop, expansion_of, expansion_of' in *; desc.

    edestruct IHpi with (table' := table) as [p IH]; eauto.
    exists (Path.hop p e v_to).

    erewrite Path.matches_full_last in Hval_from by eauto.
    injection Hval_from as Hval_from; subst.

    specialize (Hres0 v_to). specialize (Hres'0 e).
    destruct Hres0.
    { apply PartialMap.update_eq. }
    destruct Hres'0.
    { rewrite PartialMap.update_neq by auto.
      apply PartialMap.update_eq. }
    unnw.

    lift_to_update_with_mode.
    constructor; auto.
    1-2: constructor; auto.
    all: try now (intros ? ?; desf).
    { unfold Path.matches_direction in *.
      destruct (Pattern.edir pe).
      3: destruct Hdir.
      all: edestruct ends_In; eauto. }
    
    destruct (equiv_decbP (PatternT.type_of Full pi (Pattern.vname pv))
                          (Some Value.GVertexT)); auto.
  Qed.

  Theorem match_clause_spec' graph pi table' r'
    (Hres : eval_match_clause graph pi = Some table')
    (Hg_wf : PropertyGraph.wf graph)
    (Hwf : PatternT.wfT pi)
    (HIn : In r' table') :
      exists path, Path.matches Explicit graph r' path pi.
  Proof using.
    unfold eval_match_clause, translate_pattern in *; simpls.
    eval_operation_reduce in Hres eqn:Hres_return.
    eapply return_all_spec' in HIn; eauto; desf.
    edestruct eval_translate_pattern'_spec'; eauto.
    eexists.
    eapply Path.matches_explicit_proj; eauto.
  Qed.
End EvalQueryImpl.
