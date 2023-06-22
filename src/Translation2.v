Require Import Utils.
Require Import Maps.
Require Import PropertyGraph.
Require Import Cypher.
Require Import BindingTable.
Require Import Semantics.
Require Import PatternE.
Require Import ExecutionPlan.
Require Import Translation.

Import PartialMap.Notations.
Import TotalMap.Notations.
Import PropertyGraph.
Import ExecutionPlan.
Import FilterMode.
Import ExpandMode.
Import MatchMode.
Import UpdateNotations.

Definition translate_start (pv : Pattern.pvertex) : ExecutionPlan.t :=
  translate_pvertex pv (ScanVertices (Pattern.vname pv)).

Definition translate_pattern' (pi : Pattern.t) : ExecutionPlan.t :=
  let pis' := PatternSlice.split_all_with_paths pi in
  let pv := Pattern.first pi in
  let start := translate_start pv in
  let f '(pi', pi0) :=
    Traverse pi' (Pattern.vname (Pattern.last pi0))
  in fold_right f start pis'.

Definition translate_pattern (pi : Pattern.t) : ExecutionPlan.t :=
  ReturnAll (translate_pattern' pi).

Theorem translate_pattern'_ind
  (P : Pattern.t -> ExecutionPlan.t -> Prop)
  (Hstart : forall pv, P (Pattern.start pv) (translate_start pv))
  (Htraverse : forall pi pi' pi0,
    PatternSlice.split pi = (pi0, pi') ->
    pi' <> PatternSlice.empty ->
    P pi0 (translate_pattern' pi0) ->
    P pi (Traverse pi' (Pattern.vname (Pattern.last pi0)) (translate_pattern' pi0))) :
  forall pi, P pi (translate_pattern' pi).
Proof using.
  intros pi.
  unfold translate_pattern'.
  pattern pi, (PatternSlice.split_all_with_paths pi).
  apply PatternSlice.split_all_with_paths_ind; ins.
  erewrite <- PatternSlice.split_first; eauto.
Qed.

Theorem translate_start_type pv :
  type_of (translate_start pv) =
    PatternT.type_of Mixed (Pattern.start pv).
Proof using.
  unfold translate_start.
  now rewrite translate_pvertex_type.
Qed.

Theorem translate_pattern'_type pi (Hwf : PatternT.wfT pi) :
  type_of (translate_pattern' pi) = PatternT.type_of Mixed pi.
Proof using.
  pattern pi, (translate_pattern' pi).
  apply translate_pattern'_ind; ins.
  { apply translate_start_type. }

  erewrite <- PatternSlice.split_type_of; eauto.
  now f_equal.
Qed.

Theorem translate_pattern_type pi (Hwf : PatternT.wfT pi) :
  type_of (translate_pattern pi) = PatternT.type_of Explicit pi.
Proof using.
  unfold translate_pattern. simpls.
  rewrite translate_pattern'_type; auto.
  now rewrite PatternT.explicit_projT_type_of.
Qed.

Theorem translate_start_wf pv :
  ExecutionPlan.wf (translate_start pv).
Proof using.
  unfold translate_start.
  apply translate_pvertex_wf; simpls.
  apply PartialMap.update_eq.
Qed.

Theorem translate_pattern'_wf pi (Hwf : PatternT.wfT pi) :
  ExecutionPlan.wf (translate_pattern' pi).
Proof using.
  gen_dep Hwf.
  pattern pi, (translate_pattern' pi).
  apply translate_pattern'_ind; ins.
  { apply translate_start_wf. }

  erewrite translate_pattern'_type; eauto.
  all: splits.
  all: eauto using PatternSlice.split_type_of_last,
                   PatternSlice.split_wf_slice,
                   PatternSlice.split_wf_pattern.
Qed.

Theorem translate_pattern_wf pi (Hwf : PatternT.wfT pi) :
  ExecutionPlan.wf (translate_pattern pi).
Proof using.
  unfold translate_pattern. simpls.
  now apply translate_pattern'_wf.
Qed.

(* Theorem translate_pattern'_wf_slice  *)

Module EvalQueryImpl2 (S : ExecutionPlan.Spec) : EvalQuery.Spec.
  Module EvalPvertexPedgeImpl := EvalPvertexPedge S.
  Import S.
  Import EvalPvertexPedgeImpl.
  Import EvalPlanImpl.

  Definition eval_match_clause (graph : PropertyGraph.t) (pi : Pattern.t) : option BindingTable.t :=
    let plan := translate_pattern pi in
      EvalPlanImpl.eval graph plan.
    
  Ltac desf_match_result Hres :=
    unfold eval_match_clause in Hres; simpl in Hres; cbn in Hres;
    unfold translate_start in Hres;
    desf; simpls;
    unfold option_bind in *; desf.
  
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

  Lemma eval_translate_pattern'_spec graph path pi table' r'
    (Hres : eval graph (translate_pattern' pi) = Some table')
    (Hwf_G : PropertyGraph.wf graph)
    (Hwf : PatternT.wfT pi)
    (Hmatch : Path.matches Mixed graph r' path pi) :
      In r' table'.
  Proof using.
    gen_dep Hres r' table' path Hwf.
    pattern pi, (translate_pattern' pi).
    apply translate_pattern'_ind; ins.
    { inv Hmatch. destruct Hpv.
      desf_match_result Hres.
      assert (Hres' := Hres).
      apply eval_translate_pvertex_reduce in Hres as [table Hres].
      eapply eval_translate_pvertex_spec in Hres'; eauto.
      { simpls. eauto using scan_vertices_spec. }
      { apply PartialMap.update_eq. }
      { desf; auto. } }
    
    desf_match_result Hres.
    eapply PathSlice.matches_split_inv in Hmatch; eauto.
    desf.

    eapply traverse_spec; eauto.
    2: now eauto using PatternSlice.split_wf_pattern.
    erewrite <- Path.matches_type_of; eauto 1.
    eauto using PatternSlice.split_wf_slice.
  Qed.

  Theorem match_clause_spec graph path pi table' r'
    (Hres : eval_match_clause graph pi = Some table')
    (Hwf_G : PropertyGraph.wf graph)
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

  Lemma eval_translate_pattern'_spec' graph pi table' r'
    (Hres : eval graph (translate_pattern' pi) = Some table')
    (Hg_wf : PropertyGraph.wf graph)
    (Hwf : PatternT.wfT pi)
    (HIn : In r' table') :
      exists path, Path.matches Mixed graph r' path pi.
  Proof using.
    gen_dep Hres r' table' Hwf.
    pattern pi, (translate_pattern' pi).
    apply translate_pattern'_ind; ins.
    { desf_match_result Hres.
      assert (Hres' := Hres).
      apply eval_translate_pvertex_reduce in Hres as [table Hres].
      eapply eval_translate_pvertex_spec' in Hres'; eauto; desc.
      eapply scan_vertices_spec' in Hres; eauto; desc.

      specialize (Hres'0 v). subst.
      destruct Hres'0; unnw.
      { apply PartialMap.update_eq. }
      
      eexists (Path.start _).
      change (?x |-> ?v) with (x M|-> v).
      econstructor; constructor; auto.
      ins; desf. }

    desf_match_result Hres.
    eapply traverse_spec' in HIn; eauto.
    desf.

    { edestruct H1; eauto.
      { eauto using PatternSlice.split_wf_pattern. }
      eexists (PathSlice.append _ _).
      eapply PathSlice.matches_split; eauto. }
    { eauto using eval_type_of, translate_pattern'_wf,
        PatternSlice.split_wf_pattern. }
    erewrite translate_pattern'_type.
    { eauto using PatternSlice.split_wf_slice. }
    eauto using PatternSlice.split_wf_pattern.
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
End EvalQueryImpl2.
