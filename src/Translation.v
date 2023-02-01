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

Ltac desf_translate_pvertex_pedge :=
  unfold translate_pvertex, translate_pedge in *;
  desf; simpls;
  normalize_bool.

Theorem translate_pattern__type_of pi n (Hwf : Pattern.wf pi) :
  (In n (Pattern.dom_edges pi) <-> type_of (translate_pattern pi) n = Some Value.GEdgeT) /\
  (In n (Pattern.dom_vertices pi) <-> type_of (translate_pattern pi) n = Some Value.GVertexT).
Proof.
  all: induction pi; simpls.
  all: unfold Pattern.wf in *.

  { do 2 split; ins; desf; simpls.
    all: desf_translate_pvertex_pedge.
    all: desf_unfold_pat.
    all: Pattern.solve_wf_contra. }

  split.
  all: desf_translate_pvertex_pedge.
  all: split; ins; desf.

  all: try now apply update_eq.
  all: try rewrite update_neq.
  all: try now apply update_eq.
  all: try rewrite update_neq.
  all: try (apply IHpi; [ split | ]; now eauto with pattern_wf_db).

  all: try now (intros ?; subst; Pattern.solve_wf_contra).

  all: desf_unfold_pat.
  all: try now (left; eauto with pattern_wf_db).
  all: right; apply IHpi; [ split | ]; now eauto with pattern_wf_db.
Qed.

Corollary translate_pattern__type_of_GVertexT pi n (Hwf : Pattern.wf pi) :
  (In n (Pattern.dom_vertices pi) <-> type_of (translate_pattern pi) n = Some Value.GVertexT).
Proof. edestruct translate_pattern__type_of; eassumption. Qed.

Corollary translate_pattern__type_of_GEdgeT pi n (Hwf : Pattern.wf pi) :
  (In n (Pattern.dom_edges pi) <-> type_of (translate_pattern pi) n = Some Value.GEdgeT).
Proof. edestruct translate_pattern__type_of; eassumption. Qed.

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

  all: autounfold with unfold_pat in *.
  all: desf.
  all: unfold complement, equiv in *.
  all: try contradiction.
  all: try apply translate_pattern__type_of_GVertexT; try assumption.
  all: Pattern.solve_wf_contra.
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

  Theorem match_clause_dom graph pi table' r'
    (Hres : eval_match_clause graph pi = Some table')
    (HIn : In r' table') :
      Rcd.matches_pattern_dom r' pi.
  Proof.
    intros k.
    unfold eval_match_clause in Hres.
    rewrite Rcd.in_dom_iff, Pattern.In_dom.
    erewrite match_clause_type_of; try eassumption.
    clear Hres HIn.
    split.

    { intros [x Htype].
      edestruct translate_pattern__type_of__types as [H | [H | H]].
      all: erewrite H in Htype.
      all: inv H.
      all: induction pi; simpls.

      all: desf_translate_pvertex_pedge.
      all: desf_unfold_pat.

      all: destruct IHpi; auto. }

    { intros [HIn | HIn].
      all: induction pi; simpls; desf.

      all: desf_translate_pvertex_pedge.
      all: try eauto using update_eq.
      all: desf_unfold_pat.

      all: try apply IHpi.
      all: try now eexists.
      all: congruence. }
  Qed.

  Lemma matches_pattern_dom_start r' pv v
    (Hdom : Rcd.matches_pattern_dom r' (Pattern.start pv))
    (Hval : r' (Pattern.vname pv) = Some (Value.GVertex v)) :
      r' = (Pattern.vname pv |-> Value.GVertex v).
  Proof.
    extensionality k.
    desf_unfold_pat.
    unfold empty, t_empty.

    unfold Rcd.matches_pattern_dom, Rcd.in_dom in *.
    specialize Hdom with k; simpls.
    destruct (r' k) eqn:Hval'; auto.

    eassert (Hin : exists v, Some _ = Some v) by eauto.
    rewrite Hdom in Hin.
    desf.
  Qed.

  Lemma matches_pattern_dom_start' r' pv x
    (Hval : r' = (Pattern.vname pv |-> x)) :
      Rcd.matches_pattern_dom r' (Pattern.start pv).
  Proof.
    unfold Rcd.matches_pattern_dom in *; ins.
    split; ins; desf.
    all: unfold Rcd.in_dom in *.
    all: desf.
    all: try eexists.
    all: desf_unfold_pat.
    exfalso; eauto.
  Qed.

  Definition expansion_of_by_hop' graph r' r mode v_from e v_to pi pe pv :=
    expansion_of' graph r' r mode v_from e v_to
      (Pattern.vname (Pattern.last pi)) (Pattern.ename pe) (Pattern.vname pv) (Pattern.edir pe).

  Definition expansion_of_by_hop graph r' r mode pi pe pv :=
    expansion_of graph r' r mode
      (Pattern.vname (Pattern.last pi)) (Pattern.ename pe) (Pattern.vname pv) (Pattern.edir pe).

  Lemma matches_in_dom graph path pi r' n
    (Hmatch : Path.matches graph r' path pi)
    (HIn : In n (Pattern.dom pi)) :
      exists x, r' n = Some x.
  Proof.
    induction Hmatch.
    all: destruct Hpv; try destruct Hpe.
    all: simpls; desf.
    all: eauto.
  Qed.

  Lemma matches_in_dom_contra graph path pi r' n
    (Hmatch : Path.matches graph r' path pi)
    (Hval : r' n = None) :
      ~ In n (Pattern.dom pi).
  Proof.
    intro contra.
    eapply matches_in_dom in contra; eauto.
    desf.
  Qed.

  Lemma matches_last graph path pi r'
    (Hmatch : Path.matches graph r' path pi) :
      r' (Pattern.vname (Pattern.last pi)) = Some (Value.GVertex (Path.last path)).
  Proof.
    destruct pi. 
    all: inv Hmatch.
    all: destruct Hpv; try destruct Hpe.
    all: eauto.
  Qed.

  Lemma matches_exclude graph path pi r' n x
    (Hmatch : Path.matches graph r' path pi)
    (HIn : ~ In n (Pattern.dom pi)) :
      Path.matches graph (n !-> x; r') path pi.
  Proof.
    induction Hmatch.
    all: destruct Hpv; try destruct Hpe.
    1: apply Path.matches_nil.
    2: apply Path.matches_cons.
    all: try apply IHHmatch.
    all: try (intro; apply HIn; right; now right).
    all: try apply Path.Build_matches_pvertex.
    all: try apply Path.Build_matches_pedge.
    all: auto.
    all: desf_unfold_pat.
    all: exfalso; auto.
  Qed.

  Lemma matches_pattern_dom_exclude_All pi pe pv r'
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (Hdom : Rcd.matches_pattern_dom r' (Pattern.hop pi pe pv))
    (HIn : ~ In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      Rcd.matches_pattern_dom (Pattern.ename pe !-> None; Pattern.vname pv !-> None; r') pi.
  Proof.
    unfold Rcd.matches_pattern_dom in *.
    intros k. specialize Hdom with k.
    split; intro H.
    all: unfold Rcd.in_dom in *.
    all: desf_unfold_pat.
    { destruct Hdom as [? | [? | ?]]; eauto.
      all: exfalso; eauto. }
    all: rewrite Pattern.In_dom in *; desf.
    all: try Pattern.solve_wf_contra.
  Qed.

  Lemma matches_pattern_dom_exclude_Into pi pe pv r'
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (Hdom : Rcd.matches_pattern_dom r' (Pattern.hop pi pe pv))
    (HIn : In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      Rcd.matches_pattern_dom (Pattern.ename pe !-> None; r') pi.
  Proof.
    unfold Rcd.matches_pattern_dom in *.
    intros k. specialize Hdom with k.
    split; intro H.
    all: unfold Rcd.in_dom in *.
    all: desf_unfold_pat.
    { destruct Hdom as [? | [? | ?]]; subst; eauto.
      all: now (rewrite Pattern.In_dom; eauto). }
    all: rewrite Pattern.In_dom in *; desf.
    all: try Pattern.solve_wf_contra.
  Qed.

  Lemma matches_hop_All graph path e v pi pe pv r'
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (Hdom : Rcd.matches_pattern_dom r' (Pattern.hop pi pe pv))
    (Hmatch : Path.matches graph r' (Path.hop path e v) (Pattern.hop pi pe pv))
    (HIn : ~ In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      exists r, << Hexp : expansion_of_by_hop graph r' r All pi pe pv >> /\
                << Hmatch' : Path.matches graph r path pi >> /\
                << Hdom' : Rcd.matches_pattern_dom r pi >>.
  Proof.
    exists (Pattern.ename pe !-> None; Pattern.vname pv !-> None; r').
    inv Hmatch.
    destruct Hpe, Hpv.
    eauto.
    splits.
    { unfold expansion_of_by_hop, expansion_of, expansion_of'.
      do 3 eexists. splits; eauto.
      
      all: try extensionality k.
      all: desf_unfold_pat.
      all: try Pattern.solve_wf_contra.
      { exfalso. apply HIn. rewrite e0. apply Pattern.last__dom_vertices. }
      eauto using matches_last. }
    { apply matches_exclude. apply matches_exclude.
      { assumption. }
      all: rewrite Pattern.In_dom.
      all: intro; desf.
      all: Pattern.solve_wf_contra. }
    { apply matches_pattern_dom_exclude_All; eauto. }
  Qed.

  Lemma matches_hop_Into graph path e v pi pe pv r'
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (Hdom : Rcd.matches_pattern_dom r' (Pattern.hop pi pe pv))
    (Hmatch : Path.matches graph r' (Path.hop path e v) (Pattern.hop pi pe pv))
    (HIn : In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      exists r, << Hexp : expansion_of_by_hop graph r' r Into pi pe pv >> /\
                << Hmatch' : Path.matches graph r path pi >> /\
                << Hdom' : Rcd.matches_pattern_dom r pi >>.
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
      all: try Pattern.solve_wf_contra.
      eauto using matches_last. }
    { apply matches_exclude.
      { assumption. }
      all: rewrite Pattern.In_dom.
      all: intro; desf.
      all: Pattern.solve_wf_contra. }
    { eapply matches_pattern_dom_exclude_Into; eauto. }
  Qed.

  Theorem match_clause_spec graph path pi table' r'
    (Hres : eval_match_clause graph pi = Some table')
    (Hwf : Pattern.wf pi)
    (Hdom : Rcd.matches_pattern_dom r' pi)
    (Hmatch : Path.matches graph r' path pi) :
      In r' table'.
  Proof.
    generalize dependent Hdom.
    generalize dependent Hres.
    generalize dependent r'.
    generalize dependent table'.
    generalize dependent path.
    induction pi; ins.
    all: destruct path; inv Hmatch.
    all: destruct Hpv.
    all: try destruct Hpe.

    { all: desf_match_result Hres.
      1: eapply filter_vertices_by_label_spec; try eassumption.
      all: auto.
      all: assert (r' = (Pattern.vname pv |-> Value.GVertex v))
            by (eauto using matches_pattern_dom_start); subst.
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

  Lemma matches_pattern_dom_hop graph mode r r' pi pe pv
    (* (Hwf : Pattern.wf pi) *)
    (Hdom : Rcd.matches_pattern_dom r pi)
    (Hexp : expansion_of_by_hop graph r' r mode pi pe pv) :
      Rcd.matches_pattern_dom r' (Pattern.hop pi pe pv).
  Proof.
    unfold expansion_of_by_hop, expansion_of, expansion_of' in Hexp.
    unfold Rcd.matches_pattern_dom, Rcd.in_dom in *.
    ins; desf; desf.
    all: split; ins; desf.
    all: desf_unfold_pat.
    all: try rewrite <- Hdom.
    all: eauto.
    all: try now (exfalso; eauto).
    all: try now rewrite -> Hdom.
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
    all: try apply matches_exclude.
    all: try apply matches_exclude.
    all: eauto using matches_in_dom_contra.
    all: try apply Path.Build_matches_pedge.
    all: try apply Path.Build_matches_pvertex.
    all: auto.

    all: assert (Path.last path = v_from)
          by (erewrite matches_last in Hval_from; eauto;
            injection Hval_from; trivial).
    all: subst; auto.

    all: try now rewrite update_eq.
    all: try rewrite update_neq.
    all: try now rewrite update_eq.
    all: try assumption.
    all: try Pattern.solve_wf_contra.

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
        Rcd.matches_pattern_dom r' pi.
  Proof.
    generalize dependent Hres.
    generalize dependent r'.
    generalize dependent table'.
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
    all: try eapply matches_pattern_dom_hop.
    all: try unfold expansion_of_by_hop, expansion_of.
    all: eauto using matches_pattern_dom_start'.

    all: try eapply Path.matches_nil, Path.Build_matches_pvertex; eauto.
    all: try rewrite update_eq.
    all: auto.

    all: ins.
    all: try unfold expansion_of' in *; desf.
    all: repeat match goal with
          | [H1 : ?x = ?y, H2 : ?x = ?z |- _ ] =>
              rewrite H1 in H2; inj_subst; subst
          | [H : (?x |-> ?y) ?x = Some ?z |- _ ] =>
              rewrite update_eq in H; injection H as H; subst
          | [H : (?x |-> ?y; _) ?x = Some ?z |- _ ] =>
              rewrite update_eq in H; injection H as H; subst
          | [H : (Pattern.ename _ |-> _; _) _ = Some (Value.GVertex _) |- _ ] =>
              rewrite -> update_neq in H; [ | Pattern.solve_wf_contra ]
          | [H : (Pattern.vname _ |-> _; _) _ = Some (Value.GEdge _) |- _ ] =>
              rewrite -> update_neq in H; [ | Pattern.solve_wf_contra ]
          end.
    all: auto.
  Qed.
End EvalQueryImpl.
