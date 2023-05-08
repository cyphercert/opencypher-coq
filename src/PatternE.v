Require Import Lia.
Require Import FunInd.
Require Import Recdef.

Require Import Utils.
Require Import Maps.
Require Import PropertyGraph.
Require Import Cypher.
Require Import BindingTable.
Require Import Semantics.
Import PartialMap.Notations.
Import PropertyGraph.
Import MatchMode.
Import UpdateNotations.

Module PatternSlice.
  Inductive t : Type :=
  | empty
  | hop (pi : t) (pe : Pattern.pedge) (pv : Pattern.pvertex)
  .

  Fixpoint length (pi : t) : nat :=
    match pi with
    | empty => 0
    | hop pi _ _ => S (length pi)
    end.

  Fixpoint type_of (rT : Rcd.T) (pi : t) : Rcd.T :=
    match pi with
    | empty => rT
    | hop pi pe pv =>
      ((Pattern.vname pv, Pattern.ename pe) |-[Mixed]->
          (Value.GVertexT, Value.GEdgeT); type_of rT pi)
    end.

  Theorem type_of__types rT pi n
    (Htype : rT n = Some Value.GVertexT \/
             rT n = Some Value.GEdgeT \/
             rT n = None) :
    type_of rT pi n = Some Value.GVertexT \/
    type_of rT pi n = Some Value.GEdgeT \/
    type_of rT pi n = None.
  Proof using.
    induction pi; simpls.
    unfold_update_with_mode.
    desf_unfold_pat.
  Qed.

  Theorem type_of_None rT pi n
    (Htype : type_of rT pi n = None) :
      rT n = None.
  Proof.
    induction pi; simpls.
    unfold_update_with_mode.
    desf; desf_unfold_pat.
  Qed.

  Section wf.
    Variable rT : Rcd.T.

    Inductive wf' : t -> Prop :=
    | wf'_empty : wf' empty
    | wf'_hop pi pe pv (Hwf : wf' pi)
        (Hpv_neq_pe : Pattern.vname pv <> Pattern.ename pe)
        (Hname_pe : Name.is_implicit (Pattern.ename pe))
        (Hname_pv : Name.is_implicit (Pattern.vname pv))
        (Htype_pe : type_of rT pi (Pattern.ename pe) = None)
        (Htype_pv : type_of rT pi (Pattern.vname pv) = None) :
          wf' (hop pi pe pv)
    .

    Definition imp_name_unique (pi : t) (n : Name.t) : Prop :=
      match n with
      | Name.implicit n => type_of rT pi (Name.implicit n) = None
      | Name.explicit _ => True
      end.

    Inductive wf : t -> Prop :=
    | wf_empty : wf empty
    | wf_hop pi pe pv (Hwf' : wf' pi)
        (Hpv_neq_pe : Pattern.vname pv <> Pattern.ename pe)
        (Htype_pv_imp : imp_name_unique pi (Pattern.vname pv))
        (Htype_pe : type_of rT pi (Pattern.ename pe) = None)
        (Htype_pv : type_of rT pi (Pattern.vname pv) = None \/ 
                    type_of rT pi (Pattern.vname pv) = Some Value.GVertexT) :
          wf (hop pi pe pv)
    .
  End wf.

  Theorem type_of_wf' rT pi
    (Hwf' : wf' rT pi) :
      type_of rT pi = rT.
  Proof.
    induction Hwf'; simpls.
    unfold_update_with_mode.
    unfold Name.is_implicit in *.
    desf.
  Qed.

  Theorem type_of_wf rT pi pe pv
    (Hwf : wf rT (PatternSlice.hop pi pe pv)) :
      type_of rT (PatternSlice.hop pi pe pv) =
        ((Pattern.vname pv, Pattern.ename pe) M|-> (Value.GVertexT, Value.GEdgeT); rT).
  Proof.
    simpl. inv Hwf.
    now rewrite type_of_wf' by auto.
  Qed.

  Theorem type_of_wf_Some rT pi n ty
    (Hwf : wf rT pi)
    (Htype : type_of rT pi n = Some ty) :
      rT n = Some ty \/ rT n = None.
  Proof.
    inv Hwf; simpls. { now left. }
    rewrite type_of_wf' in * by assumption.
    unfold_update_with_mode.
    desf_unfold_pat.
  Qed.

  Fixpoint append (pi : Pattern.t) (pi' : t) : Pattern.t :=
    match pi' with
    | empty => pi
    | hop pi' pe pv =>
      Pattern.hop (append pi pi') pe pv
    end.

  Fixpoint split' (pi : Pattern.t) : Pattern.t * t :=
    match pi with
    | Pattern.start pv => (Pattern.start pv, empty)
    | Pattern.hop pi pe pv =>
      if (Name.is_explicit_decb (Pattern.ename pe) ||
          Name.is_explicit_decb (Pattern.vname pv)) then
        (Pattern.hop pi pe pv, empty)
      else
        let '(pi, pi') := split' pi in (pi, hop pi' pe pv)
    end.

  Definition split (pi : Pattern.t) : Pattern.t * t :=
    match pi with
    | Pattern.start pv => (Pattern.start pv, empty)
    | Pattern.hop pi pe pv =>
      let '(pi, pi') := split' pi in (pi, hop pi' pe pv)
    end.

  Example split_example :
    let pv0 := Pattern.Build_pvertex (Name.implicit "v0") None [] in
    let pe1 := Pattern.Build_pedge (Name.explicit "e1") None [] Pattern.OUT in
    let pv1 := Pattern.Build_pvertex (Name.implicit "v1") None [] in
    let pe2 := Pattern.Build_pedge (Name.implicit "e2") None [] Pattern.OUT in
    let pv2 := Pattern.Build_pvertex (Name.implicit "v2") None [] in
    
    let pi := Pattern.hop (Pattern.hop (Pattern.start pv0) pe1 pv1) pe2 pv2 in
    let pi0 := Pattern.hop (Pattern.start pv0) pe1 pv1 in
    let pi' := hop empty pe2 pv2 in
      split pi = (pi0, pi').
  Proof using. reflexivity. Qed.

  Lemma split'_append pi pi0 pi'
    (Hsplit : split' pi = (pi0, pi')) :
      pi = append pi0 pi'.
  Proof using.
    gen_dep pi0 pi'.
    induction pi; ins; desf.
    simpl. f_equal. eauto.
  Qed.

  Theorem split_append pi pi0 pi'
    (Hsplit : split pi = (pi0, pi')) :
      pi = append pi0 pi'.
  Proof using.
    unfold split in *.
    destruct pi; desf.
    simpl. f_equal.
    eauto using split'_append.
  Qed.

  Lemma split'_first pi pi0 pi'
    (Hsplit : split' pi = (pi0, pi')) :
      Pattern.first pi0 = Pattern.first pi.
  Proof using.
    gen_dep pi0 pi'.
    induction pi; ins; desf.
    simpl. eauto.
  Qed.
    
  Theorem split_first pi pi0 pi'
    (Hsplit : split pi = (pi0, pi')) :
      Pattern.first pi0 = Pattern.first pi.
  Proof using.
    unfold split in *.
    destruct pi; desf; simpl.
    eauto using split'_first.
  Qed.

  Lemma split'_type_of_last pi pi0 pi'
    (Hsplit : split' pi = (pi0, pi')) :
      PatternT.type_of Mixed pi0 (Pattern.vname (Pattern.last pi0)) =
        Some Value.GVertexT.
  Proof using.
    gen_dep pi0 pi'.
    induction pi; ins; desf.
    all: simpls; unfold_update_with_mode; desf.
    all: try apply PartialMap.update_eq.
    eauto.
  Qed.
  
  Theorem split_type_of_last pi pi0 pi'
    (Hsplit : split pi = (pi0, pi')) :
      PatternT.type_of Mixed pi0 (Pattern.vname (Pattern.last pi0)) =
        Some Value.GVertexT.
  Proof using.
    unfold split in *.
    destruct pi; desf; simpl.
    { apply PartialMap.update_eq. }
    eauto using split'_type_of_last.
  Qed.

  Lemma split'_wf_pattern pi pi0 pi'
    (Hwf : PatternT.wfT pi)
    (Hsplit : split' pi = (pi0, pi')) :
      PatternT.wfT pi0.
  Proof using.
    gen_dep pi0 pi'.
    induction pi; ins; desf.
    inv Hwf; eauto.
  Qed.

  Theorem split_wf_pattern pi pi0 pi'
    (Hwf : PatternT.wfT pi)
    (Hsplit : split pi = (pi0, pi')) :
      PatternT.wfT pi0.
  Proof using.
    unfold split in *.
    destruct pi; desf; inv Hwf.
    eauto using split'_wf_pattern.
  Qed.

  Lemma split'_type_of pi pi0 pi'
    (Hsplit : split' pi = (pi0, pi')) :
      type_of (PatternT.type_of Mixed pi0) pi' =
        PatternT.type_of Mixed pi.
  Proof using.
    gen_dep pi0 pi'.
    induction pi; ins; desf.
    all: unfold_update_with_mode.
    all: simpl; desf; eauto.
  Qed.

  Theorem split_type_of pi pi0 pi'
    (Hsplit : split pi = (pi0, pi')) :
      type_of (PatternT.type_of Mixed pi0) pi' =
        PatternT.type_of Mixed pi.
  Proof using.
    unfold split in *.
    destruct pi.
    all: desf; simpl.
    all: erewrite split'_type_of; eauto.
  Qed.

  Lemma split'_wf_slice pi pi0 pi'
    (Hwf : PatternT.wfT pi)
    (Hsplit : split' pi = (pi0, pi')) :
      wf' (PatternT.type_of Mixed pi0) pi'.
  Proof using.
    gen_dep Hwf pi0 pi'.
    induction pi; ins; inv Hwf; desf.
    all: try now constructor.
    
    all: unfold Name.is_explicit_decb in *; desf.
    all: constructor; eauto.
    all: unfold PatternT.imp_name_unique, Name.is_implicit in *; desf.
    all: erewrite split'_type_of; eauto.
    all: now apply PatternT.type_of_None_downgrade.
  Qed.

  Theorem split_wf_slice pi pi0 pi'
    (Hwf : PatternT.wfT pi)
    (Hsplit : split pi = (pi0, pi')) :
      wf (PatternT.type_of Mixed pi0) pi'.
  Proof using.
    unfold split in *.
    desf; inv Hwf.
    all: constructor; auto.
    { eauto using split'_wf_slice. }
    1: unfold imp_name_unique, PatternT.imp_name_unique in *.
    all: desf.
    all: erewrite split'_type_of; eauto.
    all: try (try left; now apply PatternT.type_of_None_downgrade).

    edestruct PatternT.type_of__types as [Hty|[Hty|Hty]]; eauto.
    apply PatternT.type_of_Some_upgrade in Hty; auto.
    congruence.
  Qed.

  Theorem split'_length pi pi0 pi'
    (Hsplit : split' pi = (pi0, pi')) :
      Pattern.length pi = Pattern.length pi0 + length pi'.
  Proof using.
    gen_dep pi0 pi'.
    induction pi; ins; desf; simpls.
    erewrite IHpi; eauto.
  Qed.

  Theorem split'_length_le pi pi0 pi'
    (Hsplit : split' pi = (pi0, pi')) :
      Pattern.length pi0 <= Pattern.length pi.
  Proof using.
    erewrite split'_length with (pi := pi); eauto.
    lia.
  Qed.

  Theorem split_length pi pi0 pi'
    (Hsplit : split pi = (pi0, pi')) :
      Pattern.length pi = Pattern.length pi0 + length pi'.
  Proof using.
    unfold split in *.
    destruct pi; desf; simpl.
    erewrite split'_length; eauto.
  Qed.

  Theorem split_length_le pi pi0 pi'
    (Hsplit : split pi = (pi0, pi')) :
      Pattern.length pi0 <= Pattern.length pi.
  Proof using.
    erewrite split_length with (pi := pi); eauto.
    lia.
  Qed.

  Function split_all (pi : Pattern.t) { measure Pattern.length pi } :
    list PatternSlice.t * Pattern.pvertex :=
    match pi with
    | Pattern.start pv => ([], pv)
    | _ =>
      let (pi0, pi') := split pi in
      let (pis', pv) := split_all pi0 in
        (pi' :: pis', pv)
    end.
  Proof using.
    ins. desf. unfold lt. apply le_n_S.
    eapply split'_length_le; eauto.
  Defined.

  Fixpoint appends (pis' : list PatternSlice.t) (pi : Pattern.t) : Pattern.t :=
    match pis' with
    | [] => pi
    | pi' :: pis' => append (appends pis' pi) pi'
    end.

  Definition partial_paths
    (pv : Pattern.pvertex)
    (pis' : list PatternSlice.t) :
      list Pattern.t
  := map (fun pis' => appends pis' (Pattern.start pv)) (tails pis').

  Theorem split_all_first pi pis' pv
    (Hsplit : split_all pi = (pis', pv)) :
      Pattern.first pi = pv.
  Proof using.
    gen_dep pv pis'.
    pattern pi, (split_all pi).
    apply split_all_ind; ins; desf.
    erewrite <- split_first; eauto.
  Qed.

  Theorem split_all_appends pis' pi pv
    (Hsplit : split_all pi = (pis', pv)) :
      appends pis' (Pattern.start pv) = pi.
  Proof using.
    gen_dep pv pis'.
    pattern pi, (split_all pi).
    apply split_all_ind; ins; desf.
    simpl. rewrite H; auto.
    erewrite split_append; eauto.
  Qed.

  Theorem split_all_idempotent pi pis' pv
    (Heq : split_all pi = (pis', pv)) :
      split_all (appends pis' (Pattern.start pv)) = (pis', pv).
  Proof using.
    erewrite <- split_all_appends with (pi := pi) in Heq; eauto.
  Qed.

  Definition split_all_with_paths (pi : Pattern.t) :
    list (PatternSlice.t * Pattern.t) :=
    let (pis', pv) := split_all pi in
      combine pis' (tl (partial_paths pv pis')).

  Theorem split_all_with_paths_ind
    (P : Pattern.t -> list (PatternSlice.t * Pattern.t) -> Prop)
    (Hbase : forall pv, P (Pattern.start pv) [])
    (Hstep : forall pi pi0 pi',
      split pi = (pi0, pi') ->
      pi' <> empty ->
      P pi0 (split_all_with_paths pi0) ->
      P pi ((pi', pi0) :: split_all_with_paths pi0)
    ) :
      forall pi, P pi (split_all_with_paths pi).
  Proof using.
    intros pi.
    unfold split_all_with_paths, split in *.
    pattern pi, (split_all pi).
    apply split_all_ind; ins; desf.
    all: rewrite tails_hd in Heq.
    all: simpls; desf.
    rewrite map_tl.
    fold (partial_paths pv pis').
    erewrite split_all_appends; eauto.
    match goal with
    | [ Heq : split' ?pi''' = _,
        Heq0 : split_all ?pi'' = _
        |- ?P (Pattern.hop ?pi''' ?pe ?pv) _ ] =>
      specialize (Hstep (Pattern.hop pi''' pe pv) pi'');
      simpls; rewrite Heq, Heq0 in Hstep; desf
    end.
    now apply Hstep.
  Qed.

  Theorem split_all_with_paths_wf_pattern pi0 pi pi'
    (Hwf : PatternT.wfT pi)
    (Hsplit : In (pi', pi0) (split_all_with_paths pi)) :
      PatternT.wfT pi0.
  Proof using.
    gen_dep pi0 pi' pi.
    intros pi. pattern pi, (split_all_with_paths pi).
    apply split_all_with_paths_ind.
    all: ins; desf.
    2: eapply H1; eauto.
    all: eapply split_wf_pattern; eauto.
  Qed.

  Lemma split_all_with_paths_split pi0 pi pi'
    (Hsplit : In (pi', pi0) (split_all_with_paths pi)) :
      split (append pi0 pi') = (pi0, pi').
  Proof using.
    gen_dep pi0 pi' pi.
    intros pi. pattern pi, (split_all_with_paths pi).
    apply split_all_with_paths_ind.
    all: ins; desf.
    { erewrite <- split_append; eauto. }
    eapply H1; eauto.
  Qed.

  Theorem split_all_step pi0 pi pi' pv pis'
    (Hsplit : split pi = (pi0, pi'))
    (Hne : pi' <> empty)
    (Hall : split_all pi0 = (pis', pv)) :
      split_all pi = (pi' :: pis', pv).
  Proof using.
    gen_dep pi0 pi' pis' pv.
    pattern pi, (split_all pi).
    apply split_all_ind; ins; desf.
    congruence.
  Qed.

  Theorem split_all_with_paths_step pi0 pi pi'
    (Hsplit : split pi = (pi0, pi'))
    (Hne : pi' <> empty) :
      split_all_with_paths pi =
        (pi', pi0) :: split_all_with_paths pi0.
  Proof using.
    unfold split_all_with_paths. desf.
    erewrite split_all_step in Heq; eauto.
    desf. simpls.
    rewrite tails_hd. simpl.
    repeat f_equal.
    { erewrite split_all_appends; eauto. }
    now rewrite map_tl.
  Qed.
  
End PatternSlice.

Module PathSlice.
  Inductive t : Set :=
  | empty
  | hop (p : t) (e : edge) (v : vertex)
  .

  Fixpoint append (p : Path.t) (p' : t) : Path.t :=
    match p' with
    | empty => p
    | hop p' e v => Path.hop (append p p') e v
    end.

  Section matches.
    Variable G : PropertyGraph.t.
    Variable r : Rcd.t.
    Variable n_from : Name.t.

    Definition last (p : t) : vertex :=
      match p with
      | empty =>
        match r n_from with
        | Some (Value.GVertex v) => v
        | _ => 0
        end
      | hop p e v => v
      end.

    Inductive matches : Rcd.t -> PathSlice.t -> PatternSlice.t -> Prop :=
    | matches_empty (Hfrom : exists v, r n_from = Some (Value.GVertex v)) :
        matches r PathSlice.empty PatternSlice.empty
    | matches_hop r' p pi v e pe pv
                  (Hpv : Path.matches_pvertex G v pv)
                  (Hpe : Path.matches_pedge G e pe)
                  (Hpi : matches r' p pi)
                  (Hdir : Path.matches_direction G (last p) v e (Pattern.edir pe))
                  (Hprev : r' (Pattern.vname pv) = None \/
                          r' (Pattern.vname pv) = Some (Value.GVertex v)) :
        matches ((Pattern.vname pv, Pattern.ename pe) |-[Mixed]->
                    (Value.GVertex v, Value.GEdge e); r')
                (PathSlice.hop p e v) (PatternSlice.hop pi pe pv)
    .
  End matches.

  Lemma matches_n_from G r r' n_from p pi
    (Hmatch : matches G r n_from r' p pi) :
      exists v, r n_from = Some (Value.GVertex v).
  Proof using. induction Hmatch; eauto. Qed.

  Lemma matches_n_from_In G r r' n_from p pi pe pv v
    (Hwf_G : PropertyGraph.wf G)
    (Hmatch : matches G r n_from r' p (PatternSlice.hop pi pe pv))
    (Hfrom : r n_from = Some (Value.GVertex v)) :
      In v (vertices G).
  Proof.
    remember (PatternSlice.hop pi pe pv) as pi'.
    gen_dep pi pe pv.
    induction Hmatch; ins; eauto.
    injection Heqpi'; clear Heqpi'; ins; subst.
    destruct pi0.
    { inv Hmatch. simpls. rewrite Hfrom in Hdir.
      unfold Path.matches_direction in Hdir.
      rewrite e_from_to in Hdir.
      destruct Hpe.
      desf; desf.
      all: now (apply wf_e_from_In || apply wf_e_to_In). }
    now eapply IHHmatch.
  Qed.
    
  Theorem matches_append G r r' p p' pi pi'
    (Hmatch : Path.matches Mixed G r p pi)
    (Hmatch' : PathSlice.matches G r (Pattern.vname (Pattern.last pi)) r' p' pi') :
      Path.matches Mixed G r' (PathSlice.append p p') (PatternSlice.append pi pi').
  Proof using.
    induction Hmatch'.
    { assumption. }
    Opaque update_with_mode_hop.
    simpl; econstructor; eauto.
    Transparent update_with_mode_hop.

    destruct p0; simpls.
    inv Hmatch'. desf.
    all: erewrite Path.matches_last; eauto.
  Qed.

  Theorem matches_append_inv G r' p0 pi pi'
    (Htype : PatternT.type_of Mixed pi (Pattern.vname (Pattern.last pi)) =
              Some Value.GVertexT)
    (Hmatch : Path.matches Mixed G r' p0 (PatternSlice.append pi pi')) :
      exists p p' r, p0 = PathSlice.append p p' /\
        Path.matches Mixed G r p pi /\
        PathSlice.matches G r (Pattern.vname (Pattern.last pi)) r' p' pi'.
  Proof.
    gen_dep r' p0.
    induction pi'; ins.
    { exists p0. exists PathSlice.empty. exists r'.
      splits; auto. constructor.
      apply Rcd.type_of_GVertexT.
      erewrite <- Path.matches_type_of; eauto. }

    inv Hmatch.
    edestruct IHpi' as [p0 [p' [r0 [Happend [Hmatch0 Hmatch']]]]]; eauto.
    
    exists p0. exists (PathSlice.hop p' e v). exists r0.
    splits; auto.
    { simpls. now f_equal. }
    constructor; auto.

    assert (exists sv, r0 (Pattern.vname (Pattern.last pi)) =
              Some (Value.GVertex sv)) as [sv ?]
      by (eauto using matches_n_from).
    assert (r0 (Pattern.vname (Pattern.last pi)) =
              Some (Value.GVertex (Path.last p0))).
      by (erewrite Path.matches_last; eauto).

    unfold last; desf.
  Qed.

  Theorem matches_split G r r' p p' pi pi0 pi'
    (Hsplit : PatternSlice.split pi = (pi0, pi'))
    (Hmatch : Path.matches Mixed G r p pi0)
    (Hmatch' : PathSlice.matches G r (Pattern.vname (Pattern.last pi0)) r' p' pi') :
      Path.matches Mixed G r' (append p p') pi.
  Proof using.
    erewrite -> PatternSlice.split_append; eauto.
    eapply matches_append; eauto.
  Qed.

  Theorem matches_split_inv G r' p pi pi0 pi'
    (Hsplit : PatternSlice.split pi = (pi0, pi'))
    (Hmatch : Path.matches Mixed G r' p pi) :
      exists p0 p' r, p = append p0 p' /\
        Path.matches Mixed G r p0 pi0 /\
        PathSlice.matches G r (Pattern.vname (Pattern.last pi0)) r' p' pi'.
  Proof using.
    eapply matches_append_inv; eauto.
    { eauto using PatternSlice.split_type_of_last. }
    erewrite <- PatternSlice.split_append; eauto.
  Qed.

  Theorem matches_type_of G r r' p' pi' n_from
    (Hmatch' : PathSlice.matches G r n_from r' p' pi') :
      Rcd.type_of r' = PatternSlice.type_of (Rcd.type_of r) pi'.
  Proof using.
    induction Hmatch'; auto.
    simpl. unfold_update_with_mode. desf.
    all: repeat rewrite Rcd.type_of_update.
    all: now repeat f_equal.
  Qed.

  Theorem matches_last_In G r r' p' pi' n_from v
    (Hprev : r n_from = Some (Value.GVertex v))
    (HIn : In v (vertices G))
    (Hmatch' : PathSlice.matches G r n_from r' p' pi') :
      In (PathSlice.last r n_from p') (vertices G).
  Proof.
    destruct Hmatch'; simpls.
    { desf. }
    inv Hpv.
  Qed.
  
  Theorem matches_wf'_eq G r r' p' pi' n_from
    (Hwf' : PatternSlice.wf' (Rcd.type_of r) pi')
    (Hmatch' : PathSlice.matches G r n_from r' p' pi') :
      r = r'.
  Proof using.
    induction Hmatch'; auto.
    unfold_update_with_mode.
    inv Hwf'. unfold Name.is_implicit.
    simpl. desf.
    all: now apply IHHmatch'.
  Qed.
End PathSlice.
