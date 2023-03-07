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
  Proof.
    induction pi; simpls.
    all: desf_unfold_pat.
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
  Proof. reflexivity. Qed.

  Lemma split'_append pi pi0 pi'
    (Hsplit : split' pi = (pi0, pi')) :
      pi = append pi0 pi'.
  Proof.
    gen_dep pi0 pi'.
    induction pi; ins; desf.
    simpl. f_equal. eauto.
  Qed.

  Theorem split_append pi pi0 pi'
    (Hsplit : split pi = (pi0, pi')) :
      pi = append pi0 pi'.
  Proof.
    unfold split in *.
    destruct pi; desf.
    simpl. f_equal.
    eauto using split'_append.
  Qed.

  Lemma split'_wf_pattern pi pi0 pi'
    (Hwf : PatternT.wfT pi)
    (Hsplit : split' pi = (pi0, pi')) :
      PatternT.wfT pi0.
  Proof.
    gen_dep pi0 pi'.
    induction pi; ins; desf.
    inv Hwf; eauto.
  Qed.

  Theorem split_wf_pattern pi pi0 pi'
    (Hwf : PatternT.wfT pi)
    (Hsplit : split pi = (pi0, pi')) :
      PatternT.wfT pi0.
  Proof.
    unfold split in *.
    destruct pi; desf; inv Hwf.
    eauto using split'_wf_pattern.
  Qed.

  Lemma split'_type_of g r p pi pi0 pi'
    (Hsplit : split' pi = (pi0, pi'))
    (Hmatch : Path.matches Mixed g r p pi0) :
      type_of (Rcd.type_of r) pi' = PatternT.type_of Mixed pi.
  Proof.
    erewrite <- Path.matches_type_of; eauto.
    gen_dep pi0 pi'.
    induction pi; ins; desf.
    all: simpl; desf; eauto.
  Qed.

  Theorem split_type_of g r p pi pi0 pi'
    (Hsplit : split pi = (pi0, pi'))
    (Hmatch : Path.matches Mixed g r p pi0) :
      type_of (Rcd.type_of r) pi' = PatternT.type_of Mixed pi.
  Proof.
    unfold split in *.
    destruct pi.
    all: do 2 (simpls; desf).
    all: repeat f_equal.
    all: eauto using split'_type_of.
    all: erewrite <- Path.matches_type_of; eauto.
    all: simpls; desf.
  Qed.

  Lemma split'_wf_slice g r p pi pi0 pi'
    (Hwf : PatternT.wfT pi)
    (Hsplit : split' pi = (pi0, pi'))
    (Hmatch : Path.matches Mixed g r p pi0) :
      wf' (Rcd.type_of r) pi'.
  Proof.
    gen_dep Hwf pi0 pi'.
    induction pi; ins; inv Hwf; desf.
    all: try now constructor.
    
    all: unfold Name.is_explicit_decb in *; desf.
    all: constructor; eauto.
    all: unfold PatternT.imp_name_unique, Name.is_implicit in *; desf.
    all: erewrite split'_type_of; eauto.
    all: now apply PatternT.type_of_None_downgrade.
  Qed.

  Theorem split_wf_slice g r p pi pi0 pi'
    (Hwf : PatternT.wfT pi)
    (Hsplit : split pi = (pi0, pi'))
    (Hmatch : Path.matches Mixed g r p pi0) :
      wf (Rcd.type_of r) pi'.
  Proof.
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
    Variable g : PropertyGraph.t.
    Variable r : Rcd.t.
    Variable svname : Name.t.

    Definition last (p : t) : vertex :=
      match p with
      | empty =>
        match r svname with
        | Some (Value.GVertex v) => v
        | _ => 0
        end
      | hop p e v => v
      end.

    Inductive matches : Rcd.t -> PathSlice.t -> PatternSlice.t -> Prop :=
    | matches_empty (Hsvname : exists v, r svname = Some (Value.GVertex v)) :
        matches r PathSlice.empty PatternSlice.empty
    | matches_hop r' p pi v e pe pv
                  (Hpv : Path.matches_pvertex g v pv)
                  (Hpe : Path.matches_pedge g e pe)
                  (Hpi : matches r' p pi)
                  (Hdir : Path.matches_direction g (last p) v e (Pattern.edir pe))
                  (Hprev : r' (Pattern.vname pv) = None \/
                          r' (Pattern.vname pv) = Some (Value.GVertex v)) :
        matches ((Pattern.vname pv, Pattern.ename pe) |-[Mixed]->
                    (Value.GVertex v, Value.GEdge e); r')
                (PathSlice.hop p e v) (PatternSlice.hop pi pe pv)
    .
  End matches.

  Lemma matches_svname g r r' svname p pi
    (Hmatch : matches g r svname r' p pi) :
      exists v, r svname = Some (Value.GVertex v).
  Proof. induction Hmatch; eauto. Qed.
    
  Theorem matches_append g r r' p p' pi pi'
    (Hmatch : Path.matches Mixed g r p pi)
    (Hmatch' : PathSlice.matches g r (Pattern.vname (Pattern.last pi)) r' p' pi') :
      Path.matches Mixed g r' (PathSlice.append p p') (PatternSlice.append pi pi').
  Proof.
    induction Hmatch'.
    { assumption. }
    Opaque update_with_mode_hop.
    simpl; econstructor; eauto.
    Transparent update_with_mode_hop.

    destruct p0; simpls.
    inv Hmatch'. desf.
    all: erewrite Path.matches_last; eauto.
  Qed.

  Theorem matches_split g r r' p p' pi pi0 pi'
    (Hsplit : PatternSlice.split pi = (pi0, pi'))
    (Hmatch : Path.matches Mixed g r p pi0)
    (Hmatch' : PathSlice.matches g r (Pattern.vname (Pattern.last pi0)) r' p' pi') :
      Path.matches Mixed g r' (append p p') pi.
  Proof.
    erewrite -> PatternSlice.split_append; eauto.
    eapply matches_append; eauto.
  Qed.

  Theorem matches_type_of g r r' p' pi' svname
    (Hmatch' : PathSlice.matches g r svname r' p' pi') :
      Rcd.type_of r' = PatternSlice.type_of (Rcd.type_of r) pi'.
  Proof.
    induction Hmatch'; auto.
    simpl. desf.
    all: repeat rewrite Rcd.type_of_update.
    all: now repeat f_equal.
  Qed.
  
End PathSlice.
