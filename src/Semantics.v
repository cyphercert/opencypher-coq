Require Import String.
Require Import List.
Require Import Bool.
Require Import BinNums.
From Coq Require Import Classes.EquivDec.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Lia.
Import ListNotations.

From hahn Require Import HahnBase.

Require Import Maps.
Require Import Utils.
Require Import Cypher.
Require Import PropertyGraph.
Require Import BindingTable.
Import PropertyGraph.
Import PartialMap.Notations.
Import TotalMap.Notations.

Module MatchMode.
  Inductive t :=
  | Explicit
  | Full
  .
End MatchMode.
Import MatchMode.

Module PatternT.
  Definition T := Rcd.T.

  Section type_of.
    Fixpoint type_of_full (pi : Pattern.t) : T :=
      match pi with
      | Pattern.start pv =>
          (Pattern.vname pv |-> Value.GVertexT)
      | Pattern.hop pi pe pv =>
          (Pattern.vname pv |-> Value.GVertexT; Pattern.ename pe |-> Value.GEdgeT; type_of_full pi)
      end.

    Fixpoint type_of_explicit (pi : Pattern.t) : T :=
      match pi with
      | Pattern.start pv =>
        match Pattern.vname pv with
        | Name.explicit _ => (Pattern.vname pv |-> Value.GVertexT)
        | Name.implicit _ => Rcd.emptyT
        end
      | Pattern.hop pi pe pv =>
        match Pattern.vname pv, Pattern.ename pe with
        | Name.explicit _, Name.explicit _ =>
          (Pattern.vname pv |-> Value.GVertexT; Pattern.ename pe |-> Value.GEdgeT; type_of_explicit pi)
        | Name.explicit _, Name.implicit _ =>
          (Pattern.vname pv |-> Value.GVertexT; type_of_explicit pi)
        | Name.implicit _, Name.explicit _ =>
          (Pattern.ename pe |-> Value.GEdgeT; type_of_explicit pi)
        | Name.implicit _, Name.implicit _ =>
          type_of_explicit pi
        end
      end.

    Definition type_of (mode : MatchMode.t) (pi : Pattern.t) : T :=
      match mode with
      | Full => type_of_full pi
      | Explicit => type_of_explicit pi
      end.
  End type_of.

  Lemma type_of__dom_vertices (pi : Pattern.t) nv
    (Hwf : Pattern.wf pi)
    (HIn : In nv (Pattern.dom_vertices pi)) :
      type_of Full pi nv = Some Value.GVertexT.
  Proof using.
    induction pi; simpls.
    all: inv Hwf.
    all: desf.
    all: try apply PartialMap.update_eq.

    desf_unfold_pat.
    contradiction.
  Qed.

  Lemma type_of_explicit__dom_vertices (pi : Pattern.t) nv
    (Hwf : Pattern.wf pi)
    (HIn : In (Name.explicit nv) (Pattern.dom_vertices pi)) :
      type_of Explicit pi (Name.explicit nv) = Some Value.GVertexT.
  Proof using.
    induction pi; simpls.
    all: inv Hwf.
    all: desf; simpls; desf.
    all: try apply PartialMap.update_eq.

    all: desf_unfold_pat.
    all: congruence.
  Qed.

  Lemma type_of__dom_edges (pi : Pattern.t) ne
    (Hwf : Pattern.wf pi)
    (HIn : In ne (Pattern.dom_edges pi)) :
      type_of Full pi ne = Some Value.GEdgeT.
  Proof using.
    induction pi; simpls.
    all: inv Hwf.
    all: desf.
    all: rewrite PartialMap.update_neq.
    all: try apply PartialMap.update_eq.
    all: try rewrite PartialMap.update_neq.
    all: auto.
    
    all: intro; subst.
    all: contradiction.
  Qed.

  Lemma type_of_explicit__dom_edges (pi : Pattern.t) ne
    (Hwf : Pattern.wf pi)
    (HIn : In (Name.explicit ne) (Pattern.dom_edges pi)) :
      type_of Explicit pi (Name.explicit ne) = Some Value.GEdgeT.
  Proof using.
    induction pi; simpls.
    all: inv Hwf.
    all: desf.
    all: try apply PartialMap.update_eq.
    all: try rewrite PartialMap.update_neq.
    all: try apply PartialMap.update_eq.
    all: try rewrite PartialMap.update_neq.
    all: auto.
    
    all: intro; subst.
    all: congruence.
  Qed.

  Lemma dom_vertices__type_of mode pi nv
    (Hwf : Pattern.wf pi)
    (Htype : type_of mode pi nv = Some Value.GVertexT) :
      In nv (Pattern.dom_vertices pi).
  Proof using.
    induction pi, mode; simpls.
    all: inv Hwf.
    all: desf_unfold_pat.
  Qed.

  Lemma dom_edges__type_of mode pi ne
    (Hwf : Pattern.wf pi)
    (Htype : type_of mode pi ne = Some Value.GEdgeT) :
      In ne (Pattern.dom_edges pi).
  Proof using.
    induction pi, mode; simpls.
    all: inv Hwf.
    all: desf_unfold_pat.
  Qed.

  Theorem In_dom_vertices__iff (pi : Pattern.t) nv
    (Hwf : Pattern.wf pi) :
      In nv (Pattern.dom_vertices pi) <-> type_of Full pi nv = Some Value.GVertexT.
  Proof using.
    split; eauto using type_of__dom_vertices, dom_vertices__type_of.
  Qed.

  Theorem In_dom_edges__iff (pi : Pattern.t) ne
    (Hwf : Pattern.wf pi) :
      In ne (Pattern.dom_edges pi) <-> type_of Full pi ne = Some Value.GEdgeT.
  Proof using.
    split; eauto using type_of__dom_edges, dom_edges__type_of.
  Qed.

  Theorem In_dom_vertices_explicit__iff (pi : Pattern.t) nv
    (Hwf : Pattern.wf pi) :
      In (Name.explicit nv) (Pattern.dom_vertices pi) <->
        type_of Explicit pi (Name.explicit nv) = Some Value.GVertexT.
  Proof using.
    split; eauto using type_of_explicit__dom_vertices, dom_vertices__type_of.
  Qed.

  Theorem In_dom_edges_explicit__iff (pi : Pattern.t) ne
    (Hwf : Pattern.wf pi) :
      In (Name.explicit ne) (Pattern.dom_edges pi) <->
        type_of Explicit pi (Name.explicit ne) = Some Value.GEdgeT.
  Proof using.
    split; eauto using type_of_explicit__dom_edges, dom_edges__type_of.
  Qed.

  Lemma last__dom_vertices pi :
    type_of Full pi (Pattern.vname (Pattern.last pi)) = Some Value.GVertexT.
  Proof using.
    destruct pi; simpl; apply PartialMap.update_eq.
  Qed.

  Theorem type_of_explicit__implicit (pi : Pattern.t) n :
    type_of Explicit pi (Name.implicit n) = None.
  Proof using.
    induction pi; simpls.
    all: desf; simpls; desf.
    all: repeat rewrite PartialMap.update_neq.
    all: auto.
    all: ins; discriminate.
  Qed.

  Theorem type_of__types mode pi k :
      type_of mode pi k = Some Value.GVertexT \/
      type_of mode pi k = Some Value.GEdgeT \/
      type_of mode pi k = None.
  Proof using.
    induction pi; simpls.
    all: destruct mode; simpls.
    all: desf_unfold_pat.
  Qed.

  Theorem In_dom__iff (pi : Pattern.t) k
    (Hwf : Pattern.wf pi) :
      In k (Pattern.dom pi) <-> PartialMap.in_dom k (type_of Full pi).
  Proof using.
    rewrite Pattern.In_dom.
    rewrite In_dom_vertices__iff, In_dom_edges__iff; auto.
    unfold PartialMap.in_dom.
    split; ins.
    all: desf; eauto.
    edestruct type_of__types with (mode := Full) as [? | [? | ?]].
    all: simpls; eauto.
    congruence.
  Qed.

  Theorem In_dom mode pi k
    (Hwf : Pattern.wf pi)
    (Hdom : PartialMap.in_dom k (type_of mode pi)) :
      In k (Pattern.dom pi).
  Proof using.
    unfold PartialMap.in_dom in *.
    destruct Hdom as [v Htype].
    rewrite Pattern.In_dom.
    destruct mode eqn:Heq, k.
    all: try (rewrite type_of_explicit__implicit in Htype; discriminate).
    1: rewrite In_dom_vertices_explicit__iff, In_dom_edges_explicit__iff; auto.
    all: try rewrite In_dom_vertices__iff, In_dom_edges__iff; auto.
    all: edestruct type_of__types with (mode := mode) (pi := pi) as [? | [? | ?]].
    all: desf.
    all: simpls; eauto.
    all: congruence.
  Qed.

  Theorem not_In_dom mode pi k
    (Hwf : Pattern.wf pi)
    (HIn : ~ (In k (Pattern.dom pi))) :
      type_of mode pi k = None.
  Proof using.
    rewrite <- PartialMap.not_in_dom_iff.
    ins; eauto using In_dom.
  Qed.

  Theorem not_In_dom__iff (pi : Pattern.t) k
    (Hwf : Pattern.wf pi) :
      ~ (In k (Pattern.dom pi)) <-> type_of Full pi k = None.
  Proof using.
    rewrite In_dom__iff; auto.
    now rewrite PartialMap.not_in_dom_iff.
  Qed.

  Lemma type_of_None pi n
    (Htype : type_of Full pi n = None) :
      type_of Explicit pi n = None.
  Proof using.
    induction pi; simpls.
    all: desf_unfold_pat.
  Qed.

  Lemma type_of_explicit_full pi n :
    type_of Explicit pi (Name.explicit n) = type_of Full pi (Name.explicit n).
  Proof using.
    induction pi; simpls.
    all: desf_unfold_pat.
  Qed.

  Definition imp_name_unique (pi : Pattern.t) (n : Name.t) : Prop :=
    match n with
    | Name.implicit n => type_of Full pi (Name.implicit n) = None
    | Name.explicit _ => True
    end.

  Inductive wfT : Pattern.t -> Prop :=
  | wfT_start pv : wfT (Pattern.start pv)
  | wfT_hop pi pe pv (Hwf : wfT pi)
      (Hpv_neq_pe : Pattern.vname pv <> Pattern.ename pe)
      (Htype_pv_imp : imp_name_unique pi (Pattern.vname pv))
      (Htype_pe : type_of Full pi (Pattern.ename pe) = None)
      (Htype_pv : type_of Full pi (Pattern.vname pv) = None \/
                type_of Full pi (Pattern.vname pv) = Some Value.GVertexT) :
        wfT (Pattern.hop pi pe pv).

  Lemma wfT_wf pi (Hwf : wfT pi) : Pattern.wf pi.
  Proof using.
    induction Hwf; constructor; auto.
    { ins. unfold imp_name_unique in *.
      rewrite Pattern.In_dom_vertices_implicit.
      apply Pattern.not_In_dom_vertices.
      rewrite not_In_dom__iff; desf. }
    { rewrite In_dom_edges__iff; auto. intro; congruence. }
    { rewrite In_dom_vertices__iff; auto. intro; desf; congruence. }
    { rewrite In_dom_edges__iff; auto.
      intros; destruct Htype_pv; congruence. }
  Qed.

  Lemma wf_wfT pi (Hwf : Pattern.wf pi) : wfT pi.
  Proof using.
    induction Hwf; constructor; auto.
    3: { edestruct type_of__types as [Hty | [Hty | Hty]]; eauto.
         exfalso. apply HIn_pv.
         rewrite In_dom_edges__iff; auto. }
    2: { rewrite <- not_In_dom__iff, Pattern.In_dom; auto.
         unfold not in *. ins; desf; auto. }
    ins; unfold imp_name_unique in *; desf.
    rewrite <- not_In_dom__iff; auto.
    rewrite Pattern.In_dom.
    rewrite <- Pattern.In_dom_vertices_implicit.
    intros [contra | contra].
    { eapply HIn_pv_imp; eauto. }
    now apply HIn_pv.
  Qed.

  Theorem wf_wfT_iff pi : Pattern.wf pi <-> wfT pi.
  Proof using.
    split; auto using wfT_wf, wf_wfT.
  Qed.

  Lemma last_neq_pe pi pe pv
    (Hwf : wfT (Pattern.hop pi pe pv)) :
      Pattern.vname (Pattern.last pi) <> Pattern.ename pe.
  Proof using.
    pose proof last__dom_vertices as H.
    specialize (H pi).
    inv Hwf.
    intro contra; congruence.
  Qed.

  Lemma last_neq_pv pi pe pv
    (Hwf : wfT (Pattern.hop pi pe pv))
    (HIn : PatternT.type_of Full pi (Pattern.vname pv) = None) :
      Pattern.vname (Pattern.last pi) <> Pattern.vname pv.
  Proof using.
    pose proof last__dom_vertices as H.
    specialize (H pi).
    inv Hwf.
    intro contra; congruence.
  Qed.

  Lemma explicit_projT_type_of mode pi :
    Rcd.explicit_projT (type_of mode pi) = type_of Explicit pi.
  Proof using.
    destruct mode.
    all: induction pi; simpls.
    all: unfold Rcd.explicit_projT in *.
    all: extensionality k.
    all: try apply (f_equal (fun f => f k)) in IHpi.
    all: desf_unfold_pat.
  Qed.

  Theorem matches_pattern_type_exclude_All mode pi pe pv r'
    (Hwf : wfT (Pattern.hop pi pe pv))
    (Htype : Rcd.type_of r' = PatternT.type_of mode (Pattern.hop pi pe pv))
    (HIn : PatternT.type_of Full pi (Pattern.vname pv) = None) :
      Rcd.type_of (Pattern.ename pe !-> None; Pattern.vname pv !-> None; r') =
        PatternT.type_of mode pi.
  Proof using.
    inv Hwf.
    repeat rewrite Rcd.type_of_t_update; simpls.
    rewrite Htype; clear Htype.
    destruct mode; simpls.
    all: extensionality k.
    all: desf_unfold_pat.
    all: now rewrite type_of_None.
  Qed.

  Lemma matches_pattern_type_exclude_Into mode pi pe pv r'
    (Hwf : wfT (Pattern.hop pi pe pv))
    (Htype : Rcd.type_of r' = PatternT.type_of mode (Pattern.hop pi pe pv))
    (HIn : PatternT.type_of Full pi (Pattern.vname pv) = Some Value.GVertexT) :
      Rcd.type_of (Pattern.ename pe !-> None; r') = PatternT.type_of mode pi.
  Proof using.
    inv Hwf.
    rewrite Rcd.type_of_t_update; simpls.
    rewrite Htype; clear Htype; unfold PartialMap.update.
    destruct mode; simpls.
    all: extensionality k.
    all: desf_unfold_pat.
    all: try now rewrite type_of_None.
    all: now rewrite type_of_explicit_full.
  Qed.
End PatternT.

Module Path.
  Inductive t :=
  | start (v : vertex)
  | hop (p : t) (e : edge) (v : vertex).

  Definition last (p : t) :=
    match p with
    | hop _ _ v => v
    | start v => v
    end.

  Definition update_with_mode (mode : MatchMode.t) (n : Name.t)
                              (v : Value.t) (r : Rcd.t) : Rcd.t := 
    match mode with
    | Full => (n |-> v; r)
    | Explicit =>
      match n with
      | Name.implicit _ => r
      | Name.explicit _ => (n |-> v; r)
      end
    end.

  Module UpdateNotations.
    Notation "n '|-[' mode ']->'  v ';' r" := (update_with_mode mode n v r)
      (at level 100, v at next level, right associativity).
    Notation "n '|-[' mode ']->' v " := (update_with_mode mode n v Rcd.empty)
      (at level 100).

    Notation "n 'F|->' v ';' r" := (update_with_mode Full n v r)
      (at level 100, v at next level, right associativity).
    Notation "n 'F|->' v " := (update_with_mode Full n v Rcd.empty)
      (at level 100).

    Notation "n 'E|->' v ';' r" := (update_with_mode Explicit n v r)
      (at level 100, v at next level, right associativity).
    Notation "n 'E|->' v " := (update_with_mode Explicit n v Rcd.empty)
      (at level 100).
  End UpdateNotations.
  Import UpdateNotations.

  #[global]
  Ltac lift_to_update_with_mode :=
    repeat change (?n |-> ?v; ?r) with (n F|-> v; r);
    repeat change (?n |-> ?v) with (n F|-> v).

  Section matches.
    Import Pattern.

    Variable mode : MatchMode.t.
    Variable g : PropertyGraph.t.

    Record matches_pvertex (v : vertex) (pv : pvertex) : Prop := {
        vertex_in_g : In v (PropertyGraph.vertices g);
        matches_vlabel : forall l, Pattern.vlabel pv = Some l ->
          In l (PropertyGraph.vlabels g v);
      }.

    Record matches_pedge (e : edge) (pe : pedge) : Prop := {
        edge_in_g : In e (PropertyGraph.edges g);
        matches_elabel : forall l, Pattern.elabel pe = Some l ->
          PropertyGraph.elabel g e = l;
      }.

    Definition matches_direction (from to : vertex) (e : edge) (d : direction) : Prop :=
        match d with
        | OUT  => ends g e = (from, to)
        | IN   => ends g e = (to, from)
        | BOTH => ends g e = (from, to) \/ ends g e = (to, from)
        end.

    Definition ends_match_decb (e : edge) (from to : vertex) : bool :=
      ends g e ==b (from, to).

    Definition matches_direction_decb (from to : vertex) (e : edge) (d : direction) : bool :=
        match d with
        | OUT   => ends_match_decb e from to
        | IN    => ends_match_decb e to from
        | BOTH  => ends_match_decb e from to || ends_match_decb e to from
        end.

    Definition matches_direction_dec (from to : vertex) (e : edge) (d : direction) :
      {matches_direction from to e d} + {~ matches_direction from to e d}.
    Proof using.
      refine (
        if matches_direction_decb from to e d == true
        then left _ else right _
      ).
      all: unfold matches_direction_decb, matches_direction,
                  ends_match_decb, equiv, complement in *.
      all: desf.
      all: try rewrite -> orb_true_iff in e0.
      all: try rewrite -> orb_true_iff in c.
      all: repeat rewrite -> equiv_decb_true_iff in e0.
      all: repeat rewrite -> equiv_decb_true_iff in c.
      all: auto.
    Defined.

    Inductive matches : Rcd.t -> Path.t -> Pattern.t -> Prop :=
    | matches_nil (pv : pvertex) (v : vertex) 
                  (Hpv : matches_pvertex v pv) :
        matches (vname pv |-[mode]-> Value.GVertex v)
                (Path.start v) (Pattern.start pv) 
    | matches_cons (v : vertex) (e : edge) (p : Path.t) (r : Rcd.t)
                   (pv : pvertex) (pe : pedge) (pi : Pattern.t) 
                   (Hpi : matches r p pi) (Hpe : matches_pedge e pe)
                   (Hdir : matches_direction (Path.last p) v e (Pattern.edir pe))
                   (Hpv : matches_pvertex v pv)
                   (Hprev : r (Pattern.vname pv) = None \/
                            r (Pattern.vname pv) = Some (Value.GVertex v)) :
        matches (vname pv |-[mode]-> Value.GVertex v;
                 ename pe |-[mode]-> Value.GEdge e; r)
                (Path.hop p e v) (Pattern.hop pi pe pv)
    .
  End matches.

  Theorem matches_in_dom_vertex mode graph path pi r' n
    (Hmatch : matches mode graph r' path pi)
    (HIn : PatternT.type_of mode pi n = Some Value.GVertexT) :
      exists v, r' n = Some (Value.GVertex v).
  Proof using.
    destruct mode.
    all: induction Hmatch.
    all: destruct Hpv; try destruct Hpe.
    all: unfold update_with_mode in *.
    all: simpls; desf_unfold_pat; desf.
    all: eauto.
  Qed.

  Theorem matches_in_dom_edge mode graph path pi r' n
    (Hmatch : matches mode graph r' path pi)
    (HIn : PatternT.type_of mode pi n = Some Value.GEdgeT) :
      exists e, r' n = Some (Value.GEdge e).
  Proof using.
    destruct mode.
    all: induction Hmatch.
    all: destruct Hpv; try destruct Hpe.
    all: unfold update_with_mode in *.
    all: simpls; desf_unfold_pat; desf.
    all: eauto.
  Qed.

  Theorem matches_not_in_dom_iff mode graph path pi r' n
    (Hmatch : matches mode graph r' path pi) :
      PatternT.type_of mode pi n = None <-> r' n = None.
  Proof using.
    destruct mode.
    all: induction Hmatch.
    all: destruct Hpv; try destruct Hpe.
    all: unfold update_with_mode in *.
    all: simpls; desf_unfold_pat; desf.
  Qed.

  Theorem matches_full_last graph path pi r'
    (Hmatch : matches Full graph r' path pi) :
      r' (Pattern.vname (Pattern.last pi)) = Some (Value.GVertex (Path.last path)).
  Proof using.
    destruct pi. 
    all: inv Hmatch.
    all: destruct Hpv; try destruct Hpe.
    all: unfold update_with_mode in *.
    all: apply PartialMap.update_eq.
  Qed.

  Lemma explicit_proj__update_with_mode mode n v r :
    Rcd.explicit_proj (n |-[mode]-> v; r) =
      (n E|-> v; (Rcd.explicit_proj r)).
  Proof.
    unfold update_with_mode, Rcd.explicit_proj in *.
    extensionality k.
    desf_unfold_pat.
  Qed.

  Theorem matches_explicit_proj mode graph path pi r
    (Hmatch : matches mode graph r path pi) :
      matches Explicit graph (Rcd.explicit_proj r) path pi.
  Proof using.
    destruct mode.
    all: induction Hmatch.
    all: repeat rewrite explicit_proj__update_with_mode.
    all: try rewrite Rcd.explicit_proj_empty.
    all: constructor; auto.
    all: unfold Rcd.explicit_proj; desf; auto.
  Qed.

  Theorem matches_two_records graph path pi r1 r2 n
    (Hmatch1 : matches Explicit graph r1 path pi)
    (Hmatch2 : matches Explicit graph r2 path pi) :
      r1 (Name.explicit n) = r2 (Name.explicit n).
  Proof using.
    gen_dep r2.
    induction Hmatch1; ins; inv Hmatch2.
    all: destruct Hpv; try destruct Hpe.
    all: destruct Hpv0; try destruct Hpe0.
    all: unfold update_with_mode in *.
    all: simpls; desf_unfold_pat; auto.
  Qed.

  Theorem matches_both_modes graph path pi r r'
    (Hmatch : matches Explicit graph r path pi)
    (Hmatch' : matches Full graph r' path pi) :
      r = Rcd.explicit_proj r'.
  Proof using.
    gen_dep r'.
    induction Hmatch; intros; inv Hmatch'.
    all: repeat rewrite explicit_proj__update_with_mode.
    { now rewrite Rcd.explicit_proj_empty. }
    erewrite IHHmatch; eauto.
  Qed.

  Theorem matches_explicit_exists_proj graph path pi r
    (Hwf : PatternT.wfT pi)
    (Hmatch : matches Explicit graph r path pi) :
      exists r', matches Full graph r' path pi.
  Proof using.
    induction Hmatch.
    all: inv Hwf.
    2: destruct IHHmatch as [r' Hmatch']; auto.
    all: eexists; splits.
    all: econstructor; eauto.

    erewrite -> matches_both_modes with (r := r) in Hprev; eauto.
    unfold Rcd.explicit_proj in Hprev.
    unfold PatternT.imp_name_unique in *.
    desf; auto.
    
    left. erewrite <- matches_not_in_dom_iff; eauto.
  Qed.

  Theorem matches_type_of mode graph path pi r
    (Hmatch : matches mode graph r path pi) :
      PatternT.type_of mode pi = Rcd.type_of r.
  Proof.
    destruct mode.
    all: induction Hmatch.
    all: unfold update_with_mode; simpls; desf.
    all: repeat rewrite Rcd.type_of_update.
    all: try rewrite IHHmatch.
    all: auto.
  Qed.
End Path.

(* Notation "g , u , p '|=' pi" := (Path.matches g u p pi) (at level 80, p at next level, u at next level, pi at next level, no associativity) : type_scope. *)

Section QueryExpr.
  Import QueryExpr.
  Import Value.

  Section eval_qexpr.
    Variable g : PropertyGraph.t.
    Variable u : Rcd.t.

    Fixpoint eval_qexpr (a : QueryExpr.t) : option Value.t :=
      match a with
      | QEVertex v => Some(GVertex v)
      | QEEdge e => Some(GEdge e)

      | QEVar n => u (Name.explicit n)

      | QEProj a k => option_map Value.from_property
        match eval_qexpr a with
        | Some (GVertex v) => get_vprop g k v
        | Some (GEdge e) => get_eprop g k e
        | _       => None
        end

      | QEEq a1 a2  =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (b1 ==b b2))
        | Some (Int i1),  Some (Int i2)  => Some (Bool (i1 ==b i2))
        | Some (Str s1),  Some (Str s2)  => Some (Bool (s1 ==b s2))
        | Some (Bool _),  Some Unknown   => Some Unknown
        | Some (Int _),   Some Unknown   => Some Unknown
        | Some (Str _),   Some Unknown   => Some Unknown
        | Some Unknown,   Some (Bool _)  => Some Unknown
        | Some Unknown,   Some (Int _)   => Some Unknown
        | Some Unknown,   Some (Str _)   => Some Unknown
        | _, _ => None
        end

      | QENe a1 a2 =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (b1 <>b b2))
        | Some (Int i1),  Some (Int i2)  => Some (Bool (i1 <>b i2))
        | Some (Str s1),  Some (Str s2)  => Some (Bool (s1 <>b s2))
        | Some (Bool _),  Some Unknown   => Some Unknown
        | Some (Int _),   Some Unknown   => Some Unknown
        | Some (Str _),   Some Unknown   => Some Unknown
        | Some Unknown,   Some (Bool _)  => Some Unknown
        | Some Unknown,   Some (Int _)   => Some Unknown
        | Some Unknown,   Some (Str _)   => Some Unknown
        | _, _ => None
        end

      | QELe a1 a2 =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (implb b1 b2))
        | Some (Int i1),  Some (Int i2)  => Some (Bool (BinIntDef.Z.leb i1 i2))
        | Some (Str s1),  Some (Str s2)  => Some (Bool (String.leb s1 s2))
        | Some (Bool _),  Some Unknown   => Some Unknown
        | Some (Int _),   Some Unknown   => Some Unknown
        | Some (Str _),   Some Unknown   => Some Unknown
        | Some Unknown,   Some (Bool _)  => Some Unknown
        | Some Unknown,   Some (Int _)   => Some Unknown
        | Some Unknown,   Some (Str _)   => Some Unknown
        | _, _ => None
        end

      | QEGe a1 a2 =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (implb b2 b1))
        | Some (Int i1),  Some (Int i2)  => Some (Bool (BinIntDef.Z.geb i1 i2))
        | Some (Str s1),  Some (Str s2)  => Some (Bool (String.leb s2 s1))
        | Some (Bool _),  Some Unknown   => Some Unknown
        | Some (Int _),   Some Unknown   => Some Unknown
        | Some (Str _),   Some Unknown   => Some Unknown
        | Some Unknown,   Some (Bool _)  => Some Unknown
        | Some Unknown,   Some (Int _)   => Some Unknown
        | Some Unknown,   Some (Str _)   => Some Unknown
        | _, _ => None
        end

      | QELt a1 a2  =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (negb (implb b2 b1)))
        | Some (Int i1),  Some (Int i2)  => Some (Bool (BinIntDef.Z.ltb i1 i2))
        | Some (Str s1),  Some (Str s2)  => Some (Bool (String.ltb s1 s2))
        | Some (Bool _),  Some Unknown   => Some Unknown
        | Some (Int _),   Some Unknown   => Some Unknown
        | Some (Str _),   Some Unknown   => Some Unknown
        | Some Unknown,   Some (Bool _)  => Some Unknown
        | Some Unknown,   Some (Int _)   => Some Unknown
        | Some Unknown,   Some (Str _)   => Some Unknown
        | _, _ => None
        end

      | QEGt a1 a2  =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool b1), Some (Bool b2) => Some (Bool (negb (implb b1 b2)))
        | Some (Int i1),  Some (Int i2)  => Some (Bool (BinIntDef.Z.gtb i1 i2))
        | Some (Str s1),  Some (Str s2)  => Some (Bool (String.ltb s2 s1))
        | Some (Bool _),  Some Unknown   => Some Unknown
        | Some (Int _),   Some Unknown   => Some Unknown
        | Some (Str _),   Some Unknown   => Some Unknown
        | Some Unknown,   Some (Bool _)  => Some Unknown
        | Some Unknown,   Some (Int _)   => Some Unknown
        | Some Unknown,   Some (Str _)   => Some Unknown
        | _, _ => None
        end
      
      | QETrue    => Some (Bool true)
      | QEFalse   => Some (Bool false)
      | QEUnknown => Some Unknown

      | QEOr a1 a2 =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool true),  Some (Bool true)  => Some (Bool true)
        | Some (Bool true),  Some (Bool false) => Some (Bool true)
        | Some (Bool false), Some (Bool true)  => Some (Bool true)
        | Some (Bool false), Some (Bool false) => Some (Bool false)

        | Some (Bool true),  Some Unknown      => Some (Bool true)
        | Some (Bool false), Some Unknown      => Some Unknown
        | Some Unknown,      Some (Bool true)  => Some (Bool true)
        | Some Unknown,      Some (Bool false) => Some Unknown
        | Some Unknown,      Some Unknown      => Some Unknown

        | _, _ => None
        end

      | QEAnd a1 a2 => 
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool true),  Some (Bool true)  => Some (Bool true)
        | Some (Bool true),  Some (Bool false) => Some (Bool false)
        | Some (Bool false), Some (Bool true)  => Some (Bool false)
        | Some (Bool false), Some (Bool false) => Some (Bool false)

        | Some (Bool true),  Some Unknown      => Some Unknown
        | Some (Bool false), Some Unknown      => Some (Bool false)
        | Some Unknown,      Some (Bool true)  => Some Unknown
        | Some Unknown,      Some (Bool false) => Some (Bool false)
        | Some Unknown,      Some Unknown      => Some Unknown
        
        | _, _ => None
        end

      | QEXor a1 a2 =>
        match eval_qexpr a1, eval_qexpr a2 with
        | Some (Bool true),  Some (Bool true)  => Some (Bool false)
        | Some (Bool true),  Some (Bool false) => Some (Bool true)
        | Some (Bool false), Some (Bool true)  => Some (Bool true)
        | Some (Bool false), Some (Bool false) => Some (Bool false)

        | Some (Bool true),  Some Unknown      => Some Unknown
        | Some (Bool false), Some Unknown      => Some Unknown
        | Some Unknown,      Some (Bool true)  => Some Unknown
        | Some Unknown,      Some (Bool false) => Some Unknown
        | Some Unknown,      Some Unknown      => Some Unknown
        
        | _, _ => None
        end

      | QENot a => 
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool false)
        | Some (Bool false) => Some (Bool true)
        | Some Unknown      => Some Unknown
        | _                 => None
        end

      | QEIsUnknown a =>
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool false)
        | Some (Bool false) => Some (Bool false)
        | Some Unknown      => Some (Bool true)
        | _                 => None
        end

      | QEIsNotUnknown a =>
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool true)
        | Some (Bool false) => Some (Bool true)
        | Some Unknown      => Some (Bool false)
        | _                 => None
        end

      | QEIsTrue a =>
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool true)
        | Some (Bool false) => Some (Bool false)
        | Some Unknown      => Some (Bool false)
        | _                 => None
        end

      | QEIsNotTrue a =>
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool false)
        | Some (Bool false) => Some (Bool true)
        | Some Unknown      => Some (Bool true)
        | _                 => None
        end

      | QEIsFalse a =>
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool false)
        | Some (Bool false) => Some (Bool true)
        | Some Unknown      => Some (Bool false)
        | _                 => None
        end

      | QEIsNotFalse a =>
        match eval_qexpr a with
        | Some (Bool true)  => Some (Bool true)
        | Some (Bool false) => Some (Bool false)
        | Some Unknown      => Some (Bool true)
        | _                 => None
        end
      end.
  End eval_qexpr.
End QueryExpr.

Module EvalQuery.
  Module Type Spec.
    Parameter eval_match_clause : PropertyGraph.t -> Pattern.t -> option BindingTable.t.

    Axiom match_clause_wf : forall graph pattern,
      PropertyGraph.wf graph -> PatternT.wfT pattern ->
        exists table', eval_match_clause graph pattern = Some table'.

    Axiom match_clause_type : forall graph pattern table',
      eval_match_clause graph pattern = Some table' ->
        PatternT.wfT pattern ->
          BindingTable.of_type table' (PatternT.type_of Explicit pattern).

    Axiom match_clause_spec : forall graph path pattern table' r',
      eval_match_clause graph pattern = Some table' ->
        PatternT.wfT pattern -> Path.matches Explicit graph r' path pattern ->
          In r' table'.

    Axiom match_clause_spec' : forall graph pattern table' r',
      eval_match_clause graph pattern = Some table' ->
        PropertyGraph.wf graph -> PatternT.wfT pattern -> In r' table' ->
          exists path, Path.matches Explicit graph r' path pattern.
  End Spec.
End EvalQuery.