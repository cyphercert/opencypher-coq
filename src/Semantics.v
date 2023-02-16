Require Import String.
Require Import List.
Require Import Bool.
Require Import BinNums.
From Coq Require Import Classes.EquivDec.
From Coq Require Import Logic.FunctionalExtensionality.
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
  Proof.
    induction pi; simpls.
    all: desf.
    all: try apply PartialMap.update_eq.

    desf_unfold_pat.
    { exfalso; eapply Pattern.wf__pe__dom_vertices; eauto. }
    eauto with pattern_wf_db.
  Qed.

  Lemma type_of__dom_edges (pi : Pattern.t) ne
    (Hwf : Pattern.wf pi)
    (HIn : In ne (Pattern.dom_edges pi)) :
      type_of Full pi ne = Some Value.GEdgeT.
  Proof.
    induction pi; simpls.
    all: desf.
    all: rewrite PartialMap.update_neq.
    all: try apply PartialMap.update_eq.
    all: try rewrite PartialMap.update_neq.
    all: eauto with pattern_wf_db.
    
    all: intro; subst.
    { eapply Pattern.wf__pe__dom_edges; eauto. }
    { eapply Pattern.wf__pv__dom_edges; eauto. }
  Qed.

  Lemma dom_vertices__type_of (pi : Pattern.t) nv
    (Hwf : Pattern.wf pi)
    (Htype : type_of Full pi nv = Some Value.GVertexT) :
      In nv (Pattern.dom_vertices pi).
  Proof.
    induction pi; simpls.
    all: desf_unfold_pat.
    all: eauto with pattern_wf_db.
  Qed.

  Lemma dom_edges__type_of (pi : Pattern.t) ne
    (Hwf : Pattern.wf pi)
    (Htype : type_of Full pi ne = Some Value.GEdgeT) :
      In ne (Pattern.dom_edges pi).
  Proof.
    induction pi; simpls.
    all: desf_unfold_pat.
    all: eauto with pattern_wf_db.
  Qed.

  Theorem In_dom_vertices__iff (pi : Pattern.t) nv
    (Hwf : Pattern.wf pi) :
      In nv (Pattern.dom_vertices pi) <-> type_of Full pi nv = Some Value.GVertexT.
  Proof.
    split; eauto using type_of__dom_vertices, dom_vertices__type_of.
  Qed.

  Theorem In_dom_edges__iff (pi : Pattern.t) ne
    (Hwf : Pattern.wf pi) :
      In ne (Pattern.dom_edges pi) <-> type_of Full pi ne = Some Value.GEdgeT.
  Proof.
    split; eauto using type_of__dom_edges, dom_edges__type_of.
  Qed.

  Theorem type_of__types mode pi k :
      type_of mode pi k = Some Value.GVertexT \/
      type_of mode pi k = Some Value.GEdgeT \/
      type_of mode pi k = None.
  Proof.
    induction pi; simpls.
    all: destruct mode; simpls.
    all: desf_unfold_pat.
  Qed.

  Theorem In_dom__iff (pi : Pattern.t) k
    (Hwf : Pattern.wf pi) :
      In k (Pattern.dom pi) <-> PartialMap.in_dom k (type_of Full pi).
  Proof.
    rewrite Pattern.In_dom.
    rewrite In_dom_vertices__iff, In_dom_edges__iff; auto.
    unfold PartialMap.in_dom.
    split; ins.
    all: desf; eauto.
    edestruct type_of__types with (mode := Full) as [? | [? | ?]].
    all: simpls; eauto.
    congruence.
  Qed.

  Corollary not_In_dom__iff (pi : Pattern.t) k
    (Hwf : Pattern.wf pi) :
      ~ (In k (Pattern.dom pi)) <-> type_of Full pi k = None.
  Proof.
    rewrite In_dom__iff; auto.
    now rewrite PartialMap.not_in_dom_iff.
  Qed.

  Lemma wf__type_of_pe pi pe pv
    (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
      type_of Full pi (Pattern.ename pe) = None.
  Proof.
    rewrite <- not_In_dom__iff. 
    all: eauto with pattern_wf_db.
  Qed.

  Lemma wf__type_of_pv__None pi pe pv
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (HIn : ~ In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      type_of Full pi (Pattern.vname pv) = None.
  Proof.
    rewrite <- not_In_dom__iff. 
    all: eauto with pattern_wf_db.
  Qed.

  Lemma wf__type_of_pv__Some pi pe pv
    (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (HIn : In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      type_of Full pi (Pattern.vname pv) = Some Value.GVertexT.
  Proof.
    rewrite <- In_dom_vertices__iff. 
    all: eauto with pattern_wf_db.
  Qed.

  #[global]
  Hint Resolve wf__type_of_pe wf__type_of_pv__None wf__type_of_pv__Some : patternT_wf_db.

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

  Section matches.
    Import Pattern.

    Variable mode : MatchMode.t.
    Variable g : PropertyGraph.t.
    Variable r : Rcd.t.

    Definition matches_name_full (n : Name.t) (v : Value.t) : Prop := 
      r n = Some v.

    Definition matches_name_explicit (n : Name.t) (v : Value.t) : Prop := 
      match n with
      | Name.implicit _ => True
      | Name.explicit _ => r n = Some v
      end.

    Definition matches_name (n : Name.t) (v : Value.t) : Prop := 
      match mode with
      | Full => matches_name_full n v
      | Explicit => matches_name_explicit n v
      end.

    Record matches_pvertex (v : vertex) (pv : pvertex) : Prop := {
        vertex_in_g : In v (PropertyGraph.vertices g);
        matches_vname : matches_name (Pattern.vname pv) (Value.GVertex v);
        matches_vlabel : forall l, Pattern.vlabel pv = Some l ->
          In l (PropertyGraph.vlabels g v);
      }.

    Record matches_pedge (e : edge) (pe : pedge) : Prop := {
        edge_in_g : In e (PropertyGraph.edges g);
        matches_ename : matches_name (Pattern.ename pe) (Value.GEdge e);
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
    Proof.
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

    Inductive matches : Path.t -> Pattern.t -> Prop :=
    | matches_nil (pv : pvertex) (v : vertex) 
                  (Hpv : matches_pvertex v pv) :
        matches (Path.start v) (Pattern.start pv) 
    | matches_cons (v : vertex) (e : edge) (p : Path.t)
                   (pv : pvertex) (pe : pedge) (pi : Pattern.t) 
                   (Hpi : matches p pi) (Hpe : matches_pedge e pe)
                   (Hdir : matches_direction (Path.last p) v e (Pattern.edir pe))
                   (Hpv : matches_pvertex v pv) :
        matches (Path.hop p e v) (Pattern.hop pi pe pv)
    .
  End matches.

  #[global]
  Hint Unfold matches_name_full matches_name_explicit matches_name : matches_name_db.

  Theorem matches_name__full_explicit r n v
    (Hmatch : matches_name Full r n v) :
      matches_name Explicit r n v.
  Proof.
    autounfold with matches_name_db.
    destruct n; auto.
  Qed.

  Theorem matches_pvertex__full_explicit graph r v pv
    (Hmatch : matches_pvertex Full graph r v pv) :
      matches_pvertex Explicit graph r v pv.
  Proof.
    destruct Hmatch; constructor; auto.
    now apply matches_name__full_explicit.
  Qed.

  Theorem matches_pedge__full_explicit graph r e pe
    (Hmatch : matches_pedge Full graph r e pe) :
      matches_pedge Explicit graph r e pe.
  Proof.
    destruct Hmatch; constructor; auto.
    now apply matches_name__full_explicit.
  Qed.

  Theorem matches__full_explicit graph path pi r
    (Hmatch : matches Full graph r path pi) :
      matches Explicit graph r path pi.
  Proof.
    induction Hmatch.
    all: constructor; auto.
    all: try now apply matches_pvertex__full_explicit.
    all: try now apply matches_pedge__full_explicit.
  Qed.

  Theorem matches_full_in_dom graph path pi r' n
    (Hmatch : matches Full graph r' path pi)
    (HIn : In n (Pattern.dom pi)) :
      PartialMap.in_dom n r'.
  Proof.
    unfold PartialMap.in_dom.
    induction Hmatch.
    all: destruct Hpv; try destruct Hpe.
    all: unfold matches_name in *.
    all: simpls; desf.
    all: eauto.
  Qed.

  Theorem matches_explicit_in_dom graph path pi r' n
    (Hmatch : matches Explicit graph r' path pi)
    (HIn : In (Name.explicit n) (Pattern.dom pi)) :
      PartialMap.in_dom (Name.explicit n) r'.
  Proof.
    unfold PartialMap.in_dom.
    induction Hmatch.
    all: destruct Hpv; try destruct Hpe.
    all: autounfold with matches_name_db in *.
    all: simpls; desf.
    all: eauto.
  Qed.

  Theorem matches_full_in_dom_contra graph path pi r' n
    (Hmatch : matches Full graph r' path pi)
    (Hval : r' n = None) :
      ~ In n (Pattern.dom pi).
  Proof.
    intro contra.
    eapply matches_full_in_dom in contra; eauto.
    unfold PartialMap.in_dom in contra.
    desf.
  Qed.

  Theorem matches_explicit_in_dom_contra graph path pi r' n
    (Hmatch : matches Explicit graph r' path pi)
    (Hval : r' (Name.explicit n) = None) :
      ~ In n (Pattern.dom_explicit pi).
  Proof.
    intro contra.
    rewrite Pattern.In_dom_explicit in contra.
    eapply matches_explicit_in_dom in contra; eauto.
    unfold PartialMap.in_dom in contra.
    desf.
  Qed.

  Theorem matches_full_last graph path pi r'
    (Hmatch : matches Full graph r' path pi) :
      r' (Pattern.vname (Pattern.last pi)) = Some (Value.GVertex (Path.last path)).
  Proof.
    destruct pi. 
    all: inv Hmatch.
    all: destruct Hpv; try destruct Hpe.
    all: simpls.
    all: unfold matches_name in *; desf.
    all: eauto.
  Qed.

  Theorem matches_exclude mode graph path pi r' n x
    (Hmatch : matches mode graph r' path pi)
    (HIn : ~ In n (Pattern.dom pi)) :
      matches mode graph (n !-> x; r') path pi.
  Proof.
    destruct mode.
    all: induction Hmatch.
    all: destruct Hpv; try destruct Hpe.
    all: try apply matches_nil.
    all: try apply matches_cons.
    all: unfold matches_name in *; desf.
    all: try apply IHHmatch.
    all: try (intro; apply HIn; right; now right).
    all: try apply Path.Build_matches_pvertex.
    all: try apply Path.Build_matches_pedge.
    all: auto.
    all: autounfold with matches_name_db in *.
    all: desf; ins.
    all: desf_unfold_pat.
    all: exfalso; auto.
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
      | QEGObj go =>
        match go with
        | gvertex v => Some (GVertex v)
        | gedge e => Some (GEdge e)
        end

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
      PropertyGraph.wf graph -> Pattern.wf pattern ->
        exists table', eval_match_clause graph pattern = Some table'.

    Axiom match_clause_type : forall graph pattern table',
      eval_match_clause graph pattern = Some table' ->
        Pattern.wf pattern ->
          BindingTable.of_type table' (PatternT.type_of Full pattern).

    Axiom match_clause_spec : forall graph path pattern table' r',
      eval_match_clause graph pattern = Some table' ->
        Pattern.wf pattern -> Rcd.type_of r' = PatternT.type_of Full pattern ->
          Path.matches Full graph r' path pattern -> In r' table'.

    Axiom match_clause_spec' : forall graph pattern table' r',
      eval_match_clause graph pattern = Some table' ->
        PropertyGraph.wf graph -> Pattern.wf pattern -> In r' table' ->
          exists path, Path.matches Full graph r' path pattern.
  End Spec.
End EvalQuery.