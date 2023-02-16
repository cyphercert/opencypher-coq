Require Import String.
Require Import List.
Import ListNotations.
From Coq Require Import Classes.EquivDec.
From hahn Require Import HahnBase.

Require Import PropertyGraph.
Require Import Maps.
Require Import Utils.
Import Property.

(** Query pattern definition. In general terms, the query pattern is the conditions on the edges *)
(** and vertices in the desired path. These conditions (patterns) are stored sequentially: **)

(** start vertex pattern --- first edge pattern --- vertex pattern --- ... --- edge pattern --- last vertex pattern **)

(** (vertex and edge pattern alternate). We decided to store this query pattern in a special way. *)
(** Pattern contains start vertex pattern and pairs (edge pattern, vertex pattern). **)

Module Name.
  Definition raw := string.

  Inductive t :=
  | explicit (n : raw)
  | implicit (n : raw)
  .

  Definition unwrap (n : t) :=
    match n with
    | explicit n => n
    | implicit n => n
    end.

  Definition eq_dec (n1 n2 : t) : {n1 = n2} + {n1 <> n2}.
    destruct n1 as [n1 | n1], n2 as [n2 | n2].
    all: destruct (equiv_decbP n1 n2).
    all: subst.
    all: try now left.
    all: right; congruence.
  Defined.

  #[global]
  Program Instance eqdec : EqDec t eq := eq_dec.

  Definition eqb (a b : t) : bool := a ==b b.
End Name.

Module Pattern.

  (** Possible conditions for edge direction. **)

  Inductive direction :=
  | OUT  (* --> *)
  | IN   (* <-- *)
  | BOTH (* --- *)
  .

  (** Vertex pattern condition. **)

  (** vname   : name for the pattern **)
  
  (** vlabels : list of labels stored in a vertex **)

  (** vprops  : list of pairs (key, value) stored in a vertex **)

  Record pvertex := {
      vname   : Name.t;
      vlabel  : option PropertyGraph.label;
      vprops  : list (Property.name * Property.t);
    }.

  (** Edge pattern. It is a pair where the first item is edge condition (contained in elabels, eprops, edir, enum) *)
  (** and the second item is pattern of following vertex (contained in evertex). **)

  (** ename   : name for the pattern **)

  (** elabels : list of labels stored in an edge **)

  (** eprops  : list of pairs (key, value) stored in an edge **)

  (** edir    : direction condition **)

  Record pedge := {
      ename   : Name.t;
      elabel  : option PropertyGraph.label;
      eprops  : list (Property.name * Property.t);
      edir    : direction;
    }.

  (** Query pattern. **)

  (** start  : pattern of the first vertex **)

  (** hop    : go to a vertex through an edge **)

  Inductive t := 
  | start (pv : pvertex)
  | hop (pi : t) (pe : pedge) (pv : pvertex).

  (*hop (start a) b c :  (a)-[b]-(c) *)

  Definition last (p : t) :=
    match p with
    | hop _ _ pv => pv
    | start pv => pv
    end.

  (* Domain of the pattern, i.e. names of the variables *)
  Fixpoint dom (p : Pattern.t) : list Name.t :=
    match p with
    | hop p pe pv =>
      vname pv :: ename pe :: dom p
    | start pv => [vname pv]
    end.

  Fixpoint dom_explicit (p : Pattern.t) : list Name.raw :=
    match p with
    | hop p pe pv =>
      match vname pv, ename pe with
      | Name.explicit nv, Name.explicit ne =>
          nv :: ne :: dom_explicit p
      | Name.implicit _,  Name.explicit ne =>
          ne :: dom_explicit p
      | Name.explicit nv, Name.implicit _  =>
          nv :: dom_explicit p
      | Name.implicit _,  Name.implicit _  =>
          dom_explicit p
      end
    | start pv =>
      match vname pv with
      | Name.explicit nv => [nv]
      | _                => []
      end
    end.

  Fixpoint dom_implicit (p : Pattern.t) : list Name.raw :=
    match p with
    | hop p pe pv =>
      match vname pv, ename pe with
      | Name.implicit nv, Name.implicit ne =>
          nv :: ne :: dom_implicit p
      | Name.explicit _,  Name.implicit ne =>
          ne :: dom_implicit p
      | Name.implicit nv, Name.explicit _  =>
          nv :: dom_implicit p
      | Name.explicit _,  Name.explicit _  =>
          dom_implicit p
      end
    | start pv =>
      match vname pv with
      | Name.implicit nv => [nv]
      | _                => []
      end
    end.

  Fixpoint dom_vertices_explicit (p : Pattern.t) : list Name.raw :=
    match p with
    | hop p pe pv =>
      match vname pv with
      | Name.explicit nv => nv :: dom_vertices_explicit p
      | _                => dom_vertices_explicit p
      end
    | start pv => 
      match vname pv with
      | Name.explicit nv => [nv]
      | _                => []
      end
    end.

  Fixpoint dom_vertices_implicit (p : Pattern.t) : list Name.raw :=
    match p with
    | hop p pe pv =>
      match vname pv with
      | Name.implicit nv => nv :: dom_vertices_implicit p
      | _                => dom_vertices_implicit p
      end
    | start pv => 
      match vname pv with
      | Name.implicit nv => [nv]
      | _                => []
      end
    end.

  Fixpoint dom_vertices (p : Pattern.t) : list Name.t :=
    match p with
    | hop p pe pv =>
      vname pv :: dom_vertices p
    | start pv => [vname pv]
    end.

  Fixpoint dom_edges_explicit (p : Pattern.t) : list Name.raw :=
    match p with
    | hop p pe pv =>
      match ename pe with
      | Name.explicit ne => ne :: dom_edges_explicit p
      | _                => dom_edges_explicit p
      end
    | start pv => []
    end.

  Fixpoint dom_edges_implicit (p : Pattern.t) : list Name.raw :=
    match p with
    | hop p pe pv =>
      match ename pe with
      | Name.implicit ne => ne :: dom_edges_implicit p
      | _                => dom_edges_implicit p
      end
    | start pv => []
    end.

  Fixpoint dom_edges (p : Pattern.t) : list Name.t :=
    match p with
    | hop p pe pv =>
      ename pe :: dom_edges p
    | start pv => nil
    end.

  Lemma In_dom_explicit p n :
    In n (dom_explicit p) <->
      In (Name.explicit n) (dom p).
  Proof.
    induction p; split; ins.
    all: desf; simpls; desf; auto.
  Qed.

  Lemma In_dom_implicit p n :
    In n (dom_implicit p) <->
      In (Name.implicit n) (dom p).
  Proof.
    induction p; split; ins.
    all: desf; simpls; desf; auto.
  Qed.

  Lemma In_dom_vertices_explicit p nv :
    In nv (dom_vertices_explicit p) <->
      In (Name.explicit nv) (dom_vertices p).
  Proof.
    induction p; split; ins.
    all: desf; simpls; desf; auto.
  Qed.

  Lemma In_dom_vertices_implicit p nv :
    In nv (dom_vertices_implicit p) <->
      In (Name.implicit nv) (dom_vertices p).
  Proof.
    induction p; split; ins.
    all: desf; simpls; desf; auto.
  Qed.

  Lemma In_dom_edges_explicit p ne :
    In ne (dom_edges_explicit p) <->
      In (Name.explicit ne) (dom_edges p).
  Proof.
    induction p; split; ins.
    all: desf; simpls; desf; auto.
  Qed.

  Lemma In_dom_edges_implicit p ne :
    In ne (dom_edges_implicit p) <->
      In (Name.implicit ne) (dom_edges p).
  Proof.
    induction p; split; ins.
    all: desf; simpls; desf; auto.
  Qed.

  Lemma In_dom p x :
    In x (dom p) <-> In x (dom_vertices p) \/ In x (dom_edges p).
  Proof.
    induction p; split; ins; desf; auto.
    match goal with
    | [ H : In _ _ -> In _ _ \/ In _ _ |- _ ] => destruct H; try assumption; auto
    end.
  Qed.

  Inductive wf : Pattern.t -> Prop :=
  | wf_start pv : wf (start pv)
  | wf_hop pi pe pv (Hwf : wf pi)
    (Hpv_neq_pe : vname pv <> ename pe)
    (HIn_pv_imp : forall n, vname pv = Name.implicit n -> ~ In n (dom_vertices_implicit pi))
    (HIn_pe : ~ In (ename pe) (dom pi))
    (HIn_pv : ~ In (vname pv) (dom_edges pi)) :
      wf (hop pi pe pv).

  #[global]
  Hint Constructors wf or and : pattern_wf_db.

  #[global]
  Hint Resolve NoDup_nil NoDup_cons NoDup_cons_l NoDup_cons_r NoDup_cons_contra conj : pattern_wf_db.

  Lemma hop_wf pi pe pv (Hwf : wf (Pattern.hop pi pe pv)) :
    wf pi.
  Proof.
    inv Hwf.
  Qed.

  Lemma wf__pe__dom_vertices pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    ~ In (Pattern.ename pe) (Pattern.dom_vertices pi).
  Proof.
    inv Hwf.
    intros ?; exfalso.
    apply HIn_pe. rewrite In_dom.
    now left.
  Qed.

  Lemma wf__pe__dom_edges pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    ~ In (Pattern.ename pe) (Pattern.dom_edges pi).
  Proof.
    inv Hwf.
    intros ?; exfalso.
    apply HIn_pe. rewrite In_dom.
    now right.
  Qed.

  Lemma wf__pe__dom pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    ~ In (Pattern.ename pe) (Pattern.dom pi).
  Proof.
    inv Hwf.
  Qed.

  Lemma wf__pv__dom_edges pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    ~ In (Pattern.vname pv) (Pattern.dom_edges pi).
  Proof.
    inv Hwf.
  Qed.

  Lemma wf__pv__dom pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (HIn : ~ In (Pattern.vname pv) (Pattern.dom_vertices pi)) :
      ~ In (Pattern.vname pv) (Pattern.dom pi).
  Proof.
    rewrite In_dom.
    intro contra; destruct contra as [contra | contra].
    { eauto. }
    { eapply wf__pv__dom_edges; eauto. }
  Qed.

  Lemma wf__pv_neq_pe pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    Pattern.vname pv <> Pattern.ename pe.
  Proof.
    inv Hwf.
  Qed.

  Lemma wf__pe_neq_pv pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    Pattern.ename pe <> Pattern.vname pv.
  Proof.
    inv Hwf.
    now symmetry.
  Qed.

  Lemma wf__last_neq_pe pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    Pattern.vname (Pattern.last pi) <> Pattern.ename pe.
  Proof.
    inv Hwf. destruct pi; simpls.
    all: intros ?; eauto.
  Qed.

  Lemma wf__pe_neq_last pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    Pattern.ename pe <> Pattern.vname (Pattern.last pi).
  Proof.
    symmetry. eapply wf__last_neq_pe; eassumption.
  Qed.

  Lemma wf__pv__dom_vertices pi pe pv n (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (Heq : Pattern.vname pv = Name.implicit n) :
      ~ In (Pattern.vname pv) (Pattern.dom_vertices pi).
  Proof.
    inv Hwf.
    rewrite Heq in *; rewrite <- In_dom_vertices_implicit.
    eauto.
  Qed.

  Lemma wf__imp_pv__dom_vertices pi pe pv n (Hwf : Pattern.wf (Pattern.hop pi pe pv))
    (Heq : Pattern.vname pv = Name.implicit n) :
      ~ In (Name.implicit n) (Pattern.dom_vertices pi).
  Proof.
    rewrite <- Heq in *.
    eauto using wf__pv__dom_vertices.
  Qed.

  Lemma last__dom_vertices pi :
    In (Pattern.vname (Pattern.last pi)) (Pattern.dom_vertices pi).
  Proof.
    destruct pi; now left.
  Qed.

  Lemma start_wf pv : wf (Pattern.start pv).
  Proof.
    apply wf_start.
  Qed.

  Ltac intros_wf_contra :=
    generalize NoDup_cons_l; intros ?;
    generalize wf__pe__dom_vertices; intros ?;
    generalize wf__pe__dom_edges; intros ?;
    generalize wf__pv__dom_edges; intros ?;
    generalize wf__pv_neq_pe; intros ?;
    generalize wf__pe_neq_pv; intros ?;
    generalize wf__last_neq_pe; intros ?;
    generalize wf__pe_neq_last; intros ?;
    generalize last__dom_vertices; intros ?;
    generalize wf__pv__dom_vertices; intros ?;
    generalize wf__imp_pv__dom_vertices; intros ?.

  #[global]
  Hint Resolve hop_wf start_wf
      wf__pv__dom wf__pe__dom
      wf__pv__dom_vertices wf__imp_pv__dom_vertices
      wf__pe__dom_vertices wf__pe__dom_edges wf__pv__dom_edges
      wf__pv_neq_pe wf__last_neq_pe last__dom_vertices : pattern_wf_db.

  Ltac solve_wf_contra := now (
    intros_wf_contra;
    unfold complement, equiv, not in *;
    solve [ exfalso; eauto with pattern_wf_db | eauto with pattern_wf_db ]
  ).
End Pattern.

(** Query definition **)

Module QueryExpr.
  Inductive t : Type :=
  | QEGObj (go : PropertyGraph.gobj)
  | QEVar  (n : Name.raw)
  | QEProj (a : t) (k : Property.name)

  | QEEq (a1 a2 : t)
  | QENe (a1 a2 : t)
  | QEGe (a1 a2 : t)
  | QELe (a1 a2 : t)
  | QELt (a1 a2 : t)
  | QEGt (a1 a2 : t)

  | QETrue
  | QEFalse
  | QEUnknown
  | QEOr (a1 a2 : t)
  | QEAnd (a1 a2 : t)
  | QEXor (a1 a2 : t)
  | QENot (a: t)
  | QEIsUnknown (e : t)
  | QEIsNotUnknown (e : t)
  | QEIsTrue (e : t)
  | QEIsNotTrue (e : t)
  | QEIsFalse (e : t)
  | QEIsNotFalse (e : t)
  .
End QueryExpr.

Module Query.
  Record t := mk {
    MATCH : Pattern.t;
    WHERE : option QueryExpr.t;
  }.

  Definition wf (query : t) := Pattern.wf query.(MATCH).
End Query.
