Require Import String.
Require Import List.
Import ListNotations.
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

  Definition name := string.

  Record pvertex := {
      vname   : name;
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
      ename   : name;
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
  Fixpoint dom (p : Pattern.t) : list Pattern.name :=
    match p with
    | hop p pe pv =>
      vname pv :: ename pe :: dom p
    | start pv => [vname pv]
    end.

  Fixpoint dom_vertices (p : Pattern.t) : list Pattern.name :=
    match p with
    | hop p pe pv =>
      vname pv :: dom_vertices p
    | start pv => [vname pv]
    end.

  Fixpoint dom_edges (p : Pattern.t) : list Pattern.name :=
    match p with
    | hop p pe pv =>
      ename pe :: dom_edges p
    | start pv => nil
    end.

  Lemma In_dom p x :
    In x (dom p) <-> In x (dom_vertices p) \/ In x (dom_edges p).
  Proof.
    induction p; split; ins; desf; auto.
    match goal with
    | [ H : In _ _ -> In _ _ \/ In _ _ |- _ ] => destruct H; try assumption; auto
    end.
  Qed.

  Definition wf (p : Pattern.t) :=
    << Hcontra : forall k, In k (dom_vertices p) -> In k (dom_edges p) -> False >> /\
    << Hdup : NoDup (dom_edges p) >>.

  #[global]
  Hint Constructors or and : pattern_wf_db.

  #[global]
  Hint Resolve NoDup_cons_l NoDup_cons_r NoDup_cons_contra conj : pattern_wf_db.

  Lemma hop_wf pi pe pv (Hwf : wf (Pattern.hop pi pe pv)) :
    wf pi.
  Proof.
    unfold wf in *.
    desf. split.
    - intros k H1 H2. eapply Hcontra; simpls; eauto.
    - eauto with pattern_wf_db.
  Qed.

  Lemma hop_wf_ind pi pe pv (Hwf : wf pi)
    (Hneq : vname pv <> ename pe)
    (HIn_vertices : ~ In (ename pe) (dom_vertices pi))
    (HIn_edges : ~ In (ename pe) (dom_edges pi))
    (HIn_edges' : ~ In (vname pv) (dom_edges pi)) :
    wf (Pattern.hop pi pe pv).
  Proof.
    unfold wf in *. split; desf; unnw.
    { intros k. ins. desf; eauto. }
    simpls. apply NoDup_cons_iff.
    split; auto.
  Qed.

  Lemma wf__pe__dom_vertices pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    ~ In (Pattern.ename pe) (Pattern.dom_vertices pi).
  Proof.
    unfold Pattern.wf in *. desf.
    intros ?; exfalso; eapply Hcontra; [ right | left ]; eauto.
  Qed.

  Lemma wf__pe__dom_edges pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    ~ In (Pattern.ename pe) (Pattern.dom_edges pi).
  Proof.
    unfold Pattern.wf in *. desf.
    apply NoDup_cons_iff in Hdup as [? ?]; auto.
  Qed.

  Lemma wf__pv__dom_edges pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    ~ In (Pattern.vname pv) (Pattern.dom_edges pi).
  Proof.
    unfold Pattern.wf in *. desf.
    intros ?; exfalso; eapply Hcontra; [ left | right ]; eauto.
  Qed.

  Lemma wf__pv_neq_pe pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    Pattern.vname pv =/= Pattern.ename pe.
  Proof.
    unfold Pattern.wf in *. desf.
    intros ?; exfalso; eapply Hcontra; [ left | left ]; eauto.
  Qed.

  Lemma wf__pe_neq_pv pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    Pattern.ename pe =/= Pattern.vname pv.
  Proof.
    symmetry. eapply wf__pv_neq_pe; eassumption.
  Qed.

  Lemma wf__last_neq_pe pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    Pattern.vname (Pattern.last pi) =/= Pattern.ename pe.
  Proof.
    unfold Pattern.wf in *. desf.
    destruct pi; simpls; intros ?; eauto.
  Qed.

  Lemma wf__pe_neq_last pi pe pv (Hwf : Pattern.wf (Pattern.hop pi pe pv)) :
    Pattern.ename pe =/= Pattern.vname (Pattern.last pi).
  Proof.
    symmetry. eapply wf__last_neq_pe; eassumption.
  Qed.

  Lemma last__dom_vertices pi :
    In (Pattern.vname (Pattern.last pi)) (Pattern.dom_vertices pi).
  Proof.
    destruct pi; now left.
  Qed.

  Lemma start_wf pv : wf (Pattern.start pv).
  Proof.
    unfold Pattern.wf; simpls.
    split.
    { ins; auto. }
    apply NoDup_nil.
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
    generalize last__dom_vertices; intros ?.

  #[global]
  Hint Resolve hop_wf start_wf wf__pe__dom_vertices wf__pe__dom_edges wf__pv__dom_edges
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
  | QEVar  (n : Pattern.name)
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

Module ProjectionExpr.
  Inductive proj := AS (from : string) (to : string).

  Definition t := list proj.
End ProjectionExpr.

Module Query.
  Record t := mk {
    MATCH : Pattern.t;
    WHERE : option QueryExpr.t;
  }.

  Definition wf (query : t) := Pattern.wf query.(MATCH).
End Query.
