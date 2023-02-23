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
  Proof using.
    induction p; split; ins.
    all: desf; simpls; desf; auto.
  Qed.

  Lemma In_dom_implicit p n :
    In n (dom_implicit p) <->
      In (Name.implicit n) (dom p).
  Proof using.
    induction p; split; ins.
    all: desf; simpls; desf; auto.
  Qed.

  Lemma In_dom_vertices_explicit p nv :
    In nv (dom_vertices_explicit p) <->
      In (Name.explicit nv) (dom_vertices p).
  Proof using.
    induction p; split; ins.
    all: desf; simpls; desf; auto.
  Qed.

  Lemma In_dom_vertices_implicit p nv :
    In nv (dom_vertices_implicit p) <->
      In (Name.implicit nv) (dom_vertices p).
  Proof using.
    induction p; split; ins.
    all: desf; simpls; desf; auto.
  Qed.

  Lemma In_dom_edges_explicit p ne :
    In ne (dom_edges_explicit p) <->
      In (Name.explicit ne) (dom_edges p).
  Proof using.
    induction p; split; ins.
    all: desf; simpls; desf; auto.
  Qed.

  Lemma In_dom_edges_implicit p ne :
    In ne (dom_edges_implicit p) <->
      In (Name.implicit ne) (dom_edges p).
  Proof using.
    induction p; split; ins.
    all: desf; simpls; desf; auto.
  Qed.

  Lemma In_dom p x :
    In x (dom p) <-> In x (dom_vertices p) \/ In x (dom_edges p).
  Proof using.
    induction p; split; ins; desf; auto.
    match goal with
    | [ H : In _ _ -> In _ _ \/ In _ _ |- _ ] => destruct H; try assumption; auto
    end.
  Qed.

  Lemma not_In_dom_vertices p nv
    (HIn : ~ In nv (dom p)) :
      ~ In nv (dom_vertices p).
  Proof using.
    intros contra. apply HIn.
    apply In_dom. now left.
  Qed.

  Lemma not_In_dom_edges p ne
    (HIn : ~ In ne (dom p)) :
      ~ In ne (dom_edges p).
  Proof using.
    intros contra. apply HIn.
    apply In_dom. now right.
  Qed.

  Inductive wf : Pattern.t -> Prop :=
  | wf_start pv : wf (start pv)
  | wf_hop pi pe pv (Hwf : wf pi)
    (Hpv_neq_pe : vname pv <> ename pe)
    (HIn_pv_imp : forall n, vname pv = Name.implicit n -> ~ In n (dom_vertices_implicit pi))
    (HIn_pe_edges : ~ In (ename pe) (dom_edges pi))
    (HIn_pe_vertices : ~ In (ename pe) (dom_vertices pi))
    (HIn_pv : ~ In (vname pv) (dom_edges pi)) :
      wf (hop pi pe pv).
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
