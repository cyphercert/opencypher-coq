Require Import String.
Require Import List.
Require Import Utils.
Require Import BinNums.
Require Import Maps.
Require Import Bool.
Import ListNotations.

From hahn Require Import HahnBase.

Module Property.

  (** Supported types in the graph database **)

  Inductive t := 
  | p_int (i : Z)
  | p_string (s : string)
  .
  
  Definition name := string.

End Property.

(** Property Graph structure **)

Module PropertyGraph.

  (** Types are used for indexing vertices and edges **)

  Definition vertex    := nat.
  Definition edge      := nat.
  Definition label     := string.

  Inductive gobj : Type :=
  | gedge (e: PropertyGraph.edge)
  | gvertex (v: PropertyGraph.vertex).

  (** Graph database model **)

  (** vertices : vertices of the graph **)

  (** edges    : edges of the graph **)

  (** ends     : maps an edge to a pair of its ends **)

  (** vlab     : maps a vertex to a list of its labels **)

  (** elab     : maps an edge to its relationship type **)

  (** vprops   : maps a vertex to key-value pairs of its properties **)

  (** eprops   : maps an edge to key-value pairs of its properties **)
  
  Record t :=
    mk { vertices : list vertex;
         edges    : list edge;
         ends     : edge -> vertex * vertex;
         vlabels  : vertex -> list label;
         elabel   : edge   -> label;
         vprops   : vertex -> list (Property.name * Property.t); 
         eprops   : edge   -> list (Property.name * Property.t); 
      }.

  Fixpoint get_prop (k : Property.name) (props : list (Property.name * Property.t)) : option Property.t :=
    match props with
    | (k', v) :: props => if k ==b k' then Some v else get_prop k props
    | nil => None
    end.

  Definition get_vprop (g : PropertyGraph.t) (k : Property.name) (v : vertex) : option Property.t :=
    get_prop k (vprops g v).

  Definition get_eprop (g : PropertyGraph.t) (k : Property.name) (e : edge) : option Property.t :=
    get_prop k (eprops g e).

  Definition get_gobj_prop (g : PropertyGraph.t) (k : Property.name) (go : gobj) : option Property.t :=
    match go with
    | gedge e => get_eprop g k e
    | gvertex v => get_vprop g k v
    end.

  Definition get_gobj_labels (g : PropertyGraph.t) (go : gobj) : list label :=
    match go with
    | gvertex v => vlabels g v
    | gedge e => [ elabel g e ]
    end.

  Definition e_from (g : t) (e : edge) := fst (ends g e).
  Definition e_to   (g : t) (e : edge) := snd (ends g e).

  Definition out_edges (g : t) (v : vertex) :=
    filter_map (fun e => if e_from g e ==b v then Some (e, e_to g e) else None) (edges g).

  Definition in_edges (g : t) (v : vertex) :=
    filter_map (fun e => if e_to g e ==b v then Some (e, e_from g e) else None) (edges g).

  Definition edges_between (g : t) (from to : vertex) :=
    filter (fun e => (e_from g e ==b from) && (e_to g e ==b to)) (edges g).

  Theorem out_in_between_edges_In g e v v' :
    (In (e, v') (out_edges g v) <-> In e (edges g) /\ e_from g e = v /\ e_to g e = v') /\
    (In (e, v') (in_edges g v) <-> In e (edges g) /\ e_to g e = v /\ e_from g e = v') /\
    (In e (edges_between g v v') <-> In e (edges g) /\ e_from g e = v /\ e_to g e = v').
  Proof using.
    split; [|split].
    
    all: unfold out_edges, in_edges, edges_between, e_from, e_to.
    all: try rewrite filter_map_In.
    all: try rewrite filter_In.
    all: split; ins; desf.
    all: try exists e.
    all: try erewrite equiv_decb_true.
    all: try match goal with 
         | Heq : (_ && _ = true) |- _ => apply andb_true_iff in Heq; destruct Heq
         end.
    all: repeat match goal with 
         | Heq : (_ = true) |- _ => apply equiv_decb_true' in Heq
         end.
    all: edestruct (ends g _); desf.
    { rewrite andb_true_iff. rewrite equiv_decb_true_iff. auto. }
  Qed.

  Lemma out_edges_In g e v v' :
    In (e, v') (out_edges g v) <-> In e (edges g) /\ e_from g e = v /\ e_to g e = v'.
  Proof using.
    edestruct out_in_between_edges_In as [? [? ?]]; eassumption.
  Qed.

  Lemma in_edges_In g e v v' :
    In (e, v') (in_edges g v) <-> In e (edges g) /\ e_to g e = v /\ e_from g e = v'.
  Proof using.
    edestruct out_in_between_edges_In as [? [? ?]]; eassumption.
  Qed.

  Lemma edges_between_In g e v v' :
    In e (edges_between g v v') <-> In e (edges g) /\ e_from g e = v /\ e_to g e = v'.
  Proof using.
    edestruct out_in_between_edges_In as [? [? ?]]; eassumption.
  Qed.

  Record wf (g : t) := mk_wf {
    ends_In : forall v v' e,
      In e (edges g) -> ends g e = (v, v') -> In v (vertices g) /\ In v' (vertices g);

    vlabels_In : forall v, vlabels g v <> nil -> In v (vertices g);

    vprops_In : forall v, vprops g v <> nil -> In v (vertices g);
    eprops_In : forall e, eprops g e <> nil -> In e (edges g);
  }.

End PropertyGraph.
