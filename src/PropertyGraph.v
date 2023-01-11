Require Import String.
Require Import List.
Require Import Utils.
Require Import BinNums.
Require Import Maps.
Import ListNotations.



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

  Record wf (g : t) := mk_wf {
    ends_In : forall v v' e,
      In e (edges g) -> ends g e = (v, v') -> In v (vertices g) /\ In v' (vertices g);

    vlabels_In : forall v, vlabels g v <> nil -> In v (vertices g);

    vprops_In : forall v, vprops g v <> nil -> In v (vertices g);
    eprops_In : forall e, eprops g e <> nil -> In e (edges g);
  }.

End PropertyGraph.
