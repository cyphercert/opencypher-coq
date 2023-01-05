Require Import String.
Require Import List.
Require Import BinNums.
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

  (** Types are used for indexing verteces and edges **)

  Definition vertex    := nat.
  Definition edge      := nat.
  Definition label     := string.

  Inductive gobj : Type :=
  | gedge (e: PropertyGraph.edge)
  | gvertex (v: PropertyGraph.vertex).

  (** Graph database model **)

  (** vertices : vertices of the graph **)

  (** edges    : edges of the graph **)

  (** st       : maps an edge to a pair of its ends **)

  (** vlab     : maps a vertex to a list of its labels **)

  (** elab     : maps an edge to its relationship type **)

  (** vprops   : maps a vertex to key-value pairs of its properties **)

  (** eprops   : maps an edge to key-value pairs of its properties **)
  
  Record t :=
    mk { vertices : list vertex;
         edges    : list edge;
         st       : edge -> vertex * vertex;
         vlabels  : vertex -> list label;
         elabel   : edge   -> label;
         vprops   : vertex -> list (Property.name * Property.t); 
         eprops   : edge   -> list (Property.name * Property.t); 
      }.

End PropertyGraph.
