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

  (** Graph database model **)

  (** vertices : list of verteces **)

  (** edges    : list of edges **)

  (** st       : matches edge's names and pairs of verteces **)

  (** vlab     : matches list of labels to verteces **)

  (** elab     : matches label to edges **)

  (** vprops   : list of triples (key, vertex, value) which provide to store smth in the database **)

  (** eprops   : list of triples (key, edge, value) which provide to store smth in the database **)
  Record t :=
    mk { vertices : list vertex;
         edges    : list edge;
         st       : edge -> vertex * vertex;
         vlab     : vertex -> list label;
         elab     : edge -> label;
         vprops   : vertex -> list (Property.name * Property.t); 
         eprops   : edge   -> list (Property.name * Property.t); 
      }.

End PropertyGraph.
