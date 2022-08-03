Require Import String.
Require Import List.
Require Import BinNums.
Import ListNotations.

(** Types supported by the database. Currently integers and strings are supported**)

Module Property.
  Inductive t := 
  | p_int (i : Z)
  | p_string (s : string)
  | p_empty
  .
  
  Definition name := string.

End Property.

(** Property Graph structure **)

Module PropertyGraph.
  Definition vertex    := nat.
  Definition edge      := nat.
  Definition label     := string.

  Record t :=
    mk { vertices : list vertex;
         edges    : list edge;
         st       : edge -> vertex * vertex;
         vlab     : vertex -> list label;
         elab     : edge -> label;
         vprops   : list (Property.name * (vertex -> Property.t)); 
         eprops   : list (Property.name * (edge   -> Property.t)); 
      }.

End PropertyGraph.
