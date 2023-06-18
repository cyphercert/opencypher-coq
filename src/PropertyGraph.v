Require Import String.
Require Import List.
Require Import BinNums.
Import ListNotations.



Module Property.

  (** Supported types in the graph database **)

  Inductive t := 
  | p_int (i : Z)
  | p_string (s : string)
  | p_empty
  .

  Definition eq_property_dec (a b : t) : {a = b} + {a <> b}.
    refine (
      match a, b with
      | p_int a,          p_int b          => if a == b then left _ else right _
      | p_string a,       p_string b       => if a == b then left _ else right _
      | _,                _                => right _
      end
    ).
    all: try discriminate. (* Solve goals with different constructors *)
    all: try now f_equal.  (* Solve goals when underlying values are equal *)
    all: injection as H; contradiction. (* Solve goals when underlying values are not equal *)
  Defined.

  #[global]
  Program Instance property_eqdec : EqDec t eq := eq_property_dec.
  
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
         vprops   : list (Property.name * (vertex -> Property.t)); 
         eprops   : list (Property.name * (edge   -> Property.t)); 
      }.

End PropertyGraph.
