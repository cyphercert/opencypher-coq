Require Import String.
Require Import List.
Import ListNotations.

Require Import PropertyGraph.
Import Property.

(** Query pattern definition. In general terms, the query pattern is the conditions on the edges *)
(** and vertices in the desired path. These conditions (patterns) are stored sequentially: **)

(** start vertex pattern --- first edge pattern --- vertex pattern --- ... --- edge pattern --- last vertex pattern **)

(** (vertex and edge pattern alternate). We decided to store this query pattern in a special way. *)
(** Pattern contains start vertex pattern and pairs (edge pattern, vertex pattern). **)

Module Pattern.

(** Possible conditions for edge direction. **)

  Inductive direction :=
  | OUT
  | IN
  | BOTH
  .

  (** Vertex pattern condition. **)

  (** vlabels : list of labels stored in a vertex **)

  (** vprops  : list of pairs (key, value) stored in a vertex **)

  Record pvertex := {
      vlabels : list string;
      vprops  : list (string * Property.t);
    }.

(** Edge pattern. It is a pair where the first item is edge condition (contained in elabels, eprops, edir, enum) *)
(** and the second item is pattern of following vertex (contained in evertex). **)

(** elabels : list of labels stored in an edge **)

(** eprops  : list of pairs (key, value) stored in an edge **)

(** edir    : direction condition **)

(** enum    : number of sequential edges with current pattern in the desired path, by default is 1 *)
(**           /future: add the range to enum/ **)

(** evertex : vertex pattern **)

  Record pedge := {
      elabels : list string;
      eprops  : list (string * Property.t);
      edir    : direction;
      enum    : nat;
      evertex : pvertex;
    }.

  Inductive tree : Type :=
  | Leaf (x : pedge)
  | Node (t1 : tree) (t2 : tree).


(** Query pattern. **)

(** start  : pattern of the first vertex **)

(** ledges : list of consequеntive pattern edges **)

  Record t := mk {
      start : pvertex;
      ledges : tree;
    }.
    
  Fixpoint tree_left_height (t : tree) := 
    match t with 
    | Leaf _ => O
    | Node t1 _ => S (tree_left_height t1)
    end.
    
  Fixpoint tree_length (t : tree) := 
    match t with
    | Leaf _ => 1
    | Node t1 t2 => (tree_length t1) + (tree_length t2)
    end.
      
  Fixpoint tree_normalize_step (t : tree) (n : nat) :=
    match n with 
    | O => t
    | S k => match t with
             | Leaf _ => t
             | Node t1 t2 => match t1 with
                             | Leaf _ => t
                             | Node t3 t4 => Node (tree_normalize_step t3 k) (Node t4 t2)
                             end
             end
    end.
    
  Fixpoint tree_normalize_depth (t : tree) (n : nat) :=
    match n with 
    | 0 => t
    | S k => match tree_normalize_step t (tree_left_height t) with
             | Leaf _ => t
             | Node t1 t2 => Node t1 (tree_normalize_depth t2 k)
             end
    end.

  Definition tree_normalize (t : tree) := tree_normalize_depth t (tree_length t).

  Definition normalize (p : t) := mk p.(start) (tree_normalize p.(ledges)).

End Pattern.

(** Query definition **)

Module ProjectionExpr.
Inductive proj := AS (from : string) (to : string).

Definition t := list proj.
End ProjectionExpr.

Module Clause.
Inductive t := 
| MATCH (patterns : list Pattern.t)
| WITH (pexpr : ProjectionExpr.t)
.           
End Clause.

Module Query.
Record t := mk {
    clauses : list Clause.t;
    ret : ProjectionExpr.t;
}.
End Query.
