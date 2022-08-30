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
