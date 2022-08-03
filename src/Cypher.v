Require Import String.
Require Import List.
Import ListNotations.

Require Import PropertyGraph.
Import Property.

(** Query pattern definition **)
Module Pattern.
(** Pattern direction **)
  Inductive direction :=
  | OUT
  | IN
  | BOTH
  .
(** Vertex pattern condition **)
  Record pvertex := {
      vlabels : list string;
      vprops  : list (string * Property.t);
    }.

(** Edge pattern. It ia a pair where the first item is edge condition *)
(** (contained in elabels, eprops, edir, enum ) and the second item is pattern of *)
(** following vertex (contained in evertex ) **)
  Record pedge := {
      elabels : list string;
      eprops  : list (string * Property.t);
      edir    : direction;
      enum    : nat;
      evertex : pvertex;
    }.
  
(** Query pattern. Field start is pattern of the first vertex, ledges is a list *)
(** of consequеntive pattern edges**)
  Record t := {
      start : pvertex;
      ledges : list pedge;
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
