Require Import String.
Require Import List.
Import ListNotations.

Require Import PropertyGraph.
Import Property.

Module Pattern.
  Inductive direction :=
  | OUT
  | IN
  | BOTH
  .

  Record pvertex := {
      vlabels : list string;
      vprops  : list (string * Property.t);
    }.

  Record pedge := {
      elabels : list string;
      eprops  : list (string * Property.t);
      edir    : direction;
      enum    : nat;
      evertex : pvertex;
    }.
  

  Record t := {
      start : pvertex;
      ledges : list pedge;
    }.


End Pattern.

(* TODO: refactor VVVVV this VVVVV *)

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

(*
Missing features:
- UNION / UNION ALL
- WHERE
- EXPRESSIONS IN PROJECTION
- DISTINCT
- OPTIONAL MATCH
- UNWIND
- ORDER BY / SKIP / LIMIT
*)
