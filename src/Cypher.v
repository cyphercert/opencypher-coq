Require Import String.

Definition label := string.

Module Pattern.
Inductive direction := 
| OUT
| IN
| BOTH
.

Inductive t :=
| vertex     (vname : string) (vlabels : list label)

| edge       (pattern : t) 
             (ename : string) (etype : list label) (edirection : direction)
             (wname : string) (wlabels : list label)

| multiedge  (pattern : t) 
             (enames : list string) (etype : label) (low : nat) (up : option nat)
             (vnames : list string) (wname : string) (vlabels : list label)
.
End Pattern.

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
