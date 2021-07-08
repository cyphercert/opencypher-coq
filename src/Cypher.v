Require Import String.

Definition label := string.
Definition var := nat.

Module Pattern.
Inductive direction := 
| OUT
| IN
| BOTH
.

Inductive t :=
| vertex     (vname : var) (vlabels : list label)

| edge       (pattern : t) 
             (ename : var) (etype : list label) (edirection : direction) 
             (wname : var) (wlabels : list label)

| multiedge  (pattern : t) 
             (enames : list var) (etype : label) (low : nat) (up : option nat) 
             (vnames : list var) (wname : var) (vlabels : list label)
.
End Pattern.

Module ProjectionExpr.
Inductive proj := AS (from : var) (to : var).

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
