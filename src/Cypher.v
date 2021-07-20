From Coq Require Import String.
From Coq Require Import List.
Import ListNotations.

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

Notation "'{(' v ';' ls ')}'" := (vertex v ls).
Notation "'{(' v ')}'" := (vertex v nil).
Notation "p '-[' e ';' els ']-{(' w ';' wls ')}'" := (edge p e els BOTH w wls)
                                       (at level 74, left associativity).
Notation "p '-[' e ';' els ']->{(' w ';' wls ')}'" := (edge p e els OUT w wls)
                                       (at level 74, left associativity).
Notation "p '<-[' e ';' els ']-{(' w ';' wls ')}'" := (edge p e els IN w wls)
                                       (at level 74, left associativity).

Open Scope string_scope.
Definition pattern1 : t :=
  {("p" ; ["USER"])}.
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
