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
  | OUT  (* --> *)
  | IN   (* <-- *)
  | BOTH (* --- *)
  .

  (** Vertex pattern condition. **)

  (** pv_name   : optional name for the pattern **)
  
  (** pv_labels : list of labels stored in a vertex **)

  (** pv_props  : list of pairs (key, value) stored in a vertex **)

  Record pvertex := {
      pv_name   : option string;
      pv_labels : list string;
      pv_props  : list (string * Property.t);
    }.

  (** Edge pattern. It is a pair where the first item is edge condition (contained in elabels, eprops, edir, enum) *)
  (** and the second item is pattern of following vertex (contained in evertex). **)

  (** pe_name   : optional name for the pattern **)

  (** pe_labels : list of labels stored in an edge **)

  (** pe_props  : list of pairs (key, value) stored in an edge **)

  (** pe_dir    : direction condition **)

  Record pedge := {
      pe_name   : option string;
      pe_labels : list string;
      pe_props  : list (string * Property.t);
      pe_dir    : direction;
    }.

(** Query pattern. **)

(** phops : list of consequtive pattern edges **)

(** pend  : pattern of the first vertex **)

  Record t := mk {
      phops : list (pvertex * pedge);
      pend : pvertex;
    }.
  
  Definition pnil (pv : pvertex) := mk nil pv.

  Definition cons (pv : pvertex) (pe : pedge) (p : t) :=
    mk ((pv, pe) :: phops p) (pend p).

  Definition hd (p : t) :=
    match phops p with
    | (pv, pe) :: h => pv
    | nil => pend p
    end.

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
