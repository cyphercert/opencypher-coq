Require Import String.
Require Import List.
Import ListNotations.

Require Import PropertyGraph.
Require Import Maps.
Require Import Utils.
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

  Definition name := string.

  Record pvertex := {
      vname   : option name;
      vlabels : list PropertyGraph.label;
      vprops  : list (Property.name * Property.t);
    }.

  (** Edge pattern. It is a pair where the first item is edge condition (contained in elabels, eprops, edir, enum) *)
  (** and the second item is pattern of following vertex (contained in evertex). **)

  (** pe_name   : optional name for the pattern **)

  (** pe_labels : list of labels stored in an edge **)

  (** pe_props  : list of pairs (key, value) stored in an edge **)

  (** pe_dir    : direction condition **)

  Record pedge := {
      ename   : option name;
      elabels : list PropertyGraph.label;
      eprops  : list (Property.name * Property.t);
      edir    : direction;
    }.

(** Query pattern. **)

(** phops : list of consequtive pattern edges **)

(** pend  : pattern of the first vertex **)

  Inductive t := 
  | start (pv : pvertex)
  | hop (pi : t) (pe : pedge) (pv : pvertex).

  Definition hd (p : t) :=
    match p with
    | hop _ _ pv => pv
    | start pv => pv
    end.

  Fixpoint dom (p : Pattern.t) : list string :=
    match p with
    | hop p pe pv =>
      match ename pe, vname pv with
      | Some ne, Some nv => ne :: nv :: dom p
      | Some ne, None    => ne :: dom p
      | None,    Some nv => nv :: dom p
      | None,    None    => dom p
      end
    | start pv =>
      match vname pv with
      | Some nv => [ nv ]
      | None    => nil
      end
    end.

End Pattern.

(** Query definition **)

Module QueryExpr.
  Inductive t : Type :=
  | QEGObj (go : PropertyGraph.gobj) : t
  | QEVar  (n : Pattern.name) : t
  | QEProj (a : t) (k : Property.name) : t

  | QEEq (a1 a2 : t) : t
  | QENe (a1 a2 : t) : t
  | QEGe (a1 a2 : t) : t
  | QELe (a1 a2 : t) : t
  | QELt (a1 a2 : t) : t
  | QEGt (a1 a2 : t) : t

  | QETrue : t
  | QEFalse : t
  | QEUnknown : t
  | QEOr (a1 a2 : t)
  | QEAnd (a1 a2 : t)
  | QEXor (a1 a2 : t)
  | QENot (a: t)
  | QEIsUnknown (e : t)
  | QEIsNotUnknown (e : t)
  | QEIsTrue (e : t)
  | QEIsNotTrue (e : t)
  | QEIsFalse (e : t)
  | QEIsNotFalse (e : t)
  .
End QueryExpr.

Module ProjectionExpr.
  Inductive proj := AS (from : string) (to : string).

  Definition t := list proj.
End ProjectionExpr.

Module Clause.
  Inductive t := 
  | MATCH (pattern : Pattern.t)
  .           
End Clause.

Module Query.
  Record t := mk {
    clause : Clause.t;
  }.
End Query.
