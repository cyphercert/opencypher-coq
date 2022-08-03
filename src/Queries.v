Require Import String.
Require Import List.
Import ListNotations.

Require Import Cypher.
Require Import PropertyGraph.
Import PropertyGraph.
Require Import Maps.
Require Import Utils.

Import Property.

(** Query semantics **)

Module QueryExpression.

Inductive gobj : Type :=
  | Edge (e: PropertyGraph.edge)
  | Vertex (v: PropertyGraph.vertex).

Inductive qexp : Type :=
  | QValue (p : Property.t)
  | QVariable (x : string)
  (*| QEdgeKey (e : PropertyGraph.edge) (k : Property.name)
  | Q*).

Inductive bqexp : Type :=
  | BQTrue
  | BQFalse
  | BQUnknown
  | BQOr (a1 a2 : bqexp)
  | BQAnd (a1 a2 : bqexp)
  | BQXor (a1 a2 : bqexp)
  | BQNot (a: bqexp)
  | BQIsUnknown (e : bqexp)
  | BQIsNotUknown (e : bqexp)
  | BQIsTrue (e : bqexp)
  | BQIsNotTrue (e : bqexp)
  | BQIsFalse (e : bqexp)
  | BQIsNotFalse (e : bqexp).

Definition store := total_map (option Property.t).

Definition qexpeval (st : store) (g : PropertyGraph.t) (a : qexp) : option Property.t :=
  match a with
  | QValue p => Some p
  | QVariable x => st x
  (*| QEdgeKey e k => g.(vprops) k e *)
  end.

Fixpoint bqexpeval (st : store) (g : PropertyGraph.t) (a : bqexp) : option bool  :=
  match a with
  | BQTrue => Some true
  | BQFalse => Some false
  | BQUnknown => None
  | BQOr a1 a2 => match bqexpeval st g a1 with
                  | None => None
                  | Some true => Some true
                  | Some false => match bqexpeval st g a2 with
                             | None => None
                             | Some true => Some true
                             | Some false => Some false
                             end
                  end
  | BQAnd a1 a2 => match bqexpeval st g a1 with
                   | None => None
                   | Some false => Some false
                   | Some true => match bqexpeval st g a2 with
                             | None => None
                             | Some true => Some true
                             | Some false => Some false
                             end
                   end
  | BQXor a1 a2 => match bqexpeval st g a1 with
                   | None => None
                   | Some true => match bqexpeval st g a2 with
                             | None => None
                             | Some true => Some false
                             | Some false => Some true
                             end
                   | Some false => match bqexpeval st g a2 with
                              | None => None
                              | Some true => Some true
                              | Some false => Some false
                             end
                  end
  | BQNot a => match bqexpeval st g a with
              | None => None
              | Some true => Some false
              | Some false => Some true
              end
  | BQIsUnknown a => match bqexpeval st g a with
                     | None => Some true
                     | _ => Some false
                     end
  | BQIsNotUknown a => match bqexpeval st g a with
                       | None => Some false
                       | _ => Some true
                       end
  | BQIsTrue a => match bqexpeval st g a with
                       | Some true => Some true
                       | _ => Some false
                       end
  | BQIsNotTrue a => match bqexpeval st g a with
                       | Some true => Some false
                       | _ => Some true
                       end
  | BQIsFalse a => match bqexpeval st g a with
                       | Some false => Some true
                       | _ => Some false
                       end
  | BQIsNotFalse a => match bqexpeval st g a with
                       | Some false => Some false
                       | _ => Some true
                       end

  end.

End QueryExpression.

Module Query.


Inductive query : Type :=
  | ReturnAll
  | ReturnAllAs
  | ReturnDistinct
  | IntersectAll (q1 q2 : query)
  | UnionAll (q1 q2 : query)
  | BQAnd (a1 a2 : QueryExpression.bqexp)
  | BQXor (a1 a2 : QueryExpression.bqexp)
  | BQNot (a: QueryExpression.bqexp)
  | BQIsUnknown (e : QueryExpression.bqexp)
  | BQIsNotUknown (e : QueryExpression.bqexp)
  | BQIsTrue (e : QueryExpression.bqexp)
  | BQIsNotTrue (e : QueryExpression.bqexp)
  | BQIsFalse (e : QueryExpression.bqexp)
  | BQIsNotFalse (e : QueryExpression.bqexp).

(*Fixpoint query_eval (q : query) (g : PropertyGraph.t) (t : binding_table) : binding_table :=
  match q with
  | ReturnAll => t
  | UnionAll q1 q2 =>
  | IntersectAll q1 q2 => binding_table
  | QEdgeKey e k => g.(vprops) k e
  end.*)

End Query.
