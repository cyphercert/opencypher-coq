Require Import String.
Require Import List.
Import ListNotations.

Require Import Cypher.
Require Import PropertyGraph.
Require Import Maps.

Import Property.

Module QueryExpression.

Inductive gobj : Type :=
  | Edge (e: PropertyGraph.edge)
  | Vertex (v: PropertyGraph.vertex).

Inductive qexp : Type :=
  | QValue (p : Property.t)
  | QVariable (x : string)
  | QEdgeKey (e : PropertyGraph.edge) (k : Property.name)
  | Q.

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

Fixpoint qexpeval (st : store) (g : PropertyGraph.t) (a : qexp) : option Property.t :=
  match a with
  | QValue p => p
  | QVariable x => st x
  | QEdgeKey e k => g.(vprops) k e
  end.

Fixpoint bqexpeval (st : store) (g : PropertyGraph.t) (a : qexp) : option  :=
  match a with
  | BQTrue => true
  | BQFalse => false
  | BQUnknown => None
  | BQOr a1 a2 => match bqexpeval a1 with
                  | None => None
                  | true => true
                  | false => match bqexpeval a2 with
                             | None => None
                             | true => true
                             | false => false
                             end
                  end
  | BQAnd a1 a2 => match bqexpeval a1 with
                   | None => None
                   | false => false
                   | true => match bqexpeval a2 with
                             | None => None
                             | true => true
                             | false => false
                             end
                   end
  | BQXor a1 a2 => match bqexpeval a1 with
                   | None => None
                   | true => match bqexpeval a2 with
                             | None => None
                             | true => false
                             | false => true
                             end
                   | false => match bqexpeval a2 with
                              | None => None
                              | true => true
                              | false => false
                             end
                  end
  | BQNot a => match bqexpeval a with
              | None => None
              | true => false
              | false => true
              end
  | BQIsUnknown a => match bqexpeval a1 with
                     | None => true
                     | _ => false
                     end
  | BQIsNotUknown a => match bqexpeval a1 with
                       | None => false
                       | _ => true
                       end
  | BQIsTrue a => match bqexpeval a1 with
                       | true => true
                       | _ => false
                       end
  | BQIsNotTrue a => match bqexpeval a1 with
                       | true => false
                       | _ => true
                       end
  | BQIsFalse a => match bqexpeval a1 with
                       | false => true
                       | _ => false
                       end
  | BQIsNotFalse a => match bqexpeval a1 with
                       | false => false
                       | _ => true
                       end

  end.

End QueryExpression.

Module Query.

Record binding_table :=
  mk { names   : list string;
       records : list (names -> Property.t);
     }.

Inductive query : Type :=
  | ReturnAll
  | ReturnAllAs
  | ReturnDistinct
  | IntersectAll (q1 q2 : query)
  | UnionAll (q1 q2 : query)
  | BQAnd (a1 a2 : bqexp)
  | BQXor (a1 a2 : bqexp)
  | BQNot (a: bqexp)
  | BQIsUnknown (e : bqexp)
  | BQIsNotUknown (e : bqexp)
  | BQIsTrue (e : bqexp)
  | BQIsNotTrue (e : bqexp)
  | BQIsFalse (e : bqexp)
  | BQIsNotFalse (e : bqexp).

Fixpoint query_eval (q : query) (g : PropertyGraph.t) (t : binding_table) : binding_table :=
  match q with
  | ReturnAll => t
  | UnionAll q1 q2 =>
  | IntersectAll q1 q2 => binding_table
  | QEdgeKey e k => g.(vprops) k e
  end.

End Query.
