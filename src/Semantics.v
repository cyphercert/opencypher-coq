Require Import String.
Require Import List.
Import ListNotations.

Require Import Cypher.
Require Import PropertyGraph.
Import PropertyGraph.
Import Pattern.

Module Path.

  Record t := mk {
    hops : list (vertex * edge);
    vend : vertex;
  }.

  Definition pnil (v : vertex) := mk nil v.

  Definition cons (v : vertex) (e : edge) (p : t) :=
    mk ((v, e) :: hops p) (vend p).

  Definition hd (p : t) :=
    match hops p with
    | (v, e) :: h => v
    | nil => vend p
    end.

  Definition assignment := string -> option gobj.

  Record matches_pvertex
    (g : PropertyGraph.t) (u : assignment) (v : vertex) (p : pvertex) : Prop := {
      matches_pv_name : match pv_name p with
                      | None => True
                      | Some name => u name = Some (gvertex v)
                      end;
      matches_pv_labels : pv_labels p = nil \/ exists l, In l (pv_labels p) /\ In l (vlabels g v);
      matches_pv_props : forall prop, In prop (pv_props p) -> In prop (vprops g v);
    }.

  Record matches_pedge
    (g : PropertyGraph.t) (u : assignment) (e : edge) (p : pedge) : Prop := {
      matches_pe_name : match pe_name p with
                      | None => True
                      | Some name => u name = Some (gedge e)
                      end;
      matches_pe_labels : pe_labels p = nil \/ In (elabel g e) (pe_labels p);
      matches_pe_props : forall prop, In prop (pe_props p) -> In prop (eprops g e);
    }.

  Definition matches_direction
    (g : PropertyGraph.t) (s t : vertex) (e : edge) (d : direction) : Prop :=
      match d with
      | OUT  => st g e = (s, t)
      | IN   => st g e = (t, s)
      | BOTH => st g e = (s, t) \/ st g e = (t, s)
      end.

  Reserved Notation "g , u , p '|=' pi" (at level 80, p at next level, u at next level, pi at next level, no associativity).
  Inductive matches (g : PropertyGraph.t) (u : assignment) 
  : Path.t -> Pattern.t -> Prop :=
  | matches_nil (pv : pvertex) (v : vertex) 
    : matches_pvertex g u v pv -> 
      (g, u, Path.pnil v |= Pattern.pnil pv) 
  | matches_cons (v : vertex) (e : edge) (p : Path.t)
                 (pv : pvertex) (pe : pedge) (pi : Pattern.t) 
    : matches_pvertex g u v pv ->
      matches_pedge g u e pe ->
      matches_direction g v (hd p) e (pe_dir pe) ->
      (g, u, p |= pi) ->
      (g, u, Path.cons v e p |= Pattern.cons pv pe pi)
  where "g , u , p '|=' pi" := (matches g u p pi) : type_scope.

End Path.