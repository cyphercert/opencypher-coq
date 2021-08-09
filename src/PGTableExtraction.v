From Coq Require Import List.
From Coq Require Import String.
Import ListNotations.
Require Import BinPos PeanoNat.
Import Pos.
From Coq Require Import BinNums.


From Qcert Require Import Data.Model.Data.
From Qcert Require Import DataNorm.

From OpencypherCoq Require Import PropertyGraph.
From OpencypherCoq Require Import ForeignGraphRuntime.

Import PropertyGraph.
Open Scope list_scope.
Open Scope string_scope.

Definition nat_to_z (n : nat) : Z := 
  Zpos (Pos.of_nat n).

Definition property_to_data (p : Property.t) : data :=
  match p with
  | Property.p_int n => dnat n
  | Property.p_string s => dstring s
  | Property.p_empty => dunit
  end.

Definition make_props {A} (a : A) (props : list (Property.name * (A -> Property.t))) :=
  dcoll (map (fun p : _ * _ => let (pname, pf) := p
                     in drec [ ("key", dstring pname)
                             ; ("value", property_to_data (pf a))
                             ]) props).

Definition pg_extract_vtable (pg : PropertyGraph.t) : data :=
  let extract_vertex (v : PropertyGraph.vertex) :=
      drec [ ("id", dnat (nat_to_z v))
           ; ("labels", dcoll (map (fun l => drec [("label", dstring l)]) (pg.(PropertyGraph.vlab) v)))
           ; ("properties", make_props v pg.(PropertyGraph.vprops))
           ]
  in normalize_data nil
       (dcoll (map (fun v => drec [("vertex", extract_vertex v)]) pg.(vertices))).

Definition pg_extract_etable (pg : PropertyGraph.t) : data :=
  let extract_edge (e : edge) :=
    let (src, trg) := pg.(st) e in
      drec [ ("id", dnat (nat_to_z e))
           ; ("src", dnat (nat_to_z src))
           ; ("trg", dnat (nat_to_z trg))
           ; ("type", dstring (pg.(elab) e))
           ; ("properties", make_props e pg.(eprops))
           ]
  in normalize_data nil
       (dcoll (map (fun v => drec [("edge", extract_edge v)]) pg.(edges))).
