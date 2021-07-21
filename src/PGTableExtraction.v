From Coq Require Import List.
From Coq Require Import String.
Import ListNotations.

From Qcert Require Import Data.Model.Data.

From OpencypherCoq Require Import PropertyGraph.
From OpencypherCoq Require Import ForeignGraphRuntime.

Open Scope list_scope.
Open Scope string_scope.

Definition property_to_data (p : Property.t) : data :=
  match p with
  | Property.p_int n => dnat (BinInt.Z.of_nat n)
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
      drec [ ("id", dforeign (Vertex v))
           ; ("labels", dcoll (map (fun l => drec [("label", dstring l)]) (pg.(PropertyGraph.vlab) v)))
           ; ("properties", make_props v pg.(PropertyGraph.vprops))
           ]
  in dcoll (map (fun v => drec [("vertex", extract_vertex v)]) pg.(PropertyGraph.vertices)).

Definition pg_extract_etable (pg : PropertyGraph.t) : data :=
  let extract_edge (e : PropertyGraph.edge) :=
      drec [ ("id", dforeign (Edge e))
           ; ("src", dforeign (Vertex (fst (pg.(PropertyGraph.st) e))))
           ; ("trg", dforeign (Vertex (snd (pg.(PropertyGraph.st) e))))
           ; ("type", dstring (pg.(PropertyGraph.elab) e))
           ; ("properties", make_props e pg.(PropertyGraph.eprops))
           ]
  in dcoll (map (fun v => drec [("edge", extract_edge v)]) pg.(PropertyGraph.edges)).
